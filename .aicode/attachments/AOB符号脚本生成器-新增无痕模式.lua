-- =============================================================
-- AOB 符号脚本生成器 v2.0
-- -------------------------------------------------------------
-- 一条指令进，一份常规 AOB 脚本出：
--   1. CE 里用 [找出是什么访问了/改写了这个地址]，得到那条指令
--   2. 把那一行粘进来（或选中记录后点[取代码]）
--   3. 点[生成脚本]，把脚本贴进 CE 的自动汇编窗口并勾选
--   4. 地址列表新增记录：地址填符号名 → 勾 Pointer → 偏移填提示里的值
--
-- 脚本本身只做两件事：AOB 定位这条指令；把指令执行时的基址寄存器
-- 写进符号。写值、锁定都由 CE 地址列表自己完成（改值 / 冻结）。
-- =============================================================

-- 版本标识：改了 UI/功能就顺手 +1。
-- 用户把插件丢进 CE 后，标题条右侧的徽章会显示它，
-- 这样一眼就能确认「跑的是不是刚换上的这个文件」，不用猜。
local PLUGIN_VER  = "v2.7.0-DLL"
local BUILD_STAMP = "2026-11-14"

local DEFAULT_SYM = "aob_base"
local MEMO_LINES  = {}
local form, memo, edtInsn
-- 反汇编「取代码」相关函数在文件后部定义，但 createUI 里要先引用（按钮回退 + 补装右键菜单）。
-- 这里必须提前声明为 local，否则 createUI 内的引用会解析成全局变量 → 运行时报 nil。
local getDisasmView, readDisasmSelection, disasmRegionLines, grabDisasmToMemo, addDisasmContextMenu
local lastScript  = nil
local lastDesc    = nil
local lastPlainScript = nil   -- [EXE导出] 永远明文的脚本副本；CE 内 lastScript 仍可加密，互不影响
local lastExportData  = nil   -- [EXE导出] buildScript(o) 的 o 表，导出契约的权威元数据源
-- [硬件断点版] 勾选后生成「不改游戏代码」的调试器断点脚本；此模式没有代码洞，不能导出
local lastHwbpMode   = false
local chkHwbp = nil

-- =============================================================
-- 日志
-- =============================================================
local function log(msg)
  msg = tostring(msg)
  MEMO_LINES[#MEMO_LINES + 1] = msg
  if memo then memo.Lines.Add(msg) end
end

local function logBlock(text)
  local i = 1
  while i <= #text do
    local nl = text:find("\n", i, true)
    if not nl then
      log(text:sub(i))
      return
    end
    log(text:sub(i, nl - 1))
    i = nl + 1
  end
end

-- =============================================================
-- 基础工具
-- =============================================================
local function trim(s)
  return (tostring(s):gsub("^%s+", ""):gsub("%s+$", ""))
end

local function isAttached()
  local ok, pid = pcall(getOpenedProcessID)
  return ok and type(pid) == "number" and pid ~= 0
end

local function targetIs64()
  local ok, v = pcall(targetIs64Bit)
  return ok and v == true
end

local function moduleName()
  local ok, n = pcall(function() return process end)
  if ok and type(n) == "string" and n ~= "" then return n end
  return nil
end

-- 指令可能在 DLL 里（如 Game.dll），aobscanmodule 用主程序名会扫错模块
local function moduleForAddress(addr)
  if not addr then return nil end
  -- CE 的 getNameFromAddress 对含 '-' 等字符的模块名会返回带引号的形式（如 "Tutorial-x86_64.exe"），
  -- 这里先剥掉，否则脚本里会写出 ""..."" 双层引号
  local function unq(s)
    local t = tostring(s or "")
    return (t:gsub('^"', ''):gsub('"$', ''))
  end
  local ok, s = pcall(getNameFromAddress, addr)
  if ok and type(s) == "string" then
    local n = s:match("^([^%+]+)%+")
    if n and n ~= "" then return unq(n) end
  end
  local ok2, list = pcall(enumModules)
  if ok2 and type(list) == "table" then
    local best, bestBase
    for _, m in ipairs(list) do
      local base = tonumber(m.Address)
      if base and addr >= base then
        local size = tonumber(m.Size)
        if not size or size <= 0 then
          local oks, sz = pcall(getModuleSize, m.Name)
          if oks then size = tonumber(sz) end
        end
        if not size or size <= 0 or addr < base + size then
          if not bestBase or base > bestBase then best, bestBase = m.Name, base end
        end
      end
    end
    if best then return unq(best), bestBase end
  end
  return nil
end

local function toBytesTable(t)
  if type(t) == "string" then
    local o = {}
    for i = 1, #t do o[i] = string.byte(t, i) end
    return o
  end
  return t
end

local function resolveAddr(s)
  if not s or s == "" then return nil end
  local ok, a = pcall(getAddress, s)
  if ok and type(a) == "number" and a ~= 0 then return a end
  return nil
end

local function readAt(addr, n)
  local ok, t = pcall(function() return readBytes(addr, n, true) end)
  if not ok or not t then return nil end
  t = toBytesTable(t)
  if not t or #t < n then return nil end
  return t
end

local function hexLine(bytes)
  local o = {}
  for i = 1, #bytes do o[i] = string.format("%02X", bytes[i]) end
  return table.concat(o, " ")
end

local function sanitizeSym(s)
  s = trim(s or "")
  if s == "" then return DEFAULT_SYM end
  s = s:gsub("[^%w_]", "_")
  if not s:match("^[%a_]") then s = "_" .. s end
  return s
end

-- =============================================================
-- 输入解析：CE 行 / 字节+指令 / 纯指令
-- =============================================================
local function looksLikeBytes(s)
  s = trim(s):upper()
  if s == "" then return false end
  local function tokenLen(tok)
    if tok == "??" or tok == "?" or tok == "*" then return 1 end
    if tok:match("^%x+$") and #tok % 2 == 0 then return #tok / 2 end
    return nil
  end
  if s:find("%s") then
    local n = 0
    for tok in s:gmatch("%S+") do
      local k = tokenLen(tok)
      if not k then return false end
      n = n + k
    end
    return n > 0
  end
  return #s >= 4 and s:match("^[%x%?%*]+$") ~= nil
end

-- 全角空格、不换行空格、各种横线统一成 ASCII，手敲/从网页拷的行也能解析
local function normalizeLine(s)
  s = s:gsub("\194\160", " ")
  s = s:gsub("\227\128\128", " ")
  s = s:gsub("\239\188\141", "-")
  s = s:gsub("\226\128\147", "-")
  s = s:gsub("\226\128\148", "-")
  s = s:gsub("\226\136\146", "-")
  s = s:gsub("\t", " ")
  return trim(s)
end

local function parseBytes(s)
  s = trim(s):upper()
  if s:find("%s") then s = s:gsub("%s+", " ") end
  local toks = {}
  if s:find(" ") then
    for tok in s:gmatch("%S+") do toks[#toks + 1] = tok end
  else
    if #s % 2 ~= 0 then return nil, "字节串长度应为偶数" end
    for i = 1, #s, 2 do toks[#toks + 1] = s:sub(i, i + 1) end
  end
  local nums = {}
  for _, tok in ipairs(toks) do
    if tok == "??" or tok == "?" or tok == "*" then
      nums[#nums + 1] = false
    elseif tok:match("^%x+$") and #tok % 2 == 0 then
      -- CE 64 位会把 4 字节立即数按 8 个十六进制字符一组显示（如 00080000）
      for i = 1, #tok, 2 do nums[#nums + 1] = tonumber(tok:sub(i, i + 1), 16) end
    else
      return nil, "无法识别的字节 " .. tok
    end
  end
  return nums
end

-- 按 " - " 切分；指令文本里逗号后的 "-1" 不会误切（要求前后都有空格）
local function splitByDash(line)
  local out, pos = {}, 1
  while true do
    local s, e = line:find("%s%-%s", pos)
    if not s then
      out[#out + 1] = line:sub(pos)
      return out
    end
    out[#out + 1] = line:sub(pos, s - 1)
    pos = e + 1
  end
end

-- CE 的 disassemble 不一定返回长度，但它输出的整行里有字节列，数字节最可靠
-- 只认“纯字节列”：各版 CE 的 splitDisassembledString 返回值顺序不一致，拿错一个
-- 字段就会把指令文本当字节数（"mov eax,[esi+00005560]" 能数出 5），从而把一条 6
-- 字节的指令截成 5 字节、返回点落在指令中间，游戏直接崩。
local function byteColCount(col, addr)
  if type(col) ~= "string" then return nil end
  local t = col:gsub("%s+", " "):gsub("^%s+", ""):gsub("%s+$", "")
  if t == "" or t:find("%?") then return nil end
  if t:match("^%x+$") and addr and tonumber(t, 16) == addr then return nil end
  if not t:match("^%x%x[%x%s]*$") then return nil end
  local n = 0
  for _ in t:gmatch("%x%x") do n = n + 1 end
  if n > 0 then return n end
  return nil
end

local function sizeFromDisasm(addr)
  local ok, s = pcall(disassemble, addr)
  if not ok or type(s) ~= "string" or s == "" then return nil end
  local cands = {}
  local segs = splitByDash(s)
  if #segs >= 3 then cands[#cands + 1] = segs[2] end
  local okSplit, r1, r2, r3 = pcall(splitDisassembledString, s)
  if okSplit then
    for _, v in ipairs({ r1, r2, r3 }) do
      if type(v) == "string" then cands[#cands + 1] = v end
    end
  end
  for _, c in ipairs(cands) do
    local n = byteColCount(c, addr)
    if n then return n end
  end
  return nil
end

-- 指令长度：字节列 → disassemble 第二返回值 → getInstructionSize
local function insnSize(addr)
  if not addr or addr == 0 then return nil end
  local n = sizeFromDisasm(addr)
  if n then return n end
  local ok, _, sz = pcall(disassemble, addr)
  if ok and type(sz) == "number" and sz > 0 then return sz end
  local ok2, sz2 = pcall(getInstructionSize, addr)
  if ok2 and type(sz2) == "number" and sz2 > 0 then return sz2 end
  return nil
end

-- 取开头的连续字节（支持 "89 74 8A 10"、"89748A10" 这种写法）
local function takeHexPairs(s)
  local out, pos = {}, 1
  while true do
    local a, b = s:find("^%x%x", pos)
    if not a then break end
    out[#out + 1] = s:sub(a, b)
    pos = b + 1
    local _, e = s:find("^%s*", pos)
    pos = e + 1
    if pos > #s then break end
  end
  if #out == 0 then return nil end
  return table.concat(out, " "), s:sub(pos)
end

-- 兜底：地址/字节/指令之间没空格、或减号紧贴时也能拆开
local function splitLoose(line)
  local addrText, rest = line:match("^(0[xX]%x+)%s*%-?%s*(.*)$")
  if not addrText then
    -- 64 位进程地址是 9~16 位十六进制（如 100048299、7FF6CE94D644）
    addrText, rest = line:match("^(%x%x%x%x%x%x%x%x%x+)%s*%-?%s*(.*)$")
  end
  if not addrText then
    addrText, rest = line:match("^(%x%x%x%x%x%x%x%x)%s*%-?%s*(.*)$")
  end
  if not addrText or rest == "" then return nil end
  local bStr, tail = takeHexPairs(rest)
  if not bStr then return addrText, nil, trim(rest) end
  tail = trim((tail or ""):gsub("^%-?%s*", ""))
  return addrText, bStr, (tail ~= "" and tail or nil)
end

-- 纯指令文本 → 机器码（借 CE 的汇编器写进临时内存再读回来）
local function assembleInsn(insn)
  if not isAttached() then
    return nil, "未附加进程，无法把指令文本汇编成字节；请粘贴 CE 窗口里「地址 - 字节 - 指令」整行"
  end
  local errs = {}

  -- 地址自己持有，不靠符号反查
  local okAlloc, mem = pcall(allocateMemory, 64)
  if not okAlloc then okAlloc, mem = pcall(allocateMemory, 64, 0x40) end
  if not (okAlloc and type(mem) == "number" and mem ~= 0) then
    errs[#errs + 1] = "allocateMemory " .. (okAlloc and "返回空地址" or "不可用")
  else
    local okAsm, asmRet = pcall(assemble, mem, insn)
    if not okAsm then
      errs[#errs + 1] = "assemble 报错: " .. tostring(asmRet)
    else
      -- assemble 的返回值在部分 CE 版本里是 nil，长度统一从反汇编字节列取
      local sz = insnSize(mem)
      local bytes = sz and readAt(mem, sz)
      if bytes then
        pcall(deallocateMemory, mem)
        return bytes
      end
      errs[#errs + 1] = "汇编后取不到指令长度（" .. tostring(asmRet) .. "）"
    end
    pcall(deallocateMemory, mem)
  end

  -- 退路：AA alloc 一个符号再按符号反查
  local sym = "__aob_gen_tmp"
  pcall(autoAssemble, "dealloc(" .. sym .. ")")
  local okAA, aaRet = pcall(autoAssemble, "alloc(" .. sym .. ", 64)\n" .. sym .. ":\n" .. insn)
  if not okAA then
    errs[#errs + 1] = "AA 报错: " .. tostring(aaRet)
  else
    local addr = resolveAddr(sym)
    local bytes
    if addr then
      local sz = insnSize(addr)
      bytes = sz and readAt(addr, sz)
      if not bytes then
        errs[#errs + 1] = string.format("反汇编或读取失败（地址 %X）", addr)
      end
    else
      errs[#errs + 1] = "AA 后拿不到符号地址"
    end
    pcall(autoAssemble, "dealloc(" .. sym .. ")")
    if bytes then return bytes end
  end
  return nil, "无法把指令汇编成机器码（" .. table.concat(errs, "；") .. "）: " .. insn
end

-- 返回 { addr, addrText, bytes, insn }
local function isRegName(n)
  if n:match("^[re]?[abcd]x$") or n:match("^[abcd][hl]$") then return true end
  if n:match("^[re]?[sd]i$") or n:match("^[re]?[sb]p$") then return true end
  if n:match("^r%d%d?[dwb]?$") then return true end
  if n:match("^[xy]mm%d+$") then return true end
  if n == "spl" or n == "bpl" or n == "sil" or n == "dil" then return true end
  return false
end

-- 行首是寄存器说明漏了助记符（如 r11d,[r15+03]），按 mov 补上；顺带把 mov[..] 的分隔补成空格
local function repairInsn(insn)
  local s = trim(insn)
  if s == "" then return s end
  s = s:gsub("^(%a%w*)%[", "%1 [")
  if s:match("^%[") then return "mov " .. s end
  local first = s:match("^([%a][%w]*)")
  if first and isRegName(first:lower()) then return "mov " .. s end
  return s
end

local function parseInput(raw)
  local lines = {}
  for l in (raw or ""):gmatch("[^\r\n]+") do
    local t = normalizeLine(l)
    if t ~= "" then lines[#lines + 1] = t end
  end
  if #lines == 0 then return nil, "请先粘贴指令内容" end

  -- 多行一起贴时先用含 [..] 的那一行；没有则报原来的错
  local line = lines[1]
  local skipped
  if #lines > 1 then
    for _, l in ipairs(lines) do
      if l:find("%[") then line = l break end
    end
    skipped = {}
    for _, l in ipairs(lines) do
      if l ~= line then skipped[#skipped + 1] = l end
    end
  end

  local addrText, bytesStr, insn
  local segs = splitByDash(line)
  if #segs >= 3 and looksLikeBytes(segs[2]) then
    addrText = trim(segs[1])
    bytesStr = trim(segs[2])
    insn     = trim(table.concat(segs, " - ", 3))
  elseif #segs == 2 and looksLikeBytes(segs[1]) then
    bytesStr = trim(segs[1])
    insn     = trim(segs[2])
  elseif #segs == 2 then
    -- 地址 - 指令（没有字节，稍后按指令文本汇编）
    addrText = trim(segs[1])
    insn     = trim(segs[2])
  elseif #segs == 1 and looksLikeBytes(line) then
    bytesStr = line
  else
    local a, b, i = splitLoose(line)
    if a then
      addrText, bytesStr, insn = a, b, i
    else
      insn = line
    end
  end

  if not insn or insn == "" then
    return nil, "缺少指令文本，无法确定要捕获哪个寄存器；请把「地址 - 字节 - 指令」整行一起粘贴"
  end
  insn = repairInsn(insn)

  local addr = resolveAddr(addrText)

  local bytes
  if bytesStr then
    local b, err = parseBytes(bytesStr)
    if not b then return nil, err end
    for i = 1, #b do
      if b[i] == false then
        return nil, "字节里含 ??，无法还原原指令；请粘贴游戏里显示的原始字节"
      end
    end
    bytes = b
  else
    local b, err = assembleInsn(insn)
    if not b then return nil, err end
    bytes = b
  end

  return { addr = addr, addrText = addrText, bytes = bytes, insn = insn,
           skipped = skipped }
end

-- =============================================================
-- 操作数解析：前缀 / 操作数拆分 / 寻址表达式 / 读改写分类
-- =============================================================
-- 寻址可用的基址寄存器：只有 32 位和 64 位形式（16 位不能当地址基址）
local function isBaseReg(name)
  local n = name:lower()
  if n:match("^[abcd]x$") or n:match("^[sd]i$") or n:match("^[sb]p$") then return false end
  return n:match("^e[abcd]x$") ~= nil or n:match("^r[abcd]x$") ~= nil
      or n:match("^e[sd]i$") ~= nil or n:match("^r[sd]i$") ~= nil
      or n:match("^e[sb]p$") ~= nil or n:match("^r[sb]p$") ~= nil
      or n:match("^r%d%d?$") ~= nil
      or n == "eip" or n == "rip"
end

local function is16BitReg(name)
  local n = tostring(name or ""):lower()
  return n:match("^[abcd]x$") ~= nil or n:match("^[sd]i$") ~= nil
      or n:match("^[sb]p$") ~= nil or n:match("^r%d%d?w$") ~= nil
end

-- 寄存器宽度（字节）；不是寄存器就返回 nil
local function regWidth(name)
  local n = tostring(name or ""):lower()
  if n:match("^r%d%d?b$") or n:match("^[abcd][lh]$")
     or n == "sil" or n == "dil" or n == "bpl" or n == "spl" then return 1 end
  if n:match("^r%d%d?w$") or n:match("^[abcd]x$") or n:match("^[sd]i$") or n:match("^[sb]p$") then return 2 end
  if n:match("^r%d%d?d$") or n:match("^e[abcd]x$") or n:match("^e[sd]i$") or n:match("^e[sb]p$") then return 4 end
  if n:match("^r%d%d?$") or n:match("^r[abcd]x$") or n:match("^r[sd]i$") or n:match("^r[sb]p$") then return 8 end
  if n:match("^xmm%d+$") then return 16 end
  if n:match("^ymm%d+$") then return 32 end
  if n:match("^mm%d$") then return 8 end
  if n:match("^st%d?$") then return 10 end
  return nil
end

-- 指令文本里的数字按 CE 反汇编的习惯一律当十六进制：0x10 / 10h / $10 / 10
local function parseAsmNum(s)
  s = tostring(s or ""):gsub("%s+", "")
  if s == "" then return nil end
  local v = s:match("^0[xX](%x+)$") or s:match("^%$(%x+)$")
  if v then return tonumber(v, 16) end
  local h = s:match("^(%x+)[hH]$")
  if h and h:match("^%d") then return tonumber(h, 16) end
  if s:match("^%x+$") then return tonumber(s, 16) end
  return nil
end

local PREFIX_WORDS = { lock = true, rep = true, repe = true, repz = true, repne = true,
                       repnz = true, xacquire = true, xrelease = true, bnd = true }
local SEG_WORDS = { cs = true, ds = true, es = true, ss = true, fs = true, gs = true }
local HEX_SEGS = { fs = true, gs = true }

-- 串操作没有显式 [..]，访问地址来自 rsi/rdi，抓不到具体地址
local IMPLICIT_MEM = { movs = true, movsb = true, movsw = true, movsd = true, movsq = true,
                       stos = true, stosb = true, stosw = true, stosd = true, stosq = true,
                       lods = true, lodsb = true, lodsw = true, lodsd = true, lodsq = true,
                       cmps = true, cmpsb = true, cmpsw = true, cmpsd = true, cmpsq = true,
                       scas = true, scasb = true, scasw = true, scasd = true, scasq = true,
                       xlat = true, xlatb = true, ins = true, insb = true, insw = true, insd = true,
                       outs = true, outsb = true, outsw = true, outsd = true }

local function splitInsn(text)
  local s = tostring(text or ""):gsub("%s+", " "):gsub("^%s+", ""):gsub("%s+$", "")
  local prefixes = {}
  while true do
    local w, rest = s:match("^([%a][%w]*) (.*)$")
    if not w then break end
    w = w:lower()
    if PREFIX_WORDS[w] then
      prefixes[#prefixes + 1] = w
      s = rest
    elseif SEG_WORDS[w] and rest:match("^%s*%[") then
      prefixes[#prefixes + 1] = w
      s = rest
    else
      break
    end
  end
  local mn, rest = s:match("^([%a][%w]*)%s*(.*)$")
  return { mn = (mn or ""):lower(), rest = rest or "", prefixes = prefixes }
end

local function splitOperands(text)
  local ops, buf, depth = {}, "", 0
  for i = 1, #text do
    local c = text:sub(i, i)
    if c == "[" then depth = depth + 1 end
    if c == "]" then depth = depth - 1 end
    if c == "," and depth == 0 then
      ops[#ops + 1] = buf
      buf = ""
    else
      buf = buf .. c
    end
  end
  if buf:gsub("%s", "") ~= "" then ops[#ops + 1] = buf end
  return ops
end

-- 把 [..] 里的表达式拆成带符号的项
local function splitAddrTerms(expr)
  local terms, buf, sign = {}, "", 1
  for i = 1, #expr do
    local c = expr:sub(i, i)
    if c == "+" or c == "-" then
      if buf == "" then
        if #terms > 0 then return nil, "表达式里有多余的 " .. c .. "：" .. expr end
        sign = (c == "-") and -1 or 1
      else
        terms[#terms + 1] = { sign = sign, text = buf }
        sign = (c == "-") and -1 or 1
        buf = ""
      end
    else
      buf = buf .. c
    end
  end
  if buf == "" then return nil, "表达式不完整：" .. expr end
  terms[#terms + 1] = { sign = sign, text = buf }
  return terms
end

local function buildFormula(base, index, scale, disp)
  local parts = {}
  if base then parts[#parts + 1] = base end
  if index then parts[#parts + 1] = (scale == 1) and index or (index .. "*" .. scale) end
  local s = table.concat(parts, " + ")
  if disp > 0 then
    s = (s == "") and ("0x" .. string.format("%X", disp)) or (s .. " + 0x" .. string.format("%X", disp))
  elseif disp < 0 then
    s = (s == "") and ("-0x" .. string.format("%X", -disp)) or (s .. " - 0x" .. string.format("%X", -disp))
  elseif s == "" then
    s = "0"
  end
  return s
end

-- 解析 [..] 里的寻址表达式：EA = base + index*scale + disp
local function parseAddrExpr(expr)
  local terms, terr = splitAddrTerms(expr)
  if not terms then return nil, terr end
  local plains, index, scale, disp = {}, nil, nil, 0
  for _, t in ipairs(terms) do
    local reg, sc = t.text:match("^([%a]%w*)%*(%w+)$")
    if reg then
      if t.sign < 0 then return nil, "索引不能带负号：" .. expr end
      local s = parseAsmNum(sc)
      if not s then return nil, "比例看不懂：" .. sc end
      if s ~= 1 and s ~= 2 and s ~= 4 and s ~= 8 then
        return nil, "比例只能是 1/2/4/8（这里是 " .. sc .. "）"
      end
      reg = reg:lower()
      if not isBaseReg(reg) then
        if is16BitReg(reg) then return nil, "16 位寻址（" .. reg .. "）在 32/64 位代码里没法用 lea 重算" end
        return nil, "不认识的寄存器：" .. reg
      end
      if reg == "rsp" or reg == "esp" then
        return nil, reg .. " 不能当索引寄存器（x86 没有这个编码）"
      end
      if index then return nil, "一个操作数里只能有一个 索引*比例：" .. expr end
      index, scale = reg, s
    elseif isBaseReg(t.text) then
      if #plains >= 2 then return nil, "一个操作数里最多两个寄存器：" .. expr end
      plains[#plains + 1] = t.text:lower()
    elseif is16BitReg(t.text) then
      return nil, "16 位寻址（" .. t.text .. "）不支持，请用 32/64 位寄存器那条指令"
    else
      local num = parseAsmNum(t.text)
      if not num then return nil, "看不懂表达式里的这一段：" .. t.text end
      disp = disp + t.sign * num
    end
  end

  local base = plains[1]
  if index == nil and plains[2] then index, scale = plains[2], 1 end

  if index and (base == "rip" or base == "eip" or index == "rip" or index == "eip") then
    return nil, "rip/eip 不能和 索引*比例 一起用（x86 没有这个编码）：" .. expr
  end

  local leaParts = {}
  if base then leaParts[#leaParts + 1] = base end
  if index then leaParts[#leaParts + 1] = (scale == 1) and index or (index .. "*" .. scale) end
  local leaText = table.concat(leaParts, "+")

  local kind = "reg"
  if (base and (base == "rip" or base == "eip")) or (index and (index == "rip" or index == "eip")) then
    kind = "rip"
  elseif not base and not index then
    kind = "abs"
  elseif not base then
    kind = "indexOnly"
  end

  return {
    expr = expr, kind = kind,
    base = base, index = index, scale = scale, disp = disp,
    formula = buildFormula(base, index, scale, disp),
    leaText = leaText,
    indexText = index and ((scale == 1) and index or (index .. "*" .. scale)) or nil,
  }
end

local function parseOperand(insn)
  local raw = tostring(insn or "")
  local low = raw:lower()
  local info = splitInsn(low)
  local open = low:find("[", 1, true)
  if not open then
    if IMPLICIT_MEM[info.mn] then
      return nil, "这是串操作（" .. info.mn .. "），访问地址来自 rsi/rdi 而不是 [..] 里的表达式，抓不到具体地址；换一条显式带 [..] 的指令"
    end
    return nil, "指令里没有内存操作数 [..]（这条只是寄存器之间传值，跟地址无关），请粘贴访问/改写该地址的那一条"
  end
  local close = low:find("]", open + 1, true)
  if not close then return nil, "内存操作数的方括号没闭合：" .. raw end
  local expr = low:sub(open + 1, close - 1):gsub("%s+", "")
  if expr:find("[", 1, true) or expr:find("]", 1, true) then
    return nil, "指令里不会有嵌套方括号；你粘的像是地址表达式（指针链），不是一条指令"
  end

  local seg = low:sub(1, open - 1):match("([%a]+):%s*$")
  if seg and HEX_SEGS[seg] then
    return nil, "这条指令用 " .. seg .. ": 段寻址（TEB/GS），段基址不在文本里，按线性地址记符号一定是错的；换一条普通指令"
  end

  local ast, err = parseAddrExpr(expr)
  if not ast then return nil, "[" .. expr .. "] " .. err end

  return ast
end

-- 读改写分类：内存操作数位置 + 助记符表
local RW_TEXT = { read = "只读", write = "写入", rmw = "读改写", compute = "只算地址（不访问内存）",
                  implicit = "隐式访问", other = "读" }
local READ_MN = { cmp = true, test = true, push = true, movzx = true, movsx = true, movsxd = true,
                  bt = true, call = true, jmp = true, div = true, idiv = true, mul = true, imul = true,
                  fld = true, fild = true, fadd = true, fsub = true, fmul = true, fdiv = true,
                  fcom = true, fcomp = true, fucom = true, fucomp = true,
                  fiadd = true, fisub = true, fimul = true, fidiv = true, ficom = true,
                  fxrstor = true, fldenv = true, fldcw = true }
local RMW_BOTH = { xchg = true, xadd = true, cmpxchg = true, cmpxchg8b = true, cmpxchg16b = true }
local RMW_DEST = { add = true, sub = true, adc = true, sbb = true, ["and"] = true, ["or"] = true,
                   xor = true, inc = true, dec = true, neg = true, ["not"] = true,
                   shl = true, shr = true, sar = true, sal = true, rol = true, ror = true,
                   rcl = true, rcr = true, bts = true, btr = true, btc = true }
local WRITE_MN = { fst = true, fstp = true, fist = true, fistp = true, fbstp = true,
                   fstsw = true, fnstsw = true, fxsave = true, movnti = true }
local MN_BYTES = { movq = 8, movd = 4, movss = 4, movsd = 8,
                   movups = 16, movupd = 16, movaps = 16, movapd = 16,
                   movdqu = 16, movdqa = 16, movntdq = 16, movntps = 16, movntpd = 16, lddqu = 16 }
local FLOAT_MN = { movss = true, movsd = true, fld = true, fst = true, fstp = true, fild = true,
                   fist = true, fistp = true, fadd = true, fsub = true, fmul = true, fdiv = true,
                   fcom = true }

-- 一条指令到底读还是写、访问多宽
local function insnMeta(insn)
  local low = tostring(insn or ""):lower()
  local info = splitInsn(low)
  local mn = info.mn
  local ops = splitOperands(info.rest)
  local memIdx
  for i, o in ipairs(ops) do
    if o:find("[", 1, true) then memIdx = i - 1 break end
  end

  local rw
  if mn == "lea" or mn == "nop" or mn:match("^prefetch") then
    rw = "compute"
  elseif IMPLICIT_MEM[mn] and memIdx == nil then
    rw = "implicit"
  elseif READ_MN[mn] then
    rw = "read"
  elseif RMW_BOTH[mn] then
    rw = "rmw"
  elseif RMW_DEST[mn] then
    rw = (memIdx == 0) and "rmw" or "read"
  elseif WRITE_MN[mn] then
    rw = "write"
  elseif mn:match("^set") then
    rw = "write"
  elseif memIdx ~= nil then
    rw = (memIdx == 0) and "write" or "read"
  else
    rw = "other"
  end

  local width
  if rw ~= "implicit" then
    local pw = low:match("(%a+)%s+ptr")
    if pw then
      width = ({ byte = 1, word = 2, dword = 4, qword = 8, tbyte = 10,
                 oword = 16, xmmword = 16, ymmword = 32 })[pw]
    end
    if not width then width = MN_BYTES[mn] end
    if not width then
      for i, o in ipairs(ops) do
        if (i - 1) ~= memIdx then
          for tok in o:gmatch("[%a][%w]*") do
            local w = regWidth(tok)
            if w and (not width or w > width) then width = w end
          end
        end
      end
    end
  end
  if not width then
    if mn == "push" or mn == "pop" then
      local ok, v = pcall(targetIs64)
      width = (ok and v) and 8 or 4
    else
      width = 4
    end
  end

  local typeConst
  if FLOAT_MN[mn] and width == 4 then typeConst = "vtSingle"
  elseif FLOAT_MN[mn] and width == 8 then typeConst = "vtDouble"
  elseif width == 1 then typeConst = "vtByte"
  elseif width == 2 then typeConst = "vtWord"
  elseif width == 8 then typeConst = "vtQword"
  else typeConst = "vtDword" end

  return { rw = rw, width = width, typeConst = typeConst, mn = mn, memIdx = memIdx }
end

-- 这条指令最少占几字节：1 字节操作码 + 1 字节 ModRM + SIB（有索引才要）+ 位移 + 立即数。
-- 只是下限，够用来发现“字节没粘全”：覆盖短了会把 return 落在指令中间，跳回去执行
-- 残留的半个位移字节（比如 00 = add [eax],al），游戏立刻崩。
local PREFIX_BYTES = { [0x26] = true, [0x2E] = true, [0x36] = true, [0x3E] = true, [0x64] = true,
                       [0x65] = true, [0x66] = true, [0x67] = true, [0xF0] = true, [0xF2] = true, [0xF3] = true }

local function minInsnLen(op, insn, bytes)
  local n = 2
  if bytes then
    local i = 1
    while bytes[i] and (PREFIX_BYTES[bytes[i]] or (bytes[i] >= 0x40 and bytes[i] <= 0x4F)) do
      n, i = n + 1, i + 1
    end
    if bytes[i] == 0x0F then n = n + 1 end
  end
  if op.index then n = n + 1 end
  local d = op.disp or 0
  if d ~= 0 then n = n + ((d >= -128 and d <= 127) and 1 or 4) end
  local info = splitInsn(tostring(insn or ""):lower())
  for _, o in ipairs(splitOperands(info.rest)) do
    local t = trim(o)
    if t ~= "" and not t:find("[", 1, true) and parseAsmNum(t) ~= nil then n = n + 1 end
  end
  return n
end

-- =============================================================
-- 代码字节收集：从 addr 起沿指令边界取字节，相对跳转位移打 ??
-- =============================================================
local function relMask(b1, b2)
  if b1 == 0xE8 or b1 == 0xE9 then return 2, 4 end
  if b1 == 0xEB or b1 == 0xE2 or b1 == 0xE3 or (b1 >= 0x70 and b1 <= 0x7F) then return 2, 1 end
  if b1 == 0x0F and b2 and b2 >= 0x80 and b2 <= 0x8F then return 3, 4 end
  return nil
end

-- firstBytes 是第一条指令的原始字节（不掩码）；后续指令的跳转位移掩码成 ??
-- 返回 完整字节表, 特征码串, 覆盖项列表（每项 addr/bytes/rel/text）
local function collectCode(addr, firstBytes, targetLen)
  if not addr then return nil, nil, nil end
  local bytes, toks = {}, {}
  for i = 1, #firstBytes do
    bytes[i] = firstBytes[i]
    toks[i]  = string.format("%02X", firstBytes[i])
  end
  local covered = { { addr = addr, bytes = firstBytes, rel = false } }
  local cur = addr + #firstBytes
  local guard = 0
  while #bytes < targetLen and guard < 32 do
    guard = guard + 1
    local ok, line = pcall(disassemble, cur)
    if not ok or type(line) ~= "string" then break end
    local sz = insnSize(cur)
    if not sz then break end
    local t = readAt(cur, sz)
    if not t then break end
    local mstart, mlen = relMask(t[1], t[2] or 0)
    for i = 1, sz do
      local idx = #bytes + 1
      bytes[idx] = t[i]
      if mstart and i >= mstart and i < mstart + mlen then
        toks[idx] = "??"
      else
        toks[idx] = string.format("%02X", t[i])
      end
    end
    local text
    if type(line) == "string" then
      local segs = splitByDash(line)
      if #segs >= 3 then text = trim(table.concat(segs, " - ", 3)) end
    end
    covered[#covered + 1] = { addr = cur, bytes = t, rel = mstart ~= nil, text = text }
    cur = cur + sz
  end
  return bytes, table.concat(toks, " "), covered
end

local function scanUnique(pattern, mod)
  mod = mod or moduleName()
  if mod then
    local ok, a = pcall(AOBScanModuleUnique, mod, pattern, "+X-C")
    if ok and type(a) == "number" and a ~= 0 then return a, true, 1 end
  end
  local ok2, res = pcall(AOBScan, pattern, "+X-C")
  if ok2 and res then
    local cnt = res.Count or 0
    local a = nil
    if cnt > 0 then a = tonumber(res[0], 16) end
    pcall(function() res.destroy() end)
    if cnt == 1 then return a, true, cnt end
    if cnt > 1 then return a, false, cnt end
  end
  return nil, false, 0
end

local function patternBytes(pattern)
  local n = 0
  for _ in pattern:gmatch("%S+") do n = n + 1 end
  return n
end

local function scanAll(pattern, limit)
  local hits = {}
  local ok, res = pcall(AOBScan, pattern, "+X-C")
  if not ok or not res then return hits, 0 end
  local total = res.Count or 0
  for i = 0, math.min(total, limit or 8) - 1 do
    local a = tonumber(res[i], 16)
    if a then hits[#hits + 1] = a end
  end
  pcall(function() res.destroy() end)
  return hits, total
end

-- =============================================================
-- 脚本模板
-- =============================================================
local R64 = { "rax","rbx","rcx","rdx","rsi","rdi","rbp","rsp",
              "r8","r9","r10","r11","r12","r13","r14","r15" }

-- 按“访问的大小”猜地址列表类型：交给 insnMeta，跟日志里 [类型] 保持一致
local function parseCondNum(s)
  s = tostring(s or ""):gsub("%s+", "")
  if s == "" then return nil end
  local h = s:match("^0[xX](%x+)$")
  if h then return tonumber(h, 16) end
  h = s:match("^%$(%x+)$")
  if h then return tonumber(h, 16) end
  h = s:match("^(%x+)h$")
  if h then return tonumber(h, 16) end
  if s:match("^%d+$") then return tonumber(s) end
  -- 不带前缀但含 a-f：按汇编习惯当十六进制（如 0C、1A）
  if s:match("^%x+$") and s:match("[a-fA-F]") then return tonumber(s, 16) end
  return nil
end

-- 指针条件：[模块+偏移]、[[模块+偏移]+层偏移]、[[[...]+a]+b]，逐层解引用
local function parsePtrChainOps(text)
  local ops = {}
  local parseExpr, parseRest

  parseRest = function(s)
    while s ~= "" do
      local sign = s:sub(1, 1)
      if sign ~= "+" and sign ~= "-" then
        return nil, "指针条件里有多余字符 " .. sign
      end
      local num = s:sub(2):match("^0[xX]%x+") or s:sub(2):match("^%x+")
      if not num then return nil, "指针条件里 " .. sign .. " 后面不是数字" end
      local v = tonumber(num:gsub("^0[xX]", ""), 16)
      if not v then return nil, "指针条件的偏移看不懂：" .. num end
      if sign == "-" then v = -v end
      ops[#ops + 1] = { op = "add", v = v }
      s = s:sub(2 + #num)
    end
    return true
  end

  parseExpr = function(s)
    if s == "" then return nil, "指针条件缺少地址" end
    if s:sub(1, 1) == "[" then
      local depth, close = 0, nil
      for j = 1, #s do
        local c = s:sub(j, j)
        if c == "[" then
          depth = depth + 1
        elseif c == "]" then
          depth = depth - 1
          if depth == 0 then close = j break end
        end
      end
      if not close then return nil, "指针条件里的方括号不成对" end
      local ok, err = parseExpr(s:sub(2, close - 1))
      if not ok then return nil, err end
      ops[#ops + 1] = { op = "deref" }
      return parseRest(s:sub(close + 1))
    end
    local j = 1
    while j <= #s and s:sub(j, j) ~= "+" and s:sub(j, j) ~= "-" do j = j + 1 end
    local name = s:sub(1, j - 1)
    if name == "" then return nil, "指针条件缺少地址" end
    -- 基础地址上的加减直接并进地址表达式（和先算地址再加常量等价）
    local rest = s:sub(j)
    while rest:sub(1, 1) == "+" do
      local num = rest:sub(2):match("^0[xX]%x+") or rest:sub(2):match("^%x+")
      if not num then break end
      name = name .. "+" .. num
      rest = rest:sub(2 + #num)
    end
    ops[#ops + 1] = { op = "load", expr = name }
    return parseRest(rest)
  end

  local ok, err = parseExpr(text)
  if not ok then return nil, err end
  return ops
end

local function ptrChainCode(ops, reg)
  local out = {}
  local i = 1
  if ops[i] and ops[i].op == "load" and ops[i + 1] and ops[i + 1].op == "deref" then
    out[#out + 1] = "  mov " .. reg .. ", [" .. ops[i].expr .. "]"
    i = i + 2
  elseif ops[i] and ops[i].op == "load" then
    out[#out + 1] = "  mov " .. reg .. ", " .. ops[i].expr
    i = i + 1
  end
  while i <= #ops do
    local o = ops[i]
    if o.op == "deref" then
      out[#out + 1] = "  mov " .. reg .. ", [" .. reg .. "]"
    elseif o.op == "add" then
      out[#out + 1] = string.format("  %s %s, 0x%X", o.v < 0 and "sub" or "add", reg, math.abs(o.v))
    end
    i = i + 1
  end
  return out
end

-- 条件写法：31089AE8 / [模块+偏移] / 100-200 / &0x100 / rsi=0C
local function isGpReg(name)
  local n = tostring(name or ""):lower()
  if n:match("^[xy]mm") or n:match("^mm%d") or n:match("^st%d?") then return false end
  local w = regWidth(n)
  return w == 1 or w == 2 or w == 4 or w == 8
end

local function parseOneGuard(text)
  local t = tostring(text or ""):gsub("%s+", "")
  if t == "" then return { kind = "none" } end
  if t:sub(1, 1) == "[" then
    local ops, err = parsePtrChainOps(t)
    if not ops then return nil, err end
    return { kind = "ptr", ops = ops, text = t }
  end
  local reg, rest = t:match("^(%a[%w]*)([<>=!~&].*)$")
  if reg and isGpReg(reg) then
    for _, sym in ipairs({ ">=", "<=", "==", "~=", "!=", "=", ">", "<" }) do
      if rest:sub(1, #sym) == sym then
        local rhs = rest:sub(#sym + 1)
        local lo, hi = rhs:match("^(.-)%-(.+)$")
        if lo then
          local a, b = parseCondNum(lo), parseCondNum(hi)
          if not a or not b then
            return nil, "寄存器条件里的区间看不懂（写成 rsi=1-5）"
          end
          if b < a then return nil, "寄存器区间看不懂（小的在前，如 rsi=1-5）" end
          return { kind = "reg", reg = reg:lower(), cmp = "range", v = a, v2 = b, text = t }
        end
        local v = parseCondNum(rhs)
        if not v then return nil, "寄存器条件里的数字看不懂（用 12、0xC 或 $0C）" end
        local cmp = ({ ["=="] = "=", ["~="] = "!=" })[sym] or sym
        return { kind = "reg", reg = reg:lower(), cmp = cmp, v = v, text = t }
      end
    end
  end
  local rmask, rmaskv = t:match("^(%a[%w]*)&(.+)$")
  if rmask and isGpReg(rmask) then
    local v = parseCondNum(rmaskv)
    if not v then return nil, "寄存器位掩码看不懂（写成 rsi&0x100）" end
    return { kind = "reg", reg = rmask:lower(), cmp = "&", v = v, text = t }
  end
  for _, sym in ipairs({ ">=", "<=", "==", "~=", "!=", "=", ">", "<" }) do
    if t:sub(1, #sym) == sym then
      local v = parseCondNum(t:sub(#sym + 1))
      if not v then return nil, "值条件里的数字看不懂（用 200 或 0xC8）" end
      local cmp = ({ ["=="] = "=", ["~="] = "!=" })[sym] or sym
      return { kind = "value", cmp = cmp, v = v, text = t }
    end
  end
  local mask = t:match("^&(.+)$")
  if mask then
    local v = parseCondNum(mask)
    if not v then return nil, "位掩码看不懂（写成 &0x100）" end
    return { kind = "value", cmp = "&", v = v, text = t }
  end
  local a, b = t:match("^([%w]+)%-(.+)$")
  if a and b then
    local lo, hi = parseCondNum(a), parseCondNum(b)
    if lo and hi then
      if hi < lo then return nil, "值区间看不懂（写成 100-200，小的在前）" end
      return { kind = "value", cmp = "range", v = lo, v2 = hi, text = t }
    end
  end
  local h = t:gsub("^0[xX]", "")
  if h:match("^%x+$") and tonumber(h, 16) and tonumber(h, 16) ~= 0 then
    return { kind = "addr", addr = tonumber(h, 16), text = t }
  end
  return nil, "看不出这是什么条件：填数据地址（31089AE8）、指针（[模块+偏移]）、值条件（=200 / >=100 / 100-200 / &0x100）或寄存器条件（rsi=0C / rcx!=5 / rsi&0x100）"
end

local function parseGuardText(text)
  local t = trim(tostring(text or ""))
  if t == "" then return { kind = "none" } end
  return parseOneGuard(t)
end

local function condSizeSuffix(typeConst, is64)
  local m = { vtByte = "byte", vtWord = "word", vtDword = "dword",
              vtSingle = "dword", vtQword = "qword", vtDouble = "qword" }
  return m[typeConst] or (is64 and "qword" or "dword")
end

local function valueCondCode(c, memOperand, sfx, skipLabel)
  local out = {}
  local mem = "[" .. memOperand .. "]"
  if c.cmp == "range" then
    out[#out + 1] = string.format("  cmp %s %s, #%d", sfx, mem, c.v)
    out[#out + 1] = "  jl " .. skipLabel
    out[#out + 1] = string.format("  cmp %s %s, #%d", sfx, mem, c.v2)
    out[#out + 1] = "  jg " .. skipLabel
  elseif c.cmp == "&" then
    out[#out + 1] = string.format("  test %s %s, #%d", sfx, mem, c.v)
    out[#out + 1] = "  jz " .. skipLabel
  else
    local jcc = ({ ["="] = "jne", ["!="] = "je", [">"] = "jle", [">="] = "jl",
                   ["<"] = "jge", ["<="] = "jg" })[c.cmp]
    out[#out + 1] = string.format("  cmp %s %s, #%d", sfx, mem, c.v)
    out[#out + 1] = "  " .. jcc .. " " .. skipLabel
  end
  return out
end

local function regCondCode(c, skipLabel, scratch)
  local out = {}
  local reg = c.reg
  local w = regWidth(reg) or 8
  local function cmpImm(v)
    if w == 8 and v > 0x7FFFFFFF then
      -- cmp r64 的立即数只占 32 位且带符号扩展，装不下就用空闲寄存器先装值
      out[#out + 1] = "  mov " .. scratch .. ", " .. string.format("%X", v)
      out[#out + 1] = "  cmp " .. reg .. ", " .. scratch
    else
      out[#out + 1] = string.format("  cmp %s, #%d", reg, v)
    end
  end
  if c.cmp == "range" then
    cmpImm(c.v)
    out[#out + 1] = "  jl " .. skipLabel
    cmpImm(c.v2)
    out[#out + 1] = "  jg " .. skipLabel
  elseif c.cmp == "&" then
    out[#out + 1] = string.format("  test %s, #%d", reg, c.v)
    out[#out + 1] = "  jz " .. skipLabel
  else
    local jcc = ({ ["="] = "jne", ["!="] = "je", [">"] = "jle", [">="] = "jl",
                   ["<"] = "jge", ["<="] = "jg" })[c.cmp]
    cmpImm(c.v)
    out[#out + 1] = "  " .. jcc .. " " .. skipLabel
  end
  return out
end

local function buildScript(o)
  lastExportData = o   -- [EXE导出] 保存本次生成的全部元数据（原有逻辑一行不改）
  local L = {}
  local function add(s) L[#L + 1] = s end
  local hexNums = {}
  for tok in o.hookHex:gmatch("%S+") do hexNums[#hexNums + 1] = "0x" .. tok end
  local byteCsv = table.concat(hexNums, ", ")
  local notes = {}
  -- verbose=false（精简模式）：去掉解释性注释，只留指令行与定位行；默认 true 保持原样
  local verbose = o.verbose ~= false

  -- 头部注释：指令 / 注意 / 条件说明 / 锁定 / 符号公式
  local function emitHeader()
    add("[ENABLE]")
    add("// 指令: " .. o.insn)
    if verbose then
      if o.warn then add("// 注意: " .. o.warn) end
      if o.cond.kind == "addr" then
        add("// 条件判断: 只有这次访问的地址 = 0x" .. o.condHex .. " 时才写符号（这条指令被别的对象调用时不覆盖）")
      elseif o.cond.kind == "ptr" then
        add("// 指针条件: 静态槽 " .. o.cond.text .. " 指向本次对象时才写符号（重启游戏也不用改条件）")
      elseif o.cond.kind == "value" then
        add("// 值条件: 只有访问到的值 " .. o.cond.text .. " 时才写符号（不看地址，重启后仍然有效）")
      end
      if o.latch then
        add("// 锁定: 命中一次后就固定住，后面的对象冲不掉（重启后重新启用脚本重新锁）")
      end
      add("// 符号 = 数据地址: " .. o.leaExpr .. "（push → lea → mov [符号] → pop；地址列表记录 = 符号 + 偏移 0，解引用一次就是它）")
    end
  end

  -- 符号与注入点声明：aobscan / alloc / label / registersymbol / 基址 dq / 钩子 jmp+pad
  local function emitSymbols()
    if o.offHex then
      -- 不用 {$lua} 注册符号：AA 在汇编阶段就要求符号已存在，运行时注册的符号解不出来
      add("// 定位: " .. tostring(o.module) .. "+0x" .. o.offHex .. "（固定偏移，只在 ±16 字节内匹配，保证唯一）")
      add('aobscanregion(' .. o.hookSym .. ', "' .. tostring(o.module) .. '"+' .. o.offHex
        .. ', "' .. tostring(o.module) .. '"+' .. o.offStopHex .. ', ' .. o.hookHex .. ')')
      add("registersymbol(" .. o.hookSym .. ")")
    else
      if o.module then
        add("aobscanmodule(" .. o.hookSym .. ", \"" .. o.module .. "\", " .. o.pattern .. ")")
      else
        add("aobscan(" .. o.hookSym .. ", " .. o.pattern .. ")")
      end
      add("registersymbol(" .. o.hookSym .. ")")
    end
    add("alloc(" .. o.memSym .. ", 0x100, " .. o.hookSym .. ")")
    add("label(" .. o.codeLabel .. ")")
    add("label(" .. o.retLabel .. ")")
    if o.patch then add("label(" .. o.patch.label .. ")") end
    if o.cond.kind ~= "none" or o.latch then
      add("label(" .. o.skipLabel .. ")")
    end
    if o.cond.kind == "ptr" then
      add("label(" .. o.leaLabel .. ")")
    end
    add("alloc(" .. o.baseSym .. ", 8)")
    add("registersymbol(" .. o.baseSym .. ")")
    if o.patch then
      -- 命中标记：条件没命中时不写值，避免写到上一条指令留下的旧地址（可能已释放 → 崩溃）
      -- 注意：alloc 已经声明了这个符号，再写 label() 会让 AA 报“label xxx 未定义”
      add("alloc(" .. o.patch.flag .. ", 1)")
      if o.patch.isFloat then
        -- 浮点常量：改值段用 xmm + 这个内联常量做写入/运算
        add("alloc(" .. o.patch.constLabel .. ", " .. (o.patch.width == "qword" and "8" or "4") .. ")")
      end
    end
    if o.scratch then
      add("alloc(" .. o.tmpSym .. ", 8)")
    end
    if o.cond.kind == "addr" then
      add("alloc(" .. o.guardSym .. ", 8)")
    end
    add("")
    add(o.baseSym .. ":")
    add("  dq 0")
    if o.scratch then
      add(o.tmpSym .. ":")
      add("  dq 0")
    end
    if o.cond.kind == "addr" then
      add(o.guardSym .. ":")
      add("  dq 0x" .. o.condHex)
    end
    if o.patch and o.patch.isFloat then
      add(o.patch.constLabel .. ":")
      add("  " .. (o.patch.width == "qword" and "dq " or "dd ") .. o.patch.constHex)
    end
  end

  -- 新内存块：push/lea/mov/pop + 原指令(db 或重放) + 附带改值 + 钩子 jmp + retLabel
  local function emitNewmem()
    add("")
    add(o.memSym .. ":")
    local needFlags = (o.cond.kind ~= "none") or o.latch
    local needSave = (o.scratch ~= nil)
    if needFlags then add("  push" .. o.flagSuffix) end
    if needSave then add("  mov [" .. o.tmpSym .. "], " .. o.scratch) end
    -- push 放在所有条件之前：后面每个 jne 都跳到 pop 之后，栈必须已经压过
    add("  push " .. o.pushReg)
    if o.latch then
      add("  cmp " .. o.latchSuffix .. " [" .. o.baseSym .. "], 0")
      add("  jne " .. o.skipLabel)
    end
    if o.cond.kind == "value" then
      for _, l in ipairs(o.valueCode) do add(l) end
    elseif o.cond.kind == "reg" then
      for _, l in ipairs(o.regCode) do add(l) end
    end
    if o.cond.kind == "ptr" then
      for _, l in ipairs(o.ptrCode) do add(l) end
      -- 槽里存的可能是对象基址（还要再加位移），也可能是字段地址；两条命中路径都得 lea 一次
      add("  cmp " .. o.cmpScratch .. ", " .. o.eaReg)
      add("  je " .. o.leaLabel)
      add("  lea " .. o.eaReg .. ", [" .. o.leaExpr .. "]")
      add("  cmp " .. o.cmpScratch .. ", " .. o.eaReg)
      add("  jne " .. o.skipLabel)
      add(o.leaLabel .. ":")
      add("  lea " .. o.eaReg .. ", [" .. o.leaExpr .. "]")
    else
      add("  lea " .. o.eaReg .. ", [" .. o.leaExpr .. "]")
      if o.cond.kind == "addr" then
        add("  cmp " .. o.eaReg .. ", [" .. o.guardSym .. "]")
        add("  jne " .. o.skipLabel)
      end
    end
    add("  mov [" .. o.baseSym .. "], " .. o.storeReg)
    if o.patch then add("  mov byte ptr [" .. o.patch.flag .. "], 1") end
    if o.cond.kind ~= "none" or o.latch then
      add(o.skipLabel .. ":")
      if o.patch then add("  mov byte ptr [" .. o.patch.flag .. "], 0") end
    end
    add("  pop " .. o.pushReg)
    if needSave then add("  mov " .. o.scratch .. ", [" .. o.tmpSym .. "]") end
    if needFlags then add("  pop" .. o.flagSuffix) end
    add(o.codeLabel .. ":")
    for _, ins in ipairs(o.covered) do
      local asText = ins.rel and ins.text and not ins.text:find("%?%?")
      if asText then
        add("  " .. ins.text)
      else
        -- 行尾注释给出原指令，方便照着手写；注释不参与汇编，不影响字节
        local txt = ins.text
        if not txt and ins == o.covered[1] then txt = o.insn end
        if txt then txt = tostring(txt):gsub("%s+", " "):gsub("//", "/ /") end
        add("  db " .. hexLine(ins.bytes) .. (txt and ("  // " .. txt) or ""))
        if ins.rel then
          notes[#notes + 1] = "覆盖范围里的跳转/调用指令没拿到反汇编文本，搬进 newmem 后会跳错位置，建议换一条指令"
        end
      end
    end
    -- 附带改值：原指令执行完之后再写，保证写进去的值不被这条指令本身覆盖
    if o.patch and o.patch.op then
      local p = o.patch
      add("")
      add("  // ── 附带改值: " .. p.text .. " ──")
      add("  push" .. o.flagSuffix)          -- 保护标志位：改值用到的 cmp/test/jz 不能影响后续指令
      add("  push " .. o.pushReg)
      add("  cmp byte ptr [" .. p.flag .. "], 0")   -- 本次没命中就不写（防止写到上一个对象的旧地址）
      add("  je " .. p.label)
      add("  mov " .. o.eaReg .. ", [" .. o.baseSym .. "]")
      add("  test " .. o.eaReg .. ", " .. o.eaReg)
      add("  jz " .. p.label)
      if p.isFloat then
        -- 浮点：xmm0 载入/运算/写回，常量走内联 alloc（单/双浮点）
        if p.op == "置0" then
          add("  xorps xmm0, xmm0")
          add(string.format("  mov%s [%s+0x%X], xmm0", p.pfx, o.eaReg, p.off))
        elseif p.op == "写入值" then
          add(string.format("  mov%s xmm0, [%s]", p.pfx, p.constLabel))
          add(string.format("  mov%s [%s+0x%X], xmm0", p.pfx, o.eaReg, p.off))
        else
          -- 加/减/乘：载入当前值 → 与常量运算 → 写回
          local fop = ({ ["加"] = "add", ["减"] = "sub", ["乘"] = "mul" })[p.op] or "add"
          add(string.format("  mov%s xmm0, [%s+0x%X]", p.pfx, o.eaReg, p.off))
          add(string.format("  %s%s xmm0, [%s]", fop, p.pfx, p.constLabel))
          add(string.format("  mov%s [%s+0x%X], xmm0", p.pfx, o.eaReg, p.off))
        end
      elseif p.op == "置0" then
        add(string.format("  mov %s ptr [%s+0x%X], 0", p.size, o.eaReg, p.off))
      elseif p.op == "加" then
        add(string.format("  add %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, p.value))
      elseif p.op == "减" then
        add(string.format("  sub %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, p.value))
      elseif p.op == "乘" then
        -- imul 不支持「内存目标 + 立即数」，改成 载入GPR → 乘 → 写回（push/pop 保护寄存器）
        local dreg = (o.flagSuffix == "fq") and "rax" or "eax"
        add("  push " .. dreg)
        if p.size == "byte" then
          add(string.format("  movzx %s, byte ptr [%s+0x%X]", dreg, o.eaReg, p.off))
        elseif p.size == "word" then
          add(string.format("  movzx %s, word ptr [%s+0x%X]", dreg, o.eaReg, p.off))
        else
          add(string.format("  mov %s, [%s+0x%X]", dreg, o.eaReg, p.off))
        end
        local valNum = tonumber(p.value) or 0
        if valNum > 0x7FFFFFFF or valNum < -0x80000000 then
          -- 立即数超出有符号 32 位：用另一个寄存器传乘数，走 imul reg,reg
          local mreg = (o.flagSuffix == "fq") and "rdx" or "edx"
          add("  push " .. mreg)
          add(string.format("  mov %s, %s", mreg, p.value))
          add(string.format("  imul %s, %s", dreg, mreg))
          add("  pop " .. mreg)
        else
          add(string.format("  imul %s, %s, %s", dreg, dreg, p.value))
        end
        add(string.format("  mov %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, dreg))
        add("  pop " .. dreg)
      elseif p.op == "除" then
        -- 除法：mov除数到ecx → test ecx,ecx(除零保护) → cdq → idiv ecx → 写回
        local dreg = (o.flagSuffix == "fq") and "rax" or "eax"
        local treg = (o.flagSuffix == "fq") and "rdx" or "edx"
        add("  push " .. dreg)
        add("  push " .. treg)
        add("  push ecx")
        if p.size == "byte" then
          add(string.format("  movzx %s, byte ptr [%s+0x%X]", dreg, o.eaReg, p.off))
        elseif p.size == "word" then
          add(string.format("  movzx %s, word ptr [%s+0x%X]", dreg, o.eaReg, p.off))
        else
          add(string.format("  mov %s, [%s+0x%X]", dreg, o.eaReg, p.off))
        end
        -- 除数为0时跳过写入
        add(string.format("  mov ecx, %s", p.value))
        add("  test ecx, ecx")
        add("  je " .. p.label)
        add("  cdq")
        add("  idiv ecx")
        add(string.format("  mov %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, dreg))
        add("  pop ecx")
        add("  pop " .. treg)
        add("  pop " .. dreg)
      elseif p.op == "取模" then
        -- 取模：mov除数到ecx → test ecx,ecx(除零保护) → cdq → idiv ecx → 取edx → 写回
        local dreg = (o.flagSuffix == "fq") and "rax" or "eax"
        local treg = (o.flagSuffix == "fq") and "rdx" or "edx"
        add("  push " .. dreg)
        add("  push " .. treg)
        add("  push ecx")
        if p.size == "byte" then
          add(string.format("  movzx %s, byte ptr [%s+0x%X]", dreg, o.eaReg, p.off))
        elseif p.size == "word" then
          add(string.format("  movzx %s, word ptr [%s+0x%X]", dreg, o.eaReg, p.off))
        else
          add(string.format("  mov %s, [%s+0x%X]", dreg, o.eaReg, p.off))
        end
        -- 除数为0时跳过写入
        add(string.format("  mov ecx, %s", p.value))
        add("  test ecx, ecx")
        add("  je " .. p.label)
        add("  cdq")
        add("  idiv ecx")
        add(string.format("  mov %s, edx", dreg))
        add(string.format("  mov %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, dreg))
        add("  pop ecx")
        add("  pop " .. treg)
        add("  pop " .. dreg)
      elseif p.op == "与" then
        add(string.format("  and %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, p.value))
      elseif p.op == "或" then
        add(string.format("  or %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, p.value))
      elseif p.op == "异或" then
        add(string.format("  xor %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, p.value))
      elseif p.op == "取反" then
        add(string.format("  not %s ptr [%s+0x%X]", p.size, o.eaReg, p.off))
      else
        add(string.format("  mov %s ptr [%s+0x%X], %s", p.size, o.eaReg, p.off, p.value))
      end
      add(p.label .. ":")
      add("  pop " .. o.pushReg)
      add("  pop" .. o.flagSuffix)
    end
    add("  jmp " .. o.retLabel)
    add("")
    add(o.hookSym .. ":")
    add("  jmp " .. o.memSym)
    for _ = 1, o.pad do add("  db 90") end
    add(o.retLabel .. ":")
  end

  -- 自愈：上次停用没跑完（CE 被强退/报错打断）时，注入点还留着 jmp，先写回原字节再重新定位
  local function emitSelfHeal()
    add("")
    -- 上次停用若没跑完（CE 被强退、或停用报错被打断），注入点还留着 jmp，aobscan
    -- 就再也扫不到原特征码；这里先替上一次收尾，再照常定位
    add("{$lua}")
    add("if syntaxcheck then return end")
    add("do")
    add("  local old = getAddressSafe(\"" .. o.hookSym .. "\")")
    add("  if old and old ~= 0 then")
    add("    local okr, ob = pcall(readBytes, old, 1, true)")
    add("    if okr and type(ob) == \"table\" then")
    add("      local b0 = (ob[0] ~= nil) and 0 or 1")
    add("      if ob[b0] == 0xE9 or ob[b0] == 0xEB then")
    add("        pcall(writeBytes, old, " .. byteCsv .. ")")
    add("        pcall(unregisterSymbol, \"" .. o.hookSym .. "\")")
    add("        pcall(unregisterSymbol, \"" .. o.memSym .. "\")")
    add("        pcall(unregisterSymbol, \"" .. o.baseSym .. "\")")
    if o.scratch then
      add("        pcall(unregisterSymbol, \"" .. o.tmpSym .. "\")")
    end
    if o.cond.kind == "addr" then
      add("        pcall(unregisterSymbol, \"" .. o.guardSym .. "\")")
    end
    add("        print(\"" .. o.hookSym .. " 处还留着上次的 jmp，已先写回原字节再重新定位\")")
    add("      end")
    add("    end")
    add("  end")
    add("end")
    add("{$asm}")
  end

  -- 启用时自动在地址列表加记录（同名就更新，不会重复）
  local function emitRecordBlock()
    add("")
    if verbose then
      add("// 启用时自动在地址列表加记录（同名就更新，不会重复）")
    end
    add("{$lua}")
    add("if syntaxcheck then return end")
    add("pcall(function()")
    add("  local al = getAddressList()")
    -- {$lua} 在 AA 解析前执行，此时符号还没 registersymbol；
    -- 默认 errorOnLookupFailure(true) 下把未定义符号写进 Address 会报错
    add("  local prev")
    add("  if errorOnLookupFailure then prev = errorOnLookupFailure(false) end")
    local function emitRecord(desc, symName, typ, aobSize)
      local function q(s) return "\"" .. s:gsub("\\", "\\\\"):gsub("\"", "\\\"") .. "\"" end
      add("  do")
      add("    local desc = " .. q(desc))
      add("    local mr, made = nil, false")
      add("    for i = 0, al.Count - 1 do")
      add("      local r = al.getMemoryRecord(i)")
      add("      if r.Description == desc then mr = r break end")
      add("    end")
      add("    if mr == nil then mr = al.createMemoryRecord() made = true end")
      add("    local ok = pcall(function()")
      add("      mr.Description = desc")
      add("      mr.Type = " .. typ)
      if aobSize then
        add("      pcall(function() mr.Aob.Size = " .. aobSize .. " end)")
      end
      add("      mr.Address = \"" .. symName .. "\"")
      -- 符号里存的是完整数据地址，记录得按「指针 + 偏移 0」解引用一次；
      -- 只写符号不加偏移层的话，CE 会把符号自己的地址当数据地址，值列显示成指针数字
      add("      mr.OffsetCount = 1")
      add("      mr.Offset[0] = 0")
      add("    end)")
      add("    if not ok and made then pcall(function() al.removeMemoryRecord(mr) end) end")
      add("  end")
    end
    emitRecord(o.desc, o.baseSym, o.recordType, o.recordSize)
    add("  if errorOnLookupFailure then errorOnLookupFailure(prev) end")
    add("end)")
    add("{$asm}")
  end

  -- [DISABLE] 还原：把原字节写回，再清理符号与内存
  local function emitDisable()
    add("")
    add("[DISABLE]")
    add("{$lua}")
    add("if syntaxcheck then return end")
    if verbose then
      add("-- 还原 = 把原字节写回去。首字节不是 E9/EB 时只报警告、照样写回并继续清理：")
      add("-- 这里不能 error —— error 会打断整个 [DISABLE] 段，unregistersymbol/dealloc 跟着不执行，")
      add("-- 连续启停就会卡在「钩子还在、符号还注册着」，下次勾选直接搜不到。")
    end
    add("local hk = getAddressSafe(\"" .. o.hookSym .. "\")")
    add("if hk and hk ~= 0 then")
    add("  local first")
    add("  local ok, b = pcall(readBytes, hk, 1, true)")
    add("  if ok and type(b) == \"table\" then")
    add("    local base = (b[0] ~= nil) and 0 or 1")
    add("    first = b[base]")
    add("  end")
    add("  if first and first ~= 0xE9 and first ~= 0xEB then")
    add("    print(string.format(\"" .. o.hookSym .. " 处当前字节是 %02X，不是钩子入口（E9/EB）；仍按原字节写回，若该位置被别的脚本占用请手动核对，原字节 " .. o.hookHex .. "\", first))")
    add("  end")
    if verbose then
      add("  -- 写完立刻回读：还原没成功就当场报出来，否则下次勾选时 aobscan 会因为残留的 jmp 搜不到特征码")
    end
    add("  local want = { " .. byteCsv .. " }")
    add("  pcall(writeBytes, hk, " .. byteCsv .. ")")
    add("  local ok2, b2 = pcall(readBytes, hk, #want, true)")
    add("  if ok2 and type(b2) == \"table\" then")
    add("    local base2 = (b2[0] ~= nil) and 0 or 1")
    add("    for i = 1, #want do")
    add("      if b2[base2 + i - 1] ~= want[i] then")
    add("        print(string.format(\"还原后回读不一致：第 %d 个字节是 %02X，应该是 %02X；注入点 " .. o.hookSym .. " 可能被别的脚本或游戏改过，已照原字节写回，请手动核对 " .. o.hookHex .. "\", i, b2[base2 + i - 1] or 0, want[i]))")
    add("      end")
    add("    end")
    add("  end")
    add("end")
    add("{$asm}")
    add(o.hookSym .. ":")
    add("  db " .. o.hookHex)
    add("unregistersymbol(" .. o.hookSym .. ")")
    add("unregistersymbol(" .. o.baseSym .. ")")
    add("dealloc(" .. o.memSym .. ")")
    add("dealloc(" .. o.baseSym .. ")")
    if o.patch then
      add("dealloc(" .. o.patch.flag .. ")")
      if o.patch.isFloat then add("dealloc(" .. o.patch.constLabel .. ")") end
    end
    if o.scratch then
      add("dealloc(" .. o.tmpSym .. ")")
    end
    if o.cond.kind == "addr" then
      add("dealloc(" .. o.guardSym .. ")")
    end
  end

  emitHeader()
  emitSymbols()
  emitNewmem()
  emitSelfHeal()
  if o.desc then emitRecordBlock() end
  emitDisable()
  return table.concat(L, "\n"), notes
end

-- =============================================================
-- 生成
-- =============================================================
local function verifyPasted(addr, bytes)
  local t = readAt(addr, #bytes)
  if not t then return false end
  for i = 1, #bytes do
    if bytes[i] ~= t[i] then return false end
  end
  return true
end

-- getAddress 是文档化的；getAddressSafe 未文档化但能静默失败，先试它再退回 getAddress
local function addrOf(expr)
  if type(expr) ~= "string" or expr == "" then return nil end
  local a
  pcall(function() a = getAddressSafe(expr) end)
  if type(a) ~= "number" or a == 0 then
    a = nil
    pcall(function() a = getAddress(expr) end)
  end
  if type(a) ~= "number" or a == 0 then return nil end
  return a
end

local function moduleBase(name)
  local mod = name or moduleName()
  if not mod then return nil end
  local base = addrOf(mod)  if base then return base end
  pcall(function()
    local list = enumModules()
    if not list then return end
    for _, m in ipairs(list) do
      if m.Name and m.Name:lower() == mod:lower() then
        base = m.Address
        break
      end
    end
  end)
  return base
end

local function probeScript(script)
  local out, swapped = {}, 0
  for line in (script .. "\n"):gmatch("(.-)\n") do
    local sym = line:match("^%s*aobscanmodule%s*%(%s*([%w_]+)%s*,")
      or line:match("^%s*aobscanregion%s*%(%s*([%w_]+)%s*,")
      or line:match("^%s*aobscan%s*%(%s*([%w_]+)%s*,")
    if sym then
      out[#out + 1] = "define(" .. sym .. ",0)"
      swapped = swapped + 1
    else
      out[#out + 1] = line
    end
  end
  return table.concat(out, "\n"), swapped
end

-- 生成后拿 AA 自检一遍语法：能提前暴露指令写法/条件写法的问题。
-- 只能在已附加进程时跑（aobscanmodule 要能在当前进程里解析模块），失败了也不影响已生成的脚本
-- 生成时自检开关：默认开（保持现状）；界面「生成时自检」复选框可关，关闭后不跑 AA 语法自检
local SELFCHECK_ENABLED = true

local function selfCheck(script)
  if not SELFCHECK_ENABLED then
    log("[自检] 已关闭（界面未勾选「生成时自检」）")
    return
  end
  if type(autoAssembleCheck) ~= "function" then return end
  if not isAttached() then
    log("[自检] 没附加进程，跳过 AA 语法自检")
    return
  end
  local probe, swapped = probeScript(script)
  local ok, pass, err = pcall(autoAssembleCheck, probe, true, false)
  if not ok then
    log("[自检] 自检本身没跑成（" .. tostring(pass) .. "）；脚本已生成，可以直接粘进 CE 试")
    return
  end
  if swapped > 0 then
    log(string.format("[自检] 校验副本里把 %d 行 aobscan* 换成了 define(符号,0)：校验轮不扫描，否则 alloc 的邻近地址参数会把「符号找不到」当成语法错", swapped))
  end
  if pass then
    log("[自检] AA 语法检查通过")
  else
    log("[自检] AA 报错：" .. tostring(err or "未知错误"))
    log("[提示] 自检看的是当前附加的进程和模块；报「模块/符号找不到」时先切到游戏进程再生成，其余报错按提示改条件或指令")
  end
end

-- =============================================================
-- 脚本加密（移植自「Lua/ASM 脚本加密器 v1.0」，只保留深度加密一套）
-- 相对原版改了两处：
--   1. 保留 [ENABLE] 段第一个 {$lua} 之前的内容。本工具的脚本是
--      aobscan/alloc/注入点在前、{$lua} 在后，原版默认 {$lua} 打头，
--      会把前半段整体丢掉，加密后勾选等于不扫描不注入。
--   2. autoAssemble 的长字符串定界符按内容长度选，避免正文里出现 ]==] 截断。
-- 自愈 {$lua} 会被提到 autoAssemble 之前执行：先清残留再扫描，顺序反而更正。
-- 强度说明：解包器就在脚本里，只挡「打开脚本照着抄」的人。
-- =============================================================
local function cryptTranspose(b64, key, b64chars)
    b64chars = b64chars or "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    -- 用密钥派生出偏移量 (1~63)
    local offset = 0
    for i = 1, #key do
        offset = (offset + string.byte(key, i)) & 0x3F
    end
    if offset == 0 then offset = 13 end
    -- 对每个 Base64 字符做 Caesar 偏移（在自定义字符集内循环）
    local charMap = {}
    for i = 1, 64 do
        local src = b64chars:sub(i, i)
        local dst = b64chars:sub(((i + offset - 1) % 64) + 1, ((i + offset - 1) % 64) + 1)
        charMap[src] = dst
    end
    charMap["="] = "="
    local result = {}
    for i = 1, #b64 do
        local c = b64:sub(i, i)
        result[i] = charMap[c] or c
    end
    -- 反转整个字符串
    local mid = table.concat(result)
    local rev = {}
    for i = 1, #mid do
        rev[i] = mid:sub(#mid - i + 1, #mid - i + 1)
    end
    return table.concat(rev), offset
end
local function cryptXor(text, key)
    local out = {}
    local kLen = #key
    -- 从密钥计算初始哈希（与解码器相同）
    local h = 0
    for i = 1, kLen do
        h = (h * 31 + string.byte(key, i)) & 0xFFFFFFFF
    end
    -- 用位置哈希索引密钥字节（与解码器相同）
    for i = 1, #text do
        local idx = ((h * i * 0x9E3779B9 + i) & 0xFFFFFFFF) % kLen + 1
        out[i] = string.byte(text, i) ~ string.byte(key, idx)
    end
    return out
end

local function cryptB64(bytes, b64chars)
    b64chars = b64chars or "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    local result = {}
    local n = #bytes
    for i = 1, n, 3 do
        local b0 = bytes[i]
        local b1 = bytes[i + 1] or 0
        local b2 = bytes[i + 2] or 0
        result[#result + 1] = b64chars:sub((b0 >> 2) + 1, (b0 >> 2) + 1)
        result[#result + 1] = b64chars:sub((((b0 & 3) << 4) | (b1 >> 4)) + 1, (((b0 & 3) << 4) | (b1 >> 4)) + 1)
        if i + 1 <= n then
            result[#result + 1] = b64chars:sub((((b1 & 15) << 2) | (b2 >> 6)) + 1, (((b1 & 15) << 2) | (b2 >> 6)) + 1)
        else
            result[#result + 1] = "="
        end
        if i + 2 <= n then
            result[#result + 1] = b64chars:sub((b2 & 63) + 1, (b2 & 63) + 1)
        else
            result[#result + 1] = "="
        end
    end
    return table.concat(result)
end
-- 统一编码：XOR加密 → Base64 → 转置混淆（所有依赖函数已在前方定义）
local function cryptEncode(text, key)
    -- 计算 8 字节完整性校验码 (HMAC-lite)
    local mac = ""
    local h1, h2 = 0x67452301, 0xEFCDAB89
    for i = 1, #text do
        h1 = ((h1 * 31) + string.byte(text, i)) & 0xFFFFFFFF
        h2 = h2 ~ ((h1 * 0x01000193) & 0xFFFFFFFF)
        h1 = h1 ~ (h1 >> 13)
    end
    for i = 1, #key do
        h2 = (h2 * 37 + string.byte(key, i)) & 0xFFFFFFFF
        h1 = h1 ~ ((h2 >> 7) | (h2 << 25))
    end
    -- 打包为 8 字节二进制 MAC
    for _, v in ipairs({h1, h2}) do
        for shift = 0, 24, 8 do
            mac = mac .. string.char((v >> shift) & 0xFF)
        end
    end
    -- 将 MAC 前置到明文
    local payload = mac .. text
    local xorBytes = cryptXor(payload, key)
    local b64raw = cryptB64(xorBytes)
    local b64trans, _ = cryptTranspose(b64raw, key)
    return b64trans
end
-- ============================================================
-- 伪随机数增强
do
    local seed = (os.time() or 0) * 1000000
    local clock = os.clock and os.clock() or 0
    seed = seed + math.floor(clock * 1e6)
    -- 混入进程级熵（若 CE 环境提供则利用）
    pcall(function()
        local qpc = getTickCount and getTickCount() or 0
        seed = seed ~ (qpc * 2654435761) & 0xFFFFFFFF
    end)
    math.randomseed(seed & 0x7FFFFFFF)
    -- 预热几轮避免 seed → 首个值的线性映射
    for _ = 1, 37 do math.random() end
end
local function cryptSalt(len)
    local chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    local s = {}
    for i = 1, len do
        -- 使用两次 random 混合以避免直接映射随机序列
        local r1 = math.random()
        local r2 = math.random()
        local idx = math.floor((r1 * r2 * 1e7) % #chars) + 1
        s[i] = chars:sub(idx, idx)
    end
    return table.concat(s)
end
-- ============================================================
-- 密钥派生函数：多轮哈希处理密码
-- ============================================================
local function cryptHashKey(key)
    local h = {
        0x9A48FC9E, 0x3B68CD85, 0x58AEF372, 0xA6FB553A,
        0x98D5CF3F, 0x27DC168C, 0x8D7C3AB5, 0x6BE0CD19
    }
    for i = 1, #key do
        local b = string.byte(key, i)
        local idx = ((i - 1) % 8) + 1
        h[idx] = h[idx] ~ (b << ((i % 4) * 8))
        h[idx] = (h[idx] * 0x01000193) & 0xFFFFFFFF
        local next_idx = (idx % 8) + 1
        h[next_idx] = h[next_idx] ~ ((h[idx] >> 17) | ((h[idx] << 15) & 0xFFFFFFFF))
    end
    for round = 1, 16 do
        for i = 1, 8 do
            local prev = ((i - 2) % 8) + 1
            h[i] = h[i] ~ ((h[prev] >> 11) | ((h[prev] << 21) & 0xFFFFFFFF))
            h[i] = (h[i] * 0x01000193 + round) & 0xFFFFFFFF
            h[i] = h[i] ~ (h[i] >> 16)
        end
    end
    local parts = {}
    for i = 1, 8 do
        parts[i] = string.format("%08x", h[i])
    end
    return table.concat(parts)
end
-- ============================================================
-- 脚本类型自动检测
-- ============================================================
local function cryptDetect(code)
    -- CE自定义数值类型API（registerCustomType / registerCustomTypeAutoAssembler / registerCustomTypeLua）
    -- 它们都是Lua函数调用，即使参数中包含ASM指令也必须走纯Lua路径
    if code:find("registerCustomType") then return "lua" end
    local hasLua = code:find("{%$lua}") ~= nil
            or (code:find("%[ENABLE%]") and not code:find("{%$asm}") and not code:find("alloc%("))
    local hasAsm = code:find("{%$asm}") ~= nil
            or code:find("alloc%(") ~= nil
            or code:find("readmem%(") ~= nil
    local hasCE  = code:find("%[ENABLE%]") ~= nil or code:find("%[DISABLE%]") ~= nil
    if (hasLua or hasCE) and hasAsm then return "mixed" end
    if hasAsm and not hasLua then return "asm" end
    return "lua"
end
-- ============================================================
-- 将密钥拆分为 3~5 个片段，加盐混淆后分片存储
-- ============================================================
local function cryptFragKey(key)
    local n = (#key % 3) + 3  -- 3~5 片
    local parts, pos = {}, 1
    local chunk = math.ceil(#key / n)
    for i = 1, n do
        local e = math.min(pos + chunk - 1, #key)
        parts[i] = key:sub(pos, e)
        pos = e + 1
    end
    -- 不随机打乱：保持原始顺序，组装用 KI={1,2,...,n} 即可还原完整密钥
    local indices = {}
    for i = 1, n do indices[i] = i end
    return parts, indices
end
-- ============================================================
-- 生成密钥片段声明+重组代码（共用，供 buildLoader 和 disable 区块使用）
-- ============================================================
local function cryptKeyCode(actualKey)
    local frags, indices = cryptFragKey(actualKey)
    local fragVars = {}
    for i, frag in ipairs(frags) do
        fragVars[i] = "local _K" .. i .. "=" .. string.format("%q", frag)
    end
    local idxStr = "{"
    for i, idx in ipairs(indices) do
        idxStr = idxStr .. idx
        if i < #indices then idxStr = idxStr .. "," end
    end
    idxStr = idxStr .. "}"
    local n = #frags
    local conds = {}
    for x = 1, n do
        conds[x] = "if _KI[_x]==" .. x .. " then _v=_K" .. x
    end
    return {
        fragVars = fragVars,
        idxStr = idxStr,
        n = n,
        conds = conds
    }
end
local function cryptKeyAsm(fc)
    local lines = {}
    for _, v in ipairs(fc.fragVars) do
        lines[#lines + 1] = v
    end
    lines[#lines + 1] = "local _KI=" .. fc.idxStr
    lines[#lines + 1] = 'local _KA={}'
    lines[#lines + 1] = 'for _x=1,#_KI do _KA[_x]=_G[""];_G[""]=nil; end'
    lines[#lines + 1] = 'for _x=1,#_KI do'
    lines[#lines + 1] = '  local _v'
    for x = 1, fc.n do
        local prefix = (x == 1) and '  ' or 'else'
        lines[#lines + 1] = prefix .. fc.conds[x]
    end
    lines[#lines + 1] = '  end'
    lines[#lines + 1] = '  _KA[_x]=_v'
    lines[#lines + 1] = 'end'
    lines[#lines + 1] = 'local _K=_kcomb(table.unpack(_KA))'
    return table.concat(lines, "\n")
end
-- ============================================================
-- 每次加密时动态生成不同的解码器，内部变量名随机化，入口函数名保持固定
-- ============================================================
local function cryptDecoder()
    -- 随机前缀（每次取单个字符，保证 3-5 字符长度）
    local p = ""
    local seeds = "abcdefghijklmnopqrstuvwxyz"
    for _ = 1, math.random(3, 5) do
        local idx = math.random(1, #seeds)
        p = p .. seeds:sub(idx, idx)
    end
    local t    = p .. "t"   -- _b64t
    local s    = p .. "s"   -- _b64s
    local i    = p .. "i"   -- 循环索引
    local a    = p .. "a"   -- b64 idx a
    local b    = p .. "b"   -- b64 idx b
    local c    = p .. "c"   -- b64 idx c
    local d    = p .. "d"   -- b64 idx d
    local y    = p .. "y"   -- bytes
    local x    = p .. "x"   -- while idx
    local l    = p .. "l"   -- klen
    local o    = p .. "o"   -- out
    local z    = p .. "z"   -- for idx
    local h    = p .. "h"   -- hash
    local di   = p .. "e"   -- derived idx
    local r    = p .. "r"   -- result

    -- 按顺序拼接生成解码器代码
    local code = {}
    local function L(s) code[#code+1] = s end

    -- Base64 反查表（紧凑版：空表 + for 循环填充，省去 64 行硬编码）
    L("local " .. t .. "={}")
    L("local " .. s .. '="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"')
    L("for " .. i .. "=1,64 do " .. t .. "[" .. s .. ":sub(" .. i .. "," .. i .. ")]=" .. i .. "-1 end")

    -- _dec 函数
    L("local function _dec(s,k)")
    -- 反置换：计算偏移
    L("  local " .. h .. "=0")
    L("  for " .. i .. "=1,#k do " .. h .. "=(" .. h .. "+k:byte(" .. i .. "))&0x3F end")
    L("  if " .. h .. "==0 then " .. h .. "=13 end")
    -- 构建反向映射
    L("  local " .. r .. "={}")
    L("  for " .. i .. "=1,64 do")
    L("    " .. r .. "[" .. s .. ":sub(((" .. i .. "+" .. h .. "-1)%64)+1,((" .. i .. "+" .. h .. "-1)%64)+1)]=" .. s .. ":sub(" .. i .. "," .. i .. ")")
    L("  end")
    L("  " .. r .. '["="]="="')
    -- 反转字符串并应用反向映射
    L("  local " .. o .. "={}")
    L("  for " .. i .. "=1,#s do")
    L("    local " .. c .. "=s:sub(#s-" .. i .. "+1,#s-" .. i .. "+1)")
    L("    " .. o .. "[" .. i .. "]=" .. r .. "[" .. c .. "] or " .. c)
    L("  end")
    L("  s=table.concat(" .. o .. ")")
    -- 清理并 Base64 解码
    L("  s=s:gsub(\"[^A-Za-z0-9+/]\",\"\")")
    L("  local " .. y .. "," .. x .. "={},1")
    L("  while " .. x .. "<=#s do")
    L("    local " .. a .. "=" .. t .. "[s:sub(" .. x .. "," .. x .. ")] or 0")
    L("    local " .. b .. "=" .. t .. "[s:sub(" .. x .. "+1," .. x .. "+1)] or 0")
    L("    local " .. c .. "=" .. t .. "[s:sub(" .. x .. "+2," .. x .. "+2)]")
    L("    local " .. d .. "=" .. t .. "[s:sub(" .. x .. "+3," .. x .. "+3)]")
    L("    " .. y .. "[#" .. y .. "+1]=(" .. a .. "<<2)|(" .. b .. ">>4)")
    L("    if " .. c .. " then " .. y .. "[#" .. y .. "+1]=((" .. b .. "&0xF)<<4)|(" .. c .. ">>2) end")
    L("    if " .. d .. " then " .. y .. "[#" .. y .. "+1]=((" .. c .. "&0x3)<<6)|" .. d .. " end")
    L("    " .. x .. "=" .. x .. "+4")
    L("  end")
    -- 哈希密钥流
    L("  local " .. l .. "," .. o .. "=#k,{}")
    L("  local " .. h .. "=0")
    L("  for " .. i .. "=1," .. l .. " do " .. h .. "=(" .. h .. "*31+k:byte(" .. i .. "))&0xFFFFFFFF end")
    L("  for " .. z .. "=1,#" .. y .. " do")
    L("    local " .. di .. "=((" .. h .. "*" .. z .. "*0x9E3779B9+" .. z .. ")&0xFFFFFFFF)%" .. l .. "+1")
    L("    " .. o .. "[" .. z .. "]=" .. y .. "[" .. z .. "]~(k:byte(" .. di .. "))")
    L("  end")
    L("  local " .. o .. "_r={}")
    L("  for " .. o .. "_x=1,#" .. o .. ",4000 do")
    L("    local " .. o .. "_c={}")
    L("    for " .. o .. "_y=" .. o .. "_x,math.min(" .. o .. "_x+3999,#" .. o .. ") do " .. o .. "_c[#" .. o .. "_c+1]=" .. o .. "[" .. o .. "_y] end")
    L("    " .. o .. "_r[#" .. o .. "_r+1]=string.char(table.unpack(" .. o .. "_c))")
    L("  end")
    L("  return table.concat(" .. o .. "_r)")
    L("end")

    -- _kcomb 函数
    L("local function _kcomb(...)")
    L("  local t={...}")
    L("  local r={}")
    L("  for _,v in ipairs(t) do r[#r+1]=tostring(v) end")
    L("  return table.concat(r)")
    L("end")

    return table.concat(code, "\n")
end
-- ============================================================
-- 加载器构建（密钥分片版）
-- ============================================================
-- 生成 HMAC 验证代码
local function cryptHmac()
    return [[
local _mac=_src:sub(1,8)
local _code=_src:sub(9)
local _h1,_h2=0x67452301,0xEFCDAB89
for _i=1,#_code do
  _h1=((_h1*31)+_code:byte(_i))&0xFFFFFFFF
  _h2=_h2~((_h1*0x01000193)&0xFFFFFFFF)
  _h1=_h1~(_h1>>13)
end
for _i=1,#_K do
  _h2=(_h2*37+_K:byte(_i))&0xFFFFFFFF
  _h1=_h1~((_h2>>7)|(_h2<<25))
end
local _emac={}
for _i, _v in ipairs({_h1,_h2}) do
  for _s=0,24,8 do _emac[#_emac+1]=string.char((_v>>_s)&0xFF) end
end
local _emacStr=table.concat(_emac)
if _mac~=_emacStr then error("") end
_src=_code]]
end

local function cryptLoader(b64, actualKey, fc)
    fc = fc or cryptKeyCode(actualKey)
    local clearVars = "_K"
    for i = 1, fc.n do
        clearVars = clearVars .. ", _K" .. i
    end
    clearVars = clearVars .. ", _KA, _KI, _b64t, _b64s, _dec, _kcomb"
    return cryptDecoder() .. "\n"
        .. cryptKeyAsm(fc) .. "\n"
        .. 'local _D=' .. string.format("%q", b64) .. '\n'
        .. 'local function _runDecode()\n'
        .. '  local _ok,_src=pcall(_dec,_D,_K)\n'
        .. '  if not _ok then error("") end\n'
        .. '  return _src\n'
        .. 'end\n'
        .. 'local _src=_runDecode();_runDecode=nil\n'
        .. cryptHmac() .. '\n'
        .. 'local function _runLoad()\n'
        .. '  if _src:match("^%s*%[ENABLE%]") then\n'
        .. '    return function() autoAssemble(_src) end\n'
        .. '  end\n'
        .. '  local _fn,_err=loadstring(_src)\n'
        .. '  if not _fn then error("") end\n'
        .. '  return _fn\n'
        .. 'end\n'
        .. 'local _fn=_runLoad();_runLoad=nil\n'
        .. 'local _mr=memrec or _G._ceCryptMR\n'
        .. 'local _origScript\n'
        .. 'if _mr then pcall(function() _origScript=_mr.Script end) end\n'
        .. 'do local _pmr=_G._ceCryptMR;_G._ceCryptMR=memrec;_fn();_G._ceCryptMR=_pmr end\n'
        .. 'if _mr and _origScript then\n'
        .. '  local _rok,_rerr=pcall(function() _mr.Script=_origScript end)\n'
        .. 'end\n'
        .. clearVars .. ',_runDecode,_runLoad=nil'
end
-- ============================================================
-- 长字符串分隔符安全检测
-- ============================================================
local function cryptDelim(text)
    local level = 2
    while text:find("]" .. string.rep("=", level) .. "]") do
        level = level + 1
    end
    return level
end
-- ============================================================
-- 加密函数：纯Lua脚本
-- ============================================================
local function cryptLua(code, key, addSalt)
    local salt = addSalt and cryptSalt(8) or ""
    local actualKey = cryptHashKey(key .. salt)
    -- 递增加密：输入已是 CE 脚本则拆分 ENABLE/DISABLE 分别加密
    if code:find("%[ENABLE%]") then
        local splitPos = code:find("\n%[DISABLE%]")
        if not splitPos then
            local b64 = cryptEncode(code, actualKey)
            return "[ENABLE]\n{$lua}\nif syntaxcheck then return end\n"
                .. cryptLoader(b64, actualKey)
                .. "\n[DISABLE]\n{$lua}"
        end
        local enablePart = code:sub(1, splitPos - 1)
        local afterHeader = code:find("]", splitPos)
        local disableBody = code:sub(afterHeader + 1)
        disableBody = disableBody:match("^%s*(.-)%s*$") or disableBody
        -- ENABLE payload: 加密完整第一层脚本（含 [DISABLE]），使 autoAssemble 创建完整 CE 记录
        local fullScript = enablePart .. "\n[DISABLE]\n" .. disableBody
        local enB64 = cryptEncode(fullScript, actualKey)
        -- DISABLE payload: 只加密第一层的 DISABLE 正文
        local disB64 = cryptEncode(disableBody, actualKey)
        local fc = cryptKeyCode(actualKey)
        local enableBlock = "[ENABLE]\n{$lua}\nif syntaxcheck then return end\n"
            .. cryptLoader(enB64, actualKey, fc)
        local disableBlock = "[DISABLE]\n{$lua}\n"
            .. cryptDecoder() .. "\n"
            .. cryptKeyAsm(fc) .. "\n"
            .. "local _K=_kcomb(table.unpack(_KA))\n"
            .. "local _D=" .. string.format("%q", disB64) .. "\n"
            .. 'local _ok,_src=pcall(_dec,_D,_K)\n'
            .. 'if not _ok then return end\n'
            .. cryptHmac() .. '\n'
            .. 'if not _src then return end\n'
            .. 'local _fullScript="[ENABLE]\\n".._src.."\\n[DISABLE]\\n"\n'
            .. 'autoAssemble(_fullScript)'
        return enableBlock .. "\n\n" .. disableBlock
    end
    -- 首次加密纯 Lua：简洁格式，CE 直接识别
    local b64 = cryptEncode(code, actualKey)
    return "if syntaxcheck then return end\n" .. cryptLoader(b64, actualKey)
end
-- ============================================================
-- 加密函数：纯ASM汇编脚本
-- ============================================================
local function cryptAsm(code, key, addSalt)
    local salt = addSalt and cryptSalt(8) or ""
    local actualKey = cryptHashKey(key .. salt)
    local luaPayload = "autoAssemble([==[\n[ENABLE]\n" .. code .. "\n[DISABLE]\n]==])"
    local b64 = cryptEncode(luaPayload, actualKey)
    return "[ENABLE]\n{$lua}\nif syntaxcheck then return end\n"
        .. cryptLoader(b64, actualKey)
        .. "\n[DISABLE]\n{$lua}"
end
-- ============================================================
-- 加密函数：混合脚本（Lua + ASM）
-- ============================================================
local function cryptMixed(code, key, addSalt)
    local salt = addSalt and cryptSalt(8) or ""
    local actualKey = cryptHashKey(key .. salt)
    local enableBody, disableRaw = code:match("%[ENABLE%](.-)\n%[DISABLE%](.*)")
    if not enableBody then
        return cryptLua(code, key, addSalt)
    end
    local disableBody = disableRaw:gsub("\n{%s*\n[/%\"%dAa].-}%s*$", "")
    disableBody = disableBody:match("^(.-)%s*$") or disableBody
    local prefixRaw, luaCode, asmBody = enableBody:match("^(.-){%$lua}(.-){%$asm}(.*)")
    local enablePrefix = prefixRaw or ""
    if not luaCode then
        local l2, a2 = enableBody:match("{%$lua}(.-){%$asm}(.*)")
        if l2 then luaCode, asmBody = l2, a2; enablePrefix = "" end
    end
    enablePrefix = enablePrefix:match("^%s*(.-)%s*$") or enablePrefix
    local ctxId = "_ceCtx_" .. cryptSalt(10)
    local enableLuaCode = luaCode or enableBody
    local declaredLocals = {}
    for varName in enableLuaCode:gmatch("local%s+(%w+)%s*=%s*{%s*}") do
        declaredLocals[#declaredLocals + 1] = varName
    end
    local sharedLocals = {}
    for _, name in ipairs(declaredLocals) do
        if disableBody:find("%f[%w]" .. name .. "%f[%W]") then
            sharedLocals[#sharedLocals + 1] = name
        end
    end
    local ctxFields = {"memrec = memrec"}
    for _, v in ipairs(sharedLocals) do
        ctxFields[#ctxFields + 1] = "['" .. v .. "'] = " .. v
    end
    local ctxSaveCode = "\n-- [脚本加密] 为禁用区块保存上下文\n_G['" .. ctxId .. "'] = { " .. table.concat(ctxFields, ", ") .. " }\n"
    local ctxRestoreLines = {
        "local _ctx = _G['" .. ctxId .. "'] or {}",
        "memrec = _ctx.memrec or memrec"
    }
    for _, v in ipairs(sharedLocals) do
        ctxRestoreLines[#ctxRestoreLines + 1] = v .. " = _ctx['" .. v .. "']"
    end
    local ctxRestoreCode = "\n-- [脚本加密] 从启用区块恢复上下文\ndo " .. table.concat(ctxRestoreLines, "; ") .. " end\n"
    local ctxCleanupCode = "\n{$lua}\n_G['" .. ctxId .. "'] = nil\n{$asm}\n"
    local allocatedSymbols = {}
    for sym in enableBody:gmatch("%f[%w]alloc%(%s*(%w+)%s*,") do
        local found = false
        for _, s in ipairs(allocatedSymbols) do if s == sym then found = true; break end end
        if not found then allocatedSymbols[#allocatedSymbols + 1] = sym end
    end
    local registeredSymbols = {}
    for content in enableBody:gmatch("%f[%w]registersymbol%(([^)]+)%)") do
        local trimmed = content:match("^%s*(.-)%s*$") or content
        if not trimmed:find(",") then
            for sym in trimmed:gmatch("%w+") do
                local found = false
                for _, s in ipairs(registeredSymbols) do if s == sym then found = true; break end end
                if not found then registeredSymbols[#registeredSymbols + 1] = sym end
            end
        end
    end
    local unregisteredAllocs = {}
    for _, a in ipairs(allocatedSymbols) do
        local isReg = false
        for _, r in ipairs(registeredSymbols) do if r == a then isReg = true; break end end
        if not isReg then unregisteredAllocs[#unregisteredAllocs + 1] = a end
    end
    local memrecRecovery = "local memrec = memrec or _G._ceCryptMR"
    local enablePayload
    if luaCode then
        local trimmedLua = luaCode:match("^%s*(.-)%s*$") or luaCode
        local trimmedAsm = asmBody:match("^%s*(.-)%s*$") or asmBody
        local luaEndsWithLongStr = trimmedLua:match("%]%]%s*$") or trimmedLua:match("%]%=+%]%s*$")
        local luaHasReturn = trimmedLua:find("%breturn%s")
        local luaGeneratesAsm = luaEndsWithLongStr and luaHasReturn
        if luaGeneratesAsm then
            local augmentedBody = enableBody:match("^%s*(.-)%s*$") or enableBody
            if #unregisteredAllocs > 0 then
                local extraRegs = {}
                for _, s in ipairs(unregisteredAllocs) do
                    extraRegs[#extraRegs + 1] = "registersymbol(" .. s .. ")"
                end
                augmentedBody = augmentedBody .. "\n" .. table.concat(extraRegs, "\n")
            end
            local delimLevel = cryptDelim(augmentedBody)
            local delimOpen  = "[" .. string.rep("=", delimLevel) .. "["
            local delimClose = "]" .. string.rep("=", delimLevel) .. "]"
            enablePayload = memrecRecovery .. "\n"
                .. ctxSaveCode
                .. "local _r=autoAssemble(" .. delimOpen .. "\n"
                .. augmentedBody .. "\n"
                .. delimClose .. ")"
        else
            local augmentedAsm = trimmedAsm
            if #unregisteredAllocs > 0 then
                local extraRegs = {}
                for _, s in ipairs(unregisteredAllocs) do
                    extraRegs[#extraRegs + 1] = "registersymbol(" .. s .. ")"
                end
                augmentedAsm = augmentedAsm .. "\n" .. table.concat(extraRegs, "\n")
            end
            local asmBlock = augmentedAsm
            if enablePrefix ~= "" then asmBlock = enablePrefix .. "\n" .. asmBlock end
            local dLevel = cryptDelim(asmBlock)
            local dOpen  = "[" .. string.rep("=", dLevel) .. "["
            local dClose = "]" .. string.rep("=", dLevel) .. "]"
            enablePayload = memrecRecovery .. "\n"
                .. trimmedLua .. "\n"
                .. ctxSaveCode
                .. "local _r=autoAssemble(" .. dOpen .. "\n[ENABLE]\n" .. asmBlock .. "\n[DISABLE]\n" .. dClose .. ")"
        end
    else
        local augmentedEnable = enableBody:match("^%s*(.-)%s*$") or enableBody
        if #unregisteredAllocs > 0 then
            local extraRegs = {}
            for _, s in ipairs(unregisteredAllocs) do
                extraRegs[#extraRegs + 1] = "registersymbol(" .. s .. ")"
            end
            augmentedEnable = augmentedEnable .. "\n" .. table.concat(extraRegs, "\n")
        end
        local delimLevel = cryptDelim(augmentedEnable)
        local dOpen  = "[" .. string.rep("=", delimLevel) .. "["
        local dClose = "]" .. string.rep("=", delimLevel) .. "]"
        enablePayload = memrecRecovery .. "\n"
            .. "local _r=autoAssemble(" .. dOpen .. "\n"
            .. "[ENABLE]\n"
            .. augmentedEnable .. "\n"
            .. "[DISABLE]\n"
            .. dClose .. ")"
    end
    local enB64 = cryptEncode(enablePayload, actualKey)
    local fc = cryptKeyCode(actualKey)  -- 密钥分片只生成一次
    local enableOut = "[ENABLE]\n{$lua}\nif syntaxcheck then return end\n" .. cryptLoader(enB64, actualKey, fc)
    local function expandWildcards(body)
        local out = body
        if #allocatedSymbols > 0 then
            local deallocExpanded = {}
            for _, s in ipairs(allocatedSymbols) do deallocExpanded[#deallocExpanded + 1] = "dealloc(" .. s .. ")" end
            out = out:gsub("[ \t]*dealloc%(%s*%*%s*%)[ \t]*", table.concat(deallocExpanded, "\n") .. "\n")
        end
        local allSyms = {}
        local seen = {}
        for _, s in ipairs(allocatedSymbols) do if not seen[s] then allSyms[#allSyms + 1] = s; seen[s] = true end end
        for _, s in ipairs(registeredSymbols) do if not seen[s] then allSyms[#allSyms + 1] = s; seen[s] = true end end
        if #allSyms > 0 then
            local unregExpanded = {}
            for _, s in ipairs(allSyms) do unregExpanded[#unregExpanded + 1] = "unregistersymbol(" .. s .. ")" end
            out = out:gsub("[ \t]*unregistersymbol%(%s*%*%s*%)[ \t]*", table.concat(unregExpanded, "\n") .. "\n")
        end
        return out
    end
    local expandedDisableBody = expandWildcards(disableBody)
    local disableHasLua = expandedDisableBody:find("{%$lua}") ~= nil
    if disableHasLua then
        expandedDisableBody = expandedDisableBody:gsub("({%$lua})", "%1" .. ctxRestoreCode, 1)
        expandedDisableBody = expandedDisableBody:match("^(.-)%s*$") .. ctxCleanupCode
    end
    local disablePayload
    local keyFragCode = cryptKeyAsm(fc)  -- 复用 ENABLE 的密钥分片
    if disableHasLua then
        local disBodyB64 = cryptEncode(expandedDisableBody, actualKey)
        disablePayload =
            cryptDecoder() .. "\n"
            .. keyFragCode .. "\n"
            .. "local _DB=" .. string.format("%q", disBodyB64) .. "\n"
            .. 'local _ok2,_src=pcall(_dec,_DB,_K)\n'
            .. 'if not _ok2 then return end\n'
            .. cryptHmac() .. '\n'
            .. 'if not _src then return end\n'
            .. 'local _fullScript="[ENABLE]\\n".._src.."\\n[DISABLE]\\n"\n'
            .. 'autoAssemble(_fullScript)\n'
            .. '_K,_DB,_src,_fullScript=nil'
    else
        local disableLuaParts = {}
        local trimmedDisable = expandedDisableBody:match("^%s*(.-)%s*$") or expandedDisableBody
        for label, hexBytes in trimmedDisable:gmatch("(%w+):%s*\n%s*db%s+([%x%s]+)") do
            local byteList = {}
            for hex in hexBytes:gmatch("%x+") do
                byteList[#byteList + 1] = "0x" .. hex
            end
            if #byteList > 0 then
                disableLuaParts[#disableLuaParts + 1] = 'do'
                disableLuaParts[#disableLuaParts + 1] = '  local _addr = getAddressSafe("' .. label .. '")'
                disableLuaParts[#disableLuaParts + 1] = '  if _addr then'
                disableLuaParts[#disableLuaParts + 1] = '    writeBytes(_addr, ' .. table.concat(byteList, ', ') .. ')'
                disableLuaParts[#disableLuaParts + 1] = '  end'
                disableLuaParts[#disableLuaParts + 1] = 'end'
            end
        end
        for label, src, len in trimmedDisable:gmatch("(%w+):%s*\n%s*readmem%((%w+)%s*,%s*(%d+)%)") do
            disableLuaParts[#disableLuaParts + 1] = 'do'
            disableLuaParts[#disableLuaParts + 1] = '  local _dst = getAddressSafe("' .. label .. '")'
            disableLuaParts[#disableLuaParts + 1] = '  local _src = getAddressSafe("' .. src .. '")'
            disableLuaParts[#disableLuaParts + 1] = '  if _dst and _src then'
            disableLuaParts[#disableLuaParts + 1] = '    local _bytes = readBytes(_src, ' .. len .. ', true)'
            disableLuaParts[#disableLuaParts + 1] = '    if _bytes then writeBytes(_dst, _bytes) end'
            disableLuaParts[#disableLuaParts + 1] = '  end'
            disableLuaParts[#disableLuaParts + 1] = 'end'
        end
        local allSyms = {}
        local seenSyms = {}
        for _, s in ipairs(allocatedSymbols) do if not seenSyms[s] then allSyms[#allSyms + 1] = s; seenSyms[s] = true end end
        for _, s in ipairs(registeredSymbols) do if not seenSyms[s] then allSyms[#allSyms + 1] = s; seenSyms[s] = true end end
        if #allocatedSymbols > 0 then
            disableLuaParts[#disableLuaParts + 1] = 'local _deallocAddrs = {}'
            for _, s in ipairs(allocatedSymbols) do
                disableLuaParts[#disableLuaParts + 1] = '_deallocAddrs["' .. s .. '"] = getAddressSafe("' .. s .. '")'
            end
        end
        for _, s in ipairs(allSyms) do
            disableLuaParts[#disableLuaParts + 1] = 'pcall(function() unregisterSymbol("' .. s .. '") end)'
        end
        if #allocatedSymbols > 0 then
            for _, s in ipairs(allocatedSymbols) do
                disableLuaParts[#disableLuaParts + 1] = 'do'
                disableLuaParts[#disableLuaParts + 1] = '  local _addr = _deallocAddrs["' .. s .. '"]'
                disableLuaParts[#disableLuaParts + 1] = '  if _addr then deAlloc(_addr) end'
                disableLuaParts[#disableLuaParts + 1] = 'end'
            end
        end
        disablePayload = table.concat(disableLuaParts, "\n")
    end
    local disB64 = cryptEncode(disablePayload, actualKey)
    local disableOut = "[DISABLE]\n{$lua}\n"
        .. cryptDecoder() .. "\n"
        .. keyFragCode .. "\n"
        .. "local _D=" .. string.format("%q", disB64) .. "\n"
        .. 'local _ok,_src=pcall(_dec,_D,_K)\n'
        .. 'if not _ok then return end\n'
        .. cryptHmac() .. '\n'
        .. 'if not _src then return end\n'
        .. 'if _src:match("^%s*%[ENABLE%]") then\n'
        .. '  autoAssemble(_src)\n'
        .. 'else\n'
        .. '  local _fn,_err=loadstring(_src)\n'
        .. '  if not _fn then return end\n'
        .. '  local _mr=memrec or _G._ceCryptMR\n'
        .. '  local _origScript\n'
        .. '  if _mr then pcall(function() _origScript=_mr.Script end) end\n'
        .. '  do local _pmr=_G._ceCryptMR;_G._ceCryptMR=memrec;_fn();_G._ceCryptMR=_pmr end\n'
        .. '  if _mr and _origScript then pcall(function() _mr.Script=_origScript end) end\n'
        .. 'end\n'
        .. '_K,_D,_fn,_src=nil'
    return enableOut .. "\n\n" .. disableOut
end
-- ============================================================
-- 主加密调度函数
-- ============================================================
local function cryptBuild(code, key, addSalt)
    local scriptType = cryptDetect(code)
    if scriptType == "mixed" then
        return cryptMixed(code, key, addSalt), scriptType
    elseif scriptType == "asm" then
        return cryptAsm(code, key, addSalt), scriptType
    else
        return cryptLua(code, key, addSalt), scriptType
    end
end
-- ============================================================
local CRYPT_CHARS = "abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ23456789"
local function cryptRandomKey(n)
  n = n or 16
  local t = {}
  for i = 1, n do
    local r = math.random(#CRYPT_CHARS)
    t[i] = CRYPT_CHARS:sub(r, r)
  end
  return table.concat(t)
end

-- 返回密文脚本；失败返回 nil, 原因
local function cryptScript(code, key, addSalt)
  if not code or code == "" then return nil, "脚本是空的" end
  local ok, res = pcall(cryptBuild, code, key, addSalt)
  if not ok then return nil, tostring(res) end
  if type(res) ~= "string" or res == "" then return nil, "加密结果是空的" end
  return res
end
-- =============================================================
-- 硬件断点版（不改游戏代码）：靠 CE 调试器的执行断点取寄存器
-- -------------------------------------------------------------
-- 与 inline 版的区别：
--   * 不写注入点、没有 alloc/代码洞、没有 jmp 回跳
--   * 定位与字节校验在脚本启用时由 Lua 自己做（getAddressSafe / AOBScanModuleUnique）
--   * 符号槽用 allocateMemory + registerSymbol 建，回调里 writeQword 写入
--   * 必须 CE 调试器开着；每次命中会暂停全部线程再继续
-- =============================================================

-- 寄存器名 → Lua 取值片段（CE 命中时把值放在 RAX/RBX… 这些全局里）
local function luaRegToken(name, is64)
  local n = tostring(name or ""):lower()
  if n == "" then return nil end
  local parent, mask, shift
  local r, suf = n:match("^(r%d%d?)([dwb]?)$")
  if r then
    parent = r:upper()
    if suf == "d" then mask = 0xFFFFFFFF
    elseif suf == "w" then mask = 0xFFFF
    elseif suf == "b" then mask = 0xFF end
  else
    local p1, l1 = n:match("^([re]?)([abcd])x$")
    local p2, l2 = n:match("^([re]?)([sd])i$")
    local p3, l3 = n:match("^([re]?)([sb])p$")
    local e4, l4 = n:match("^([abcd])([lh])$")
    if l1 then
      parent = "R" .. l1:upper() .. "X"
      if p1 == "e" then mask = 0xFFFFFFFF elseif p1 == "" then mask = 0xFFFF end
    elseif l2 then
      parent = "R" .. l2:upper() .. "I"
      if p2 == "e" then mask = 0xFFFFFFFF elseif p2 == "" then mask = 0xFFFF end
    elseif l3 then
      parent = "R" .. l3:upper() .. "P"
      if p3 == "e" then mask = 0xFFFFFFFF elseif p3 == "" then mask = 0xFFFF end
    elseif l4 then
      parent = "R" .. l4:upper() .. "X"
      mask = 0xFF
      if l4:lower() == "h" then shift = 8 end
    elseif n == "sil" then parent, mask = "RSI", 0xFF
    elseif n == "dil" then parent, mask = "RDI", 0xFF
    elseif n == "bpl" then parent, mask = "RBP", 0xFF
    elseif n == "spl" then parent, mask = "RSP", 0xFF end
  end
  if not parent then return nil end
  if not is64 then
    -- 32 位进程：CE 只给 EAX… 这些全局，且寄存器本身就是 32 位
    local map32 = { RAX = "EAX", RBX = "EBX", RCX = "ECX", RDX = "EDX",
                    RSI = "ESI", RDI = "EDI", RBP = "EBP", RSP = "ESP" }
    parent = map32[parent] or parent
    mask, shift = nil, nil
  end
  local base = string.format('_R("%s")', parent)
  if shift then return string.format("((%s >> %d) & 0x%X)", base, shift, mask) end
  if mask then return string.format("(%s & 0x%X)", base, mask) end
  return base
end

-- 把反汇编表达式（如 "rbx + 0x800" / "rbx + rsi*8 + 0x20"）换成 Lua 可算的表达式
local function hwbpExprLua(expr, is64)
  return (tostring(expr or "0"):gsub("(%a[%w]*)", function(w)
    local frag = luaRegToken(w, is64)
    return frag or w
  end))
end

local function hwbpReplace(s, from, to)
  local out, pos = {}, 1
  while true do
    local a, b = s:find(from, pos, true)
    if not a then out[#out + 1] = s:sub(pos) break end
    out[#out + 1] = s:sub(pos, a - 1)
    out[#out + 1] = to
    pos = b + 1
  end
  return table.concat(out)
end

local HWBP_TPL = [==[
[ENABLE]
{$lua}
if syntaxcheck then return end
-- ==== AOB 硬件断点版（不改游戏代码）====
-- 指令：@@INSN@@
-- 模块：@@MODULE@@    特征码：@@PATTERN@@    RVA：@@RVA_TXT@@
-- 说明：用 CE 调试器的执行断点取寄存器；CE 的调试器必须保持开启
--       脚本启用时会自己尝试启动调试器（VEH），已经开着则不动
--       每次命中都会暂停全部线程再继续，高频指令会明显卡顿
--       硬件断点只有 4 个槽位，CE 自己和其它脚本也会占用
--       本模式没有代码洞，不能导出独立 EXE / DLL
-- 用法：勾选本脚本 → 游戏执行一次这条指令 → 地址列表里的 @@SYM@@ 就有值了
do
  local SYM   = "@@SYM@@"
  local MODN  = "@@MODULE@@"
  local PAT   = "@@PATTERN@@"
  local RVA   = @@RVA@@
  local ORIG  = { @@ORIGBYTES@@ }
  local LATCH = @@LATCH@@
  local IPN   = "@@IPNAME@@"

  local function _R(n)
    local v = _G[n]
    if type(v) ~= "number" then return 0 end
    return v
  end
  local function _EA()
    return @@EXPR@@
  end

  -- 1) 模块基址
  local base = getAddressSafe(MODN)
  if not base or base == 0 then
    error("找不到模块 " .. MODN .. "：确认 CE 已经附加到游戏进程")
  end

  -- 2) 定位指令：固定偏移优先（顺带校验原字节），不行再按特征码扫
  local addr
  if RVA > 0 then
    local cand = base + RVA
    local okb, bytes = pcall(readBytes, cand, #ORIG, true)
    if okb and type(bytes) == "table" then
      local b0 = (bytes[0] ~= nil) and 0 or 1
      local same = true
      for i = 1, #ORIG do
        if bytes[b0 + i - 1] ~= ORIG[i] then same = false break end
      end
      if same then addr = cand end
    end
  end
  if not addr then
    local hit = AOBScanModuleUnique(MODN, PAT, "+X-C")
    if type(hit) ~= "number" or hit == 0 then
      error("特征码在 " .. MODN .. " 里没有唯一命中：游戏可能更新了，请重新生成")
    end
    addr = hit
  end

  -- 3) 符号槽：地址列表记录用「符号 + 偏移 0」，和 inline 版一致
  local slot = allocateMemory(8)
  if not slot or slot == 0 then error("allocateMemory 失败") end
  writeQword(slot, 0)
  registerSymbol(SYM, slot)

  -- 4) 调试器 + 执行断点（硬件断点，不改代码）
  if not debug_isDebugging() then
    local okd = pcall(debugProcess, 2)   -- 2 = VEH 调试器
    if not okd or not debug_isDebugging() then
      unregisterSymbol(SYM)
      deallocateMemory(slot)
      error("CE 调试器启动失败：先在 CE 里手动开调试器（Debug → Start Debugging）再勾本脚本")
    end
  end
  local method = bpmDebugRegister
  if method == nil then
    unregisterSymbol(SYM)
    deallocateMemory(slot)
    error("这个 CE 版本没有暴露 bpmDebugRegister，硬件断点方式不可用")
  end
  local trig = bptExecute or 1
  local okbp, bperr = pcall(debug_setBreakpoint, addr, 1, trig, method)
  if not okbp then
    unregisterSymbol(SYM)
    deallocateMemory(slot)
    error("设置硬件断点失败：" .. tostring(bperr))
  end

  -- 5) 命中回调：只处理我们这条地址，其它断点交回上一个回调
  local prev = debugger_onBreakpoint
  local mine
  local failed = false
  mine = function()
    if _R(IPN) ~= addr then
      if prev then return prev() end
      return 0
    end
    -- 取值出错也必须继续，绝不能把游戏卡在断点上
    local okv, v = pcall(_EA)
    if okv and type(v) == "number" and v ~= 0 then
      if LATCH then
        if readQword(slot) == 0 then writeQword(slot, v) end
      else
        writeQword(slot, v)
      end
    elseif not okv and not failed then
      failed = true
      print("[HWBP] 取值表达式出错（只报一次）：" .. tostring(v))
    end
    debug_continueFromBreakpoint(co_run)
    return 1
  end
  debugger_onBreakpoint = mine

  local st = _G.__AOB_HWBP or {}
  _G.__AOB_HWBP = st
  st[SYM] = { addr = addr, slot = slot, mine = mine, prev = prev }
  print(string.format("[HWBP] %s 已挂钩 0x%X（不改代码，调试器断点）", SYM, addr))
end
{$asm}

{$lua}
if syntaxcheck then return end
-- 自动在地址列表加记录（同名就更新，不重复建；符号已在上个 {$lua} 块注册好）
pcall(function()
  local al = getAddressList()
  local prev
  if errorOnLookupFailure then prev = errorOnLookupFailure(false) end
  do
    local desc = "@@DESC@@"
    local mr, made = nil, false
    for i = 0, al.Count - 1 do
      local r = al.getMemoryRecord(i)
      if r.Description == desc then mr = r break end
    end
    if mr == nil then mr = al.createMemoryRecord() made = true end
    local ok = pcall(function()
      mr.Description = desc
      mr.Type = @@RECTYPE@@
      @@AOB_SIZE@@
      mr.Address = "@@SYM@@"
      mr.OffsetCount = 1
      mr.Offset[0] = 0
    end)
    if not ok and made then pcall(function() al.removeMemoryRecord(mr) end) end
  end
  if errorOnLookupFailure then errorOnLookupFailure(prev) end
end)
{$asm}

[DISABLE]
{$lua}
if syntaxcheck then return end
-- 摘断点 → 还原上一个回调 → 注销符号 → 释放槽
do
  local SYM = "@@SYM@@"
  local st = _G.__AOB_HWBP
  local e = st and st[SYM]
  if e then
    pcall(debug_removeBreakpoint, e.addr)
    if debugger_onBreakpoint == e.mine then debugger_onBreakpoint = e.prev end
    st[SYM] = nil
  end
  local slot = getAddressSafe(SYM)
  pcall(unregisterSymbol, SYM)
  if slot and slot ~= 0 then pcall(deallocateMemory, slot) end
  print("[HWBP] " .. SYM .. " 已摘除")
end
{$asm}
]==]

-- 返回脚本文本
local function buildHwbpScript(p)
  local s = HWBP_TPL
  s = hwbpReplace(s, "@@INSN@@", tostring(p.insn or ""))
  s = hwbpReplace(s, "@@MODULE@@", tostring(p.module or ""))
  s = hwbpReplace(s, "@@PATTERN@@", tostring(p.pattern or ""))
  s = hwbpReplace(s, "@@RVA@@", string.format("0x%X", p.rva or 0))
  s = hwbpReplace(s, "@@RVA_TXT@@", (p.rva and p.rva > 0) and string.format("0x%X", p.rva) or "-（用特征码）")
  s = hwbpReplace(s, "@@SYM@@", tostring(p.baseSym or "aob_base"))
  s = hwbpReplace(s, "@@DESC@@", tostring(p.desc or p.baseSym or "aob_base"))
  s = hwbpReplace(s, "@@ORIGBYTES@@", tostring(p.origHex or ""))
  s = hwbpReplace(s, "@@LATCH@@", p.latch and "true" or "false")
  s = hwbpReplace(s, "@@IPNAME@@", p.is64 and "RIP" or "EIP")
  s = hwbpReplace(s, "@@EXPR@@", tostring(p.exprLua or "0"))
  s = hwbpReplace(s, "@@RECTYPE@@", tostring(p.recordType or "vtDword"))
  if p.recordSize then
    s = hwbpReplace(s, "@@AOB_SIZE@@", "pcall(function() mr.Aob.Size = " .. tostring(p.recordSize) .. " end)")
  else
    s = hwbpReplace(s, "@@AOB_SIZE@@", "")
  end
  return s
end

-- =============================================================
-- 主生成流程
-- =============================================================

local function generate(raw, symInput, useOffset, descInput, guardInput, latchInput, semInput, encryptOn, patchInput, verboseInput, hwbpInput)
  if memo then memo.Lines.Clear() end
  MEMO_LINES = {}
  lastScript = nil
  lastDesc = nil

  local cond, condErr = parseGuardText(guardInput)
  if not cond then
    log("[错误] " .. condErr)
    return nil
  end
  local guardNum = cond.kind == "addr" and cond.addr or nil
  local hasCond = cond.kind ~= "none"

  local info, err = parseInput(raw)
  if not info then
    log("[错误] " .. err)
    return nil
  end

  local bytes = info.bytes
  local insn  = info.insn
  local op, opErr = parseOperand(insn)
  if not op then
    log("[错误] " .. opErr)
    return nil
  end
  if op.kind == "abs" then
    log(string.format("[结果] 该指令直接寻址绝对地址 %X，数据地址不会变，不需要生成脚本", op.disp))
    return nil
  end
  local meta = insnMeta(insn)

  local minLen = minInsnLen(op, insn, bytes)
  if #bytes < minLen then
    log(string.format("[错误] 只粘了 %d 字节，这条指令至少要 %d 字节（操作码 + 寻址字节 + 位移/立即数）；请把 CE 里整行的字节复制完整再生成",
                      #bytes, minLen))
    log("[原因] 字节粘少了，jmp 的返回点会落在指令中间，跳回去执行的是残缺字节（比如 00 就是 add [eax],al），游戏当场崩")
    return nil
  end

  local addr = info.addr
  if addr and not isAttached() then addr = nil end
  if not isAttached() then
    log("[提示] 未附加进程：跳过字节校验、长度补齐与唯一性检查；覆盖长度只能按粘贴的字节算，务必粘完整整条指令")
  end

  -- 只给了指令没给地址：用它的字节去扫，命中唯一就当作地址用
  if not addr and isAttached() and not info.addr then
    local hit, uniq = scanUnique(hexLine(bytes))
    if hit and uniq then
      addr = hit
      log(string.format("[提示] 没给地址，按指令字节扫到唯一位置 %X，按这条指令处理", hit))
    elseif hit then
      log("[提示] 没给地址，这条指令的字节命中多处，无法确定是哪一条；不补齐、不验证唯一性")
    else
      log("[提示] 没给地址，也没扫到这条指令的字节；不补齐、不验证唯一性")
    end
  end

  -- 地址对不上就不生成：这时候既不知道钩的是哪条指令，也不知道该覆盖几字节，
  -- 硬生成出去的脚本要么钩在别人身上，要么 cover 长度错位，都是崩。宁可让用户重新取代码。
  if addr then
    local ok, same = pcall(verifyPasted, addr, bytes)
    if not ok then
      log(string.format("[错误] 校验 %X 处内存时出错，无法确认这条指令还在不在；请重新附加进程后点[取代码]", addr))
      return nil
    end
    if not same then
      local t = readAt(addr, #bytes)
      if t then
        log(string.format("[错误] %X 处内存与粘贴的不一致：内存 %s / 粘贴 %s",
          addr, hexLine(t), hexLine(bytes)))
        log("[错误] 地址对不上就不生成：可能游戏已重启或代码变了，请重新点[取代码]。硬生成会钩到别的指令、覆盖长度也会算错")
      else
        log(string.format("[错误] %X 处读不到内存（游戏可能已重启）；请重新附加进程后点[取代码]", addr))
      end
      return nil
    end
  end

  -- 粘贴的字节必须刚好是一条完整指令（多了会把后面的指令当成一条）
  if addr then
    local sz = insnSize(addr)
    if sz and sz ~= #bytes then
      if sz < #bytes then
        local cut = {}
        for i = 1, sz do cut[i] = bytes[i] end
        local need = minInsnLen(op, insn, cut)
        if sz < need then
          log(string.format("[警告] 反汇编说这条指令 %d 字节，但按寻址结构至少要 %d 字节；按粘贴的 %d 字节覆盖（截短会把 return 落在指令中间，游戏会崩）",
            sz, need, #bytes))
        else
          log(string.format("[提示] 粘贴了 %d 字节，这条指令实际 %d 字节，按 %d 字节处理", #bytes, sz, sz))
          bytes = cut
        end
      else
        log(string.format("[错误] 粘贴的字节（%d）比实际指令（%d）短，请重新粘贴完整指令", #bytes, sz))
        return nil
      end
    end
  end

  local hookBytes, pattern, covered
  local targetModule = moduleForAddress(addr) or moduleName()
  if #bytes >= 5 then
    -- hook 只覆盖首条指令，特征码可以往后接更多指令用于唯一性
    -- （解析阶段就要求有内存操作数，所以首条不可能是相对跳转，直接 db 原字节）
    hookBytes = bytes
    covered   = { { bytes = bytes, rel = false } }
    pattern   = hexLine(bytes)
    if addr then
      local _, t = collectCode(addr, bytes, 16)
      if t then pattern = t end
    end
  else
    if not addr then
      log(string.format("[错误] 这条指令只有 %d 字节，放不下 5 字节的 jmp；请把下一条指令的字节一起粘贴，或附加进程后点[取代码]", #bytes))
      return nil
    end
    local b, t, cov = collectCode(addr, bytes, 5)
    if not b or #b < 5 then
      log("[错误] 无法沿指令边界补齐到 5 字节")
      return nil
    end
    -- 被吞的那段一旦是别处跳转的目标，那条路径会绕过 hook；含相对跳转的指令要靠
    -- 反汇编文本重放（buildScript 里的 asText）才能重定位，文本拿不到就只能 db 硬搬、位移错位。
    -- 5 字节最少也得 1+1+1+1+1，所以最多连带 4 条，再多就让人换指令。
    if cov and #cov > 5 then
      log(string.format("[错误] 这条指令只有 %d 字节，要连带覆盖后面 %d 条指令才够放 5 字节的 jmp；覆盖面越大，别的跳转入口绕过 hook 的机会越多。请换一条能整条覆盖的指令，或在 CE 里选它下面那条",
        #bytes, #cov - 1))
      return nil
    end
    for i = 2, #cov do
      local ins = cov[i]
      if ins.rel and not (ins.text and not ins.text:find("%?%?")) then
        log(string.format("[错误] 要连带覆盖的第 %d 条指令是相对跳转（%s），拿不到它的目标地址，原字节搬进 newmem 后位移会错位。请在 CE 里选一条能整条覆盖的指令",
          i - 1, tostring(ins.text or ("字节 " .. hexLine(ins.bytes)))))
        return nil
      end
    end
    if cov and #cov > 1 then
      log(string.format("[提示] 首条指令不足 5 字节，连带覆盖了后面 %d 条指令；若那段是别处跳转的目标，那条路径会绕过 hook",
        #cov - 1))
    end
    hookBytes, pattern, covered = b, t, cov
  end

  -- 特征码不够唯一时，先沿指令边界往后接指令（最多到 32 字节），再按原始字节继续加长
  local nonUnique = false
  local notFound = false
  local offHex = nil
  local offStopHex = nil
  -- 模块里这串字节的第一处命中不是你贴的地址时，绝不能就这么生成：
  -- aobscanmodule 拿到的是第一处，钩上去就是别的指令（地址错、甚至崩）。
  -- 改成窗口定位，只在你那条指令附近扫，保证钩的是你看到的那一条。
  if not useOffset and addr and moduleForAddress(addr) then
    local firstHit = scanUnique(pattern, targetModule)
    if firstHit and firstHit ~= addr then
      log(string.format("[定位] 这串字节在模块里先命中 %X，不是你贴的 %X；自动改用 模块+偏移 窗口定位，保证钩在你那条指令上",
                        firstHit, addr))
      useOffset = true
    end
  end
  if useOffset then
    if not addr then
      log("[错误] 固定偏移定位需要地址：请粘贴带地址的整行，或在地址列表选中记录后点[取代码]")
      return nil
    end
    local mod, base = targetModule, moduleBase(targetModule)
    if not mod or not base or base == 0 then
      log("[错误] 拿不到模块基址，无法算固定偏移；确认已附加进程")
      return nil
    end
    if addr < base then
      log(string.format("[错误] 地址 %X 低于模块 %s 的基址 %X，不能用固定偏移", addr, mod, base))
      return nil
    end
    offHex = string.format("%X", addr - base)
    offStopHex = string.format("%X", addr - base + #hookBytes + 16)
    log(string.format("[定位] 固定偏移: %s+0x%s（在该位置 ±16 字节内按指令字节定位，保证唯一；游戏更新后需重新生成）", mod, offHex))
  elseif addr then
    local target = math.max(#hookBytes, 16)
    local hit, uniq, cnt = scanUnique(pattern, targetModule)
    local grew = false
    while not uniq and target < 32 do
      target = target + 8
      local b, t = collectCode(addr, bytes, target)
      if not b then break end
      pattern = t
      hit, uniq, cnt = scanUnique(pattern, targetModule)
      grew = grew or uniq
    end
    if not uniq then
      -- 定位不需要跟指令对齐：直接往后吞原始字节，位移是文件里的常量，不会被重定位影响
      local raw
      for _, n in ipairs({ 64, 56, 48, 40, 32 }) do
        raw = readAt(addr, n)
        if raw then break end
      end
      local have = patternBytes(pattern)
      while raw and not uniq and have < 64 do
        local step = math.min(8, 64 - have)
        if have + step > #raw then break end
        local chunk = {}
        for i = have + 1, have + step do chunk[#chunk + 1] = raw[i] end
        pattern = pattern .. " " .. hexLine(chunk)
        have = have + step
        hit, uniq, cnt = scanUnique(pattern, targetModule)
        grew = grew or uniq
      end
    end
    if not uniq then
      if cnt and cnt > 0 then
        nonUnique = true
        log(string.format("[警告] 特征码加到 %d 字节在代码段里仍不唯一（命中 %d 处），勾选脚本时可能定位到别处",
                          patternBytes(pattern), cnt))
      else
        notFound = true
        log(string.format("[警告] 特征码加到 %d 字节在代码段里一处也没扫到：可能没附加进程、内存已变或模板块不对；勾选脚本时 aobscan 会报找不到",
                          patternBytes(pattern)))
      end
      local hits, total = scanAll(pattern, 8)
      local foundSelf = false
      for _, a in ipairs(hits) do
        if a == addr then foundSelf = true end
        local okd, line = pcall(disassemble, a)
        local text = (okd and type(line) == "string") and line or "?"
        log(string.format("  %s%X  %s", a == addr and "*" or " ", a, text))
      end
      if total > #hits then
        log(string.format("  … 共 %d 处，只列前 %d 处", total, #hits))
      end
      if #hits > 0 and not foundSelf then
        log(string.format("[警告] 命中列表里没有你粘贴的 %X，内存可能已变（游戏重启？），这串特征码未必能用", addr))
      end
      log("[提示] 补救：勾选下方的「用 模块+偏移 定位」，只在这条指令附近 ±16 字节内匹配；或在 CE 里对这条指令做 AOB 扫描看命中位置，挑带常量/字符串引用的片段反着扩展")
    elseif hit and hit ~= addr then
      log(string.format("[警告] 扫描命中 %X，与粘贴的地址 %X 不同；请确认是不是同一条指令", hit, addr))
    elseif grew then
      log(string.format("[提示] 原特征码不唯一，已加长到 %d 字节定位", patternBytes(pattern)))
    end
  else
    -- 没有地址就只够检查唯一性，没法自动加长特征码
    local _, uniq, cnt = scanUnique(pattern, targetModule)
    if not uniq then
      if cnt and cnt > 0 then
        nonUnique = true
        log(string.format("[警告] 特征码在代码段里不唯一（命中 %d 处），勾选脚本时可能定位到别处；粘贴带地址的整行可以让工具自动加长", cnt))
      else
        notFound = true
        log("[警告] 特征码在代码段里一处也没扫到：可能没附加进程、内存已变或模板块不对；勾选脚本前先用 CE 的 AOB 扫描确认能定位到这条指令")
      end
    end
  end

  if op.kind == "rip" then
    if addr then
      local target = addr + #bytes + (op.disp or 0)
      log(string.format("[结果] 这条指令用 [rip%s0x%X] 相对寻址，访问的是固定地址 %X（= 指令地址 %X + 指令长度 %d + 位移 0x%X）",
                        ((op.disp or 0) < 0 and "-" or "+"), math.abs(op.disp or 0), target, addr, #bytes, math.abs(op.disp or 0)))
      log(string.format("[提示] 地址列表里直接填 %X；重启后地址一般会变，到时用 CE 的「模块+偏移」重新定位", target))
      log("[提示] 相对寻址的地址是固定的，本来就跟着指令走，不用生成脚本")
    else
      log("[错误] 这条指令用 [rip+..] 相对寻址，得先知道指令地址才能算出实际访问地址；请粘贴带地址的整行（如 004A2B3C - 字节 - 指令）")
    end
    return nil
  end
  if op.kind == "indexOnly" and cond.kind == "ptr" then
    log("[错误] 这条指令只有 索引*比例、没有固定基址，指针条件判断不了是哪个对象；请把条件判断留空，或改用地址/值条件")
    return nil
  end

  local baseSym = sanitizeSym(symInput)
  -- aob_base / aob_base_loc 是 registersymbol 注册的全局符号：同一 CT 里两份脚本默认同名会互相顶掉，
  -- 停用其中一份时可能把原字节写到另一份的注入点上。没自定义名字时补上指令地址来区分。
  if baseSym == DEFAULT_SYM and addr then baseSym = baseSym .. "_" .. string.format("%X", addr) end
  local hookSym = baseSym .. "_loc"
  -- 同名符号还注册着（旧脚本没停）时，勾选新脚本会报「符号已注册」；生成时先说清楚
  if isAttached() then
    for _, nm in ipairs({ baseSym, hookSym }) do
      local a
      pcall(function() a = getAddressSafe(nm) end)
      if type(a) == "number" and a ~= 0 then
        log(string.format("[警告] 符号 %s 现在已存在（%X），多半是旧脚本还没停；勾选新脚本会报「符号已注册」，先停掉旧脚本或换个符号名",
                          nm, a))
      end
    end
  end

  -- 记录语义只决定索引算不算进符号；两种语义下符号都存完整数据地址，记录的偏移层固定是 0（把符号当指针解引用一次）
  local sem = (semInput == "element") and "element" or "container"
  if op.kind == "indexOnly" and sem == "container" then
    log("[错误] 这条指令只有 索引*比例、没有固定基址，「容器」语义没有基址可记；语义请选「元素」")
    return nil
  end
  local hasIndex = op.index ~= nil
  local indexMode = hasIndex and sem == "element"
  -- 通用模板：借基址寄存器自己当 lea 目标，push 保存、pop 还原，不占额外空闲寄存器
  local eaReg = (((op.kind == "indexOnly") and op.index) or op.base or ""):lower()
  local idxLower = (op.index or ""):lower()
  if eaReg == "" then
    log("[错误] 这条指令里没有可当基址的寄存器，生成不了 push/lea/mov/pop 模板；换一条指令")
    return nil
  end
  -- push 会先动栈指针：拿 esp/rsp 寻址时算出来的地址就不是原指令访问的地址了
  if eaReg == "rsp" or eaReg == "esp" or idxLower == "rsp" or idxLower == "esp" then
    log("[错误] 这条指令拿栈指针寻址：push 本身就会改栈指针，算出来的地址是错的；换一条指令")
    return nil
  end

  -- 索引寻址：用空闲寄存器把 基址+索引*比例 算出来再存，偏移就只剩常量
  -- 条件：地址条件/指针条件需要借一个空闲寄存器；值条件直接用原指令的内存操作数
  local scratch
  local regLower = (op.base or ""):lower()
  local regCond = (cond.kind == "reg") and cond or nil
  local condNeedsScratch = hasCond and cond.kind == "ptr"
  local regCondBig = false
  if regCond then
    local w = regWidth(regCond.reg) or 8
    regCondBig = (w == 8) and (((regCond.v or 0) > 0x7FFFFFFF) or ((regCond.v2 or 0) > 0x7FFFFFFF))
    if regCondBig then condNeedsScratch = true end
  end
  if hasCond and (regLower == "rsp" or regLower == "esp" or idxLower == "rsp" or idxLower == "esp") then
    log("[错误] 这条指令用栈指针寻址，加条件要动栈，会把原程序的栈弄乱；请把条件判断留空")
    return nil
  end
  if condNeedsScratch then
    local used = { [regLower] = true }
    if idxLower ~= "" then used[idxLower] = true end
    if regCond then used[regCond.reg] = true end
    local cands = targetIs64() and { "rax", "rcx", "rdx", "r8", "r9", "r10", "r11" }
                                  or { "eax", "ecx", "edx", "edi", "esi" }
    for _, c in ipairs(cands) do
      if not used[c] then scratch = c used[c] = true break end
    end
    if not scratch then
      log("[错误] 找不到空闲寄存器来算访问地址，这条指令不能加这个条件；请把条件判断留空")
      return nil
    end
  end

  local notes
  local disp = op.disp or 0
  local ok64, is64 = pcall(targetIs64)
  if ok64 and is64 and regLower ~= "" and regWidth(regLower) == 4 then
    log("[警告] 64 位进程里这条指令拿 32 位寄存器（" .. regLower .. "）当地址：寄存器值会被零扩展，只有目标在低 4GB 内才指得对；符号记的是零扩展后的地址")
  end
  local dispConst
  if disp > 0 then
    dispConst = "+0x" .. string.format("%X", disp)
  elseif disp < 0 then
    dispConst = "-0x" .. string.format("%X", -disp)
  end
  -- 元素：索引算进去（这条指令真正访问的地址）；容器：只算 基址+位移
  local fullExpr = ((op.indexText and op.leaText) or op.base) .. (dispConst or "")
  local leaExpr = indexMode and fullExpr or (op.base .. (dispConst or ""))
  local typeConst = meta.typeConst
  local recordType, recordSize = typeConst, nil
  if meta.width ~= 1 and meta.width ~= 2 and meta.width ~= 4 and meta.width ~= 8 then
    recordType, recordSize = "vtByteArray", meta.width
  end

  local desc = tostring(descInput or ""):gsub("^%s+", ""):gsub("%s+$", "")
  if desc == "" then desc = baseSym end
  lastDesc = desc
  local condTable = { kind = cond.kind, text = cond.text }
  local extra = {}
  if cond.kind == "addr" then
    extra.condHex = string.format("%X", cond.addr)
  elseif cond.kind == "ptr" then
    extra.ptrCode = ptrChainCode(cond.ops, scratch)
  elseif cond.kind == "value" then
    local memOperand = op.expr
    if not memOperand then
      log("[错误] 从指令里取不到内存操作数，用不了值条件")
      return nil
    end
    local sfx = condSizeSuffix(typeConst, targetIs64())
    if sfx == "qword" and not targetIs64() then
      sfx = "dword"
      log("[提示] 32 位进程里比不了 8 字节，值条件按低 4 字节比；高 4 字节不管")
    end
    extra.valueCode = valueCondCode(cond, memOperand, sfx, baseSym .. "_skip")
    local big = (cond.v or 0) > 0x7FFFFFFF or (cond.v2 or 0) > 0x7FFFFFFF
    if big then
      log("[警告] 判断值超过 0x7FFFFFFF，cmp 的立即数会当有符号数；建议改用位掩码（&）或换小一点的判断值")
    end
  end
  if regCond then
    local w = regWidth(regCond.reg) or 8
    if w == 8 and not targetIs64() then
      log("[错误] 32 位进程里没有 " .. regCond.reg .. "，寄存器条件请用 esi/ecx/edi 这类 32 位写法")
      return nil
    end
    local vmax = 2 ^ (w * 8) - 1
    local top = math.max(regCond.v or 0, regCond.v2 or 0)
    if top > vmax then
      log(string.format("[错误] 判断值 0x%X 超过寄存器 %s 的范围（最多 0x%X）；请换个寄存器或缩小判断值",
                        top, regCond.reg, vmax))
      return nil
    end
    if regCond.cmp == "&" and top > 0x7FFFFFFF then
      log("[警告] 位掩码超过 0x7FFFFFFF，test 的立即数会按有符号扩展；建议只测低位")
    end
    if regCondBig and not scratch then
      log("[错误] 判断值超过 0x7FFFFFFF，64 位寄存器要借一个空闲寄存器才能比；请换个小一点的判断值或换个符号名")
      return nil
    end
    extra.regCode = regCondCode(cond, baseSym .. "_skip", scratch)
  end
  local function reg64(n)
    local m = { eax = "rax", ebx = "rbx", ecx = "rcx", edx = "rdx", esi = "rsi", edi = "rdi", ebp = "rbp" }
    if m[n] then return m[n] end
    return n:match("^(r%d+)d$") or n
  end
  local function reg32(n)
    local m = { rax = "eax", rbx = "ebx", rcx = "ecx", rdx = "edx", rsi = "esi", rdi = "edi", rbp = "ebp" }
    if m[n] then return m[n] end
    return n:match("^(r%d+)$") and (n .. "d") or n
  end
  local pushReg, storeReg = eaReg, eaReg
  if targetIs64() then
    -- x64 没有 push eax：压栈只能借 64 位别名；写符号按基址寄存器本来的宽度
    -- （32 位基址只写低 4 字节，高位靠 dq 0 保持 0，就是零扩展后的地址）
    pushReg = reg64(eaReg)
  end
  -- 和基址寄存器比大小/比地址时宽度得一致，否则汇编器拒收
  local cmpScratch = scratch
  if scratch and regWidth(eaReg) == 4 then cmpScratch = reg32(scratch) end

  -- 定位特征码必须与这条指令的字节同源：aobscan 按特征码定位到哪，jmp 与还原用的 db
  -- 就写在哪。两份字节一旦不是同一份（手改过 aobscan 行等），钩的和恢复的就不是同一条
  -- 指令，启用即崩，所以这里硬拦一次。
  do
    local hh = hexLine(hookBytes)
    local want, got = {}, {}
    for tok in hh:gmatch("%S+") do want[#want + 1] = tok end
    for tok in pattern:gmatch("%S+") do got[#got + 1] = tok end
    local bad = #got < #want
    -- pattern 里的 ?? 只可能来自「连带覆盖的那段指令」的相对位移（collectCode 掩码），
    -- 首条指令的字节从不掩码；拿它当通配不会放过两份字节真的不同源的情况
    if not bad then
      for i = 1, #want do
        if got[i] ~= want[i] and got[i] ~= "??" then bad = true break end
      end
    end
    if bad then
      log("[错误] 定位特征码和这条指令的字节不是同一份，这次不生成：特征码 " .. pattern .. " / 指令字节 " .. hh)
      log("[原因] aobscan 按特征码找位置，jmp 和还原的 db 却写在你这条指令上；两者不一致时钩到的是别的指令、恢复也会写错位置。请重新点[取代码]原样生成，不要手改脚本里的 aobscan 行")
      return nil
    end
  end

  -- 附带改值（可选）：生成脚本时把改值指令直接写进注入代码，原指令跑完再写，不会被覆盖
  local patchCfg
  if patchInput and patchInput.on then
    local pop = tostring(patchInput.op or "写入值")
    local pv = tostring(patchInput.value or ""):match("^%s*(.-)%s*$") or ""
    -- 类型：整数宽度 + 单/双浮点；浮点用 xmm 写入/运算
    local sizeMap = { ["字节"] = "byte", ["2字节"] = "word", ["4字节"] = "dword", ["8字节"] = "qword",
                      ["单浮点"] = "float", ["双浮点"] = "double" }
    local psize = sizeMap[tostring(patchInput.vt or "4字节")] or "dword"
    local isFloat, pwidth, pfx = false, nil, nil
    if psize == "float" then isFloat, pwidth, pfx = true, "dword", "ss"
    elseif psize == "double" then isFloat, pwidth, pfx = true, "qword", "sd" end
    if not isFloat and psize == "qword" and not targetIs64() then psize = "dword" end
    if pop ~= "置0" then
      if pv == "" then
        log("[错误] 勾选了「附带改值」，但操作数为空")
        return nil
      end
      if isFloat then
        if not (pv:match("^[-+]?%d+%.?%d*$") or pv:match("^[-+]?%.%d+$")
                or pv:match("^[-+]?%d+%.?%d*[eE][-+]?%d+$")) then
          log("[错误] 「附带改值」浮点类型的操作数不是合法浮点数: " .. pv)
          return nil
        end
      else
        if not (pv:match("^%-?%d+$") or pv:match("^0[xX]%x+$")) then
          log("[错误] 「附带改值」的操作数不是数字: " .. pv)
          return nil
        end
      end
    end
    local rawOff = tostring(patchInput.off or "0"):match("^%s*(.-)%s*$") or "0"
    local poff = 0
    local hexOff = rawOff:match("^0[xX](%x+)$")
    if hexOff then poff = tonumber(hexOff, 16) or 0 else poff = tonumber(rawOff) or 0 end
    local ptext
    if pop == "置0" then
      ptext = string.format("[符号+0x%X] = 0", poff)
    else
      ptext = string.format("[符号+0x%X] %s %s", poff, pop, pv)
    end
    local num = tonumber(pv) or (pv:match("^0[xX](%x+)$") and tonumber(pv:match("^0[xX](%x+)$"), 16))
    if num and psize == "byte" and (num > 255 or num < -128) then
      log("[错误] 「附带改值」选了字节类型，操作数 " .. pv .. " 超出 -128~255")
      return nil
    end
    if num and psize == "word" and (num > 65535 or num < -32768) then
      log("[错误] 「附带改值」选了 2 字节类型，操作数 " .. pv .. " 超出 -32768~65535")
      return nil
    end
    -- 浮点：把操作数打包成 IEEE754 机器码，改值段用 xmm + 内联常量写入/运算
    local constHex, constLabel
    if isFloat then
      local v = tonumber(pv) or 0
      local okp, packed = pcall(string.pack, isFloat and (psize == "float" and "<f" or "<d"), v)
      if not okp or not packed then
        log("[错误] 浮点常量打包失败: " .. pv)
        return nil
      end
      if psize == "float" then
        constHex = string.format("0x%08X", string.unpack("<I4", packed))
      else
        constHex = string.format("0x%016X", string.unpack("<I8", packed))
      end
      constLabel = baseSym .. "_pc"
    end
    patchCfg = { on = true, op = pop, value = pv, off = poff, size = isFloat and pwidth or psize,
                 isFloat = isFloat, width = pwidth, pfx = pfx, constHex = constHex, constLabel = constLabel,
                 text = ptext, label = baseSym .. "_pv", flag = baseSym .. "_pf" }
    if pop == "加" or pop == "减" or pop == "乘" then
      log("[提醒] 运算选了「" .. pop .. "」：这条指令每执行一次就" .. pop .. "一次，会累积；只要固定值请改用「写入值」")
    end
    if pop == "除" or pop == "取模" then
      log("[提醒] 运算选了「" .. pop .. "」：注意除零保护已内置（除零时跳过写入）")
    end
    if pop == "与" or pop == "或" or pop == "异或" or pop == "取反" then
      log("[提醒] 运算选了「" .. pop .. "」：按位运算，直接对目标值的位进行操作")
    end
  end

  -- ---------- 硬件断点版（不改游戏代码） ----------
  if hwbpInput then
    lastHwbpMode = true
    lastExportData = nil            -- 没有代码洞字节，导出契约不成立
    lastDesc = desc
    local rva = 0
    if offHex and offHex ~= "" then rva = tonumber(offHex, 16) or 0 end
    log("[模式] 硬件断点版：不写游戏代码，用 CE 调试器的执行断点取寄存器")
    log("[解析] " .. insn)
    log("[公式] " .. (op.formula or tostring(op.expr)))
    log(string.format("[访问] %s；%d 字节", RW_TEXT[meta.rw] or meta.rw, meta.width))
    log(string.format("[定位] %s", (rva > 0)
      and string.format("模块 %s + 固定偏移 0x%X（启用时先校验原字节，不符再扫特征码）", tostring(targetModule), rva)
      or string.format("模块 %s 内按特征码扫：%s", tostring(targetModule), pattern)))
    log(string.format("[符号] %s = 指令执行时的 %s（命中时由调试器回调 writeQword 写入）", baseSym, leaExpr))
    log(string.format("[记录] 启用后自动加到地址列表:「%s」 地址 %s 加偏移 0（符号存的是数据地址）", desc, baseSym))
    log("[前提] CE 的调试器必须保持开启；脚本会自动尝试用 VEH 启动，启动不了会报错不启用")
    log("[代价] 每次命中都会暂停全部线程再继续：这条指令若是每帧执行，游戏会明显卡顿")
    log("[限制] 硬件断点只有 4 个槽位，CE 自己和其它脚本也会占用；与其它调试断点会相互影响")
    log("[限制] 本模式没有代码洞，不能导出独立 EXE / DLL")
    if patchCfg then
      log("[提示] 「生成时附带改值」在硬件断点模式下不生效，本次忽略")
    end
    if encryptOn then
      log("[提示] 硬件断点模式输出明文（加密路径只适用于自动汇编脚本）")
    end
    log("---------------------------------------------")
    local origLua = {}
    for i = 1, #hookBytes do origLua[i] = string.format("0x%02X", hookBytes[i]) end
    lastScript = buildHwbpScript({
      insn = insn, module = targetModule, pattern = pattern,
      rva = rva, baseSym = baseSym, desc = desc,
      origHex = table.concat(origLua, ", "), is64 = is64,
      latch = latchInput and true or false,
      exprLua = hwbpExprLua(leaExpr, is64),
      recordType = recordType, recordSize = recordSize,
    })
    lastPlainScript = lastScript
    logBlock(lastScript)
    log("---------------------------------------------")
    selfCheck(lastScript)
    return lastScript
  end
  lastHwbpMode = false

  lastScript, notes = buildScript({
    insn    = insn,
    desc    = desc,
    typeConst = typeConst,
    recordType = recordType,
    recordSize = recordSize,
    reg     = op.base,
    hookHex = hexLine(hookBytes),
    offHex  = offHex,
    offStopHex = offStopHex,
    warn    = nonUnique and "特征码不唯一，勾选前先确认 aobscan 扫到的是目标指令"
              or (notFound and "这条特征码一处也没扫到，勾选前先用 CE 的 AOB 扫描确认能定位到这条指令")
              or nil,
    covered = covered,
    pattern = pattern,
    -- 5 = 注入点那句 jmp 的字节数，按 E9 rel32 算。新内存由 alloc 就近分配，
    -- 分配不到近处时 AA 会报错、脚本装不上，不会静默变成 14 字节绝对跳转；
    -- 「AA 对 jmp 标签不做短跳优化」只是社区经验，未核实，不算依据。
    -- 换成手写编码或改分配策略时，这个 5 得跟着重算。
    pad     = #hookBytes - 5,
    baseSym = baseSym,
    hookSym = hookSym,
    memSym  = baseSym .. "_mem",
    codeLabel = baseSym .. "_code",
    retLabel = baseSym .. "_ret",
    scratch = scratch,
    eaReg   = eaReg,
    pushReg = pushReg,
    storeReg = storeReg,
    cmpScratch = cmpScratch,
    leaExpr = leaExpr,
    leaLabel = baseSym .. "_lea",
    tmpSym  = baseSym .. "_tmp",
    module  = targetModule,
    cond    = condTable,
    condHex = extra.condHex,
    ptrCode = extra.ptrCode,
    valueCode = extra.valueCode,
    regCode = extra.regCode,
    latch = latchInput and true or false,
    latchSuffix = targetIs64() and "qword" or "dword",
    guardSym = baseSym .. "_guard",
    skipLabel = baseSym .. "_skip",
    flagSuffix = targetIs64() and "fq" or "fd",
    indexMode = indexMode,
    fullExpr = fullExpr,
    patch   = patchCfg,
    verbose = verboseInput ~= false,
  })

  -- ---------- 结果 ----------
  log("[解析] " .. insn)
  log("[公式] " .. (op.formula or tostring(op.expr)))
  log(string.format("[访问] %s；%d 字节", RW_TEXT[meta.rw] or meta.rw, meta.width))
  if meta.rw == "compute" then
    log("[提示] 这条指令不访问内存（lea/nop 只算地址），抓到的是算出来的地址；如果这就是你要的数据地址就可以用")
  elseif meta.rw == "rmw" then
    log("[提示] 这是读改写指令：先读旧值再写回，记录里的值会被游戏持续改写，不能当固定开关；要固定值用[锁定首次]")
  end
  if indexMode then
    log(string.format("[语义] 符号 = 数据地址 %s，记录 = 符号+偏移0（元素：索引也算进去，换下标就指到另一个元素）", leaExpr))
  elseif hasIndex then
    log(string.format("[语义] 符号 = 数据地址 %s，记录 = 符号+偏移0（容器：索引 %s 不算进去）", leaExpr, tostring(op.indexText)))
  else
    log(string.format("[语义] 符号 = 数据地址 %s，记录 = 符号+偏移0", leaExpr))
  end
  log(string.format("[模板] push %s → lea %s,[%s] → mov [%s],%s → pop %s（借用基址寄存器本身，不占别的寄存器）",
                    pushReg, eaReg, leaExpr, baseSym, storeReg, pushReg))
  if recordSize then
    log(string.format("[类型] %s（%d 字节，按字节数组记，不会截断）", recordType, meta.width))
  else
    log("[类型] " .. recordType .. "（" .. meta.width .. " 字节）")
  end
  if info.skipped and #info.skipped > 0 then
    log(string.format("[解析] 粘贴了 %d 行，只用含 [..] 的这一行；其余 %d 行已忽略",
                      #info.skipped + 1, #info.skipped))
    for _, l in ipairs(info.skipped) do log("[忽略] " .. l) end
  end
  if info.addrText and info.addrText ~= "" then
    log("[地址] " .. info.addrText)
  end
  if targetModule and targetModule ~= moduleName() then
    log(string.format("[模块] 指令在 %s（主程序 %s），特征码只在该模块内扫",
                      targetModule, tostring(moduleName())))
  end
  if cond.kind == "addr" then
    log(string.format("[条件] 只有这条指令访问的地址正好是 %X 时才写 %s；它被别的对象调用时不会被冲掉",
                      cond.addr, baseSym))
  elseif cond.kind == "ptr" then
    log(string.format("[条件] 静态指针 %s 指向本次对象时才写 %s（槽里存基址或字段地址都算）",
                      cond.text, baseSym))
  elseif cond.kind == "value" then
    log(string.format("[条件] 只有访问到的值 %s 时才写 %s；不靠地址，重启后还能用",
                      cond.text, baseSym))
  elseif cond.kind == "reg" then
    log(string.format("[条件] 只有 %s 时才写 %s（共用代码靠寄存器值区分字段/下标时用这个）",
                      cond.text, baseSym))
  end
  local regHint = regCond
  if regHint then
    local creg = regHint.reg:lower()
    local cval = regHint.v or 0
    if idxLower ~= "" and creg == idxLower then
      log(string.format("[条件] 比较的就是索引寄存器 %s：下标固定成 0x%X 后，符号只会针对这个元素更新",
                        creg, cval))
      log("[提示] 不知道下标该填几：在 CE 里给这条指令下断点，命中时看寄存器窗口里 " .. creg .. " 的值，按十六进制填进来")
      if not indexMode then
        log("[提示] 容器语义下索引不进符号，下标固定也只会让你看到同一个字段地址；要把索引算进去就把语义改成「元素」")
      end
    elseif creg ~= regLower and creg ~= idxLower then
      log(string.format("[提示] %s 不在寻址表达式里，脚本只是拿它做开关；要确保它在这条指令执行时的值确实是你想要的那个",
                        creg))
    end
    if creg == "rsp" or creg == "esp" then
      log("[提示] 拿栈指针做条件基本不会命中你要的对象，慎用")
    end
  end
  log("[特征码] " .. pattern)
  log(string.format("[注入] 覆盖 %d 字节：jmp 5 字节 + %d 字节 90 填充", #hookBytes, #hookBytes - 5))
  if #covered > 1 then
    log(string.format("[提示] 首条指令只有 %d 字节，放不下 5 字节 jmp，连带覆盖了后面 %d 条指令（补丁区里会按原样再执行一遍）；若那段正好是别处跳转的目标，那条路径会绕过 hook",
                      #bytes, #covered - 1))
  end
  if scratch then
    log(string.format("[符号] %s = 指令执行时的 %s（借 %s 算地址、条件比完再还原）", baseSym, leaExpr, tostring(scratch)))
  else
    log(string.format("[符号] %s = 指令执行时的 %s", baseSym, leaExpr))
  end
  if meta.rw == "read" then
    log("[提示] 这是读指令：它只读取该地址，改记录里的值不会影响游戏；要改数值请找写入这个地址的指令")
  elseif meta.rw == "rmw" then
    log("[提示] 记录可以直接改值/冻结，但这条指令每次执行都会先读旧值再写回，值会被它改写")
  end
  if not hasCond then
    log("[提示] 这类指令往往被多个对象共用，符号记的是最后执行那一次的对象；要固定你查的那个对象，把它的数据地址填进「条件判断」再生成")
  end

  local typeName = ({ ["vtByte"] = "1 字节", ["vtWord"] = "2 字节", ["vtDword"] = "4 字节",
                     ["vtQword"] = "8 字节", ["vtSingle"] = "float", ["vtDouble"] = "double",
                     ["vtByteArray"] = tostring(recordSize or 0) .. " 字节数组" })[recordType] or recordType
  log(string.format("[记录] 启用后自动加到地址列表:「%s」 地址 %s 加偏移 0（符号存的是数据地址，记录把它当指针读一次，%s）", desc, baseSym, typeName))
  if patchCfg then
    log(string.format("[改值] 已并入脚本：原指令执行后写 [%s+0x%X] %s %s（%s）——勾选脚本即生效，不用再单独操作",
        baseSym, patchCfg.off, patchCfg.op == "置0" and "=" or patchCfg.op,
        patchCfg.op == "置0" and "0" or patchCfg.value, patchCfg.size))
  end
  log("[提示] 类型按指令访问宽度猜的，不对就在列表里右键改")
  log("[提示] 关闭脚本后这条记录会失效（符号已注销），重新勾选脚本就恢复")
  log("[提示] 也可以点[加到列表]，把整段脚本当成自动汇编条目加进 CT 表，勾选那条就等于启用")
  log("[提示] 脚本勾选后要让游戏执行一次这条指令，" .. baseSym .. " 才会有值")
  if indexMode and hasIndex then
    log(string.format("[提示] 地址里的 %s 已算进 %s（元素语义）", op.indexText, baseSym))
  elseif hasIndex then
    log(string.format("[提示] 地址里的 %s 没写进符号（容器语义）；要把索引算进去就把语义改成「元素」", op.indexText))
  end
  local relOk = 0
  for _, ins in ipairs(covered) do
    if ins.rel and ins.text and not ins.text:find("%?%?") then relOk = relOk + 1 end
  end
  if relOk > 0 then
    log("[提示] 覆盖范围里的 " .. relOk .. " 条跳转/调用指令已按绝对目标重写，不是原样搬字节")
  end
  for _, n in ipairs(notes or {}) do log("[警告] " .. n) end
  if cond.kind == "addr" then
    log("[注意] 只有访问到 " .. string.format("%X", cond.addr) .. " 的那一次会写符号；游戏重启后这个数据地址会变，那时要重新查、重新生成")
  elseif cond.kind == "ptr" then
    log("[注意] 条件靠静态槽 " .. cond.text .. " 判定，重启后不用改；但它指向的对象要游戏里已经创建才有意义")
  elseif cond.kind == "value" then
    log("[注意] 条件是看值不看地址，重启后仍然有效；但你自己改值/其它对象同值时会影响判断，必要时勾上[锁定首次]")
    if typeConst == "vtSingle" or typeConst == "vtDouble" then
      log("[提示] 这是浮点字段，条件比的是原始 4/8 字节位，不是浮点值；要按数值比就先改成整数类型对比")
    end
  else
    log("[注意] 符号记的是最后一次执行这条指令时的 "
        .. leaExpr
        .. "；若它会被多个对象共用，符号会跟着最后一个对象变")
  end
  if latchInput then
    log("[锁定] 命中一次后不再改写符号，后面的对象冲不掉；重启或重新启用脚本会重新锁")
  end
  log("---------------------------------------------")
  local plainScript = lastScript
  lastPlainScript = plainScript   -- [EXE导出] 明文副本；下面的加密分支只改写 lastScript
  if encryptOn then
    local key = cryptRandomKey()
    local enc, cerr = cryptScript(plainScript, key, true)
    if not enc then
      log("[错误] 加密失败：" .. tostring(cerr) .. "；没有输出脚本，取消[加密输出]再生成")
      lastScript = nil
      log("---------------------------------------------")
      return nil
    end
    lastScript = enc
    log(string.format("[加密] 已加密输出：密钥 %s", key))
    log(string.format("[加密] 明文 %d 字符 → 密文 %d 字符；[复制脚本]/[另存为]/[加到列表] 输出的都是密文", #plainScript, #enc))
    log("[提示] 密钥不用记也能跑（解包器在脚本里）；只有想用同一密钥重新加密时才需要它")
  end
  logBlock(lastScript)
  log("---------------------------------------------")
  selfCheck(plainScript)

  return lastScript
end

-- =============================================================
-- 界面
-- =============================================================
-- TMemo 在 CE 里不保证暴露 Text 属性（读出来是空串），优先走 Lines
local function memoText(m)
  if not m then return "" end
  local ok, s = pcall(function() return m.Lines.Text end)
  if ok and type(s) == "string" and s:match("%S") then return s end
  local ok2, t = pcall(function()
    local n = m.Lines.Count
    local w = {}
    for i = 0, n - 1 do w[#w + 1] = m.Lines[i] end
    return table.concat(w, "\n")
  end)
  if ok2 and type(t) == "string" and t:match("%S") then return t end
  local ok3, v = pcall(function() return m.Text end)
  if ok3 and type(v) == "string" then return v end
  return ""
end

local function setMemo(m, s)
  if not m then return end
  if pcall(function() m.Lines.Text = s end) then return end
  pcall(function()
    m.Lines.Clear()
    for line in s:gmatch("[^\r\n]+") do m.Lines.Add(line) end
  end)
end

local doGenerate

local function saveScriptTo(path)
  if not path or path == "" then return end
  local f, err = io.open(path, "wb")
  if not f then
    log("[错误] 无法写入 " .. tostring(path) .. "：" .. tostring(err))
    return
  end
  f:write(lastScript)
  if not lastScript:find("\n$") then f:write("\n") end
  f:close()
  log("[提示] 已保存: " .. tostring(path))
end

local function exportScript()
  if not lastScript then
    log("[提示] 还没有生成脚本，先点[生成脚本]")
    return
  end
  local ok = pcall(function()
    local dlg = createSaveDialog(form)
    dlg.Title = "保存 AOB 脚本"
    dlg.Filter = "CE 自动汇编 (*.cea)|*.cea|文本文件 (*.txt)|*.txt|所有文件 (*.*)|*.*"
    dlg.DefaultExt = "cea"
    dlg.FileName = "aob_" .. os.date("%Y%m%d_%H%M%S") .. ".cea"
    local saved = false
    dlg.OnClose = function(sender)
      if saved then return end
      saved = true
      local fn
      pcall(function() fn = sender.FileName end)
      if fn and fn ~= "" then saveScriptTo(fn) end
    end
    dlg.Execute()
  end)
  if not ok then
    log("[错误] 保存对话框打不开，请用[复制脚本]或手动粘贴")
  end
end

local function addScriptToTable()
  if not lastScript then
    log("[提示] 还没有生成脚本，先点[生成脚本]")
    return
  end
  local desc = "AOB 脚本 " .. tostring(lastDesc or "")
  local madeMr = nil
  local ok, err = pcall(function()
    local al = getAddressList()
    local mr = nil
    for i = 0, al.Count - 1 do
      local r = al.getMemoryRecord(i)
      if r.Description == desc then mr = r break end
    end
    if mr == nil then
      mr = al.createMemoryRecord()
      madeMr = mr
    end
    mr.Description = desc
    mr.Type = vtAutoAssembler
    mr.Script = lastScript
  end)
  if not ok then
    if madeMr then pcall(function() getAddressList().removeMemoryRecord(madeMr) end) end
    log("[错误] 加到列表失败（" .. tostring(err) .. "），改用[复制脚本]粘进 CE 自动汇编窗口")
    return
  end
  log("[提示] 已加到地址列表:「" .. desc .. "」，勾选它就等于启用；重复点只会更新同一条")
  log("[注意] 不要再把同一份脚本另外粘进 CE 再启用一次，注入点会被重复修改")
end

-- ===== 内嵌 Logo 动画帧（DeepSeek 鲸鱼娘 · 3D 手办风 · 12 帧）=====
-- 【为什么是图片】TShape 只能画圆/矩形/三角，画不出立体渲染、光影、表情，
-- 所以走 CE 官方的 createImage + Picture.loadFromStream（PGN 解码由 CE 自己做）。
-- 【为什么 base64 内嵌】插件必须保持单文件；12 帧 40px 圆形 PNG 共 43KB，
-- base64 后 58KB，插件从 270KB 涨到约 317KB，可以接受。
-- 【为什么 12 帧 / 40px】原 GIF 是 62 帧 25fps（2.48s 一轮），全部内嵌要 300KB+。
-- 均匀抽 12 帧，40px 下相邻帧仍有明显差异（实测平均像素差 11.5/255），动作读得出来；
-- 40px 同时是显示尺寸，1:1 不缩放，最锐利（源图放大到 48px 反而变糊）。
-- 【为什么圆外填 #0F141C】CE 的透明 PNG 有 alpha 变黑的已知问题，
-- 直接把圆外刷成标题条底色就不依赖 alpha；标题条底色固定，不会露馅。
local LOGO_FRAMES = {
  -- 帧 1（源帧 #0）
  [[
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
  ]],
  -- 帧 2（源帧 #5）
  [[
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
1yClSikpBRdcAQABhEpJqZQCWCmqBEpCnAQkjSyMIq5mb7XWW2nHS3SKt1u7q3c7d1ev3bp+TjcsbFgFAFHk7zLoQGoahgak
qFaKF2Yvrq9ea9QKtVIJQKARkgKgNI1xnqYp55wnqeQZBwAgJIRAQEnGQMYUFwjC0Pf/450Lb5270mxHtXpvFCXXbq+3vW5n
7QOl5CcWBkIEZMbSsG/vNNH0+cU7tpUb2TsgWLynt2zpmAMgMfbjWAJlmBZCJAoCyTkEimUcUU3TtTCKIQRKSCGlkJJQEqTJ
peurvY3D3SBa33G7KfC3LvK4DTH5lHeCGHBfo8ae0WOtTnd5s5UJZdmlj24sEiwpgVESp0kshfC7XhIEGkEAQqEAAiDLWBTF
SRJHYRAlcZLEQRLPLW2enW9l+sB6M1pY2bRL/UFrwd2Yw9QASn3atCmEaeRtmnZxeOKYYeiI2pvN5rWlteWN3abrMS6lFIKz
SqnouZ04jqMoypLE63Sgkhjj9u6u53mbre788tZPzt3617evXl4NIlXwEjY0st/d+mhl/nVEdADUZ5g2iMj1C68CRA4dfxJA
FvuDcRRvdLbZcnRra9mi0tDpYH2xZKQ9eb2/ViEYQ0y6i8s7ftzy2d0O22j6fqKCRPoZrNXz4+OTtlO9+uFr1869TKj+f/hj
iBDeufORBLAxeaTS0zPSGNnZ3gjamxoIRob6d7ve9Zu3zr7387WtLSuXbwfJ5WsLZ89ffvG1d5Y23W1fYUJ7qpVuIhIBTp/+
tcF9E3PvvXr+pz8gVAcA/mLczzTmEBOyuXQpaG8NjE0Pju3vcQrvvvFK2ll75MTB0T0lk2Jds37zy7/xzJkzra7PFTBsh9D8
gfHG/pHqg0cObNxZXFrd+MIXv9YY3ffjH31v9uxLmmED+D+o90wEqG42NxdvX3mn6waDg0NRe4OF7szMTLlcpkT71h//wZO/
cqpWyR+ePjQ2Nl6r96Yp7++rHz96aGx07O2fvcUkdgrmq3/3l5tL84btACV/mfAFIcEzlibV+kDBLgAe/vbzv/XoQyd7a4WB
vprne5gQjBCEMFcsX5m77npxIW//+D//6+//+aW2F4aBSwglVJdSfKb+Z08MAABKIYQ1zYgi3/M7fhg12y7LsiQOZJYWbAMh
BCDiWXr9xo2t7dZ752f/5vs/fOXfX3N9HyhJqY4QUkreK276b0StyooWExwPAAAAAElFTkSuQmCC
  ]],
  -- 帧 3（源帧 #10）
  [[
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
  ]],
  -- 帧 4（源帧 #15）
  [[
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
  ]],
  -- 帧 5（源帧 #20）
  [[
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
  ]],
  -- 帧 6（源帧 #25）
  [[
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
fXXjggAAAABJRU5ErkJggg==
  ]],
  -- 帧 7（源帧 #31）
  [[
iVBORw0KGgoAAAANSUhEUgAAACgAAAAoCAIAAAADnC86AAAOJ0lEQVR42pWYy2/c13XHz33/XvObGc5wOCTFt0RKJmXJUiTb
suLKdmQbRuK0Tls0BdoGabtp4UWzarJoA7R/QYEuii66aLpIELSIUyR1bdeWH5Eli5JlvUVS4ms45JDz/M3M73UfXTAB3EZG
0bu4wL2L88E5+N578D0oWzwAX7AQACAkpZRScsEPDA+Pj4+PjQwP5HNDgyVGCSaYc1FvNhuNxoPVteWVByura2EUcc4F58YY
Y8wXBv8iMEJIaa2kHMjnZ6YnZg/OlEtDtmVjghillFBhCduyGaWMEa0UYyyRam1945OrV69cu769U2OMUUq11v8PMEIoSRLb
tk8cO7owP2fbNiPMGEAYM8Y4I67t2LZVKhb8jM8511qFUdzv98M4AQP1vZ33L156670Pu72ebVmPZBPL8X/9Nk7SmcmJ8899
efbgZMbzCMJKa2MMQtgYY1mW6zi+5+Vz2XK5PDwynM/lBGMyjdvtVqsTEMomx8ZnD810OsHm1hZn7P8AIwQAIJV68sTjp08c
tRzBKM5lPK1NnCrGqODctoTv+UOl0vjocLlctgXvBr16ve77HsIojmKMjDEmjCLB2OHZWcbo8oNVQjDaj/5FGadSPn3yifm5
Q1KDZTHOqG3ZnFNKqRCW69ie4wjBPMexLM4Z7odhu93u9QJKsFY6lSnGOIoTY0wq0yiOJ8fHbdu6t7RMCPk8iH7+IJV65vSp
mYnRbi/M5TKFrE8pxYQDGDBpFKVhlGjVMhqtr29xTgXnmYyXzWVdx61s7xqjCEIIEc5ZmiYEAwJotFtH549gjH/+n2+zz9X8
l+LaV9O5Z8/OTk+E/dD3fS64lqrfD3b3WhuV7b16vReaOJFxGCRJKGWkldJaCu5Yli0s3/F8z3MLOW9oMF8aKg0Wc5zzfU10
gk7W92/cuvPDf/uJ69ham19mjDEKo/jQ9NSZJ5+sVitKywcPHjJuUYw2q3uLN5eDTgzMA6VBp4Aw5b6dHSdMIKPDMGxGfeil
UNsDEgBFEAVA0cSB/JHZ6dGRcjbjFYt5Y8xTp07cvH3n7vKKJYTWmgKAUtoS4vSJ43u7OzvbW9Vq1bK94SHv48VbzR54Q0cG
pnKNelNQLGzh5waKhSE/k0MYUYKiJG3UG2G/E0Vhq9GIUjk8XA47zWplqbV45wymqw9WAMxj848NlUrPnP7S+mYllRIhhHKD
Y3EcP33q5GNzh65du1oaLPm5LKHOhYu3qD8+MnbI8XJ7zTqjNJ/NGa09P5NKDWAQACEEI6SVkkoBQkrrVrMZJcnYyEi329lY
W2pVl37j1KGgXdMqzWS8w3Nz77z/4eVr123LIkCs6anJYwvz7737DiXkuXMvaEM/u7t98PFnJw8dM5iEUcS5yPpZY8DzPAAU
xhEAMgaUUkobDWAAaWMQwpmMLxiLoyiT8Q+MTY2NT2/t7J09c3J4qNBstu4v3ZuemtittzpBQJjlHpk7vL72QKbxn/zxn6Zp
ent5d2L+y48dP7m5WQ2jiFGGMZZagzFa6yiJR0aGHUt0ez1jACGEMN7fwRgDgMAAwgghSvD8sWPMymyubxyfn/7G17++uvbw
2rXrA8ViZWsbcyGMDJfu3Xr5xZcW5ucrtdAqzEwcPFLfbXSDgFJaLpdAK07JfnzLskpDpZHRkUJxIF8YKJdLGGPHtpRUUkrH
tsbHDyAEvX4fERJG4fjEuJUZQTw7OTUxNzd7+colTrAQnOTyRd8WrXbrtddek8b6+LMq90pbWzuVre2g23UdO4piqVTGc8Mw
BIBMJjMwkO12e/1eyCg1YIKgh8HEcaSkZJTuF6HZask0iftxEASYu0v3V7HuuYLcvXsnTlMmBPH87OBA9hu/9drU5PTP/utG
K3V6YRTHcT+OtTFa6yROAOF6swFaY0woJXGcbFV2+mHY63a73a4BUFKlaVypVj3Xa3c6URRywbpBV3CeJKlSGmFKIfnd33zx
hfNfuXrliuu4BBA+++Spb3/rj5pBcm25k6RGaaUN6gQdxiiljDFW26nUqhsjI6OEUalk2O1hjJDR6FffO0YIaRXs3Gd2Rliu
VBIBKKWiJLYsO01TyjghZmw4c3j2kG3xRmOPYEyOzi8MDx/45FZlbSdMlNGA4yTWaeq6HoBJkpQm2zPjpUQzShkmhFECYDDG
lBCEEBiTpGqkYH/zhbFPb6wgkQMERhulZJIklhDGGExZvdnRSRfSvtZJvx9gY1Aqk0/vbi7e3kk1kkobY5IkoYwhYzDGcb99
+vFZhqEbtDHSBGuEDafAKGIMc0YYIVKmu3t72YHS9EgmaDUxAEKACU6SZF8ZcZIA4ls77aGhAuW26+TwS+df9AsTV+81NeFK
KYSQVlLKFGGkjWq32xTJTi+O4zSf8ygBjDQjRjAsmLGYsZmxuSn61sLUQLsVzBwYsHWt3WkpKQkmGlAYh3r/xQNu6GxEvOsr
7Vu7Lvnu9/765lpyc7kykMsmUhGMtYEkiTHGGEMS9s8++dipx8dcknbDlBJOCWEE24JzQhgBTpHFCVLRV89Onjs1efzwmM+j
5YfVyDgYQRSFAODYLsak0WoNTkyuVhqtvnJH5/CJ00/ttKNDM5NJEhOkBcOCojSNGUE6TY7ODB+fHbEgHfBRIUMtiiyiPYsI
BoKBzZEtsOB4uECHfFyv1be2arOT5fMnigO8TZBhlCVRSMAgMErJZn1vpxPLBPrdNqkFTifCg77d6XQoo5awjEk7QccVGEU1
iKrLty9vrC2rpEeZI4lT390eLOYpwYIRzrBgGNLwS0cKOG69+c6Fi4uffvDh5fW1h5sr1zOeY7Ddj+JsNkcw0UpWt7eznv/W
OxfAxCSiJYyFa7EwTrmwHctSSsZhL4dqKzffLRXsx+cPD5cHkzhc3VjzMjmBEoqM4EJQoAS128FQjh4ey6ytrZ88e+6VV197
4vTTv/j4smPxXn1tMO/2U5LN5TBmwhJr6xuC82plc2/rId2rrskYlQseJYgQIBgcQVG429y+9fu//erv/N4f5vNZJdPd3dqD
hys3720pJgYzSTNuKpwjhGYdOHtiPJ/hE4e+mi8OW4596/atD957+6++/32C0A9+8M+OO2vzg9IowsTxhYWVB/cLGWd3cwlD
0my321EUM0oQSIKU59g7lSU/Y7/08suMMwSac1IaKodhNJonnoDBDBrNQrtRDbt132X5rOf6WUZZnCTNTvfosZN//4//9Nzz
579y/oW876uobTFscUyx8RzLs20lYwpdIiw7lx8aHBxBhDJKXMEoof1O5fyXj09NT7teRjBq2yIO+3/x+uulQvb5Mye8jBcl
uuDTqZKtkoAzXiwOIMoYtxQgSvDs3ByjJOn3Clmv1SdI5GzOEECUmFzGLTm9e3euUKXS4YKI44gi7NmcGO3aIpVE2K7SOkli
KXiaaGE5f/m9744Wc6PlAsZoZhJ7rg1aK6ls2wpkEhtMmUUZAw2dVlOrFIzK53MGsOs4Mk2xMZ2g/9SJuahe/3G7TTGm6xtL
ReUWBkeIZjLVtsj6vre3Vyc66Ta3LaqN5ASj5589k/Q7IGOMkGCMATDb1ggjBC7VzW6vr1MmHEQ40kka9S1KoijmtmNx3Oyl
yiCt5Op65aO33hCWRQmhYa+zsfmAWtlB38aAOu3G1NSUoN0x3wpaTdQCJjjjHCS3KTVEaK2jOGYuo4ymBgxCgpJBD8JeH+LA
aEBGC4zzxaJGws8NtTtBKlMNqNFuVVavba49tCybWI6PMJJxJwWvVPAdxwr7oUzk6Gh5yEW+YFhrgZCgiDBuMMYI9sFGaUzo
r/qBQlJimUAamyQGpYjRi7eXLt6prFeDJFUW5zvN9md37jY3Lu03tH0ngTBSSqV2bpRAWiiUFq8s3rixODtR9CyhASihhjKN
UGogVVJKBQRTxhBGSZImcaykVEoapUBKA8gYY7RpNhofXP5kvRaNjU21g+DeemN3/TKWHUDkcxYGEUgDQ+y9kKu498T8JEOR
L4xrc0KoQZCC0UZLo6WU2miVJAAQpSpOEsA4CkNlNNpvzMZIrQ1G1Mnc2WjmBqc3dxq7Aa5v3+7u3sZUAJjPWxgDmNbWr5XH
9Z//2R+8cGY+k/EerDz86KOLe52t4ZFyDjEUSSXTwlB5oDhklEwVEM64sBu1rdbeLhcWxogAgJKA4P5m7Y2LlXaa365XmyGo
7sbu2iVChTH6f3snhBAhpLbxadh7OTuY7+3UxksD+VdelnZeWFYU9vvdrjYmmx9AmBktdZx0ut3m2hJJgjDokjBCCMIoqbb6
y+u1d6+uVDusNDrnDIzbW5/du/cOofzRps0YgxBSQL71nb+t7TZe/+bXojCEMHzvwoc/+umbrWZzYf7w8YX5Qj5nux4hJE2S
OI7atQoB1I2iar2zG8TV3e5ez1TbutVNpg7Onnzq2ZuX/v3+4k8I5QBov8iPcIvGGEqw59rf+Zu/u7z42be/du7EwtyFC+//
68/etAlHhAZhXC4MWJbNLQtp2W7sBUE3TOWHFxe55ZbHRnMZz8Vxd7c2ufD8yVOnf/Ef/3D7ylvCzgAC+J/zkEePIgjBrU5v
wHdfOXfm0uUrtUYjjMLnnz0zMz2xsrpx//5DpU1psDg8XNYqfbhe1RLmD0+NlHODg6Uf/fiNexu9Z86/evf6u3s7m7abNVr9
OoI+cjKilM5l3Fiqf/np265tMeFAFAPgsdHRRjMsDiZxnHb6OiedysYqJZnh4aFCsTAxcaCyvdcKlbDg43d/iAA5blY/ivqF
YABQWhOMs56jtJYaMTd7Y2mN265MjdaaC8d2zBMLU829HcodRGCrtnv19t0795aU1pQQxgQAfBEVAP4bYiuRj74kJ58AAAAA
SUVORK5CYII=
  ]],
  -- 帧 8（源帧 #36）
  [[
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
/gOXfoRAP8tTOwAAAABJRU5ErkJggg==
  ]],
  -- 帧 9（源帧 #41）
  [[
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
  ]],
  -- 帧 10（源帧 #46）
  [[
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
O/Gs5zUVMNoh8X0/mXAoBo5lXXj3Yi7Ox/q7MKEEY0opIEQCqJQUUnAuFA8hAFLKIIq0EFoKrTWEAEGogYYQhkF4ZWrmwqXr
xVIXY+TO/OJeK9pbn/1k+opp2tiw4wCiVn1HkFw6nYWGPb+82dlR6EhbuTjqLmaFFMQyNcYCgkgpLqQQkVIqCiM/CKSUACHX
c4WQQkmltYQASBXwyInZe436WoVn8z2rm3vzm3Uh/N2lDzT4vb2FEEEtQr8Zzw4UuwaWNvbWtqrJdE4KhUBoUux7rlJaaa2U
EjwSnAvOhRBSSilEJGTotqMolEpKzoOItwKfc75Urr1zu8pRdnJ2peJK00nsLr2vgirE5PPQpgHC2gsi2b/vSC6T1pi4gVzZ
3J1dWs6lLIJA5LeDIPSCIHA9t9UOfJ9HkVKKRxGPonaz2Wq1Aj8IfN932203WCzXXnrzdzdWos1qqBHr7h2qrU1W1q5jagGt
vxBhIIQ8CvrHv3LwxDOUAIzR9tb65UsX4sQ7PNQ93JXozsUyScdkxDIIxRhoSTC5Z4O41F4Y+qFo+2GjFc2sN24ulPc8fHzi
rGHHLCc1e/2t25d+jjADQN8/H0vBhx46P3T4bKEjyxjZXFu+eOE3JhSOSZJmFAW+bVpENvoz5oH9Q8ywoBKLqxuzK2Un3bHX
Am0vDCVqS9r05bGjJ49MPKaoNXnxP67+90uEmgDAz8B/mI8RwrWtucXF+UShv2ffUKm3N2OZszcuCG/36IFBi8G9SvXOnTmM
MTOZVLpcbWxUWh9eu1X3pACk1JErdJSWN3cH9x96+pnnoelMXnz18q//iVATwM+pX4ipn7MJixpzUxdf2X9wzPNINl9iUDR3
7ibsidHBkbgTz2fypmnhWCbb1x+PhKuXH3kslUvZHfn42OiBn/3n64zXz537aq1Rfee1v5/+6C3TSQAAwBfvIX+o+N4LQg2/
UZ678W55dQ1K7uCQEHJi4uiRI0cXl9fS6ZLSZLcW2R1jM9MzrXbY1dU3sq/70VMTiWTy8uUrXOJ2u/7mKz8qL09bTlLr+5wi
yH0vI1opwmy3UWvV3t5eutqRLxiGEY8nTk6cnF9Y+Xh23bBsCFUpoW9Udzs7OwmSJyeOFTuyL/30ldm7q/WWN79wk1Jm2gml
5H0R91P8ezrCGGMqRFRv1KuNesv1yts7EJFI6N3dyvEj+08d219vtpdX1pwYXV5b+cef/tt/vX2x0WojCAgzAET31Xqv/ge2
PAv2W4KrqQAAAABJRU5ErkJggg==
  ]],
  -- 帧 11（源帧 #51）
  [[
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
  ]],
  -- 帧 12（源帧 #56）
  [[
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
Alp92bnpvwFZJgK4bnyd1gAAAABJRU5ErkJggg==
  ]]
}

local LOGO_FRAME_MS = 120          -- 单帧 120ms；12 帧约 1.44s 一轮，比原速略快，咀嚼感更明显

-- base64 解码（纯 Lua，不依赖 CE 自带库）。按 4 字符一组算，避免大整数溢出。
local B64_MAP = {}
do
  local tbl = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  for i = 1, 64 do B64_MAP[tbl:sub(i, i)] = i - 1 end
end

local function b64decode(s)
  s = s:gsub("[^%w%+/=]", "")          -- 去掉换行/空格
  local out, n = {}, #s
  for i = 1, n, 4 do
    local a = B64_MAP[s:sub(i, i)] or 0
    local b = B64_MAP[s:sub(i + 1, i + 1)] or 0
    local c = B64_MAP[s:sub(i + 2, i + 2)]
    local d = B64_MAP[s:sub(i + 3, i + 3)]
    out[#out + 1] = string.char(a * 4 + math.floor(b / 16))
    if c then out[#out + 1] = string.char((b % 16) * 16 + math.floor(c / 4)) end
    if d then out[#out + 1] = string.char((c % 4) * 64 + d) end
  end
  return table.concat(out)
end

-- 取 Picture 的真实宽度：CE 各版本有的给 Picture.Width，有的只给 Picture.Bitmap.Width
local function picWidth(p)
  local w = 0
  pcall(function() w = p.Width end)
  if not w or w <= 0 then pcall(function() w = p.Bitmap.Width end) end
  return w or 0
end

-- 把 12 帧预解码成 12 个【独立 Picture 对象】。
-- 【为什么不再往 img.Picture 里灌流】社区验证过的写法是「先 createPicture 载好，
-- 再整体赋给 img.Picture」；直接 img.Picture.loadFromStream 在部分 CE 版本上
-- 数据是进去了、控件却不重绘，表现就是「加载成功但看不见图」——真机退回几何头像就是这么来的。
-- 整体赋值还有个好处：12 帧在启动时一次性解码，切帧只是换指针，不重复解码。
-- 【双路径】内存流优先（不落盘）；内存流不可用或解码失败，退回写 %TEMP% 再 loadFromFile。
local function buildLogoPictures()
  local pics, why = {}, nil
  local tmp = os.getenv("TEMP") or os.getenv("TMP") or "."
  for i = 1, #LOGO_FRAMES do
    local ok, data = pcall(b64decode, LOGO_FRAMES[i])
    if ok and type(data) == "string" and #data > 100 then
      local pic

      -- 路径 1：内存流 → createPicture
      local sok, st = pcall(createMemoryStream)
      if sok and st then
        pcall(function() st.write(data, #data) end)
        pcall(function() st.Position = 0 end)
        local pok, pp = pcall(createPicture)
        if pok and pp then
          local lok = pcall(function() pp.loadFromStream(st) end)
          if not lok then lok = pcall(function() pp.LoadFromStream(st) end) end
          if lok and picWidth(pp) > 0 then
            pic = pp
          elseif not why then
            why = "内存流解码失败"
          end
        elseif not why then
          why = "这个 CE 没有 createPicture"
        end
      elseif not why then
        why = "这个 CE 没有 createMemoryStream"
      end

      -- 路径 2：临时文件 → createPicture
      if not pic then
        local path = tmp .. "/aob_wg_" .. i .. ".png"     -- 正斜杠：Windows/Linux 都认
        local f = io.open(path, "wb")
        if f then
          pcall(function() f:write(data) end)
          pcall(function() f:close() end)
          local pok, pp = pcall(createPicture)
          if pok and pp then
            local lok = pcall(function() pp.loadFromFile(path) end)
            if not lok then lok = pcall(function() pp.LoadFromFile(path) end) end
            if lok and picWidth(pp) > 0 then
              pic = pp
            elseif not why then
              why = "PNG 解不开（" .. path .. "）"
            end
          end
        elseif not why then
          why = "写不进临时目录"
        end
      end

      if pic then pics[#pics + 1] = pic end
    end
  end
  return pics, why
end

-- 启动帧循环。失败就保持静态首帧，不影响任何功能。
local function startLogoAnim(owner, img, pics)
  if #pics < 2 then
    LOGO_ANIM_NOTE = "静态首帧（只有 1 帧解码成功）"
    return false
  end
  local ok, t = pcall(createTimer, owner, false)
  if not ok or not t then
    ok, t = pcall(createComponentClass, "TTimer", owner)
    if not ok or not t then
      LOGO_ANIM_NOTE = "静态首帧（这个 CE 版本没有定时器）"
      return false
    end
  end
  local idx = 1
  local alive = true
  pcall(function() t.Interval = LOGO_FRAME_MS end)
  local sok = pcall(function()
    t.OnTimer = function(sender)
      if not alive then return end
      idx = idx % #pics + 1
      if not pcall(function() img.Picture = pics[idx] end) then
        -- 赋值失败就彻底停：宁可退回静态，也不让定时器空转刷错误
        alive = false
        pcall(function() sender.Enabled = false end)
      end
    end
  end)
  if not sok then
    LOGO_ANIM_NOTE = "静态首帧（定时器事件不可写）"
    return false
  end
  LOGO_ANIM_NOTE = string.format("%d 帧 / %dms / Picture 对象", #pics, LOGO_FRAME_MS)
  pcall(function() t.Enabled = true end)
  return true
end

-- 创建图片控件、装载帧、启动动画。任何一步失败都返回 nil（调用方降级到几何头像），
-- 并把「卡在哪一步」写进 LOGO_ANIM_NOTE，⑤ 区第二行能直接看到。
local function loadLogoImage(owner, x, y, size)
  local ok, img = pcall(createImage, owner)
  if not ok or not img then
    ok, img = pcall(createComponentClass, "TImage", owner)
    if not ok or not img then
      LOGO_ANIM_NOTE = "几何版（这个 CE 没有 createImage）"
      return nil
    end
  end

  local pics, why = buildLogoPictures()
  local shown = false
  if #pics > 0 then
    shown = pcall(function() img.Picture = pics[1] end)
  end

  if not shown then
    -- 最后一搏：老 API —— 直接往 img.Picture 里灌首帧文件。
    -- 这条路的观感不如「Picture 对象赋值」，但只要能出图，静态也比退回几何版强。
    local tmp = os.getenv("TEMP") or os.getenv("TMP") or "."
    local path = tmp .. "/aob_wg_1.png"
    for _, fn in ipairs({ "loadFromFile", "LoadFromFile" }) do
      if not shown then
        pcall(function() img.Picture[fn](img.Picture, path) end)
        if picWidth(img.Picture) > 0 then shown = true end
      end
    end
    if shown then
      LOGO_ANIM_NOTE = "静态首帧（" .. tostring(why or "Picture 对象不可用") .. "）"
      pics = {}
    else
      LOGO_ANIM_NOTE = "几何版（" .. tostring(why or "图片解码失败") .. "）"
      pcall(function() img.Destroy() end)        -- 别留一个空白控件在标题条上
      return nil
    end
  end

  pcall(function() img.Parent = owner end)
  pcall(function() img.Left = x end)
  pcall(function() img.Top = y end)
  pcall(function() img.Width = size end)
  pcall(function() img.Height = size end)
  pcall(function() img.Stretch = true end)
  pcall(function() img.Proportional = true end)
  pcall(function() img.Center = true end)
  if #pics > 1 then startLogoAnim(owner, img, pics) end   -- 动画起不来也只是静态，不报错
  return img
end

-- ===== 标题栏 Logo（模块级）=====
-- 【为什么放外面】createUI 已经用掉 Lua 单个函数 200 个局部变量的上限，
-- 再往里加函数就会编译失败（too many local variables）。所以这里做成模块级 + 参数传入。
-- 准星造型：外环 + 四向刻度 + 中心点，呼应工具「定位」的表达；不依赖任何图片文件。
local function decoShape(owner, x, y, w, h, opt)
  if type(_G.createComponentClass) ~= "function" then return nil end
  local ok, shp = pcall(_G.createComponentClass, "TShape", owner)
  if not ok or not shp then return nil end
  pcall(function() shp.Parent = owner end)
  shp.Left = x shp.Top = y shp.Width = w shp.Height = h
  if opt.shape then pcall(function() shp.Shape = opt.shape end) end
  if opt.fill then
    pcall(function() shp.Brush.Style = "bsSolid" end)
    pcall(function() shp.Brush.Color = opt.fill end)
  else
    pcall(function() shp.Brush.Style = "bsClear" end)       -- 空心：只留描边
  end
  if opt.pen then
    pcall(function() shp.Pen.Style = "bsSolid" end)
    pcall(function() shp.Pen.Color = opt.pen end)
    pcall(function() shp.Pen.Width = opt.penW or 1 end)
  else
    pcall(function() shp.Pen.Style = "bsClear" end)
  end
  return shp
end

-- 鲸鱼娘头像：蓝圆头 + 白色女仆头带 + 金色双眼 + 鲸尾。
-- 【为什么用这几个形状】TShape 只有圆/椭圆/矩形/三角/菱形，画不了插画，
-- 所以只保留「24px 下还能读出轮廓」的色块；元素再多就会糊成一团。
-- 【为什么眼睛用金色】蓝底 + 白脸 + 蓝眼试过：24px 下白脸和白头带连成一片，
-- 蓝眼睛又和白脸糊在一起，整张脸读不出五官。改成「白帽沿 + 金瞳」后层次才清楚。
-- 【绘制顺序有讲究】后画的压前画的：鲸尾垫底 → 头 → 头带 → 眼睛。
local function drawLogo(owner, accent, white, gold, K, x, y, s)
  local function U(v) return math.max(1, math.floor(v * K + 0.5)) end
  -- 1) 鲸尾：右侧三角，朝上斜出，根部让头部压住
  decoShape(owner, x + U(s * 0.63), y + U(s * 0.30), U(s * 0.34), U(s * 0.30),
    { shape = "stTriangle", fill = accent })
  -- 2) 头部
  decoShape(owner, x + U(s * 0.17), y + U(s * 0.24), U(s * 0.56), U(s * 0.56),
    { shape = "stCircle", fill = accent })
  -- 3) 白色女仆头带：用【矩形】而不是椭圆 —— 椭圆压扁后读起来像盘子/草帽。
  --    宽度只覆盖头顶中间一小段（0.34s），横跨整个头会变成「白色礼帽」。
  decoShape(owner, x + U(s * 0.28), y + U(s * 0.205), U(s * 0.34), U(s * 0.105),
    { shape = "stRectangle", fill = white })
  -- 4) 金色双眼（24px 下取 2px 下限，再小就看不见了）
  local ed = math.max(2, U(s * 0.075))
  local ey = y + U(s * 0.44)
  decoShape(owner, x + U(s * 0.36), ey, ed, ed, { shape = "stCircle", fill = gold })
  decoShape(owner, x + U(s * 0.48), ey, ed, ed, { shape = "stCircle", fill = gold })
end

local function createUI()
  if form then
    local ok, valid = pcall(function() return form.valid end)
    if ok and valid then
      form.show()
      return
    end
    form = nil
  end

  -- 控件挂载根容器 / 滚动容器 / 操作条顶部坐标。
  -- 【必须在各 helper 闭包定义之前声明】——否则 helper 里的 ROOT 会被解析成全局 nil。
  local ROOT, scb, opTop = nil, nil, 0

  -- ===== 屏幕自适应 =====
  -- CE 是 DPI-unaware 应用，高分屏上窗体会被系统按比例放大，很容易超出屏幕。
  -- 这里探测屏幕高度（拿不到就保持 1:1），按比例缩放整套坐标。
  local function screenDim(...)
    for i = 1, select('#', ...) do
      local f = rawget(_G, (select(i, ...)))
      if type(f) == "function" then
        local ok, v = pcall(f)
        if ok and type(v) == "number" and v > 0 then return v end
      end
    end
    return nil
  end

  local sh = screenDim("getScreenHeight", "getscreenheight", "screenHeight")
  local K = 1
  if sh then
    if sh < 800 then K = 0.74
    elseif sh < 920 then K = 0.83
    elseif sh < 1060 then K = 0.91 end
  end
  local function px(v) return math.floor(v * K + 0.5) end

  -- ================================================================
  -- 视觉规范：深色卡片 + 单一强调色（青蓝）+ 琥珀点缀
  -- 关键点：字段名/正文用高亮白（text），说明文字用中灰（text2）。
  -- 上一版把字段名也用 text2，在深色底上对比度不足，真实环境里几乎看不见。
  -- 所有装饰性调用都走 pcall：个别 CE 版本缺属性时自动降级，绝不影响功能
  -- ================================================================
  -- 【踩坑记录·配色全反】CE/Lazarus 的颜色是 Windows COLORREF（$00BBGGRR，字节序「蓝绿红」），
  --   而我们习惯写的是 HTML 的 #RRGGBB。直接写 0x38BDF8 渲染出来是 #F8BD38（琥珀），
  --   卡片底 0x141A24 会变成 #241A14（偏棕）—— 整块主题反着来。
  --   统一用 CR() 转一道，源码里仍然写看得懂的 #RRGGBB。
  local function CR(hex)
    -- RGB hex 里高位是红、低位是蓝；COLORREF 要求低位是红 → 三个字节整体倒过来
    local b = hex % 256
    local g = math.floor(hex / 256) % 256
    local r = math.floor(hex / 65536) % 256
    return b * 65536 + g * 256 + r
  end

  local C = {
    bg     = CR(0x0A0D13),   -- 窗体底（近黑蓝）
    head   = CR(0x0F141C),   -- 标题条 / 底条
    card   = CR(0x141A24),   -- 卡片底
    input  = CR(0x070A0F),   -- 输入控件底（比卡片更暗，形成"凹陷"感）
    line   = CR(0x252F3E),   -- 自绘分隔线 / 卡片边框
    btn    = CR(0x1C2431),   -- 次按钮底
    badge  = CR(0x223047),   -- 版本徽章底（明显亮于标题条，才看得出是块牌子）
    accent = CR(0x38BDF8),   -- 强调色（青蓝）：主按钮 + 标题竖条
    gold   = CR(0xE0A64B),   -- 点缀色（琥珀）
    text   = CR(0xEEF3FB),   -- 主文字 / 字段名（高亮白）
    text2  = CR(0xA7B5C9),   -- 说明文字（中等灰，保证可读）
    onDark = CR(0x06121C),   -- 强调色按钮上的文字色
  }

  -- 字号（磅）。9 磅 ≈ 12px，10 磅 ≈ 14px，12 磅 ≈ 16px
  local FS_TITLE, FS_SEC, FS_BODY, FS_HINT = 12, 10, 9, 9

  -- ===== 窗体与客户区尺寸 =====
  -- 注意：Lazarus 的 form.Width 含边框、form.Height 含标题栏，
  -- 直接拿 Width 当内容宽度会让右侧控件被裁掉 → 这里一律按客户区排版。
  local DW = 900          -- 设计稿宽度
  local HEAD_H = 76      -- 标题条高
  local GAP = 12         -- 卡片间距
  local PAD = 22         -- 外边距
  local CH_1, CH_2, CH_3, CH_4, CH_5 = 140, 110, 92, 68, 152
  local BAR_H = 56       -- 底部操作条高
  local CONTENT_H = HEAD_H + GAP + CH_1 + GAP + CH_2 + GAP + CH_3 + GAP + CH_4
    + GAP + CH_5 + GAP + BAR_H + PAD


  -- 样式助手：只设视觉属性，任何一个属性缺失都不会抛错
  --
  -- 【踩坑记录】字号必须用 Font.Size（标准「磅」属性），绝对不能用 Font.Height：
  --   Lazarus 里 Font.Height 是「设备无关像素」，负值=像素、正值=磅，
  --   不同 Lazarus 版本/CE 构建对正值的换算不一致，CE 7.7 上设成正值后
  --   Label 的文字直接不绘制（控件还在、字全没了），而 Button/CheckBox 不受影响。
  --   Font.Size 在各版本都是稳定的磅值，失效时也只是字号不变，不会吞字。
  local THEME = {}   -- 记录目标配色，窗体 show 之后统一再刷一遍（见文件末尾 retheme）

  local function style(c, o)
    o = o or {}
    if o.bg then pcall(function() c.Color = o.bg end) end
    if o.fg then pcall(function() c.Font.Color = o.fg end) end
    if o.bold then pcall(function() c.Font.Style = "fsBold" end) end
    if o.size then pcall(function() c.Font.Size = o.size end) end
    if o.border then pcall(function() c.BorderStyle = o.border end) end
    if o.align then pcall(function() c.Alignment = o.align end) end
    -- Label 是图形控件，默认会画自己的底色；设成透明，文字才不会带出一块方块
    pcall(function() c.Transparent = true end)
    -- 关掉自动尺寸：否则 Label 会按文字自适应宽度，右对齐标签会压到旁边的输入框
    pcall(function() c.AutoSize = false end)
    THEME[#THEME + 1] = { c = c, bg = o.bg, fg = o.fg, size = o.size }
    return c
  end

  -- ===== 布局登记簿 =====
  -- 记录每个控件的矩形，窗体建好后统一做一次「越界 + 同层重叠」自检，
  -- 有问题才写进日志，避免用户遇到错位却查不出原因。
  local BOX = {}
  local function reg(name, l, t, w, h, layer)
    BOX[#BOX + 1] = { n = name, l = l, t = t, w = w, h = h, lay = layer or 0 }
  end

  -- 文字可见性登记表：Label 是图形控件（文字画在窗体画布上），
  -- 窗口控件（Panel/Button…）永远盖在画布之上，两者相交就等于「那行字看不见」。
  local LABELS, WINOBJS = {}, {}
  local function newLabel()
    local l = createLabel(ROOT)
    LABELS[#LABELS + 1] = l
    return l
  end

  -- ===== 背景绘制方式（图形控件 / 扁平降级）=====
  -- 【踩坑记录·这次「界面所有文字消失」的真正原因】
  --   Lazarus 里 TLabel 是「图形控件」(TGraphicControl)：文字画在**父容器的画布**上，
  --   而不是自己的窗口里；TPanel / TButton 这类「窗口控件」是独立 HWND，
  --   永远盖在父容器画布之上 —— 卡片面板一旦压住 Label 所在区域，那行字就彻底看不见
  --   （控件还在、字全没了）。这正是之前「Label 全没、Button/CheckBox 正常」的原因。
  --   对策：卡片背景改用 TShape（同样是图形控件）。图形控件之间按**创建顺序**叠放，
  --   先建 Shape（卡片底）、再建 Label（文字），文字就压在卡片底之上，不会被盖住。
  --   万一这个 CE 版本没有 createShape，则自动降级为「扁平模式」：不画卡片底，
  --   窗体底色直接当卡片色；此时没有任何窗口控件压住 Label，文字照样看得见。
  local SHAPE_OK = false
  local CARD_BG, HEAD_BG = C.bg, C.bg
  local SHAPES = {}          -- 所有图形控件，show 之前统一 SendToBack

  -- ===== 造一个图形控件（TShape）=====
  -- 【踩坑记录·createShape 不是 CE 官方 API】
  --   CE 官方 Lua API 里**没有** createShape（wiki 的 Lua:createShape 页面是空的）。
  --   社区通用写法是 createComponentClass('TShape', owner)：
  --       local sh = createComponentClass('TShape', parent); sh.Parent = parent
  --   TShape 继承自 TGraphicControl（和 TLabel 同层）—— 画在父容器画布上，
  --   不会像 TPanel 那样盖住文字。之前直接 pcall(createShape, form) 永远失败，
  --   于是 SHAPE_OK 一直是 false，深色卡片底一次都没画出来（用户日志：
  --   「卡片底=扁平模式(无卡片底)」）。
  --   两条路都试：优先 createShape（万一某个 CE 构建真的加了），再退回官方组件类。
  local function newShape(parent)
    if type(_G.createShape) == "function" then
      local ok, sh = pcall(_G.createShape, parent)
      if ok and sh then return sh end
    end
    if type(_G.createComponentClass) == "function" then
      local ok, sh = pcall(_G.createComponentClass, "TShape", parent)
      if ok and sh then
        pcall(function() sh.Parent = parent end)
        return sh
      end
    end
    return nil
  end

  -- 卡片 / 分隔条：所有面板先于内容控件创建，保证压在最底层不遮挡
  -- createPanel 若在个别 CE 版本缺失，pcall 兜底降级为「没有卡片背景但功能照常」
  local function panel(x, y, w, h, bg, border)
    local okp, p = pcall(createPanel, ROOT)
    if not okp or not p then return nil end
    p.Left = x p.Top = y p.Width = w p.Height = h
    pcall(function() p.Color = bg end)
    pcall(function() p.BorderStyle = border or "bsNone" end)
    WINOBJS[#WINOBJS + 1] = p
    return p
  end

  -- 背景块（图形控件）：画在窗体画布上，位于所有 Label 之下，不会遮挡文字
  local function bgRect(x, y, w, h, fill, border)
    if not SHAPE_OK then return nil end
    local oks, shp = pcall(newShape, ROOT)
    if not oks or not shp then return nil end
    shp.Left = x shp.Top = y shp.Width = w shp.Height = h
    pcall(function() shp.Brush.Style = "bsSolid" end)
    pcall(function() shp.Brush.Color = fill end)
    pcall(function() shp.Pen.Style = "bsSolid" end)
    pcall(function() shp.Pen.Color = border or fill end)
    pcall(function() shp.Pen.Width = 1 end)
    -- 图形控件（TShape）与 TLabel 同层，都画在窗体画布上。
    -- TGraphicControl 之间的上下关系由父容器的控件顺序决定：
    --   SendToBack → 排到最后（最底）；BringToFront → 排到最前（最上）。
    -- 所以卡片底要 SendToBack，文字 Label 自然就在它上面。
    pcall(function() shp.SendToBack() end)
    SHAPES[#SHAPES + 1] = shp
    -- 记下边框色，show 之后要补刷一遍（TShape 的 Pen.Color 也可能因为还没建 handle 而被丢弃）
    THEME[#THEME + 1] = { c = shp, shape = true, bg = fill, pen = border or fill }
    return shp
  end

  -- 1px 水平分隔线（自绘，避免系统 BorderStyle 的亮色边框毁掉深色主题）
  local function hline(x, y, w, color)
    local col = color or C.line
    if SHAPE_OK then return bgRect(x, y, w, 1, col, col) end
    return panel(x, y, w, 1, col, "bsNone")
  end

  -- 文本标签
  -- Label 是图形控件，只能画在「父容器画布」上，所以底色必须与所在背景一致，
  -- 否则（Transparent 不生效时）会出现一块突兀的色块。
  local function label(x, y, w, h, text, o)
    o = o or { fg = C.text }
    o.bg = o.bg or CARD_BG
    local l = newLabel()
    l.Left = x l.Top = y l.Width = w l.Height = h or px(18)
    l.Caption = text
    style(l, o)
    return l
  end

  -- 卡片标题左侧的强调竖条
  local function tick(x, y, col, h)
    local c2 = col or C.accent
    if SHAPE_OK then return bgRect(x, y, px(4), h or 16, c2, c2) end
    local okp, p = pcall(createPanel, ROOT)
    if not okp or not p then return nil end
    p.Left = x p.Top = y p.Width = px(4) p.Height = px(h or 16)
    pcall(function() p.Color = c2 end)
    pcall(function() p.BorderStyle = "bsNone" end)
    WINOBJS[#WINOBJS + 1] = p
    return p
  end

  -- 输入类控件统一样式
  local function inputStyle(c)
    style(c, { bg = C.input, fg = C.text })
    pcall(function() c.BorderStyle = "bsSingle" end)
    return c
  end
  -- 次要按钮
  local function ghost(c)
    style(c, { bg = C.btn, fg = C.text })
    return c
  end

  -- ===== 关掉 Windows 主题（Visual Styles）=====
  -- 【踩坑记录·勾选框文字在深色底上几乎看不见】
  --   CE 的 CECheckbox 走系统主题绘制，**不吃 Font.Color**：
  --   我们明明设了 fg = C.text（近白色），真机上文字仍然是系统默认的深灰/黑，
  --   压在深色卡片上几乎看不清（用户实拍确认）。
  --   社区验证的解法：先把控件的 Visual Style 关掉，
  --   它就会退回走 WM_CTLCOLORSTATIC，字色这才用上我们自己的 Font.Color。
  --   用法：uxtheme.SetWindowTheme(handle, '', '', 0)
  --   注意：这会连方块外观一起退回经典样式（方块变成经典黑白勾），
  --   换来的是文字可读 —— 可读性优先。
  local UNTHEMED = 0
  -- 给控件设置 Windows 主题：
  --   theme = ''        → 完全关闭 Visual Styles（勾选框用，字色这才听我们的）
  --   theme = 'Explorer'→ 恢复系统默认主题
  --   theme = 'DarkMode_CFD' → 请求系统深色（编辑框 / 下拉框用，底色字色一起变）
  local function setWinTheme(ctrl, theme)
    if not ctrl then return false end
    local okh, h = pcall(function() return ctrl.handle end)
    if not okh or not h or h == 0 then return false end
    local ok, r = pcall(function()
      return executeCodeLocalEx('uxtheme.SetWindowTheme', h, theme or '', '', 0)
    end)
    if ok and r ~= nil then
      UNTHEMED = UNTHEMED + 1
      return true
    end
    return false
  end
  local function untheme(ctrl)
    return setWinTheme(ctrl, '')
  end
  -- 勾选框统一样式：先关主题（字色才生效），再给浅色字 + 与卡片一致的底色
  local function checkStyle(c)
    untheme(c)
    style(c, { bg = CARD_BG, fg = C.text2 })
    pcall(function() c.Font.Color = C.text2 end)
    return c
  end

  -- ===== 深色外观（按钮 / 编辑框 / 下拉框）=====
  --
  -- 【为什么这些控件一直是系统原生白底】
  --   * 按钮：Lazarus 的 TButton 绘制用的是 **Face / Light / Dark** 三个属性，
  --     **不是** TControl.Color —— 所以之前给按钮设 Color 一点用都没有。
  --   * 编辑框 / 下拉框：真正的原生 EDIT / COMBOBOX，底色完全由 Windows 主题决定。
  --   社区通用做法：先把 Visual Styles 关掉（或换成深色主题类），再自己设颜色。
  --
  -- 【安全底线 · 为什么底色取「中间调」】
  --   万一某个 CE 版本不让改成功（底色变了字色没变），深底 + 黑字就彻底看不见了。
  --   所以这里的底色一律选**中间调**：明显亮于卡片底、但没亮到黑字看不清。
  --     字色生效 → 浅字配深底，好看；
  --     字色没生效 → 黑字配中间底，依然看得见。
  --   绝不会出现「白底浅字」这种彻底看不见的情况。
  local DARK = {
    face  = CR(0x3C4A63),   -- 次要按钮面（中间调）
    light = CR(0x4E5E7A),
    dark  = CR(0x2B3648),
    input = CR(0x33405A),   -- 输入框底（若系统深色主题生效则用它兜底）
    fg    = CR(0xE6EDF3),   -- 浅色字
  }
  local DARKSNAP = {}       -- 原始状态快照，用于「一键还原」
  local DARKTARGETS = {}    -- 需要跟着切换的控件
  local DARK_ON = false

  -- 登记一个控件（kind: btn / btnMain / edit / combo）
  local function snapDark(c, kind)
    if not c then return end
    local s = { c = c, kind = kind }
    pcall(function() s.face = c.Face end)
    pcall(function() s.light = c.Light end)
    pcall(function() s.dark = c.Dark end)
    pcall(function() s.bg = c.Color end)
    pcall(function() s.fg = c.Font and c.Font.Color end)
    DARKSNAP[#DARKSNAP + 1] = s
    DARKTARGETS[#DARKTARGETS + 1] = c
  end

  -- 切换深色外观。返回 (按钮数, 输入类数, 是否有控件没能改)
  local function applyDark(on)
    DARK_ON = (on and true or false)
    local nBtn, nInput, nFail = 0, 0, 0
    for _, s in ipairs(DARKSNAP) do
      local c = s.c
      if s.kind == 'btn' or s.kind == 'btnMain' then
        if on then
          local face = (s.kind == 'btnMain') and C.accent or DARK.face
          local fg   = (s.kind == 'btnMain') and C.onDark or DARK.fg
          -- Color 和 Face 都设：不同 Lazarus/CE 版本走的绘制属性不一样，
          -- 两个都写，哪条路通算哪条。
          pcall(function() c.Color = face end)
          pcall(function() c.Face = face end)
          pcall(function() c.Light = DARK.light end)
          pcall(function() c.Dark = DARK.dark end)
          pcall(function() c.Font.Color = fg end)
        else
          pcall(function() c.Color = s.bg end)
          pcall(function() c.Face = s.face end)
          pcall(function() c.Light = s.light end)
          pcall(function() c.Dark = s.dark end)
          pcall(function() c.Font.Color = s.fg end)
        end
        nBtn = nBtn + 1
      else
        -- 编辑框 / 下拉框：交给系统深色主题
        -- 【安全】这里**刻意不设 Color、也不设 Font.Color** ——
        --   输入框在 CE 里不吃 Font.Color（实测：明明设了浅色，真机仍是黑字）。
        --   万一它只吃 Color 不吃字色，就会变成「深底黑字」彻底看不见；
        --   万一它只吃字色不吃 Color，就会变成「白底浅字」也彻底看不见。
        --   所以两个都不碰，只让系统主题整体接管：
        --     主题生效 → 深底白字；主题没生效 → 白底黑字。两种都可读。
        if on then
          setWinTheme(c, 'DarkMode_CFD')
        else
          setWinTheme(c, 'Explorer')
          pcall(function() c.Color = s.bg end)
          pcall(function() c.Font.Color = s.fg end)
        end
        nInput = nInput + 1
      end
      -- 读回校验：底色属性写不进去的控件要报出来（说明这个 CE 版本改不动）
      local got = nil
      pcall(function() got = c.Face end)
      if on and (s.kind == 'btn' or s.kind == 'btnMain') and got == nil then
        nFail = nFail + 1
      end
    end
    return nBtn, nInput, nFail
  end

  form = createForm(false)
  form.Caption = "AOB 符号脚本生成器"
  form.Width = px(DW) + 16
  form.Height = px(CONTENT_H) + 30   -- 临时值；下方按屏幕高度重算（启用滚动容器时窗体自适应）
  form.Position = "poScreenCenter"
  style(form, { bg = C.bg })

  -- ===== 滚动容器（TScrollBox）=====
  -- 把「标题条 + 5 张卡」全部装进滚动容器；窗体高度按屏幕自适应，
  -- 内容超高时自动出现滚动条。底部「操作」条（复制 / 另存为 / 加到列表）固定在窗体上，
  -- 始终可见、始终够得着 —— 解决小屏装不下整窗、下拉被任务栏切掉的问题。
  -- 【CE 兼容性】TScrollBox 用 createComponentClass('TScrollBox', form) 创建（社区验证可用）；
  -- 若该 CE 版本不支持，则退回「固定高度、不滚动」的旧布局（功能零影响）。
  ROOT  = form                -- 当前控件挂载的父容器：默认窗体；滚动启用后切到 scb
  scb   = nil                 -- 滚动容器
  opTop = 0                   -- 底部操作条在窗体客户区的顶部坐标（滚动启用后生效）
  local function createScrollBox(owner)
    if type(_G.createComponentClass) == "function" then
      local ok, b = pcall(_G.createComponentClass, "TScrollBox", owner)
      if ok and b then b.Parent = owner; return b end
    end
    return nil
  end

  -- 探测图形控件（TShape）是否可用：可用就用它画卡片底（文字压在卡片底之上，不会被盖住）；
  -- 不可用则走扁平模式（不画卡片底，窗体底色直接当卡片色，文字同样不被任何窗口控件遮挡）。
  do
    local shp = newShape(ROOT)
    if shp then
      local ok1 = pcall(function() shp.Brush.Style = "bsSolid" end)
      local ok2 = pcall(function() shp.Brush.Color = C.card end)
      local ok3, got = pcall(function() return shp.Brush.Color end)
      SHAPE_OK = (ok1 and ok2 and ok3 and got == C.card)
      pcall(function() shp.Visible = false end)   -- 探针，丢弃
    end
  end
  CARD_BG = SHAPE_OK and C.card or C.bg
  HEAD_BG = SHAPE_OK and C.head or C.bg

  -- 真实客户区尺寸：所有横向定位都以它为基准，右侧元素贴右对齐
  local CW, CH = 0, 0
  pcall(function() CW = form.ClientWidth end)
  pcall(function() CH = form.ClientHeight end)
  if type(CW) ~= "number" or CW < 400 then CW = px(DW) end
  if type(CH) ~= "number" or CH < 300 then CH = px(CONTENT_H) end

  local CX = px(PAD)              -- 卡片左边界
  local CARDW = CW - 2 * px(PAD)  -- 卡片宽
  local IX = px(PAD + 34)         -- 内容左边界（给标题栏 40px 头像留位）
  local IW = CARDW - 2 * px(16)   -- 内容宽

  -- 创建滚动容器（仅当该 CE 版本支持 TScrollBox 时；不支持则 ROOT 保持 form，退回旧布局）
  do
    local okSB, sb = pcall(createScrollBox, form)
    if okSB and sb then
      scb = sb
      scb.Left = 0; scb.Top = 0; scb.Width = CW
      pcall(function() scb.AutoScroll = true end)
      pcall(function() scb.Color = C.bg end)
      pcall(function() scb.VertScrollBar.Visible = true end)
      pcall(function() scb.HorzScrollBar.Visible = false end)
      pcall(function() scb.BorderStyle = "bsNone" end)
      ROOT = scb                    -- 此后标题条 + 5 卡 全部装进滚动容器
    end
  end

  local function RX(w)            -- 右对齐元素的左边界（w 需已 px 化）
    return CW - px(PAD + 16) - w
  end

  -- 卡片标题：竖条 + 标题 + 可选右侧副说明
  -- 入参 x / y / rightLimit 都是「已按屏幕比例缩放过」的真实像素，
  -- 里面的尺寸用 px() 转成设计稿像素，避免两套坐标混用导致错位。
  -- 估算一段文字的渲染宽度（像素）。
  --   用途：给标题留出**刚好够**的空间。写死宽度会出事：
  --   「② 符号与定位」是 6 个全角字，固定 104px 装不下 → 最后一个字被裁掉，
  --   副标题又从固定位置开始 → 两段文字直接叠在一起（用户实拍）。
  --   宽度系数是**实测校准**出来的：
  --     用户实拍（125% DPI 的 Win11，CE 7.7）：10 磅的全角汉字实际渲染约 19px/字，
  --     即 约 1.9 em。取 2.0 留一点余量，保证「宁可空一点也不压字」。
  --     ASCII 取 0.9 em（英文/数字比全角窄，但留余量）。
  --   返回值取整，避免把小数带进控件坐标。
  local function estTextWidth(s, sizePt)
    local w = 0
    -- 按 UTF-8 切分：一个中文字 3 字节，ASCII 1 字节
    for ch in s:gmatch("[\1-\127\194-\244][\128-\191]*") do
      if #ch > 1 then w = w + sizePt * 2.0 else w = w + sizePt * 0.9 end
    end
    return math.floor(w + 0.5)
  end

  local function cardTitle(x, y, text, sub, col, rightLimit)
    tick(x, y + px(1), col, 15)
    -- 标题宽度按文字长度动态给；副标题紧跟在标题实际宽度之后，绝不压字
    local tw = estTextWidth(text, FS_SEC) + 8
    label(x + px(12), y - px(2), tw, px(20), text,
      { bg = CARD_BG, fg = C.text, bold = true, size = FS_SEC })
    local subLbl = nil
    if sub and sub ~= "" then
      local lim = rightLimit or (CW - px(PAD + 16))
      local sx = x + px(12) + tw + px(10)
      local sw = lim - sx
      if sw > 40 then
        subLbl = label(sx, y - px(1), sw, px(18), sub,
          { bg = CARD_BG, fg = C.text2, size = FS_HINT })
      end
    end
    return subLbl
  end

  -- ===== 背景层：标题条 + 5 张卡片 + 底部操作条 =====
  -- 全部用图形控件（TShape）绘制：它们与 Label 同在窗体画布上，按创建顺序叠放，
  -- 先建底、后建字，文字永远在卡片底之上，不会被盖住。
  bgRect(0, 0, CW, px(HEAD_H), C.head, C.line)                      -- 标题条
  bgRect(0, px(HEAD_H - 3), CW, px(3), C.accent, C.accent)           -- 标题条下的强调线

  local y = HEAD_H + GAP
  bgRect(CX, px(y), CARDW, px(CH_1), C.card, C.line); hline(CX, px(y + CH_1 - 1), CARDW, C.line)
  local y1 = y; y = y + CH_1 + GAP
  bgRect(CX, px(y), CARDW, px(CH_2), C.card, C.line); hline(CX, px(y + CH_2 - 1), CARDW, C.line)
  local y2 = y; y = y + CH_2 + GAP
  bgRect(CX, px(y), CARDW, px(CH_3), C.card, C.line); hline(CX, px(y + CH_3 - 1), CARDW, C.line)
  local y3 = y; y = y + CH_3 + GAP
  bgRect(CX, px(y), CARDW, px(CH_4), C.card, C.line); hline(CX, px(y + CH_4 - 1), CARDW, C.line)
  local y4 = y; y = y + CH_4 + GAP
  bgRect(CX, px(y), CARDW, px(CH_5), C.card, C.line); hline(CX, px(y + CH_5 - 1), CARDW, C.line)
  local y5 = y; y = y + CH_5 + GAP

  -- ===== 窗体高度自适应屏幕：保证底部「操作」条始终在可视范围内 =====
  -- 内容（标题条 + 5 卡）整体装进上面的滚动容器 scb；若内容高过可用屏高，
  -- scb 自动出现滚动条，操作条固定在窗体底部、永远够得着。
  local content_h = px(y)                       -- 全部内容设计高度（标题条 + 卡片）
  local OPS_RESERVE = px(52)                    -- 底部工具条高度（真实像素；px() 已含 DPI 缩放）
  local screen_avail = 900
  pcall(function() screen_avail = math.max(500, (getScreenHeight() or 900) - 64) end)
  local client
  if scb then
    -- 有滚动容器：窗体收敛到屏高，内容超出部分靠滚动条查看，工具条始终在底部可见
    client = math.min(content_h + OPS_RESERVE, math.max(220, screen_avail - 30))
  else
    -- 无滚动容器（该 CE 版本不支持 TScrollBox）：退回原「全高布局」，与旧版行为一致
    client = content_h + OPS_RESERVE
  end
  form.Height = client + 30                      -- 窗体（含标题条 30px）
  if scb then scb.Height = math.max(60, client - OPS_RESERVE) end
  -- 【坐标系】opTop 是【真实像素】，后面绝不能再套 px()（否则高 DPI/小屏会二次缩放 → 按钮上浮「飘」在内容中间）
  opTop = (scb and scb.Height or content_h)

  -- ===== 控件登记 =====
  -- barAdd 为预留的空操作接口（当前底部是固定工具条，无需折叠）。
  local function barAdd(c) end

  -- ===== 标题条 =====
  -- 左侧 Logo（24px 鲸鱼娘头像）；没有图形控件能力时退回一根强调竖条，左侧不留空
  -- 优先用内嵌的真图（3D 手办风）；加载不出来再退回几何头像，最后退回竖条。
  -- 【不加局部变量】createUI 已经贴着 200 个局部变量的上限，这里用 do 块 + 内联条件。
  do
    if not loadLogoImage(ROOT, px(9), px(9), px(40)) then
      if SHAPE_OK then
        drawLogo(ROOT, C.accent, C.text, C.gold, K, px(12), px(11), px(24))
      else
        tick(IX - px(14), px(16), C.accent, 26)
      end
    end
    -- 头像到底走到了哪一步：真机不动/不显示时，这行是唯一线索
    log("[界面] 标题栏头像：" .. LOGO_ANIM_NOTE)
  end
  label(IX, px(11), px(380), px(24), "AOB 符号脚本生成器",
    { bg = HEAD_BG, fg = C.text, bold = true, size = FS_TITLE })
  -- 副标题框宽给到刚好放得下文字为止（右边要让出「深色外观」开关的位置）
  label(IX, px(37), px(420), px(18), "一行指令 → 一份可直接启用的常规 AOB 脚本",
    { bg = HEAD_BG, fg = C.text2, size = FS_HINT })
  -- 版本徽章：深色小方块 + 琥珀描边 + 琥珀色文字
  -- 【踩坑记录·徽章整个消失（用户真机实拍）】
  --   老写法是「琥珀色 TShape 当底 + 深色字」，这依赖两件事同时成立：
  --     ① TShape 真的画出来了  ② 它压在所有 Label 之下、却盖在标题条之上
  --   但 style() 给所有 Label 都设了 Transparent = true —— Label **不画自己的背景色**，
  --   于是底色 100% 依赖那个 TShape；TShape 一旦被别的图形控件盖住，
  --   剩下的就是「深色字画在深色底上」= 一个字都看不见（真机就是这样整块消失的）。
  --   现在改成：文字固定用琥珀色（深色底上永远看得见），色块只当装饰（被盖也不影响可读性）。
  --   Label 的 bg 填成与标题条同色，和真机渲染一致（预览也就不会画出假色块）。
  --   宽度必须够放下「v2.1.4 · 2026-11-03」，否则居中对齐会把两端裁掉（曾经只剩「.3 · 2026-1」）
  local bw = math.max(px(120), estTextWidth(PLUGIN_VER .. "  ·  " .. BUILD_STAMP, FS_HINT) + 24)
  bgRect(RX(bw), px(20), bw, px(22), C.badge, C.gold)
  local lblBadge = label(RX(bw), px(22), bw, px(18), PLUGIN_VER .. "  ·  " .. BUILD_STAMP,
    { bg = HEAD_BG, fg = C.gold, bold = true, size = FS_HINT, align = "taCenter" })

  -- 「深色外观」开关：把按钮 / 输入框 / 下拉框从系统原生白底换成深色，
  -- 和卡片风格统一。默认关闭（保持系统原生，最稳），随时可一键还原。
  chkDark = createCheckBox(ROOT)
  chkDark.Left = RX(bw) - px(152) chkDark.Top = px(28) chkDark.Width = px(140) chkDark.Height = px(22)
  chkDark.Caption = "深色外观"
  chkDark.Hint = "把按钮、输入框、下拉框从系统原生白底换成深色，和卡片风格统一；随时可以再点一下还原"
  style(chkDark, { bg = HEAD_BG, fg = C.text2 })
  pcall(function() chkDark.Font.Color = C.text2 end)
  untheme(chkDark)
  reg("chkDark", chkDark.Left, chkDark.Top, chkDark.Width, chkDark.Height, 0)
  chkDark.OnClick = function()
    local on = (chkDark.Checked and true) or false
    local nBtn, nInput, nFail = applyDark(on)
    if on then
      log(string.format("[深色外观] 已开启：按钮 %d 个、输入框/下拉框 %d 个改为深色。"
        .. "底色特意取中间调 —— 就算这个 CE 版本不让改字色，黑字配中间底也照样看得见",
        nBtn, nInput))
      if nFail > 0 then
        log(string.format("[深色外观] 注意：有 %d 个按钮的底色属性这个 CE 版本不支持，"
          .. "它们会保持系统原样（不影响使用）", nFail))
      end
    else
      log("[深色外观] 已关闭：按钮 / 输入框 / 下拉框全部还原为系统原生外观")
    end
  end

  -- 控件统一在此声明，保证事件回调能捕获到局部变量（而不是全局 nil）
  local edtSym, edtDesc, edtGuard
  local chkOff, chkLatch, chkCrypt, chkPatch, chkVerbose, chkSelfCheck
  local cbSem, cbPatchOp, cbPatchVt, edPatchVal, edPatchOff
  local btnGetCode, btnGen, btnClearIn, btnClear, btnCopy, btnSave, btnAddTable
  local chkDark
  local lblInsn, lblFmt, lblSym, lblDesc, lblGuard, lblSem, lblSemHint
  local lblPatchOp, lblPatchVal, lblPatchOff, lblPatchVt

  -- ===== ① 指令内容 =====
  cardTitle(IX, px(y1 + 8), "① 指令内容", "支持「地址 - 字节 - 指令」与纯指令两种写法", nil, RX(px(96)) - px(12))

  btnGetCode = createButton(ROOT)
  btnGetCode.Left = RX(px(96)) btnGetCode.Top = px(y1 + 2) btnGetCode.Width = px(96) btnGetCode.Height = px(26)
  btnGetCode.Caption = "取代码"
  btnGetCode.Hint = "取指令：优先取地址列表选中的记录；若没选记录，则取内存查看器反汇编里选中的一行/一段"
  ghost(btnGetCode)
  reg("btnGetCode", btnGetCode.Left, btnGetCode.Top, btnGetCode.Width, btnGetCode.Height, 1)
  snapDark(btnGetCode, "btn")
  btnGetCode.OnClick = function()
    local al = getAddressList()
    local mr = nil
    if al then
      local okSel, sel = pcall(function() return al.getSelectedRecord() end)
      if okSel then mr = sel end
      if not mr then
        pcall(function()
          for i = 0, al.Count - 1 do
            local m = al.getMemoryRecord(i)
            if m and m.Selected then mr = m break end
          end
        end)
      end
    end
    if not mr then
      if grabDisasmToMemo() then return end
      log("[错误] 请先在地址列表选中一条指向指令的记录（[找出是什么访问了/改写了这个地址]得到的），或在内存查看器反汇编里选中指令后点[取代码]")
      return
    end
    local rawAddr = tostring(mr.Address or "")
    local addr = resolveAddr(rawAddr)
    if not addr then
      log("[错误] 选中记录的地址无法解析（" .. rawAddr .. "）：这一条是脚本条目或符号还没值（地址显示 ?? / <脚本>），不是指令地址。请改选「找出是什么访问了/改写了这个地址」结果里那一条，或把整行直接粘进输入框再点[生成脚本]")
      return
    end
    local ok, line = pcall(disassemble, addr)
    if not ok or not line then
      log(string.format("[错误] 无法反汇编 %X，确认 CE 已附加进程", addr))
      return
    end
    setMemo(edtInsn, tostring(line))
    log("[取代码] " .. tostring(line))
  end

  lblInsn = newLabel()
  lblInsn.Left = IX lblInsn.Top = px(y1 + 30) lblInsn.Width = IW lblInsn.Height = px(18)
  lblInsn.Caption = "粘贴那一行指令（可多行）"
  style(lblInsn, { bg = CARD_BG, fg = C.text2, size = FS_HINT })
  reg("lblInsn", lblInsn.Left, lblInsn.Top, lblInsn.Width, lblInsn.Height, 1)

  edtInsn = createMemo(ROOT)
  edtInsn.Left = IX edtInsn.Top = px(y1 + 48) edtInsn.Width = IW edtInsn.Height = px(64)
  edtInsn.ScrollBars = "ssBoth"
  edtInsn.Lines.Clear()
  inputStyle(edtInsn)
  pcall(function() edtInsn.Font.Name = "Consolas" end)
  pcall(function() if edtInsn.Font.Name ~= "Consolas" then edtInsn.Font.Name = "Courier New" end end)
  reg("edtInsn", edtInsn.Left, edtInsn.Top, edtInsn.Width, edtInsn.Height, 1)
  snapDark(edtInsn, "edit")

  lblFmt = newLabel()
  lblFmt.Left = IX lblFmt.Top = px(y1 + 114) lblFmt.Width = IW lblFmt.Height = px(18)
  lblFmt.Caption = "格式: 004A2B3C - 89 81 60 55 00 00 - mov [ecx+00005560],eax   （也认纯指令，空格不标准也能解析）"
  style(lblFmt, { bg = CARD_BG, fg = C.text2, size = FS_HINT })
  reg("lblFmt", lblFmt.Left, lblFmt.Top, lblFmt.Width, lblFmt.Height, 1)

  -- ===== ② 符号与定位 =====
  cardTitle(IX, px(y2 + 8), "② 符号与定位", "符号名会注册进 CE 的符号表，勾选脚本即生效")

  -- 字段标签统一列宽。
  -- 【用户实拍·「条件判断」被遮】原来标签是**右对齐 + 固定 52/64px 宽**，
  --   而「条件判断」4 个全角字在真机上渲染得比 64px 还宽
  --   （布局坐标被 px() 按屏幕缩放压小了，字号却没跟着缩）→
  --   右对齐时文字从框的左边缘**向左溢出**，左缘顶到卡片左边框线上，
  --   看着就是「条字被卡片边框压住了」。
  -- 改成**左对齐**：文字永远从列首开始，不可能溢出到卡片边框外面；
  -- 列宽取「最长的标签 + 余量」，两个输入框的左缘也就自然对齐了。
  local FLBL_W = math.max(px(60), estTextWidth("条件判断", FS_BODY) + px(12))

  -- 行 1：符号名 / 记录名 / 锁定首次
  lblSym = newLabel()
  lblSym.Left = IX lblSym.Top = px(y2 + 32) lblSym.Width = FLBL_W lblSym.Height = px(20)
  lblSym.Alignment = "taLeftJustify"
  lblSym.Caption = "符号名"
  style(lblSym, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblSym", lblSym.Left, lblSym.Top, lblSym.Width, lblSym.Height, 2)

  edtSym = createEdit(ROOT)
  -- 左缘跟着标签列走，右缘保持不变（后面「记录名」那一列的位置不受影响）
  edtSym.Left = IX + FLBL_W + px(8) edtSym.Top = px(y2 + 30)
  edtSym.Width = IX + px(208) - edtSym.Left edtSym.Height = px(24)
  edtSym.Text = DEFAULT_SYM
  edtSym.Hint = "符号名：生成脚本后可用它读写；默认 aob_base"
  inputStyle(edtSym)
  reg("edtSym", edtSym.Left, edtSym.Top, edtSym.Width, edtSym.Height, 2)
  snapDark(edtSym, "edit")

  lblDesc = newLabel()
  -- 第二列没有第一列那么宽（右边要留给「记录名」输入框），单独给一个窄一点的列
  lblDesc.Left = IX + px(216) lblDesc.Top = px(y2 + 32) lblDesc.Width = px(60) lblDesc.Height = px(20)
  lblDesc.Alignment = "taLeftJustify"
  lblDesc.Caption = "记录名"
  style(lblDesc, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblDesc", lblDesc.Left, lblDesc.Top, lblDesc.Width, lblDesc.Height, 2)

  edtDesc = createEdit(ROOT)
  edtDesc.Left = IX + px(282) edtDesc.Top = px(y2 + 30) edtDesc.Width = px(210) edtDesc.Height = px(24)
  edtDesc.Text = ""
  edtDesc.Hint = "自动加进地址列表的那条记录叫什么；留空就用 符号名+偏移"
  inputStyle(edtDesc)
  reg("edtDesc", edtDesc.Left, edtDesc.Top, edtDesc.Width, edtDesc.Height, 2)
  snapDark(edtDesc, "edit")

  chkLatch = createCheckBox(ROOT)
  chkLatch.Left = IX + px(510) chkLatch.Top = px(y2 + 31) chkLatch.Width = px(160) chkLatch.Height = px(22)
  chkLatch.Caption = "锁定首次"
  chkLatch.Hint = "符号有值后就不再改写：后面的其它对象执行这条指令时不会把你锁定的那个冲掉（重启或重新启用脚本后重新锁）"
  style(chkLatch, { bg = CARD_BG, fg = C.text2 })
  pcall(function() chkLatch.Font.Color = C.text2 end)
  untheme(chkLatch)
  reg("chkLatch", chkLatch.Left, chkLatch.Top, chkLatch.Width, chkLatch.Height, 2)

  -- 行 2：条件判断 + 三个按钮（按钮贴右）
  lblGuard = newLabel()
  lblGuard.Left = IX lblGuard.Top = px(y2 + 64) lblGuard.Width = FLBL_W lblGuard.Height = px(20)
  lblGuard.Alignment = "taLeftJustify"
  lblGuard.Caption = "条件判断"
  style(lblGuard, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblGuard", lblGuard.Left, lblGuard.Top, lblGuard.Width, lblGuard.Height, 3)

  edtGuard = createEdit(ROOT)
  -- 左缘跟着标签列走，和上面「符号名」的输入框左缘对齐
  edtGuard.Left = IX + FLBL_W + px(8) edtGuard.Top = px(y2 + 62)
  -- 【用户反馈】条件判断的输入框原来一路顶到按钮区（设计稿里 428px 宽），
  --   太长、把右侧按钮挤得很紧，看着像「压住了字」。
  --   现在给它明确的上限 px(300)，并永远不超过「到生成脚本按钮」的可用空间
  --   （窗体再窄也不会溢出压到按钮上）。
  local guardAvail = RX(px(312)) - px(24) - edtGuard.Left
  edtGuard.Width = math.max(px(120), math.min(px(300), guardAvail))
  edtGuard.Height = px(24)
  edtGuard.Text = ""
  edtGuard.Hint = "数据地址（31089AE8）、指针（[模块+偏移]）、值条件（=200 / >=100 / 100-200 / &0x100）或寄存器条件（rsi=0C / rcx!=5 / rsi&0x100）；留空就是无条件记最后那次"
  inputStyle(edtGuard)
  reg("edtGuard", edtGuard.Left, edtGuard.Top, edtGuard.Width, edtGuard.Height, 3)
  snapDark(edtGuard, "edit")

  -- 输入框右侧的用法提示：把缩短出来的空隙用起来，而不是留一块没来由的白
  --（宽度算到「生成脚本」按钮左边为止，文字再长也只会自己被裁，不会压到按钮上）
  do
    local hx = edtGuard.Left + edtGuard.Width + px(12)
    local hw = RX(px(312)) - px(12) - hx
    if hw > px(56) then
      label(hx, px(y2 + 66), hw, px(18), "=200 / rsi=0C",
        { bg = CARD_BG, fg = C.text2, size = FS_HINT })
      reg("lblGuardHint", hx, px(y2 + 66), hw, px(18), 3)
    end
  end

  btnGen = createButton(ROOT)
  btnGen.Left = RX(px(312)) btnGen.Top = px(y2 + 60) btnGen.Width = px(112) btnGen.Height = px(28)
  btnGen.Caption = "生成脚本"
  btnGen.Hint = "按上面的设置生成一段 [ENABLE]/[DISABLE] 的常规 AOB 脚本"
  style(btnGen, { bg = C.accent, fg = C.onDark, bold = true })
  reg("btnGen", btnGen.Left, btnGen.Top, btnGen.Width, btnGen.Height, 3)
  snapDark(btnGen, "btnMain")
  btnGen.OnClick = function()
    local sem = "container"
    if cbSem then
      local idx = tonumber(cbSem.ItemIndex) or 0
      if idx == 1 then sem = "element" end
    end
    local patch
    if chkPatch and chkPatch.Checked then
      local op = "写入值"
      local vt = "4字节"
      if cbPatchOp then op = cbPatchOp.Items[cbPatchOp.ItemIndex] or cbPatchOp.Text or "写入值" end
      if cbPatchVt then vt = cbPatchVt.Items[cbPatchVt.ItemIndex] or cbPatchVt.Text or "4字节" end
      patch = {
        on = true, op = op, value = edPatchVal and edPatchVal.Text or "",
        off = edPatchOff and edPatchOff.Text or "0", vt = vt,
      }
    end
    doGenerate(memoText(edtInsn), edtSym.Text, chkOff and chkOff.Checked, edtDesc.Text, edtGuard.Text,
      chkLatch and chkLatch.Checked, sem, chkCrypt and chkCrypt.Checked, patch, chkVerbose and chkVerbose.Checked,
      chkHwbp and chkHwbp.Checked)
  end

  btnClearIn = createButton(ROOT)
  btnClearIn.Left = RX(px(192)) btnClearIn.Top = px(y2 + 61) btnClearIn.Width = px(92) btnClearIn.Height = px(26)
  btnClearIn.Caption = "清空输入"
  btnClearIn.Hint = "清掉指令输入框和取代码留下的内容"
  ghost(btnClearIn)
  reg("btnClearIn", btnClearIn.Left, btnClearIn.Top, btnClearIn.Width, btnClearIn.Height, 3)
  snapDark(btnClearIn, "btn")
  btnClearIn.OnClick = function()
    setMemo(edtInsn, "")
  end

  btnClear = createButton(ROOT)
  btnClear.Left = RX(px(92)) btnClear.Top = px(y2 + 61) btnClear.Width = px(92) btnClear.Height = px(26)
  btnClear.Caption = "清空日志"
  ghost(btnClear)
  reg("btnClear", btnClear.Left, btnClear.Top, btnClear.Width, btnClear.Height, 3)
  snapDark(btnClear, "btn")
  btnClear.OnClick = function()
    MEMO_LINES = {}
    if memo then memo.Lines.Clear() end
  end

  -- ===== ③ 选项 =====
  cardTitle(IX, px(y3 + 8), "③ 选项", "影响定位方式、脚本体积与是否附带改值", C.gold)

  chkOff = createCheckBox(ROOT)
  chkOff.Left = IX chkOff.Top = px(y3 + 30) chkOff.Width = px(150) chkOff.Height = px(22)
  chkOff.Caption = "用 模块+偏移 定位"
  chkOff.Hint = "用模块+固定偏移定位：只在那个偏移附近十几个字节内扫，保证唯一；游戏更新后扫不到会直接报错"
  checkStyle(chkOff)
  reg("chkOff", chkOff.Left, chkOff.Top, chkOff.Width, chkOff.Height, 4)

  chkCrypt = createCheckBox(ROOT)
  chkCrypt.Left = IX + px(162) chkCrypt.Top = px(y3 + 30) chkCrypt.Width = px(104) chkCrypt.Height = px(22)
  chkCrypt.Caption = "加密输出"
  chkCrypt.Hint = "生成的脚本加密后再输出：复制/另存/加到列表拿到的都是密文，启用时脚本自己解密再汇编。每次生成随机密钥，日志里会打出来。只挡想直接抄脚本的人，解包器就在脚本里"
  checkStyle(chkCrypt)
  reg("chkCrypt", chkCrypt.Left, chkCrypt.Top, chkCrypt.Width, chkCrypt.Height, 4)

  chkPatch = createCheckBox(ROOT)
  chkPatch.Left = IX + px(278) chkPatch.Top = px(y3 + 30) chkPatch.Width = px(140) chkPatch.Height = px(22)
  chkPatch.Caption = "生成时附带改值"
  chkPatch.Hint = "勾上后生成脚本会把改值指令写进注入代码（原指令执行完再写，不会被覆盖）；勾选脚本即生效"
  checkStyle(chkPatch)
  pcall(function() chkPatch.Font.Style = "fsBold" end)
  reg("chkPatch", chkPatch.Left, chkPatch.Top, chkPatch.Width, chkPatch.Height, 4)

  chkVerbose = createCheckBox(ROOT)
  chkVerbose.Left = IX + px(430) chkVerbose.Top = px(y3 + 30) chkVerbose.Width = px(104) chkVerbose.Height = px(22)
  chkVerbose.Caption = "精简注释"
  chkVerbose.Hint = "勾上后生成的脚本只保留指令行和定位行，去掉条件/锁定/符号说明等解释性注释，给熟手省篇幅"
  checkStyle(chkVerbose)
  reg("chkVerbose", chkVerbose.Left, chkVerbose.Top, chkVerbose.Width, chkVerbose.Height, 4)

  chkSelfCheck = createCheckBox(ROOT)
  chkSelfCheck.Left = IX + px(546) chkSelfCheck.Top = px(y3 + 30) chkSelfCheck.Width = px(120) chkSelfCheck.Height = px(22)
  chkSelfCheck.Caption = "生成时自检"
  chkSelfCheck.Checked = true
  chkSelfCheck.Hint = "取消勾选后生成不再调用 AA 语法自检（不影响生成的脚本，仅跳过开发期的语法校验）"
  checkStyle(chkSelfCheck)
  reg("chkSelfCheck", chkSelfCheck.Left, chkSelfCheck.Top, chkSelfCheck.Width, chkSelfCheck.Height, 4)
  chkSelfCheck.OnClick = function()
    SELFCHECK_ENABLED = chkSelfCheck.Checked
  end

  -- [硬件断点版] 不改游戏代码：用 CE 调试器的执行断点取寄存器
  -- 用模块级 local（chkHwbp），不再往 createUI 里加新局部变量
  chkHwbp = createCheckBox(ROOT)
  chkHwbp.Left = IX + px(672) chkHwbp.Top = px(y3 + 30) chkHwbp.Width = px(140) chkHwbp.Height = px(22)
  chkHwbp.Caption = "硬件断点模式"
  chkHwbp.Hint = "不写游戏代码：改用 CE 调试器的执行断点取寄存器（代码段保持干净）。代价：CE 必须开着调试器、每次命中暂停全部线程、只有 4 个断点槽位、不能导出 EXE/DLL"
  checkStyle(chkHwbp)
  reg("chkHwbp", chkHwbp.Left, chkHwbp.Top, chkHwbp.Width, chkHwbp.Height, 4)
  chkHwbp.OnClick = function()
    if chkHwbp.Checked then
      log("[模式] 已勾选硬件断点：生成的是「不改游戏代码」的调试器断点脚本；CE 的调试器要一直开着")
      log("[模式] 这个模式不能导出 EXE/DLL（没有代码洞），也不能用「生成时附带改值」")
    else
      log("[模式] 已取消硬件断点：回到常规的 inline hook（写 5 字节 jmp）")
    end
  end

  -- 语义（容器/元素）：决定符号是否把「索引*比例」算进去
  lblSem = newLabel()
  lblSem.Left = IX lblSem.Top = px(y3 + 60) lblSem.Width = px(40) lblSem.Height = px(20)
  lblSem.Alignment = "taRightJustify"
  lblSem.Caption = "语义"
  style(lblSem, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblSem", lblSem.Left, lblSem.Top, lblSem.Width, lblSem.Height, 5)

  cbSem = createComboBox(ROOT)
  cbSem.Left = IX + px(46) cbSem.Top = px(y3 + 58) cbSem.Width = px(170) cbSem.Height = px(24)
  cbSem.Items.Add("容器（不含索引）")
  cbSem.Items.Add("元素（含索引）")
  cbSem.ItemIndex = 0
  cbSem.Hint = "容器：符号只算 基址+位移，索引不算进去；元素：基址+索引*比例+位移，符号就是这条指令访问的地址；两种的记录都是 符号+偏移0"
  style(cbSem, { bg = C.input, fg = C.text })
  reg("cbSem", cbSem.Left, cbSem.Top, cbSem.Width, cbSem.Height, 5)
  snapDark(cbSem, "combo")

  lblSemHint = newLabel()
  lblSemHint.Left = IX + px(226) lblSemHint.Top = px(y3 + 60) lblSemHint.Width = IW - px(226) lblSemHint.Height = px(20)
  lblSemHint.Caption = "容器 = 不含索引；元素 = 含索引；两种的记录都是 符号+偏移0"
  style(lblSemHint, { bg = CARD_BG, fg = C.text2, size = FS_HINT })
  reg("lblSemHint", lblSemHint.Left, lblSemHint.Top, lblSemHint.Width, lblSemHint.Height, 5)

  -- ===== ④ 附带改值 =====
  cardTitle(IX, px(y4 + 8), "④ 附带改值", "需先勾选「生成时附带改值」")

  lblPatchOp = newLabel()
  lblPatchOp.Left = IX lblPatchOp.Top = px(y4 + 34) lblPatchOp.Width = px(40) lblPatchOp.Height = px(20)
  lblPatchOp.Alignment = "taRightJustify"
  lblPatchOp.Caption = "运算"
  style(lblPatchOp, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblPatchOp", lblPatchOp.Left, lblPatchOp.Top, lblPatchOp.Width, lblPatchOp.Height, 6)

  cbPatchOp = createComboBox(ROOT)
  cbPatchOp.Left = IX + px(46) cbPatchOp.Top = px(y4 + 32) cbPatchOp.Width = px(118) cbPatchOp.Height = px(24)
  cbPatchOp.Items.Add("写入值"); cbPatchOp.Items.Add("加"); cbPatchOp.Items.Add("减"); cbPatchOp.Items.Add("乘"); cbPatchOp.Items.Add("除"); cbPatchOp.Items.Add("取模"); cbPatchOp.Items.Add("置0"); cbPatchOp.Items.Add("与"); cbPatchOp.Items.Add("或"); cbPatchOp.Items.Add("异或"); cbPatchOp.Items.Add("取反")
  cbPatchOp.ItemIndex = 0
  cbPatchOp.Hint = "写入值=直接写；加减乘除取模=算术运算；与/或/异或/取反=位运算；置0=清零"
  style(cbPatchOp, { bg = C.input, fg = C.text })
  reg("cbPatchOp", cbPatchOp.Left, cbPatchOp.Top, cbPatchOp.Width, cbPatchOp.Height, 6)
  snapDark(cbPatchOp, "combo")

  lblPatchVal = newLabel()
  lblPatchVal.Left = IX + px(180) lblPatchVal.Top = px(y4 + 34) lblPatchVal.Width = px(56) lblPatchVal.Height = px(20)
  lblPatchVal.Alignment = "taRightJustify"
  lblPatchVal.Caption = "操作数"
  style(lblPatchVal, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblPatchVal", lblPatchVal.Left, lblPatchVal.Top, lblPatchVal.Width, lblPatchVal.Height, 6)

  edPatchVal = createEdit(ROOT)
  edPatchVal.Left = IX + px(242) edPatchVal.Top = px(y4 + 32) edPatchVal.Width = px(118) edPatchVal.Height = px(24)
  edPatchVal.Text = "9999"
  edPatchVal.Hint = "写入/运算的操作数，支持 9999 或 0x270F"
  inputStyle(edPatchVal)
  reg("edPatchVal", edPatchVal.Left, edPatchVal.Top, edPatchVal.Width, edPatchVal.Height, 6)
  snapDark(edPatchVal, "edit")

  lblPatchOff = newLabel()
  lblPatchOff.Left = IX + px(376) lblPatchOff.Top = px(y4 + 34) lblPatchOff.Width = px(40) lblPatchOff.Height = px(20)
  lblPatchOff.Alignment = "taRightJustify"
  lblPatchOff.Caption = "偏移"
  style(lblPatchOff, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblPatchOff", lblPatchOff.Left, lblPatchOff.Top, lblPatchOff.Width, lblPatchOff.Height, 6)

  edPatchOff = createEdit(ROOT)
  edPatchOff.Left = IX + px(422) edPatchOff.Top = px(y4 + 32) edPatchOff.Width = px(84) edPatchOff.Height = px(24)
  edPatchOff.Text = "0"
  edPatchOff.Hint = "相对符号地址的偏移，一般填 0"
  inputStyle(edPatchOff)
  reg("edPatchOff", edPatchOff.Left, edPatchOff.Top, edPatchOff.Width, edPatchOff.Height, 6)
  snapDark(edPatchOff, "edit")

  lblPatchVt = newLabel()
  lblPatchVt.Left = IX + px(522) lblPatchVt.Top = px(y4 + 34) lblPatchVt.Width = px(40) lblPatchVt.Height = px(20)
  lblPatchVt.Alignment = "taRightJustify"
  lblPatchVt.Caption = "类型"
  style(lblPatchVt, { bg = CARD_BG, fg = C.text, bold = true, size = FS_BODY })
  reg("lblPatchVt", lblPatchVt.Left, lblPatchVt.Top, lblPatchVt.Width, lblPatchVt.Height, 6)

  cbPatchVt = createComboBox(ROOT)
  cbPatchVt.Left = IX + px(568) cbPatchVt.Top = px(y4 + 32) cbPatchVt.Width = px(150) cbPatchVt.Height = px(24)
  cbPatchVt.Items.Add("4字节"); cbPatchVt.Items.Add("8字节"); cbPatchVt.Items.Add("2字节"); cbPatchVt.Items.Add("字节"); cbPatchVt.Items.Add("单浮点"); cbPatchVt.Items.Add("双浮点")
  cbPatchVt.ItemIndex = 0
  cbPatchVt.Hint = "写值用的数据类型；单浮点 / 双浮点会把数字按 IEEE754 处理"
  style(cbPatchVt, { bg = C.input, fg = C.text })
  reg("cbPatchVt", cbPatchVt.Left, cbPatchVt.Top, cbPatchVt.Width, cbPatchVt.Height, 6)
  snapDark(cbPatchVt, "combo")

  -- ===== ⑤ 结果输出 =====
  cardTitle(IX, px(y5 + 8), "⑤ 结果输出", "生成的脚本与运行日志")

  memo = createMemo(ROOT)
  memo.Left = IX memo.Top = px(y5 + 30) memo.Width = IW memo.Height = px(110)
  memo.ScrollBars = "ssBoth"
  memo.Lines.Clear()
  for _, l in ipairs(MEMO_LINES) do memo.Lines.Add(l) end
  inputStyle(memo)
  reg("memo", memo.Left, memo.Top, memo.Width, memo.Height, 7)

  -- ===== 底部操作条：复制脚本 / 另存为 / 加到列表 =====
  local function doCopy()
    if not lastScript then
      log("[提示] 还没有生成脚本，先点[生成脚本]")
      return
    end
    local ok, err = pcall(writeToClipboard, lastScript)
    if not ok then ok, err = pcall(setClipboard, lastScript) end
    if ok then
      log(string.format("[提示] 脚本已复制到剪贴板（%d 字符），直接粘进 CE 的自动汇编窗口", #lastScript))
    else
      log("[错误] 写剪贴板失败（" .. tostring(err) .. "），改用[另存为]导出")
    end
  end
  local function doSave() exportScript() end
  local function doAddTable() addScriptToTable() end

  -- ===== 底部工具条（固定在窗体上，不随内容滚动，始终可见够得着）=====
  -- 【观感】用 TPanel（窗口控件）铺一条整宽实心条，而不是 TShape：
  --   TShape 是图形控件，会被滚动容器里的窗口控件盖住 → 按钮看起来「飘」在内容上。
  --   TPanel 与滚动容器同为窗口控件，创建更晚 → 天然压在滚动内容之上，视觉是干净的一条工具栏。
  ROOT = form                                     -- 工具条挂到窗体本身，不进入滚动容器
  -- 【为什么打包成 BAR 表】createUI 已逼近 Lua 单函数 200 个局部变量的硬上限，
  -- 这里 6 个平铺的局部变量合并成 1 个表，纯粹是为了给编译器腾寄存器。
  local BAR = { top = opTop, h = OPS_RESERVE }    -- 工具条上沿/高度（真实像素，不再 px()）
  panel(0, BAR.top - px(1), CW, px(1), C.line, "bsNone")                  -- 顶部 1px 分隔线
  BAR.panel = panel(0, BAR.top, CW, BAR.h, HEAD_BG, "bsNone")             -- 整宽实心条
  -- 按钮/提示必须【做工具条的子控件】：TPanel 是窗口控件，会盖住同级 Label
  -- （TLabel 是图形控件，永远输给窗口控件）。挂进去之后它们画在条内，才是真正的工具栏。
  BAR.pad = BAR.top
  if BAR.panel then
    ROOT = BAR.panel
    BAR.pad = 0
    pcall(function() BAR.panel.BringToFront() end)
  else
    bgRect(CX, BAR.top, CARDW, BAR.h, C.head, C.line)   -- 降级：没有 TPanel 时退回图形块
  end

  -- 三个按钮（恢复原版布局：复制脚本 / 另存为 / 加到列表）
  btnCopy = createButton(ROOT)
  btnCopy.Left = IX btnCopy.Top = BAR.pad + px(10) btnCopy.Width = px(118) btnCopy.Height = px(32)
  btnCopy.Caption = "复制脚本"
  btnCopy.Hint = "只把 [ENABLE] 整段脚本复制到剪贴板，不带上面的日志"
  ghost(btnCopy)
  reg("btnCopy", btnCopy.Left, btnCopy.Top, btnCopy.Width, btnCopy.Height, 8)
  snapDark(btnCopy, "btn")
  barAdd(btnCopy)
  btnCopy.OnClick = function() doCopy() end

  btnSave = createButton(ROOT)
  btnSave.Left = IX + px(130) btnSave.Top = BAR.pad + px(10) btnSave.Width = px(118) btnSave.Height = px(32)
  btnSave.Caption = "另存为..."
  btnSave.Hint = "存成 .cea，CE 里 File → Load 载入"
  ghost(btnSave)
  reg("btnSave", btnSave.Left, btnSave.Top, btnSave.Width, btnSave.Height, 8)
  snapDark(btnSave, "btn")
  barAdd(btnSave)
  btnSave.OnClick = function() doSave() end

  btnAddTable = createButton(ROOT)
  btnAddTable.Left = IX + px(260) btnAddTable.Top = BAR.pad + px(10) btnAddTable.Width = px(118) btnAddTable.Height = px(32)
  btnAddTable.Caption = "加到列表"
  btnAddTable.Hint = "把脚本作为自动汇编条目加到当前 CT 表，列表里勾选它就等于启用（重复点会更新同一条）"
  ghost(btnAddTable)
  reg("btnAddTable", btnAddTable.Left, btnAddTable.Top, btnAddTable.Width, btnAddTable.Height, 8)
  snapDark(btnAddTable, "btn")
  barAdd(btnAddTable)
  btnAddTable.OnClick = function() doAddTable() end

  -- ===== [EXE导出] 独立 EXE 按钮：挂进 BAR 表，避免 createUI 局部变量逼近 200 上限 =====
  BAR.btnExport = createButton(ROOT)
  BAR.btnExport.Left = IX + px(382) BAR.btnExport.Top = BAR.pad + px(10) BAR.btnExport.Width = px(96) BAR.btnExport.Height = px(32)
  BAR.btnExport.Caption = "生成EXE"
  BAR.btnExport.Hint = "把当前已勾选激活的 AOB 脚本固化成不依赖 CE 的独立修改器（桌面 CE_Trainer_Output）"
  ghost(BAR.btnExport)
  snapDark(BAR.btnExport, "btn")
  barAdd(BAR.btnExport)
  BAR.btnExport.OnClick = function() if AOBEXE and AOBEXE.onExport then AOBEXE.onExport() end end

  -- [DLL导出] 原生 C++ 注入 DLL：与 EXE 共用同一份固化数据，产物是 .dll
  BAR.btnExportDll = createButton(ROOT)
  BAR.btnExportDll.Left = IX + px(484) BAR.btnExportDll.Top = BAR.pad + px(10) BAR.btnExportDll.Width = px(96) BAR.btnExportDll.Height = px(32)
  BAR.btnExportDll.Caption = "生成DLL"
  BAR.btnExportDll.Hint = "把当前已勾选激活的 AOB 脚本固化成原生 DLL（注入游戏即生效，不需要 CE / .NET）"
  ghost(BAR.btnExportDll)
  snapDark(BAR.btnExportDll, "btn")
  barAdd(BAR.btnExportDll)
  BAR.btnExportDll.OnClick = function() if AOBEXE and AOBEXE.onExportDll then AOBEXE.onExportDll() end end

  -- 右侧提示（缩短给「生成独立 EXE」腾位；完整提示移到启动日志）
  barAdd(label(RX(px(200)), BAR.pad + px(17), px(200), px(18),
    "勾选脚本激活后再导出",
    { bg = HEAD_BG, fg = C.text2, size = FS_HINT, align = "taRightJustify" }))

  -- 改值区随「生成时附带改值」启用/禁用
  local function setPatchEnabled(on)
    for _, c in ipairs({ cbPatchOp, edPatchVal, edPatchOff, cbPatchVt }) do
      pcall(function() c.Enabled = on end)
    end
  end
  setPatchEnabled(false)
  chkPatch.OnClick = function()
    setPatchEnabled(chkPatch.Checked)
    if chkPatch.Checked then
      log("[改值] 已开启：生成脚本时会自动带上改值（原指令执行后写，勾选脚本即生效）")
    else
      log("[改值] 已关闭：生成的脚本只定位符号，不改值")
    end
  end

  -- ===== 布局自检：越界 + 同层重叠 =====
  -- 只有真出问题才写日志（正常时保持输出区干净）
  do
    local bad = {}
    for _, b in ipairs(BOX) do
      if b.l < 0 or b.t < 0 or b.l + b.w > CW + 1 or b.t + b.h > CH + 1 then
        bad[#bad + 1] = string.format("%s 越界(l=%d t=%d w=%d h=%d, 客户区 %dx%d)", b.n, b.l, b.t, b.w, b.h, CW, CH)
      end
    end
    for i = 1, #BOX do
      for j = i + 1, #BOX do
        local a, c = BOX[i], BOX[j]
        if a.lay == c.lay and a.lay > 0 then
          local ox = math.min(a.l + a.w, c.l + c.w) - math.max(a.l, c.l)
          local oy = math.min(a.t + a.h, c.t + c.h) - math.max(a.t, c.t)
          if ox > 2 and oy > 2 then
            bad[#bad + 1] = string.format("%s 与 %s 重叠(%dx%d)", a.n, c.n, ox, oy)
          end
        end
      end
    end
    if #bad > 0 then
      log("[界面自检] 发现 " .. #bad .. " 处布局问题：")
      for _, s in ipairs(bad) do log("  - " .. s) end
    end
  end

  form.OnDestroy = function()
    form = nil
    memo = nil
  end

  -- ===== 文字可见性自检（用真实矩形数一遍）=====
  -- Label 是图形控件：文字画在窗体画布上；窗口控件是独立 HWND，永远盖在画布之上。
  -- 只要两者矩形相交，那行字就彻底看不见（控件还在、字全没了）。
  do
    local hidden = 0
    for _, l in ipairs(LABELS) do
      for _, w in ipairs(WINOBJS) do
        local ox = math.min(l.Left + l.Width, w.Left + w.Width) - math.max(l.Left, w.Left)
        local oy = math.min(l.Top + l.Height, w.Top + w.Height) - math.max(l.Top, w.Top)
        if ox > 2 and oy > 2 then
          hidden = hidden + 1
          if hidden <= 3 then
            log(string.format("[界面自检] 文字可能被遮挡：「%s」与窗口控件重叠 %dx%d",
              tostring(l.Caption), ox, oy))
          end
        end
      end
    end
    log(string.format("[界面体检] 卡片底=%s；文字 %d 处，被窗口控件遮挡 %d 处",
      SHAPE_OK and "图形控件(TShape)" or "扁平模式(无卡片底)", #LABELS, hidden))
  end

  -- ===== 徽章可见性自检 =====
  -- 徽章曾经整个消失过（深色字画在深色底上）。这里读回它的字色与背景色比对，
  -- 万一某个 CE 版本不吃 Font.Color，这里会直接写进日志，不用再靠肉眼找。
  do
    local okf, fg = pcall(function() return lblBadge.Font.Color end)
    if not okf or type(fg) ~= "number" then
      log("[界面自检] 徽章字色读不回来，版本号可能不显示，请反馈此日志")
    elseif fg == HEAD_BG or fg == C.badge then
      log("[界面自检] 徽章字色与背景同色（不可见），请反馈此日志")
    else
      log(string.format("[界面自检] 版本徽章就位：%s（色块=%s）",
        PLUGIN_VER .. " · " .. BUILD_STAMP, SHAPE_OK and "已绘制" or "扁平模式无色块"))
    end
  end

  -- 勾选框关主题统计：关掉 Windows 主题，勾选框文字才会用上我们设的浅色
  if UNTHEMED > 0 then
    log(string.format("[界面自检] 已关闭 %d 个勾选框的 Windows 主题（文字改用浅色，之前是深色字看不清）", UNTHEMED))
  end

  -- ===== 图形控件归属自检 =====
  -- TShape 必须真正挂到窗体上（Parent 有效）才会显示。
  -- 万一某个 CE 版本建得出控件却挂不上 Parent，这里会直接写进日志，
  -- 用户反馈「卡片底还是没有」时，一眼就能看出是「没建出来」还是「建了没挂上」。
  if SHAPE_OK then
    local orphan = 0
    for _, shp in ipairs(SHAPES) do
      local okp, par = pcall(function() return shp.Parent end)
      if not okp or par == nil then orphan = orphan + 1 end
    end
    if orphan > 0 then
      log(string.format("[界面自检] 图形控件有 %d 个没挂到窗体上（卡片底可能不显示），请反馈此日志", orphan))
    end
  end

  -- 所有图形控件（卡片底 / 分隔线 / 竖条 / 徽章色块）统一压到最底层。
  --
  -- 【踩坑记录·SendToBack 的语义】
  --   Lazarus 里控件按父容器的**控件列表顺序**绘制：列表靠前的先画、后画的盖在上面。
  --   SendToBack = 把自己挪到列表**最前**（= 最底）。
  --   同一个 shape 每被 SendToBack 一次就往前挪一位，于是：
  --     「按创建顺序依次 SendToBack」的结果是 —— **最后创建的反而在最底**。
  --   之前标题条的色块比徽章色块**晚**创建 → 标题条被 SendToBack 到最底之后，
  --   反而把徽章色块整个盖住 → 用户实拍就是「徽章文字在、底色牌子不见了」。
  --   正确做法：**倒序**遍历，让「先创建的在下、后创建的在上」，
  --   徽章色块才会压在标题条之上。
  for i = #SHAPES, 1, -1 do
    local shp = SHAPES[i]
    pcall(function() shp.SendToBack() end)
  end

  form.show()

  -- ===== 二次上色（retheme）=====
  -- CE 的控件在窗体 show 之前可能还没建立 handle，此时赋 Color/Font.Color 会被丢弃；
  -- show 之后统一再刷一遍，并读回校验，把异常写进日志，便于反馈定位。
  for _, t in ipairs(THEME) do
    if t.shape then
      -- 图形控件（TShape）：底色画在 Brush 上，边框画在 Pen 上
      if t.bg then pcall(function() t.c.Brush.Color = t.bg end) end
      if t.pen then pcall(function() t.c.Pen.Color = t.pen end) end
    else
      if t.bg then pcall(function() t.c.Color = t.bg end) end
      if t.fg then pcall(function() t.c.Font.Color = t.fg end) end
    end
  end

  -- 读回校验 + 兜底：
  --   症状 A：这个 CE 版本把 Font.Size 换算坏了（Font.Height 读回非负）→ 退回负像素高度写法
  --   症状 B：这个 CE 版本不吃 Label 的 Font.Color（文字变默认黑）→ 改「浅底深字」保证可见
  local fsFix, fgFix = 0, 0
  for _, t in ipairs(THEME) do
    if t.size then
      local okh, hh = pcall(function() return t.c.Font.Height end)
      if okh and type(hh) == "number" and (hh == 0 or hh > 0) then
        -- Font.Size 在这个版本换算异常 → 改用「负像素高度」（Lazarus 最通用的写法）
        pcall(function() t.c.Font.Height = -(t.size + 3) end)
        fsFix = fsFix + 1
      end
    end
    if t.fg then
      local ok, cur = pcall(function() return t.c.Font.Color end)
      if ok and type(cur) == "number" and cur ~= t.fg then
        -- 不吃前景色 → 把背景换成「看得见默认黑字」的底色。
        -- 深色外观开着时用中间调（黑字照样能看清），否则用浅底（维持原行为）。
        local fallbackBg = DARK_ON and DARK.face or C.text
        pcall(function() t.c.Color = fallbackBg end)
        pcall(function() t.c.Font.Color = 0x101418 end)
        fgFix = fgFix + 1
      end
    end
  end
  if fsFix > 0 or fgFix > 0 then
    log(string.format("[界面自检] 已自动降级：字号修正 %d 处，前景色修正 %d 处（这个 CE 版本对字体属性支持有限）",
      fsFix, fgFix))
  end

  -- 深色外观如果开着，重新补刷一遍（retheme 会覆盖按钮字色）
  if DARK_ON then pcall(function() applyDark(true) end) end

  -- 打开生成器时顺手确保反汇编右键菜单已装（内存查看器已开则立即装，否则由 init 的定时器稍后补装）
  -- 注意：addDisasmContextMenu 每次成功都会往日志里写一行，重复调用会让日志刷屏。
  -- 这里只在「之前没装上」的情况下补装，避免同一件事打两遍。
  if not disasmMenuItem then pcall(addDisasmContextMenu) end
end

doGenerate = function(raw, sym, useOffset, desc, guard, latch, sem, encryptOn, patch, verbose, hwbp)
  local ok, err = pcall(generate, raw, sym, useOffset, desc, guard, latch, sem, encryptOn, patch, verbose, hwbp)
  if not ok then
    log("[错误] 生成失败: " .. tostring(err))
  end
end

-- =============================================================
-- 右键菜单入口
-- =============================================================
local MENU_CAPTION = "AOB 符号脚本生成"

-- 旧版右键项（改值、中文脚本编辑器）已并进主窗体，启动时把残留清掉，右键只留一个入口
local LEGACY_CAPTIONS = {
  "中文改值（符号+偏移·加减乘除）",
  "中文改值（符号+偏移 · 加减乘除）",
  "中文改值",
  "中文脚本编辑器(表达式/符号)",
  "中文脚本编辑器",
}

local function isLegacyCaption(cap)
  for _, c in ipairs(LEGACY_CAPTIONS) do
    if cap == c then return true end
  end
  return false
end

local function removeMenuItemAt(popup, i)
  local items = popup.Items
  if pcall(function() items.delete(i) end) then return true end
  if pcall(function() items.Delete(i) end) then return true end
  local it = items.Item[i]
  if it and pcall(function() items.Remove(it) end) then return true end
  return false
end

-- 清掉旧项与重复项；返回是否已经存在唯一的主入口
local function cleanupContextMenu(popup)
  local kept = false
  for i = popup.Items.Count - 1, 0, -1 do
    local it = popup.Items.Item[i]
    local cap = (it and it.Caption) or ""
    if isLegacyCaption(cap) then
      removeMenuItemAt(popup, i)
    elseif cap == MENU_CAPTION then
      if kept then
        removeMenuItemAt(popup, i)
      else
        kept = true
      end
    end
  end
  return kept
end

local function addContextMenu()
  local popup = getAddressList().popupMenu
  if cleanupContextMenu(popup) then
    -- 已存在就复用，并把点击行为重新绑到当前这份脚本的 createUI
    pcall(function()
      for i = 0, popup.Items.Count - 1 do
        local it = popup.Items.Item[i]
        if it and it.Caption == MENU_CAPTION then
          it.OnClick = function() createUI() end
          break
        end
      end
    end)
    return
  end
  local item = createMenuItem(popup)
  item.Caption = MENU_CAPTION
  item.OnClick = function()
    createUI()
  end
  popup.Items.add(item)
end

-- ===== 反汇编视图「取选中代码」=====
-- 让取代码也能从内存查看器（Memory Viewer）反汇编选区拿指令：
--   单选一行 → 取那一行的完整指令；框选一段 → 把整段一起取进来（首行当挂钩指令，其余补足跳转长度）
-- 通过 CE Lua 的反汇编视图 API 实现，所有调用都包 pcall，CE 里拿不到就静默降级。

local DISASM_MENU_CAPTION = "取选中代码到 AOB 生成器"

-- 最近一次选区两端（由 onSelectionChange 回调维护；右键/点按钮时读取）
local disasmSel1, disasmSel2 = 0, 0
-- 持有右键菜单项的强引用：否则 Lua GC 可能回收，菜单项点击时变哑
local disasmMenuItem = nil

-- 安全调用：返回结果或 nil（不抛），避免任一 CE API 缺失就把整段逻辑带崩
local function tryCall(f, ...)
  if type(f) ~= "function" then return nil end
  local ok, r = pcall(f, ...)
  return ok and r or nil
end

-- 拿到反汇编视图对象：优先官方封装，失败直接取属性（跨 CE 版本更稳）
function getDisasmView()
  local mv = tryCall(getMemoryViewForm)
  if not mv then return nil end
  local dv = tryCall(memoryview_getDisassemblerView, mv)
  if not dv then dv = tryCall(function() return mv.DisassemblerView end) end
  return dv
end

-- 读取反汇编当前选区：[a1, a2]；a1 为焦点行，a2 为框选的另一端（无框选时等于 a1）
function readDisasmSelection()
  local mv = tryCall(getMemoryViewForm)
  local dv = getDisasmView()
  if not dv then return nil end
  local a1 = tryCall(disassemblerview_getSelectedAddress, dv)
  if not a1 or a1 == 0 then
    -- 个别版本这个函数只接受 MemoryViewForm（官方示例里也有传 mv 的写法）
    a1 = tryCall(disassemblerview_getSelectedAddress, mv)
  end
  if not a1 or a1 == 0 then
    a1 = tryCall(function() return dv.SelectedAddress end)
  end
  if not a1 or a1 == 0 then a1 = disasmSel1 end
  if not a1 or a1 == 0 then return nil end
  local a2 = (disasmSel2 and disasmSel2 ~= 0) and disasmSel2 or a1
  return a1, a2
end

-- 把 [a1,a2] 区间反汇编成多行（按指令长度逐步推进，最多 256 行防呆）
function disasmRegionLines(a1, a2)
  local lo, hi = math.min(a1, a2), math.max(a1, a2)
  local lines, addr, guard = {}, lo, 0
  while addr and addr <= hi and guard < 256 do
    local ok, line = pcall(disassemble, addr)
    if not ok or not line or line == "" then break end
    lines[#lines + 1] = line
    local sz = 1
    local ok2, s = pcall(getInstructionSize, addr)
    if ok2 and s and s > 0 then sz = s end
    addr = addr + sz
    guard = guard + 1
  end
  return lines
end

-- 把反汇编选区填进指令输入框；返回是否取到
function grabDisasmToMemo()
  local a1, a2 = readDisasmSelection()
  if not a1 then
    log("[取代码] 内存查看器反汇编里没有选中指令（先在反汇编视图点/框选一行或一段）")
    return false
  end
  local lines = disasmRegionLines(a1, a2)
  if #lines == 0 then
    log(string.format("[取代码] 无法反汇编选中地址 %X（确认 CE 已附加进程）", a1))
    return false
  end
  createUI()                 -- 确保窗体已建（已建则只是 show，不会重复建）
  if not edtInsn then return false end
  setMemo(edtInsn, table.concat(lines, "\n"))
  log(string.format("[取代码] 从反汇编取了 %d 行 → %s", #lines, lines[1]))
  if #lines > 1 then
    log("[取代码] 多行已填入：首行作为挂钩指令，其余用于补足跳转长度；若只想钩首行可在生成前删掉多余行")
  end
  return true
end

-- 反汇编右键菜单的对象名：CE 官方写法（Dark Byte 论坛示例）是
--   getMemoryViewForm().DisassemblerView.PopupMenu
-- 少数版本才用 control_getPopupMenu(dv)。顺序一定不能反：
-- 若 mv.PopupMenu 存在，它通常是窗体级菜单，挂上去反汇编区右键不显示。
local function findDisasmPopupMenu()
  local mv = tryCall(getMemoryViewForm)
  if not mv then return nil, "内存查看器未打开" end
  local dv = tryCall(memoryview_getDisassemblerView, mv)
  if not dv then dv = tryCall(function() return mv.DisassemblerView end) end
  if not dv then return nil, "反汇编视图未就绪" end

  local cands = {
    { "DisassemblerView.PopupMenu", function() return dv.PopupMenu end },
    { "control_getPopupMenu(dv)",   function() return tryCall(control_getPopupMenu, dv) end },
    { "mv.PopupMenu1",              function() return mv.PopupMenu1 end },
    { "mv.PopupMenu",               function() return mv.PopupMenu end },
  }
  for _, c in ipairs(cands) do
    local ok, pm = pcall(c[2])
    if ok and pm then
      local okc, n = pcall(function() return pm.Items.Count end)
      if okc and type(n) == "number" then return pm, c[1], dv end
    end
  end
  return nil, "反汇编右键菜单不可用", dv
end

-- 往 popup 里加菜单项：CE 7.x 用 pm.Items.add(mi)；老版本/个别构建用函数式 API
local function appendMenuItem(pm, mi)
  local okCnt, before = pcall(function() return pm.Items.Count end)
  -- 路径 A：CE 7.x 官方写法（pm.Items.add(mi) 为点调用，item 即首参）
  local okA = pcall(function() pm.Items.add(mi) end)
  if okA then
    if not (okCnt and type(before) == "number") then return true end   -- 不能计数就信任调用成功
    local ok2, after = pcall(function() return pm.Items.Count end)
    if ok2 and type(after) == "number" and after > before then return true end
  end
  -- 路径 B：函数式 API（老版本 / 个别构建仍保留）
  local okB = pcall(function() menuItem_add(menu_getItems(pm), mi) end)
  if okB then return true end
  return false
end

-- 在反汇编视图右键菜单加「取选中代码」项
-- 返回 true=已装上；false=内存查看器还没就绪/装不上，调用方应延时重试
function addDisasmContextMenu()
  local pm, src, dv = findDisasmPopupMenu()
  if not pm then return false end

  -- 追踪选区变化（右键时读两端），覆盖框选一段的场景
  pcall(function()
    disassemblerview_onSelectionChange(dv, function(view, a1, a2)
      disasmSel1, disasmSel2 = a1, a2
    end)
  end)

  -- 去重：清掉同名旧项，避免重复加载脚本后菜单项越加越多
  pcall(function()
    for i = (pm.Items.Count or 0) - 1, 0, -1 do
      local it = tryCall(function() return pm.Items.Item[i] end)
      if it and it.Caption == DISASM_MENU_CAPTION then
        pcall(function() pm.Items.Delete(i) end)
      end
    end
  end)

  local okmi, mi = pcall(createMenuItem, pm)
  if not okmi or not mi then return false end
  mi.Caption = DISASM_MENU_CAPTION
  mi.Hint = "把反汇编视图里选中的一行/一段指令取进 AOB 符号脚本生成器"
  mi.OnClick = function(sender) grabDisasmToMemo() end
  pcall(function() mi.ShortCut = textToShortCut("Ctrl+Shift+A") end)

  if not appendMenuItem(pm, mi) then return false end

  disasmMenuItem = mi          -- 持住引用，防被 GC 回收后点击无效
  log("[菜单] 反汇编右键已就绪（" .. tostring(src) .. "）：" .. DISASM_MENU_CAPTION)
  return true
end

-- ============================================================
-- [独立 EXE 导出模块]  —— 单文件交付，以 AOB 为主
-- ------------------------------------------------------------
-- 来源：CE 修改器 EXE 生成器 v1.0 的 C# 模板 / 预汇编抓字节 / 编译链，
--       裁剪移植（未移植数据库 / 游戏库 / 图标工具 / 进程选择 / 署名）。
-- 设计要点（与《AOB插件对接EXE生成器_方案定稿.md》一致）：
--   1) 导出副本取 lastPlainScript（永远明文），CE 内 lastScript 仍可加密；
--   2) 契约 table 直传元数据，不反推脚本文本（绕开三参数 alloc / {$lua} 块）；
--   3) 复用「预汇编抓字节」：脚本必须已在 CE 里勾选激活，导出只搬字节+重定位；
--   4) aobscanregion 保留，C# 侧按 模块基址+起止偏移 收窄扫描范围；
--   5) aob_base 成为与 CE 一致的可读/可改/可锁定记录（AllocSymbolName + offsets{0}）；
--   6) 32/64 由 C# 侧 IsWow64Process → ptrSize 4/8 处理，/platform:anycpu。
-- r4：点按钮弹出「选择要生成的条目」勾选窗口，读取 CE 地址列表全部条目
--      （AA 注入脚本 / 自动 aob_base 记录 / 手动记录 / 模块+偏移 / 静态地址），
--      默认全选，勾选后一起生成；多 alloc 块（条件/改值/锁定）已放开，逐块固化重定位。
-- ============================================================
AOBEXE = {}   -- 全局入口表：createUI 的按钮回调在运行时解析，定义先后无关

do
  local function exTrim(s)
    if s == nil then return "" end
    return (tostring(s):gsub("^%s*(.-)%s*$", "%1"))
  end
  local function exEscapeCS(s)
    if s == nil then return "" end
    s = tostring(s)
    s = s:gsub("\\", "\\\\")
    s = s:gsub('"', '\\"')
    s = s:gsub("\n", "\\n")
    s = s:gsub("\r", "\\r")
    s = s:gsub("\t", "\\t")
    return s
  end
  local function exSafeReplace(code, placeholder, value)
    local out = "" local start = 1
    while true do
      local s, e = string.find(code, placeholder, start, true)
      if s == nil then out = out .. string.sub(code, start) break end
      out = out .. string.sub(code, start, s - 1) .. value
      start = e + 1
    end
    return out
  end
  -- 一期 obfuscate 恒 false；下面两个只供 Lua 编译期解析 upvalue，不会被调用
  local function exXorByte(a, b) return 0 end
  local function exEncryptStr(s) return "new byte[0]" end

  local function exWriteFile(path, content, withBOM)
    local f = io.open(path, "wb") if not f then return false end
    if withBOM then f:write(string.char(0xEF, 0xBB, 0xBF)) end
    f:write(content) f:close() return true
  end
  local function exGetDesktop()
    return (os.getenv("USERPROFILE") or "C:\\Users\\Public") .. "\\Desktop"
  end
  local function exCreateDir(path)
    pcall(function() shellExecute("cmd.exe", '/c if not exist "' .. path .. '" mkdir "' .. path .. '" 2>nul', path, 0) end)
    sleep(300)
    return true
  end
  local function exFindCSC()
    local wd = os.getenv("WINDIR") or "C:\\Windows"
    local ps = { wd .. "\\Microsoft.NET\\Framework64\\v4.0.30319\\csc.exe",
                 wd .. "\\Microsoft.NET\\Framework\\v4.0.30319\\csc.exe" }
    for _, p in ipairs(ps) do local f = io.open(p, "rb") if f then f:close() return p end end
    return nil
  end

local function exParseAOBScript(scriptText, contract)
    -- ★ 新增：allocBlocks存储所有alloc块信息，ripFixups存储RIP-relative重定位点
    local result={aobPattern="",aobModule="",aobSymbolName="",origInstrBytes={},origInstrLen=5,fullScript=scriptText or "",customCodeBytes={},customCodeLen=0,hasOriginalCode=false,fullCaveBytes={},fullCaveLen=0,returnHereFixups="",allocBlocks={},ripFixups="",preAssembled=false,enableDbBytes={},hasAlloc=false}
    if scriptText==nil or scriptText=="" then return result end
    local enableStart,enableEnd=string.find(scriptText,"%[ENABLE%]")
    local disableStart,disableEnd=string.find(scriptText,"%[DISABLE%]")
    local enableScript="" local disableScript=""
    if enableStart then if disableStart then enableScript=exTrim(string.sub(scriptText,enableEnd+1,disableStart-1)) else enableScript=exTrim(string.sub(scriptText,enableEnd+1)) end end
    if disableStart then disableScript=exTrim(string.sub(scriptText,disableEnd+1)) end

    -- ★ 先解析[DISABLE]段的db行，获取原始指令字节（预汇编需要这些信息）
    for line in string.gmatch(disableScript,"[^\r\n]+") do
        local dbContent=string.match(line,"db%s+(.+)")
        if dbContent then
            dbContent=string.match(dbContent,"^(.-)//") or dbContent dbContent=string.match(dbContent,"^(.-);") or dbContent
            local bytes={} for hexByte in string.gmatch(dbContent,"(%x%x)") do local val=tonumber(hexByte,16) if val then table.insert(bytes,val) end end
            if #bytes>0 then result.origInstrBytes=bytes result.origInstrLen=#bytes break end
        end
    end

    -- 统一转小写匹配关键字
    local lowerScript=string.lower(scriptText)
    local _,_,sym,mod,pat=string.find(lowerScript,"aobscanmodule%(%s*(%w+)%s*,%s*(%S+)%s*,%s*([%x%?%s]+)%)")
    if mod and pat then
        result.aobModule = mod
        result.aobPattern = string.gsub(pat,"%s+"," ")
    else
        local _,_,sym2,pat2=string.find(lowerScript,"aobscan%(%s*(%w+)%s*,%s*([%x%?%s]+)%)")
        if sym2 and pat2 then
            result.aobPattern = string.gsub(pat2,"%s+"," ")
        end
    end
    -- 逐行查找含aobscan的行
    if result.aobPattern=="" then
        for line in string.gmatch(scriptText,"[^\r\n]+") do
            local lowerLine=string.lower(line)
            if string.find(lowerLine,"aobscanmodule") or string.find(lowerLine,"aobscan") then
                local inner=string.match(line,"%((.+)%)")
                if inner then
                    local parts={}
                    for p in string.gmatch(inner,"[^,]+") do table.insert(parts,exTrim(p)) end
                    if #parts>=2 then
                        local lastPart=exTrim(parts[#parts])
                        if string.find(lastPart,"[%x%?]") then
                            result.aobPattern=string.gsub(lastPart,"%s+"," ")
                            if #parts>=3 then
                                result.aobModule=exTrim(parts[2])
                            end
                        end
                    end
                end
            end
        end
    end
    -- 提取aobscan标签名
    local aobSymbolName=""
    local _,_,sn=string.find(lowerScript,"aobscanmodule%(%s*(%w+)%s*,")
    if sn then aobSymbolName=sn else local _,_,sn2=string.find(lowerScript,"aobscan%(%s*(%w+)%s*,") if sn2 then aobSymbolName=sn2 end end
    result.aobSymbolName=aobSymbolName
    -- [AOB导出] aobscanregion 标签名（原解析器只认 aobscanmodule / aobscan）
    if aobSymbolName=="" then local _,_,sr=string.find(lowerScript,"aobscanregion%(%s*(%w+)%s*,") if sr then aobSymbolName=sr result.aobSymbolName=sr end end
    -- 提取alloc名称列表及大小
    local allocNames={}
    local allocSizes={}
    -- ★ 修复：正确解析alloc大小（$前缀=十六进制，否则=十进制）
    for allocName,allocSizeRaw in string.gmatch(lowerScript,"alloc%(%s*(%w+)%s*,%s*([%w%.%$]+)") do
        local allocSize=2048
        local sizeStr=allocSizeRaw
        if string.find(sizeStr,"^%$") then
            -- $前缀：十六进制
            allocSize=tonumber(string.sub(sizeStr,2),16) or 2048
        elseif string.find(sizeStr,"^0[xX]") then
            -- 0x前缀：十六进制
            allocSize=tonumber(sizeStr,16) or 2048
        else
            -- 无前缀：十进制
            allocSize=tonumber(sizeStr) or tonumber(sizeStr,16) or 2048
        end
        table.insert(allocNames,allocName)
        table.insert(allocSizes,allocSize)
    end
    result.hasAlloc = #allocNames > 0

    -- ★ 检测脚本是否包含originalcode标签
    result.hasOriginalCode = string.find(lowerScript,"originalcode:")~=nil or string.find(lowerScript,"original_code:")~=nil or string.find(lowerScript,"origcode:")~=nil

    -- ===== [AOB导出] 契约覆盖：AOB 侧直接给出权威元数据，不再靠正则反推脚本文本 =====
    if contract then
        aobSymbolName        = contract.hookSym or aobSymbolName
        result.aobSymbolName = aobSymbolName
        if contract.aobPattern and contract.aobPattern~="" then result.aobPattern=contract.aobPattern end
        if contract.aobModule  and contract.aobModule ~="" then result.aobModule =contract.aobModule  end
        if contract.origBytes and #contract.origBytes>0 then
            result.origInstrBytes=contract.origBytes
            result.origInstrLen  =#contract.origBytes
        end
        if contract.allocNames and #contract.allocNames>0 then
            allocNames=contract.allocNames
            allocSizes=contract.allocSizes
            result.hasAlloc=true
        end
    end
    -- ★★★ 预汇编：从CE已激活的脚本中直接捕获注入JMP地址和所有alloc块字节 ★★★
    local pid=getOpenedProcessID()
    if pid and pid~=0 and result.aobPattern~="" and aobSymbolName~="" then
        local injectAddr=0
        local newmemAddr=0
        local scriptIsActive=false
        local assembledByUs=false

        -- ★ 方法A：检查脚本是否已在CE中激活（AOB符号已存在）
        pcall(function()
            local addr=getAddress(aobSymbolName)
            if addr then
                injectAddr=tonumber(addr) or 0
                if injectAddr~=0 then scriptIsActive=true end
            end
        end)

        -- ★ 如果已激活，直接读取注入点的JMP指令来获取代码洞地址
        if scriptIsActive then
            pcall(function()
                local jmpBytes=readBytes(injectAddr,5,true)
                if jmpBytes and #jmpBytes>=5 and jmpBytes[1]==0xE9 then
                    local rel=jmpBytes[2]+jmpBytes[3]*256+jmpBytes[4]*65536+jmpBytes[5]*16777216
                    if rel>=0x80000000 then rel=rel-0x100000000 end
                    newmemAddr=injectAddr+5+rel
                end
            end)
            -- 如果JMP读取失败，回退到alloc符号查找
            if newmemAddr==0 and #allocNames>0 then
                pcall(function()
                    local addr=getAddress(allocNames[1])
                    if addr then newmemAddr=tonumber(addr) or 0 end
                end)
            end
        end

        -- ★ 方法B：如果脚本未激活，尝试用CE汇编激活
        if not scriptIsActive and not contract then   -- [AOB导出] 契约模式禁止自动汇编，未激活直接失败
            local okAsm=pcall(function() autoAssemble(scriptText) end)
            if okAsm then
                assembledByUs=true
                pcall(function()
                    local addr=getAddress(aobSymbolName)
                    if addr then injectAddr=tonumber(addr) or 0 end
                end)
                -- 汇编后同样从JMP指令读取代码洞地址
                if injectAddr~=0 then
                    pcall(function()
                        local jmpBytes=readBytes(injectAddr,5,true)
                        if jmpBytes and #jmpBytes>=5 and jmpBytes[1]==0xE9 then
                            local rel=jmpBytes[2]+jmpBytes[3]*256+jmpBytes[4]*65536+jmpBytes[5]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            newmemAddr=injectAddr+5+rel
                        end
                    end)
                    if newmemAddr==0 and #allocNames>0 then
                        pcall(function()
                            local addr=getAddress(allocNames[1])
                            if addr then newmemAddr=tonumber(addr) or 0 end
                        end)
                    end
                end
            end
        end

        -- ★★★ 有了注入点和代码洞地址后，提取所有alloc块字节 ★★★
        if injectAddr~=0 and newmemAddr~=0 then
            result.preAssembled = true
            -- ★ 计算returnhere地址：注入点 + max(原始指令长度, 5)
            local codeLenCalc=math.max(result.origInstrLen,5)
            local returnHereAddr=injectAddr+codeLenCalc

            -- 也尝试从CE标签获取更精确的returnhere地址
            pcall(function()
                local addr=getAddress("returnhere")
                if addr then
                    local rh=tonumber(addr) or 0
                    if rh~=0 and rh>injectAddr and rh-injectAddr<=64 then
                        returnHereAddr=rh
                        result.origInstrLen=rh-injectAddr
                    end
                end
            end)

            -- ★★★ 收集所有alloc块的地址和字节 ★★★
            local allocAddrMap={} -- name -> address
            -- 第一个alloc映射到代码洞地址
            if #allocNames>0 then
                allocAddrMap[allocNames[1]]=newmemAddr
            end
            -- 获取其他alloc块的地址
            for i=2,#allocNames do
                pcall(function()
                    local addr=getAddress(allocNames[i])
                    if addr then
                        allocAddrMap[allocNames[i]]=tonumber(addr) or 0
                    end
                end)
            end

            -- ★ 读取每个alloc块的字节
            local allAllocBlocks={}
            for i=1,#allocNames do
                local name=allocNames[i]
                local addr=allocAddrMap[name] or 0
                local size=allocSizes[i] or 2048
                if addr~=0 then
                    local bytes=readBytes(addr,size,true)
                    if bytes and #bytes>=1 then
                        local byteArr={}
                        for ci=1,#bytes do table.insert(byteArr,bytes[ci]) end
                        table.insert(allAllocBlocks,{name=name,origAddr=addr,size=math.min(size,#bytes),bytes=byteArr})
                    end
                end
            end
            result.allocBlocks=allAllocBlocks

            -- ★ 扫描所有alloc块中的跳转到returnHereAddr的指令（returnhere修复点）
            local fixups={}
            local maxCaveEnd=0
            -- 只扫描第一个alloc块（代码洞主块）
            if #allAllocBlocks>0 then
                local caveBytes=allAllocBlocks[1].bytes
                local scanEnd=#caveBytes
                for si=1,scanEnd-4 do
                    if caveBytes[si]==0xE9 then
                        local rel=caveBytes[si+1]+caveBytes[si+2]*256+caveBytes[si+3]*65536+caveBytes[si+4]*16777216
                        if rel>=0x80000000 then rel=rel-0x100000000 end
                        local jmpDest=newmemAddr+(si-1)+5+rel
                        if jmpDest==returnHereAddr then
                            table.insert(fixups,string.format("%d:5",si-1))
                            if (si-1)+5>maxCaveEnd then maxCaveEnd=(si-1)+5 end
                        end
                    elseif caveBytes[si]==0x0F and si+5<=#caveBytes then
                        local cc=caveBytes[si+1]
                        if cc>=0x80 and cc<=0x8F then
                            local rel=caveBytes[si+2]+caveBytes[si+3]*256+caveBytes[si+4]*65536+caveBytes[si+5]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            local jmpDest=newmemAddr+(si-1)+6+rel
                            if jmpDest==returnHereAddr then
                                table.insert(fixups,string.format("%d:6",si-1))
                                if (si-1)+6>maxCaveEnd then maxCaveEnd=(si-1)+6 end
                            end
                        end
                    end
                end

                -- ★ 范围扫描：找跳转回注入点附近(±64字节)的E9/0F8x指令
                if #fixups==0 then
                    for si=1,scanEnd-4 do
                        if caveBytes[si]==0xE9 then
                            local rel=caveBytes[si+1]+caveBytes[si+2]*256+caveBytes[si+3]*65536+caveBytes[si+4]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            local jmpDest=newmemAddr+(si-1)+5+rel
                            if jmpDest>=injectAddr and jmpDest<=injectAddr+64 then
                                table.insert(fixups,string.format("%d:5",si-1))
                                if (si-1)+5>maxCaveEnd then maxCaveEnd=(si-1)+5 end
                                local calcLen=jmpDest-injectAddr
                                if calcLen>=5 and calcLen<=64 then
                                    result.origInstrLen=calcLen
                                    returnHereAddr=jmpDest
                                end
                            end
                        elseif caveBytes[si]==0x0F and si+5<=#caveBytes then
                            local cc=caveBytes[si+1]
                            if cc>=0x80 and cc<=0x8F then
                                local rel=caveBytes[si+2]+caveBytes[si+3]*256+caveBytes[si+4]*65536+caveBytes[si+5]*16777216
                                if rel>=0x80000000 then rel=rel-0x100000000 end
                                local jmpDest=newmemAddr+(si-1)+6+rel
                                if jmpDest>=injectAddr and jmpDest<=injectAddr+64 then
                                    table.insert(fixups,string.format("%d:6",si-1))
                                    if (si-1)+6>maxCaveEnd then maxCaveEnd=(si-1)+6 end
                                    local calcLen=jmpDest-injectAddr
                                    if calcLen>=5 and calcLen<=64 then
                                        result.origInstrLen=calcLen
                                        returnHereAddr=jmpDest
                                    end
                                end
                            end
                        end
                    end
                end

                -- ★ 反向扫描作为最终回退
                if #fixups==0 then
                    local fallbackLen=math.min(#caveBytes,512)
                    for si=math.min(fallbackLen,512),6,-1 do
                        if caveBytes[si]==0xE9 then
                            local rel=caveBytes[si+1]+caveBytes[si+2]*256+caveBytes[si+3]*65536+caveBytes[si+4]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            local jmpDest=newmemAddr+(si-1)+5+rel
                            if jmpDest>=injectAddr and jmpDest<=injectAddr+64 then
                                fallbackLen=(si-1)+5
                                table.insert(fixups,string.format("%d:5",si-1))
                                local calcLen=jmpDest-injectAddr
                                if calcLen>=5 and calcLen<=64 then
                                    result.origInstrLen=calcLen
                                end
                                break
                            end
                        elseif caveBytes[si]==0x0F and si+5<=#caveBytes then
                            local cc=caveBytes[si+1]
                            if cc>=0x80 and cc<=0x8F then
                                local rel=caveBytes[si+2]+caveBytes[si+3]*256+caveBytes[si+4]*65536+caveBytes[si+5]*16777216
                                if rel>=0x80000000 then rel=rel-0x100000000 end
                                local jmpDest=newmemAddr+(si-1)+6+rel
                                if jmpDest>=injectAddr and jmpDest<=injectAddr+64 then
                                    fallbackLen=(si-1)+6
                                    table.insert(fixups,string.format("%d:6",si-1))
                                    local calcLen=jmpDest-injectAddr
                                    if calcLen>=5 and calcLen<=64 then
                                        result.origInstrLen=calcLen
                                    end
                                    break
                                end
                            end
                        end
                    end
                    if #fixups>0 then
                        maxCaveEnd=fallbackLen
                    end
                end

                -- ★ 捕获完整代码洞字节
                if maxCaveEnd>0 and #fixups>0 then
                    result.fullCaveLen=maxCaveEnd
                    result.fullCaveBytes={}
                    for ci=1,maxCaveEnd do
                        table.insert(result.fullCaveBytes,caveBytes[ci])
                    end
                    result.returnHereFixups=table.concat(fixups,",")
                end
            end

            -- ★★★ 使用CE反汇编器按指令边界扫描所有alloc块 ★★★
            local ripFixList={}
            local blockRanges={}
            for i=1,#allAllocBlocks do
                local blk=allAllocBlocks[i]
                table.insert(blockRanges,{name=blk.name,startAddr=blk.origAddr,endAddr=blk.origAddr+blk.size})
            end
table.insert(blockRanges,{name="__inject__",startAddr=injectAddr,endAddr=injectAddr+64})

-- ★ ASLR修复：构建模块地址表用于绝对地址重定位（32位和64位均需要）
            local moduleAddrs = {}
            local function tryField(obj, ...)
                for _, k in ipairs({...}) do
                    local v = obj[k]
                    if v ~= nil then return v end
                end
                return nil
            end
            pcall(function()
                local mods = enumModules()
                if mods and mods.Count then
                    for i = 0, mods.Count - 1 do
                        pcall(function()
                            local m = mods[i]
                            local mAddr = tonumber(tryField(m, "Address", "BaseAddress", "address", "baseaddress")) or 0
                            local mSize = tonumber(tryField(m, "Size", "ModuleSize", "size", "modulesize", "Length")) or 0
                            local mName = tryField(m, "Name", "ModuleName", "name", "modulename", "Path")
                            if type(mName) ~= "string" then mName = "" end
                            if mAddr > 0 and mSize > 0 and mName ~= "" then
                                table.insert(moduleAddrs, {name=mName, base=mAddr,
                                    endAddr=mAddr+mSize-1})
end
                        end)
                    end
                end
            end)
            -- ★ 回退：如果枚举失败，至少用AOB模块名查地址
            if #moduleAddrs == 0 and result.aobModule and result.aobModule ~= "" then
                pcall(function()
                    local addr = getAddress(result.aobModule)
                    if addr then
                        local a = tonumber(addr) or 0
                        if a > 0 then
                            table.insert(moduleAddrs, {name=result.aobModule, base=a, endAddr=a+0x10000000-1})
                        end
                    end
                end)
            end

            for bi=1,#allAllocBlocks do
                local blk=allAllocBlocks[bi]
                local data=blk.bytes
                local addr=blk.origAddr
                local endAddr=blk.origAddr+#data

                while addr<endAddr do
                    local instrLen=1
                    pcall(function()
                        local ds=disassemble(addr)
                        if ds then
                            local byteStr=ds:match(" %- (.-) %- ")
                                        or ds:match(" : (.-) : ")
                                        or ds:match(" ([%x ]+) ")
                            if byteStr then
                                local cnt=0
                                for _ in byteStr:gmatch("%x%x") do cnt=cnt+1 end
                                if cnt>0 and cnt<=15 then instrLen=cnt end
                            end
                        end
                    end)

                    local offset=addr-blk.origAddr
                    local absTarget=nil
                    local fixType=nil

                    if offset+instrLen<=#data and instrLen>=2 then
                        local b0=data[offset+1]

                        if b0==0xE9 and instrLen==5 then
                            local rel=data[offset+2]+data[offset+3]*256+data[offset+4]*65536+data[offset+5]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            absTarget=addr+5+rel
                            fixType="r"
                        elseif b0==0xE8 and instrLen==5 then
                            local rel=data[offset+2]+data[offset+3]*256+data[offset+4]*65536+data[offset+5]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            absTarget=addr+5+rel
                            fixType="r"
                        elseif b0==0x0F and instrLen==6 and offset+6<=#data and data[offset+2]>=0x80 and data[offset+2]<=0x8F then
                            local rel=data[offset+3]+data[offset+4]*256+data[offset+5]*65536+data[offset+6]*16777216
                            if rel>=0x80000000 then rel=rel-0x100000000 end
                            absTarget=addr+6+rel
                            fixType="r"
elseif b0==0xEB and instrLen==2 then
                            local rel=data[offset+2]
                            if rel>=0x80 then rel=rel-256 end
                            absTarget=addr+2+rel
                            fixType="sr"
                        elseif b0>=0x70 and b0<=0x7F and instrLen==2 then
                            local rel=data[offset+2]
                            if rel>=0x80 then rel=rel-256 end
                            absTarget=addr+2+rel
                            fixType="sr"
                        -- ★ mov eax,[abs] / mov [abs],eax (opcodes A1/A3，5字节绝对地址)
                        elseif (b0==0xA1 or b0==0xA3) and instrLen==5 and offset+5<=#data then
                            local absAddr=data[offset+2]+data[offset+3]*256+data[offset+4]*65536+data[offset+5]*16777216
                            absTarget=absAddr
                            fixType="a"
                        end

                        if not absTarget and b0~=0x0F and instrLen>=6 then
                            local isRex=(b0>=0x40 and b0<=0x4F)
                            local modRMIdx
                            if isRex then
                                modRMIdx=offset+3
                            else
                                modRMIdx=offset+2
                            end
                            if modRMIdx and modRMIdx<=#data then
                                local modRM=data[modRMIdx]
                                local mod=(modRM-modRM%64)/64
                                local rm=modRM%8
                                if mod==0 and rm==5 then
                                    local dispIdx=modRMIdx+1
                                    if dispIdx+3<=#data then
                                        local rel=data[dispIdx]+data[dispIdx+1]*256+data[dispIdx+2]*65536+data[dispIdx+3]*16777216
                                        if rel>=0x80000000 then rel=rel-0x100000000 end
                                        local is64=targetIs64Bit()
                                        if is64 then
                                            absTarget=addr+instrLen+rel
                                            fixType="r"
                                        else
                                            absTarget=rel
                                            fixType="a"
                                        end
                                    end
                                end
                            end
                        end
                    end

if absTarget and fixType then
                        if absTarget>=injectAddr and absTarget<=injectAddr+64 then
                            local injOffset=absTarget-injectAddr
                            table.insert(ripFixList,string.format("%d:%d:%d:ri:0x%X",bi,offset,instrLen,injOffset))
                        elseif #moduleAddrs>0 then
                            local modName = ""
                            local modOffset = 0
                            for _, m in ipairs(moduleAddrs) do
                                if absTarget >= m.base and absTarget <= m.endAddr then
                                    modName = m.name
                                    modOffset = absTarget - m.base
                                    break
                                end
                            end
                            if modName ~= "" then
                                table.insert(ripFixList,string.format("%d:%d:%d:%s:0x%X:%s:%X",bi,offset,instrLen,fixType,absTarget,modName,modOffset))
                            else
                                table.insert(ripFixList,string.format("%d:%d:%d:%s:0x%X",bi,offset,instrLen,fixType,absTarget))
                            end
                        else
                            table.insert(ripFixList,string.format("%d:%d:%d:%s:0x%X",bi,offset,instrLen,fixType,absTarget))
                        end
                    end

                    addr=addr+instrLen
                end
            end
result.ripFixups=table.concat(ripFixList,"|")

            -- ★ 数据扫描：只处理没有指令fixup的纯数据块，避免误改代码指令
            local blocksWithFixup = {}
            for _, f in ipairs(ripFixList) do
                local bi = tonumber(string.match(f, "^(%d+):")) or 0
                blocksWithFixup[bi] = true
            end
            for bi=1,#allAllocBlocks do
                if not blocksWithFixup[bi] then
                    local blk=allAllocBlocks[bi]
                    local data=blk.bytes
                    for di=0,#data-4 do
                        local val=data[di+1]+data[di+2]*256+data[di+3]*65536+data[di+4]*16777216
                        if val>=0x80000000 then val=val-0x100000000 end
                        if val~=0 then
                            local foundAlloc = false
                            for bj=1,#allAllocBlocks do
                                local tBlk=allAllocBlocks[bj]
                                if val>=tBlk.origAddr and val<tBlk.origAddr+tBlk.size then
                                    table.insert(ripFixList,string.format("%d:%d:4:d:0x%X",bi,di,val))
                                    foundAlloc = true
                                    break
                                end
                            end
                            if not foundAlloc and #moduleAddrs>0 then
                                local modName = ""
                                local modOffset = 0
                                for _, m in ipairs(moduleAddrs) do
                                    if val >= m.base and val <= m.endAddr then
                                        modName = m.name
                                        modOffset = val - m.base
                                        break
                                    end
                                end
                                if modName ~= "" then
                                    table.insert(ripFixList,string.format("%d:%d:4:d:0x%X:%s:%X",bi,di,val,modName,modOffset))
                                end
                            end
                        end
                    end
                end
            end
            result.ripFixups=table.concat(ripFixList,"|")

            -- 如果是我们自己汇编的，禁用恢复
            if assembledByUs then
                local ok, err = pcall(function()
                    if disableScript and disableScript~="" then
                        autoAssemble("[DISABLE]\n"..disableScript)
                    end
                end)
                if not ok then
                    -- [DISABLE]前缀失败，尝试直接执行disable脚本
                    pcall(function()
                        if disableScript and disableScript~="" then
                            autoAssemble(disableScript)
                        end
                    end)
                end
            end
        end
    end
    -- 不再强制最小5字节，保留实际指令长度
    -- C#端的 patchLen = Math.Max(origInstrLen, 5) 会处理JMP补丁大小
    if #result.origInstrBytes>0 then
        result.origInstrLen=math.max(result.origInstrLen,#result.origInstrBytes)
    end
    -- ★ 如果脚本没有alloc（byte-patch类型），从[ENABLE]段提取db字节作为直接补丁数据
    --   这些db字节位于注入标签（如 hack:）下的代码段
    if not result.hasAlloc and not result.preAssembled then
        local foundInjectLabel = false
        for line in string.gmatch(scriptText,"[^\r\n]+") do
            local trimmed = exTrim(line)
            if trimmed == "" or string.find(trimmed,"^//") or string.find(trimmed,"^;") then
                -- do nothing
            elseif string.find(trimmed,"^%[DISABLE%]") then
                break
            elseif string.find(trimmed,"^%[ENABLE%]") then
                -- skip
            elseif string.find(trimmed,":%s*$") then
                -- label
                local labelName = exTrim(string.sub(trimmed,1,#trimmed-1))
                if string.lower(labelName) == aobSymbolName then
                    foundInjectLabel = true
                else
                    -- 非注入标签，停止
                    foundInjectLabel = false
                end
            elseif foundInjectLabel then
                -- 在注入标签下，提取db字节
                local dbContent = string.match(trimmed,"db%s+(.+)")
                if dbContent then
                    dbContent = string.match(dbContent,"^(.-)//") or dbContent
                    dbContent = string.match(dbContent,"^(.-);") or dbContent
                    for hexByte in string.gmatch(dbContent,"(%x%x)") do
                        local val = tonumber(hexByte,16)
                        if val then table.insert(result.enableDbBytes,val) end
                    end
                end
            end
        end
        -- 如果提取到了db字节，也同步设置origInstrBytes和origInstrLen
        if #result.enableDbBytes > 0 then
            result.origInstrBytes = result.enableDbBytes
            result.origInstrLen = #result.enableDbBytes
        end
    end
    -- 如果既没有db字节也没有预汇编结果，保持默认值5作为fallback
    return result
end

local function exBuildCSharpCode(process, knownPID, entries)
    -- [AOB导出] 一期固定关闭反调试 / 字符串混淆 / 署名 / 游戏库；原函数体零改动
    local anti, obfuscate, signInfo = false, false, nil
    local function bytesToCS(bytes) if bytes==nil or #bytes==0 then return "new byte[0]" end local parts={} for _,b in ipairs(bytes) do table.insert(parts,string.format("0x%02X",b)) end return "new byte[]{ "..table.concat(parts,", ").." }" end
    local function allocBlocksToCS(blocks) if blocks==nil or #blocks==0 then return "new AllocBlock[0]" end local parts={} for _,blk in ipairs(blocks) do table.insert(parts,'new AllocBlock("'..exEscapeCS(blk.name)..'", '..string.format("%.0f",blk.origAddr)..', '..tostring(blk.size)..', '..bytesToCS(blk.bytes)..')') end return "new AllocBlock[]{ "..table.concat(parts,", ").." }" end
    local entryInits={} for i,e in ipairs(entries) do
        local offStr if #e.offsets==0 then offStr="new long[0]" else local offParts={} for j,o in ipairs(e.offsets) do table.insert(offParts,tostring(o).."L") end offStr="new long[]{ "..table.concat(offParts,", ").." }" end
        local isAA=e.isAA and "true" or "false" local aaEn=e.aaEnabled and "true" or "false"
        local aobPattern=e.isAA and e.aaParsed.aobPattern or "" local aobModule=e.isAA and e.aaParsed.aobModule or ""
        local fullAAScript=e.isAA and e.aaParsed.fullScript and e.aaParsed.fullScript or "" local origInstrBytes=e.isAA and bytesToCS(e.aaParsed.origInstrBytes) or "new byte[0]"
        local origInstrLen=e.isAA and tostring(e.aaParsed.origInstrLen) or "5"
        local customCodeBytes=e.isAA and bytesToCS(e.aaParsed.customCodeBytes) or "new byte[0]"
        local hasOrigCode=e.isAA and tostring(e.aaParsed.hasOriginalCode) or "true"
        local fullCaveBytes=e.isAA and bytesToCS(e.aaParsed.fullCaveBytes) or "new byte[0]"
        local rhFixups=e.isAA and '"'..exEscapeCS(e.aaParsed.returnHereFixups)..'"' or '""'
        local allocBlocksCS=e.isAA and allocBlocksToCS(e.aaParsed.allocBlocks) or "new AllocBlock[0]"
        local ripFixupsCS=e.isAA and '"'..exEscapeCS(e.aaParsed.ripFixups)..'"' or '""'
        local isAllocScript=e.isAA and e.aaParsed.hasAlloc and "true" or "false"
        local enableDbBytes=e.isAA and bytesToCS(e.aaParsed.enableDbBytes) or "new byte[0]"
        local aobSymNameCS=e.isAA and (e.aaParsed.aobSymbolName or "") or ""
        local init if obfuscate then init='            new TrainerEntry(D('..exEncryptStr(e.description)..'), D('..exEncryptStr(e.addressStr)..'), '..string.format("%.0f",e.currentAddr)..'L, '..string.format("%.0f",e.baseResolvedAddr or 0)..'L, '..tostring(e.vtype)..', '..offStr..', D('..exEncryptStr(e.moduleName)..'), '..string.format("%.0f",e.moduleOffset)..'L, '..isAA..', '..aaEn..', D('..exEncryptStr(aobPattern)..'), D('..exEncryptStr(aobModule)..'), D('..exEncryptStr(fullAAScript)..'), '..origInstrBytes..', '..origInstrLen..', '..customCodeBytes..', '..hasOrigCode..', '..fullCaveBytes..', D('..exEncryptStr(e.aaParsed.returnHereFixups or "")..'), '..allocBlocksCS..', D('..exEncryptStr(e.aaParsed.ripFixups or "")..'), '..isAllocScript..', '..enableDbBytes..', D('..exEncryptStr(e.allocSymbol or "")..'), D('..exEncryptStr(aobSymNameCS)..'), D('..exEncryptStr(e.dataAobPattern or "")..'), '..string.format("%.0f", e.dataAobOffset or 0)..'),' else init='            new TrainerEntry("'..exEscapeCS(e.description)..'", "'..exEscapeCS(e.addressStr)..'", '..string.format("%.0f",e.currentAddr)..'L, '..string.format("%.0f",e.baseResolvedAddr or 0)..'L, '..tostring(e.vtype)..', '..offStr..', "'..exEscapeCS(e.moduleName)..'", '..string.format("%.0f",e.moduleOffset)..'L, '..isAA..', '..aaEn..', "'..exEscapeCS(aobPattern)..'", "'..exEscapeCS(aobModule)..'", "'..exEscapeCS(fullAAScript)..'", '..origInstrBytes..', '..origInstrLen..', '..customCodeBytes..', '..hasOrigCode..', '..fullCaveBytes..', '..rhFixups..', '..allocBlocksCS..', '..ripFixupsCS..', '..isAllocScript..', '..enableDbBytes..', "'..exEscapeCS(e.allocSymbol or "")..'", "'..exEscapeCS(aobSymNameCS)..'", "'..exEscapeCS(e.dataAobPattern or "")..'", '..string.format("%.0f", e.dataAobOffset or 0)..'),' end
        -- [AOB导出] region 条目用对象初始化器带入扫描范围，不改 TrainerEntry 构造函数签名
        if e.regionStartOff and e.regionEndOff and e.regionEndOff > e.regionStartOff then
            init = string.gsub(init, ",%s*$", " { RegionStartOff = " .. string.format("%.0f", e.regionStartOff) .. "L, RegionEndOff = " .. string.format("%.0f", e.regionEndOff) .. "L },")
        end
        table.insert(entryInits,init)
    end
    local entriesBlock=table.concat(entryInits,"\n")
    local panelRows={} for i,e in ipairs(entries) do
        local row='            BuildRow(panel, '..tostring(i-1)..', '
        if obfuscate then row=row..'D('..exEncryptStr(e.description)..'), ' else row=row..'"'..exEscapeCS(e.description)..'", ' end
        row=row..(e.isAA and "true" or "false")..', '..(e.aaEnabled and "true" or "false")..', '
        if obfuscate then row=row..'D('..exEncryptStr(e.currentValue)..'));' else row=row..'"'..exEscapeCS(e.currentValue)..'");' end
        table.insert(panelRows,row)
    end
    local panelBlock=table.concat(panelRows,"\n")
    local procExpr if obfuscate then procExpr='D('..exEncryptStr(process)..')' else procExpr='"'..exEscapeCS(process)..'"' end
    local titleExpr if signInfo and signInfo.title~="" then local titleStr=signInfo.title if signInfo.version~="" then titleStr=titleStr.." "..signInfo.version end if obfuscate then titleExpr='D('..exEncryptStr(titleStr)..')' else titleExpr='"'..exEscapeCS(titleStr)..'"' end else if obfuscate then titleExpr='D('..exEncryptStr(process.." 修改器")..')' else titleExpr='"'..exEscapeCS(process)..' 修改器"' end end
    local obfDecryptCode="" if obfuscate then obfDecryptCode=[=[        static byte[] _dk = new byte[]{ 0x43, 0x45, 0x54, 0x34, 0x4F, 0x42, 0x46, 0x78 };
        static string D(byte[] d)
        {
            if (d == null || d.Length == 0) return "";
            byte[] r = new byte[d.Length];
            for (int i = 0; i < d.Length; i++)
                r[i] = (byte)(d[i] ^ _dk[i % _dk.Length]);
            // ★ 编码智能检测：UTF-8优先，回退系统默认编码(ANSI/GBK)
            bool isUtf8 = true;
            int idx = 0;
            while (idx < r.Length)
            {
                byte b = r[idx];
                if (b < 0x80) { idx++; }
                else if (b >= 0xC2 && b < 0xE0 && idx + 1 < r.Length && (r[idx + 1] & 0xC0) == 0x80) { idx += 2; }
                else if (b >= 0xE0 && b < 0xF0 && idx + 2 < r.Length && (r[idx + 1] & 0xC0) == 0x80 && (r[idx + 2] & 0xC0) == 0x80) { idx += 3; }
                else if (b >= 0xF0 && b < 0xF5 && idx + 3 < r.Length && (r[idx + 1] & 0xC0) == 0x80 && (r[idx + 2] & 0xC0) == 0x80 && (r[idx + 3] & 0xC0) == 0x80) { idx += 4; }
                else { isUtf8 = false; break; }
            }
            if (isUtf8)
                return System.Text.Encoding.UTF8.GetString(r);
            else
                return System.Text.Encoding.Default.GetString(r);
        }
]=] end
    local antiDebugCode="" local antiThreadField="" local antiThreadStart="" local antiThreadStop="" if anti then
        antiThreadField="        Thread antiDebugThread;"
        antiThreadStart=[=[
                antiDebugThread = new Thread(AntiDebugMonitor);
                antiDebugThread.IsBackground = true;
                antiDebugThread.Start();
]=]
        antiThreadStop=[=[
            if (antiDebugThread != null && antiDebugThread.IsAlive)
                antiDebugThread.Join(500);
]=]
        antiDebugCode=[=[
        void AntiDebugMonitor()
        {
            while (!bStopping)
            {
                try
                {
                    CheckAntiDebug();
                    if (System.Diagnostics.Debugger.IsAttached)
                        EmergencyExit();
                }
                catch { }
                Thread.Sleep(500);
            }
        }
]=]
    end
    local signLabelsCode="" if signInfo and signInfo.name~="" then
        local items={{label="修改器标题",value=signInfo.title},{label="版本号",value=signInfo.version},{label="制作者",value=signInfo.name},{label="制作日期",value=signInfo.date},{label="联系方式",value=signInfo.contact},{label="网站/主页",value=signInfo.website},{label="备注说明",value=signInfo.note}}
        local lines={} for i,item in ipairs(items) do if item.value~="" then
            table.insert(lines,'            Label lblS'..i..' = new Label();')
            table.insert(lines,'            lblS'..i..'.Text = "'..exEscapeCS(item.label)..': '..exEscapeCS(item.value)..'";')
            table.insert(lines,'            lblS'..i..'.Left = 30; lblS'..i..'.Top = ay; lblS'..i..'.Width = 300;')
            table.insert(lines,'            aboutForm.Controls.Add(lblS'..i..');')
            table.insert(lines,'            ay += 28;')
        end end
        signLabelsCode=table.concat(lines,"\n")
    end

    -- C#完整代码（双地址显示）
    local code=[=[
using System;
using System.Collections.Generic;
using System.Drawing;
using System.Windows.Forms;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Threading;
using System.Text;
using System.Security.Principal;

namespace Trainer
{
    static class Program
    {
        [STAThread]
        static void Main(string[] args)
        {
            // 强制管理员模式：首次启动自动提权重启（防止死循环）
            if (args.Length == 0 || args[0] != "--elevated")
            {
                try
                {
                    ProcessStartInfo psi = new ProcessStartInfo();
                    psi.FileName = Application.ExecutablePath;
                    psi.Arguments = "--elevated";
                    psi.Verb = "runas";
                    psi.UseShellExecute = true;
                    Process.Start(psi);
                }
                catch { }
                return;
            }
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            Application.Run(new MainForm());
        }
    }

    class AllocBlock
    {
        public string Name;
        public long OrigAddr;   // CE中该alloc块的原始地址
        public int Size;
        public byte[] Bytes;    // CE预汇编的该块字节
        public IntPtr NewAddr;  // 运行时分配的新地址（重定位时填写）

        public AllocBlock(string name, long origAddr, int size, byte[] bytes)
        {
            Name = name; OrigAddr = origAddr; Size = size; Bytes = bytes;
            NewAddr = IntPtr.Zero;
        }
    }

    class TrainerEntry
    {
        public string Desc;
        public string AddrStr;
        public long ResolvedAddr;
        public long BaseResolvedAddr;  // ★ 基址解析地址（指针链的真正起始地址）
        public int VType;
        public long[] Offsets;
        public string ModuleName;
        public long ModuleOffset;
        public bool IsAA;
        public bool AAEnabled;
        public string AOBPattern;
        public string AOBModule;
        public string AAScriptPreview;
        public byte[] OrigInstrBytes;
        public int OrigInstrLen;
        public byte[] CustomCodeBytes;
        public bool HasOriginalCode;
        public byte[] FullCaveBytes;      // ★ CE预汇编的完整代码洞字节(自定义代码+原始代码+jmp returnhere)
        public string ReturnHereFixups;   // ★ returnhere修复点列表 "offset:len,offset:len"
        public AllocBlock[] AllocBlocks;  // ★ 所有alloc块的预汇编字节和重定位信息
        public string RipFixups;          // ★ 跨alloc块RIP-relative重定位列表
        public bool IsAllocScript;        // ★ 是否有alloc（true=代码洞注入，false=直接字节补丁）
        public byte[] DirectPatchBytes;   // ★ 直接补丁字节（byte-patch脚本用，无代码洞）
        public string AllocSymbolName;    // ★ alloc符号名（如hack），用于指针链解析
        public long RegionStartOff = 0;   // [AOB导出] aobscanregion 起始偏移（模块基址相对）
        public long RegionEndOff = 0;     // [AOB导出] aobscanregion 结束偏移；0 表示不限范围
        public string AOBSymbolName;      // ★ aobscan标签名（如INJECT），用于指针链解析
        public IntPtr InjectAddress;
        public IntPtr AllocatedMem;
        public long LastAllocStart;
        public long LastAllocSize;
        public byte[] OriginalCode;
        public List<IntPtr> ExtraAllocs; // 运行时汇编的额外alloc块
        // ★ 数据段AOB字段(独立于代码段AOB,用于数据段重定位)
        public string DataAOBPattern;      // 数据段AOB特征码(独立于AOBPattern)
        public long DataAOBOffset;         // 数据段偏移(独立于ModuleOffset)
        public long DataSegBaseAddr;       // 数据段基址缓存(独立于InjectAddress)
        public bool DataSegNeedsRescan;    // 失效重扫标志

        public TrainerEntry(string desc, string addrStr, long resolvedAddr, long baseResolvedAddr, int vtype,
            long[] offsets, string modName, long modOff, bool isAA, bool aaEnabled,
            string aobPattern, string aobModule, string fullAAScript, byte[] origInstrBytes, int origInstrLen,
            byte[] customCodeBytes, bool hasOriginalCode, byte[] fullCaveBytes, string returnHereFixups,
            AllocBlock[] allocBlocks, string ripFixups,
            bool isAllocScript, byte[] directPatchBytes,
            string allocSymbolName, string aobSymbolName,
            string dataAobPattern, long dataAobOffset)
        {
            Desc = desc; AddrStr = addrStr; ResolvedAddr = resolvedAddr; BaseResolvedAddr = baseResolvedAddr; VType = vtype;
            Offsets = offsets; ModuleName = modName; ModuleOffset = modOff;
            IsAA = isAA; AAEnabled = aaEnabled; AOBPattern = aobPattern; AOBModule = aobModule;
            AAScriptPreview = fullAAScript; OrigInstrBytes = origInstrBytes; OrigInstrLen = origInstrLen;
            CustomCodeBytes = customCodeBytes; HasOriginalCode = hasOriginalCode;
            FullCaveBytes = fullCaveBytes; ReturnHereFixups = returnHereFixups;
            AllocBlocks = allocBlocks; RipFixups = ripFixups;
            IsAllocScript = isAllocScript; DirectPatchBytes = directPatchBytes;
            AllocSymbolName = allocSymbolName ?? "";
            AOBSymbolName = aobSymbolName ?? "";
            InjectAddress = IntPtr.Zero; AllocatedMem = IntPtr.Zero; OriginalCode = null;
            // ★ 数据段AOB字段初始化
            DataAOBPattern = dataAobPattern ?? "";
            DataAOBOffset = dataAobOffset;
            DataSegBaseAddr = 0;
            DataSegNeedsRescan = true;
        }

        public void ResetState()
        {
            AAEnabled = false;
            InjectAddress = IntPtr.Zero;
            AllocatedMem = IntPtr.Zero;
            OriginalCode = null;
            ExtraAllocs = null;
            if (AllocBlocks != null)
            {
                foreach (var blk in AllocBlocks) blk.NewAddr = IntPtr.Zero;
            }
            // ★ 数据段AOB:游戏重启后必须清除缓存,强制重扫
            DataSegBaseAddr = 0;
            DataSegNeedsRescan = true;
        }
    }

    class PanelEntry
    {
        public Label lblDesc;
        public Label lblCurrent;
        public TextBox txtValue;
        public CheckBox chkFreeze;
        public Button btnWrite;
        public Button btnToggleAA;
    }

    class AOBScanner
    {
        [DllImport("kernel32.dll")]
        static extern bool ReadProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer, uint nSize, out int lpNumberOfBytesRead);
        [DllImport("kernel32.dll")]
        static extern IntPtr VirtualQueryEx(IntPtr hProcess, IntPtr lpAddress, out MEMORY_BASIC_INFORMATION lpBuffer, uint dwLength);

        [StructLayout(LayoutKind.Sequential)]
        public struct MEMORY_BASIC_INFORMATION
        {
            public IntPtr BaseAddress;
            public IntPtr AllocationBase;
            public uint AllocationProtect;
            public IntPtr RegionSize;
            public uint State;
            public uint Protect;
            public uint Type;
        }

        const uint MEM_COMMIT = 0x1000;
        const uint PAGE_NOACCESS = 0x01;
        const uint PAGE_GUARD = 0x100;

        public static IntPtr Scan(IntPtr hProcess, string pattern, IntPtr scanStart, IntPtr scanEnd)
        {
            pattern = pattern.Trim();
            while (pattern.Contains("  "))
                pattern = pattern.Replace("  ", " ");
            string[] parts = pattern.Split(new char[]{' '}, StringSplitOptions.RemoveEmptyEntries);
            List<byte> patternBytes = new List<byte>();
            List<bool> mask = new List<bool>();

            foreach (string part in parts)
            {
                if (part.Contains("?"))
                {
                    patternBytes.Add(0);
                    mask.Add(false);
                }
                else
                {
                    try
                    {
                        patternBytes.Add(Convert.ToByte(part, 16));
                        mask.Add(true);
                    }
                    catch
                    {
                        patternBytes.Add(0);
                        mask.Add(false);
                    }
                }
            }

            int patternLength = patternBytes.Count;
            if (patternLength == 0) return IntPtr.Zero;

            IntPtr currentAddress = scanStart;
            MEMORY_BASIC_INFORMATION mbi;
            byte[] buffer = new byte[4096];

            while (currentAddress.ToInt64() < scanEnd.ToInt64())
            {
                if (VirtualQueryEx(hProcess, currentAddress, out mbi, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION))) == IntPtr.Zero)
                    break;

                if (mbi.State == MEM_COMMIT && (mbi.Protect & PAGE_NOACCESS) == 0 && (mbi.Protect & PAGE_GUARD) == 0)
                {
                    long regionStart = mbi.BaseAddress.ToInt64();
                    long regionEnd = regionStart + mbi.RegionSize.ToInt64();

                    if (regionStart < scanStart.ToInt64()) regionStart = scanStart.ToInt64();
                    if (regionEnd > scanEnd.ToInt64()) regionEnd = scanEnd.ToInt64();

                    if (regionStart >= regionEnd)
                    {
                        currentAddress = new IntPtr(regionEnd);
                        continue;
                    }

                    long pos = regionStart;
                    while (pos + patternLength <= regionEnd)
                    {
                        int bytesToRead = (int)Math.Min(buffer.Length, regionEnd - pos);
                        if (bytesToRead < patternLength) break;

                        int bytesRead;
                        if (!ReadProcessMemory(hProcess, new IntPtr(pos), buffer, (uint)bytesToRead, out bytesRead) || bytesRead < patternLength)
                        {
                            // 读取失败只跳过当前页面，继续扫描后续页面（而不是跳过整个区域）
                            pos += 4096;
                            continue;
                        }

                        for (int i = 0; i <= bytesRead - patternLength; i++)
                        {
                            bool match = true;
                            for (int j = 0; j < patternLength; j++)
                            {
                                if (mask[j] && buffer[i + j] != patternBytes[j])
                                {
                                    match = false;
                                    break;
                                }
                            }
                            if (match)
                            {
                                return new IntPtr(pos + i);
                            }
                        }
                        pos += bytesRead - patternLength + 1;
                    }
                }
                currentAddress = new IntPtr(mbi.BaseAddress.ToInt64() + mbi.RegionSize.ToInt64());
            }
            return IntPtr.Zero;
        }
    }

    // ★ 数据段AOB扫描器(独立于代码段AOBScanner,用于数据段重定位)
    class DataSegmentScanner
    {
        [DllImport("kernel32.dll")]
        static extern bool ReadProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer, uint nSize, out int lpNumberOfBytesRead);
        [DllImport("kernel32.dll")]
        static extern IntPtr VirtualQueryEx(IntPtr hProcess, IntPtr lpAddress, out MEMORY_BASIC_INFORMATION lpBuffer, uint dwLength);

        [StructLayout(LayoutKind.Sequential)]
        public struct MEMORY_BASIC_INFORMATION
        {
            public IntPtr BaseAddress;
            public IntPtr AllocationBase;
            public uint AllocationProtect;
            public IntPtr RegionSize;
            public uint State;
            public uint Protect;
            public uint Type;
        }

        const uint MEM_COMMIT = 0x1000;
        const uint PAGE_NOACCESS = 0x01;
        const uint PAGE_GUARD = 0x100;

        // 全进程扫描,返回首个命中地址(不弹窗,自动取首个)
        public static long Scan(IntPtr hProcess, string pattern)
        {
            if (string.IsNullOrEmpty(pattern)) return 0;
            pattern = pattern.Trim();
            while (pattern.Contains("  ")) pattern = pattern.Replace("  ", " ");
            string[] parts = pattern.Split(new char[]{' '}, StringSplitOptions.RemoveEmptyEntries);
            List<byte> patternBytes = new List<byte>();
            List<bool> mask = new List<bool>();
            foreach (string part in parts)
            {
                if (part.Contains("?")) { patternBytes.Add(0); mask.Add(false); }
                else { try { patternBytes.Add(Convert.ToByte(part, 16)); mask.Add(true); } catch { patternBytes.Add(0); mask.Add(false); } }
            }
            int patternLength = patternBytes.Count;
            if (patternLength == 0) return 0;

            byte[] buffer = new byte[65536];
            long queryAddr = 0x10000;
            MEMORY_BASIC_INFORMATION mbi;
            while (VirtualQueryEx(hProcess, new IntPtr(queryAddr), out mbi, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION))) != IntPtr.Zero)
            {
                if (mbi.State == MEM_COMMIT && (mbi.Protect & PAGE_NOACCESS) == 0 && (mbi.Protect & PAGE_GUARD) == 0)
                {
                    long regionStart = mbi.BaseAddress.ToInt64();
                    long regionSize = mbi.RegionSize.ToInt64();
                    if (regionSize > 0 && regionSize <= 512 * 1024 * 1024)
                    {
                        long pos = regionStart;
                        long regionEnd = regionStart + regionSize;
                        while (pos + patternLength <= regionEnd)
                        {
                            int toRead = (int)Math.Min(buffer.Length, regionEnd - pos);
                            if (toRead < patternLength) break;
                            int bytesRead;
                            if (!ReadProcessMemory(hProcess, new IntPtr(pos), buffer, (uint)toRead, out bytesRead) || bytesRead < patternLength)
                            {
                                pos += 4096;
                                continue;
                            }
                            for (int i = 0; i <= bytesRead - patternLength; i++)
                            {
                                bool match = true;
                                for (int j = 0; j < patternLength; j++)
                                {
                                    if (mask[j] && buffer[i + j] != patternBytes[j]) { match = false; break; }
                                }
                                if (match) return pos + i;  // 首个命中立即返回
                            }
                            pos += bytesRead - patternLength + 1;
                        }
                    }
                }
                long nextAddr = mbi.BaseAddress.ToInt64() + mbi.RegionSize.ToInt64();
                if (nextAddr <= queryAddr) break;
                queryAddr = nextAddr;
            }
            return 0;
        }

        // 验证缓存基址是否仍有效(读取基址处字节与pattern前N字节比对)
        public static bool VerifyBaseAddr(IntPtr hProcess, long baseAddr, string pattern)
        {
            if (baseAddr == 0 || string.IsNullOrEmpty(pattern)) return false;
            pattern = pattern.Trim();
            while (pattern.Contains("  ")) pattern = pattern.Replace("  ", " ");
            string[] parts = pattern.Split(new char[]{' '}, StringSplitOptions.RemoveEmptyEntries);
            int pLen = parts.Length;
            if (pLen == 0) return false;
            byte[] buf = new byte[pLen];
            int read;
            if (!ReadProcessMemory(hProcess, new IntPtr(baseAddr), buf, (uint)pLen, out read) || read < pLen)
                return false;
            for (int i = 0; i < pLen; i++)
            {
                if (parts[i].Contains("?")) continue;  // 通配位跳过
                try
                {
                    byte expect = Convert.ToByte(parts[i], 16);
                    if (buf[i] != expect) return false;  // 字节不匹配,缓存失效
                }
                catch { }
            }
            return true;  // 全部匹配,缓存有效
        }
    }

    class MemoryProtector
    {
        [DllImport("kernel32.dll", SetLastError = true)]
        public static extern bool VirtualProtectEx(IntPtr hProcess, IntPtr lpAddress, uint dwSize, uint flNewProtect, out uint lpflOldProtect);

        public const uint PAGE_EXECUTE_READWRITE = 0x40;
        public const uint PAGE_READWRITE = 0x04;
        public const uint PAGE_READONLY = 0x02;
        public const uint PAGE_EXECUTE_READ = 0x20;
        public const uint PAGE_EXECUTE_WRITECOPY = 0x80;
        public const uint PAGE_WRITECOPY = 0x08;
        const int PAGE_SIZE = 4096;

        static IntPtr AlignDown(IntPtr addr)
        {
            return new IntPtr(addr.ToInt64() & ~(PAGE_SIZE - 1));
        }

        static uint AlignUp(uint size, IntPtr origAddr, IntPtr alignedAddr)
        {
            long diff = origAddr.ToInt64() - alignedAddr.ToInt64();
            return (uint)(((long)size + diff + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1));
        }

        public static bool UnprotectMemory(IntPtr hProcess, IntPtr address, int size, out uint oldProtect)
        {
            oldProtect = 0;
            IntPtr alignedAddr = AlignDown(address);
            uint alignedSize = AlignUp((uint)size, address, alignedAddr);
            uint[] tryFlags = new uint[] { PAGE_EXECUTE_READWRITE, PAGE_READWRITE, PAGE_EXECUTE_WRITECOPY, PAGE_WRITECOPY };
            foreach (uint flag in tryFlags)
            {
                if (VirtualProtectEx(hProcess, alignedAddr, alignedSize, flag, out oldProtect))
                    return true;
            }
            return false;
        }

        public static bool ReprotectMemory(IntPtr hProcess, IntPtr address, int size, uint oldProtect)
        {
            IntPtr alignedAddr = AlignDown(address);
            uint alignedSize = AlignUp((uint)size, address, alignedAddr);
            uint dummy;
return VirtualProtectEx(hProcess, alignedAddr, alignedSize, oldProtect, out dummy);
        }
    }

// ★★★ AA脚本引擎 v3 — 完整x86/x64汇编器+脚本解析器 ★★★
    class AAEngine
    {
        [DllImport("kernel32.dll")]
        static extern IntPtr VirtualAllocEx(IntPtr hProcess, IntPtr lpAddress, uint dwSize,
            uint flAllocationType, uint flProtect);
        [DllImport("kernel32.dll")]
        static extern bool VirtualFreeEx(IntPtr hProcess, IntPtr lpAddress, uint dwSize, uint dwFreeType);
        [DllImport("kernel32.dll")]
        static extern bool WriteProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer,
            uint nSize, out int lpNumberOfBytesWritten);
        [DllImport("kernel32.dll")]
        static extern bool ReadProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer,
            uint nSize, out int lpNumberOfBytesRead);

        // ========== 寄存器定义 (x86 & x64) ==========
        static int GetReg(string s, out bool is64)
        {
            is64 = false; s = s.Trim().ToLower();
            if (s=="eax") return 0; if (s=="ecx") return 1; if (s=="edx") return 2;
            if (s=="ebx") return 3; if (s=="esp") return 4; if (s=="ebp") return 5;
            if (s=="esi") return 6; if (s=="edi") return 7;
            is64 = true;
            if (s=="rax") return 0; if (s=="rcx") return 1; if (s=="rdx") return 2;
            if (s=="rbx") return 3; if (s=="rsp") return 4; if (s=="rbp") return 5;
            if (s=="rsi") return 6; if (s=="rdi") return 7;
            if (s=="r8") return 0; if (s=="r9") return 1; if (s=="r10") return 2;
            if (s=="r11") return 3; if (s=="r12") return 4; if (s=="r13") return 5;
            if (s=="r14") return 6; if (s=="r15") return 7;
            return -1;
        }
        static bool IsExtReg(string s) {
            s = s.Trim().ToLower();
            return (s=="r8"||s=="r9"||s=="r10"||s=="r11"
                 ||s=="r12"||s=="r13"||s=="r14"||s=="r15");
        }
        static long ParseNum(string s) {
            s = s.Trim(); if (string.IsNullOrEmpty(s)) return -1;
            if (s.StartsWith("0x")||s.StartsWith("0X")) return long.Parse(s.Substring(2), System.Globalization.NumberStyles.HexNumber);
            if (s.StartsWith("$")) return long.Parse(s.Substring(1), System.Globalization.NumberStyles.HexNumber);
            long v; if (long.TryParse(s, out v)) return v;
            try { return long.Parse(s, System.Globalization.NumberStyles.HexNumber); } catch { return -1; }
        }
        static void WriteLE(byte[] b, int off, long val, int bytes) {
            for (int i=0;i<bytes;i++) b[off+i]=(byte)((val>>(i*8))&0xFF);
        }
        static long ReadLE(byte[] b, int off, int bytes) {
            long v=0; for (int i=0;i<bytes;i++) v|=((long)b[off+i])<<(i*8); return v;
        }

        // ========== 地址解析 ==========
        static long ResolveAddr(string expr, Dictionary<string,long> syms, string allocName, long allocAddr) {
            expr = expr.Trim();
            if (string.IsNullOrEmpty(expr)) return -1;
            // alloc+偏移 / alloc名
            if (!string.IsNullOrEmpty(allocName)) {
                if (expr.StartsWith(allocName+"+", StringComparison.OrdinalIgnoreCase))
                { long o=ParseNum(expr.Substring(allocName.Length+1)); if(o>=0) return allocAddr+o; }
                if (expr.Equals(allocName, StringComparison.OrdinalIgnoreCase)) return allocAddr;
            }
            // 符号表
            if (syms.ContainsKey(expr)) return syms[expr];
            // 十六进制数字
            return ParseNum(expr);
        }

        // ========== 核心汇编器 (x86 + x64) ==========
        // 返回: byte[] or null(失败)
        public static byte[] Assemble(string line, long curAddr, Dictionary<string,long> syms,
            string allocName, long allocAddr, bool target64)
        {
            line = line.Trim();
            if (line==""||line.StartsWith("//")||line.StartsWith(";")) return new byte[0];
            string lower = line.ToLower();

            // db XX XX ...
            if (lower.StartsWith("db ")) {
                var ps=line.Substring(3).Split(new char[]{' ',','},StringSplitOptions.RemoveEmptyEntries);
                var r=new byte[ps.Length]; for(int i=0;i<ps.Length;i++) r[i]=(byte)ParseNum(ps[i]); return r;
            }
            if (lower=="nop") return new byte[]{0x90};
            if (lower=="ret") return new byte[]{0xC3};
            // int3
            if (lower=="int3"||lower=="int 3") return new byte[]{0xCC};

            // === 跳转/调用 ===
            { var m=System.Text.RegularExpressions.Regex.Match(line, @"^(jmp|je|jne|jz|jnz|jl|jg|jle|jge|jb|ja|jbe|jae|call)\s+(.+)$", System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) {
                string op=m.Groups[1].Value.ToLower(); long tgt=ResolveAddr(m.Groups[2].Value,syms,allocName,allocAddr);
                if (tgt<0) return null;
                long rel=tgt-(curAddr+2);
                if (op=="jmp"&&rel>=-128&&rel<=127) { var b=new byte[2]; b[0]=0xEB; b[1]=(byte)rel; return b; }
                byte opc=(byte)(op=="call"?0xE8: (op=="jmp"?0xE9:0x0F));
                if (opc==0x0F) { // 条件跳转
                    rel=tgt-(curAddr+6); var b2=new byte[6]; b2[0]=0x0F;
                    switch(op){case"je":case"jz":b2[1]=0x84;break;case"jne":case"jnz":b2[1]=0x85;break;
                    case"jl":b2[1]=0x8C;break;case"jge":b2[1]=0x8D;break;case"jle":b2[1]=0x8E;break;case"jg":b2[1]=0x8F;break;
                    case"jb":b2[1]=0x82;break;case"jae":b2[1]=0x83;break;case"jbe":b2[1]=0x86;break;case"ja":b2[1]=0x87;break;
                    default:return null;}
                    WriteLE(b2,2,rel,4); return b2;
                }
                rel=tgt-(curAddr+5); var b5=new byte[5]; b5[0]=opc; WriteLE(b5,1,rel,4); return b5;
            }}

            // === push/pop reg ===
            { var pm=System.Text.RegularExpressions.Regex.Match(line,@"^(push|pop)\s+(\w+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (pm.Success) { bool is64; int r=GetReg(pm.Groups[2].Value,out is64);
                if (r<0) return null; byte opc=(byte)(pm.Groups[1].Value.ToLower()=="push"?0x50:0x58);
                if (IsExtReg(pm.Groups[2].Value)) return new byte[]{0x41,(byte)(opc+r)};
                return new byte[]{(byte)(opc+r)}; }}

            // === mov reg, reg ===
            { var mm=System.Text.RegularExpressions.Regex.Match(line,@"^mov\s+(\w+)\s*,\s*(\w+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (mm.Success) { bool d64,s64; int dr=GetReg(mm.Groups[1].Value,out d64); int sr=GetReg(mm.Groups[2].Value,out s64);
                if (dr<0||sr<0) return null;
                bool dExt=IsExtReg(mm.Groups[1].Value), sExt=IsExtReg(mm.Groups[2].Value);
                if (dExt||sExt||d64||s64) {
                    byte rex=0x40;
                    if (d64||s64) rex|=0x08;
                    if (sExt) rex|=0x04;
                    if (dExt) rex|=0x01;
                    return new byte[]{rex,0x89,(byte)(0xC0+sr*8+dr)};
                }
                return new byte[]{0x89,(byte)(0xC0+sr*8+dr)}; }}

            // === mov [mem], reg ===
            { var m=System.Text.RegularExpressions.Regex.Match(line,@"^mov\s+\[([^\]]+)\]\s*,\s*(\w+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) { bool is64; int reg=GetReg(m.Groups[2].Value,out is64); if(reg<0) return null;
                string ae=m.Groups[1].Value.Trim();
                // [reg+disp]
                { var rm=System.Text.RegularExpressions.Regex.Match(ae,@"^(\w+)\s*\+\s*(.+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (rm.Success) { bool b64; int br=GetReg(rm.Groups[1].Value,out b64); if(br<0) return null;
                    long disp=ParseNum(rm.Groups[2].Value); if(disp<0) return null;
                    byte rex=0; if(is64||b64) rex=0x48;
                    if (is64&&!b64) rex=0x44; // REX.R
                    var b=new byte[rex>0?7:6]; int o=0;
                    if (rex>0) b[o++]=rex;
                    b[o++]=0x89; b[o++]=(byte)(0x80+reg*8+br); WriteLE(b,o,disp,4); return b;
                }}
                // [disp32] or [rip+disp32]
                long addr=ResolveAddr(ae,syms,allocName,allocAddr); if(addr<0) return null;
                if (target64) {
                    // x64 RIP-relative
                    long ripRel=addr-(curAddr+7); // REX + opcode + modRM + 4-byte disp
                    var b=new byte[7]; b[0]=is64?(byte)0x48:(byte)0x44; b[1]=0x89;
                    b[2]=(byte)(reg*8+5); WriteLE(b,3,ripRel,4); return b;
                } else {
                    var b=new byte[6]; b[0]=0x89; b[1]=(byte)(reg*8+5); WriteLE(b,2,addr,4); return b;
                }
            }}

            // === mov reg, [mem] ===
            { var m=System.Text.RegularExpressions.Regex.Match(line,@"^mov\s+(\w+)\s*,\s*\[([^\]]+)\]$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) { bool is64; int reg=GetReg(m.Groups[1].Value,out is64); if(reg<0) return null;
                string ae=m.Groups[2].Value.Trim();
                { var rm=System.Text.RegularExpressions.Regex.Match(ae,@"^(\w+)\s*\+\s*(.+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (rm.Success) { bool b64; int br=GetReg(rm.Groups[1].Value,out b64); if(br<0) return null;
                    long disp=ParseNum(rm.Groups[2].Value); if(disp<0) return null;
                    byte rex=0; if(is64||b64) rex=0x48; if(is64&&!b64) rex=0x44;
                    var b=new byte[rex>0?7:6]; int o=0;
                    if (rex>0) b[o++]=rex;
                    b[o++]=0x8B; b[o++]=(byte)(0x80+reg*8+br); WriteLE(b,o,disp,4); return b;
                }}
                long addr=ResolveAddr(ae,syms,allocName,allocAddr); if(addr<0) return null;
                if (target64) {
                    long ripRel=addr-(curAddr+7);
                    var b=new byte[7]; b[0]=is64?(byte)0x48:(byte)0x44; b[1]=0x8B;
                    b[2]=(byte)(reg*8+5); WriteLE(b,3,ripRel,4); return b;
                } else {
                    var b=new byte[6]; b[0]=0x8B; b[1]=(byte)(reg*8+5); WriteLE(b,2,addr,4); return b;
                }
            }}

            // === mov reg, imm ===
            { var m=System.Text.RegularExpressions.Regex.Match(line,@"^mov\s+(\w+)\s*,\s*(.+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) { bool is64; int reg=GetReg(m.Groups[1].Value,out is64); if(reg<0) return null;
                long imm=ParseNum(m.Groups[2].Value); if(imm<0) return null;
                if (is64) { byte rex=0x48; if(IsExtReg(m.Groups[1].Value)) rex|=0x01; var b=new byte[10]; b[0]=rex; b[1]=0xB8; b[2]=(byte)reg; WriteLE(b,3,imm,8); return b; }
                var b2=new byte[5]; b2[0]=(byte)(0xB8+reg); WriteLE(b2,1,imm,4); return b2;
            }}

            // === add/sub/and/or/xor/cmp reg, imm32 ===
            { var m=System.Text.RegularExpressions.Regex.Match(line,@"^(add|sub|and|or|xor|cmp)\s+(\w+)\s*,\s*(.+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) { bool is64; int reg=GetReg(m.Groups[2].Value,out is64); if(reg<0) return null;
                long imm=ParseNum(m.Groups[3].Value); if(imm<0) return null;
                byte opc=0; switch(m.Groups[1].Value.ToLower()){case"add":opc=0x81;break;case"sub":opc=0x81;break;
                case"and":opc=0x81;break;case"or":opc=0x81;break;case"xor":opc=0x81;break;case"cmp":opc=0x81;break;}
                byte modRM; switch(m.Groups[1].Value.ToLower()){
                case"add":modRM=0xC0;break;case"sub":modRM=0xE8;break;case"and":modRM=0xE0;break;
                case"or":modRM=0xC8;break;case"xor":modRM=0xF0;break;case"cmp":modRM=0xF8;break;default:return null;}
                modRM=(byte)(modRM|reg);
                if (is64||IsExtReg(m.Groups[2].Value)) { byte rex=0x40; if(is64) rex|=0x08; if(IsExtReg(m.Groups[2].Value)) rex|=0x01; var b=new byte[7]; b[0]=rex; b[1]=opc; b[2]=modRM; WriteLE(b,3,imm,4); return b; }
                var b2=new byte[6]; b2[0]=opc; b2[1]=modRM; WriteLE(b2,2,imm,4); return b2;
            }}

            // === lea reg, [base+disp] ===  (x64 only for simplicity, but same encoding)
            { var m=System.Text.RegularExpressions.Regex.Match(line,@"^lea\s+(\w+)\s*,\s*\[([^\]]+)\]$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) { bool is64; int reg=GetReg(m.Groups[1].Value,out is64); if(reg<0) return null;
                string ae=m.Groups[2].Value.Trim();
                var rm=System.Text.RegularExpressions.Regex.Match(ae,@"^(\w+)\s*\+\s*(.+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (!rm.Success) return null;
                bool b64; int br=GetReg(rm.Groups[1].Value,out b64); if(br<0) return null;
                long disp=ParseNum(rm.Groups[2].Value); if(disp<0) return null;
                byte rex=0; if(is64||b64) rex=0x48; if (is64&&!b64) rex=0x44;
                var b=new byte[rex>0?7:6]; int o=0;
                if (rex>0) b[o++]=rex;
                b[o++]=0x8D; b[o++]=(byte)(0x80+reg*8+br); WriteLE(b,o,disp,4); return b;
            }}

            // === test reg, reg ===
            { var m=System.Text.RegularExpressions.Regex.Match(line,@"^test\s+(\w+)\s*,\s*(\w+)$",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (m.Success) { bool d64,s64; int dr=GetReg(m.Groups[1].Value,out d64); int sr=GetReg(m.Groups[2].Value,out s64);
                if (dr<0||sr<0) return null;
                bool dExt=IsExtReg(m.Groups[1].Value), sExt=IsExtReg(m.Groups[2].Value);
                if (dExt||sExt||d64||s64) {
                    byte rex=0x40;
                    if (d64||s64) rex|=0x08;
                    if (sExt) rex|=0x04;
                    if (dExt) rex|=0x01;
                    return new byte[]{rex,0x85,(byte)(0xC0+sr*8+dr)};
                }
                return new byte[]{0x85,(byte)(0xC0+sr*8+dr)}; }}

            return null;
        }

        // ========== AA脚本执行引擎 ==========
        // 解析并执行AA脚本的[ENABLE]段，返回代码洞字节数组
        // 同时填充out参数用于指针链注册
        public static byte[] ExecuteScript(string script, long injectAddr, byte[] origBytes,
            bool target64, out string allocName, out long allocAddr, out int allocSize,
            IntPtr hProcess, uint MEM_COMMIT, uint MEM_RESERVE, uint PAGE_EXECUTE_READWRITE)
        {
            allocName=""; allocAddr=0; allocSize=4096;
            // 提取[ENABLE]段
            int eIdx=script.IndexOf("[ENABLE]",StringComparison.OrdinalIgnoreCase);
            int dIdx=script.IndexOf("[DISABLE]",StringComparison.OrdinalIgnoreCase);
            if (eIdx<0) return null;
            string enable=(dIdx>eIdx)?script.Substring(eIdx+9,dIdx-eIdx-9):script.Substring(eIdx+9);
            if (string.IsNullOrWhiteSpace(enable)) return null;

            // 提取alloc
            var am=System.Text.RegularExpressions.Regex.Match(enable,
                @"alloc\s*\(\s*(\w+)\s*,\s*(\S+)\s*\)",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (am.Success) {
                allocName=am.Groups[1].Value;
                string sz=am.Groups[2].Value;
                if (sz.StartsWith("$")||sz.StartsWith("0x",StringComparison.OrdinalIgnoreCase))
                    allocSize=(int)long.Parse(sz.Replace("$","").Replace("0x","").Replace("0X",""),System.Globalization.NumberStyles.HexNumber);
                else int.TryParse(sz,out allocSize);
            }
            allocSize=Math.Max(4096,allocSize);

            // 提取label声明
            var syms=new Dictionary<string,long>(StringComparer.OrdinalIgnoreCase);
            foreach (System.Text.RegularExpressions.Match lm in System.Text.RegularExpressions.Regex.Matches(enable,
                @"label\s*\(\s*(\w+)\s*\)",System.Text.RegularExpressions.RegexOptions.IgnoreCase))
                syms[lm.Groups[1].Value]=0;

            // 提取aobscan标签 → 映射到注入地址
            var aobM=System.Text.RegularExpressions.Regex.Match(script,
                @"aobscan(?:module)?\s*\(\s*(\w+)\s*,",System.Text.RegularExpressions.RegexOptions.IgnoreCase);
            if (aobM.Success) syms[aobM.Groups[1].Value]=injectAddr;

            // 分配代码洞
            var alAddr=VirtualAllocEx(hProcess,IntPtr.Zero,(uint)allocSize,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE);
            if (alAddr==IntPtr.Zero) return null;
            allocAddr=alAddr.ToInt64();

            // 计算returnhere
            int codeLen=Math.Max(origBytes.Length,5);
            long retHere=injectAddr+codeLen;
            syms["returnhere"]=retHere;

            // 解析并汇编指令
            var lines=enable.Split(new char[]{'\r','\n'},StringSplitOptions.RemoveEmptyEntries);
            var cave=new List<byte>();
            long cur=allocAddr;
            bool inCode=false; string curLabel="";
            foreach (string raw in lines) {
                string l=raw.Trim();
                if (l==""||l.StartsWith("//")||l.StartsWith(";")) continue;
                string lo=l.ToLower();
                if (lo.StartsWith("alloc(")||lo.StartsWith("aobscan")||lo.StartsWith("label(")
                    ||lo.StartsWith("registersymbol")||lo.StartsWith("unregistersymbol")
                    ||lo.StartsWith("dealloc")||lo.StartsWith("createthread")||lo.StartsWith("fullaccess"))
                    continue;
                // 标签行
                if (l.EndsWith(":")) {
                    curLabel=l.Substring(0,l.Length-1).Trim();
                    syms[curLabel]=cur; inCode=true; continue;
                }
                // originalcode / readmem
                if (lo.Contains("originalcode")) {
                    cave.AddRange(origBytes); cur+=origBytes.Length; continue;
                }
                if (lo.StartsWith("readmem")) {
                    var rm=System.Text.RegularExpressions.Regex.Match(l,
                        @"readmem\s*\(\s*([^,]+)\s*,\s*(\d+)\s*\)",
                        System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                    if (rm.Success) {
                        long rmAddr=ResolveAddr(rm.Groups[1].Value.Trim(),syms,allocName,allocAddr);
                        int rmSize;
                        if (rmAddr>=0 && int.TryParse(rm.Groups[2].Value,out rmSize) && rmSize>0 && rmSize<=4096) {
                            byte[] rmBuf=new byte[rmSize];
                            int rmRd;
                            if (hProcess!=IntPtr.Zero && ReadProcessMemory(hProcess,new IntPtr(rmAddr),rmBuf,(uint)rmSize,out rmRd) && rmRd==rmSize) {
                                cave.AddRange(rmBuf); cur+=rmSize; continue;
                            }
                        }
                    }
                    // readmem解析或读取失败，回退originalBytes
                    cave.AddRange(origBytes); cur+=origBytes.Length; continue;
                }
                if (!inCode) continue;
                // 汇编
                byte[] asm=Assemble(l,cur,syms,allocName,allocAddr,target64);
                if (asm==null||asm.Length==0) continue;
                cave.AddRange(asm); cur+=asm.Length;
            }
// 确保末尾有jmp returnhere
            if (cave.Count>0&&cave[cave.Count-1]!=0xE9&&cave[cave.Count-1]!=0xC3) {
                long rel=retHere-(cur+5);
                cave.Add(0xE9);
                var tmp=new byte[4]; WriteLE(tmp,0,rel,4);
                cave.AddRange(tmp);
            }
            return cave.ToArray();
        }
    }

    class MainForm : Form
    {
        [DllImport("kernel32.dll")]
        static extern IntPtr OpenProcess(uint dwDesiredAccess, bool bInheritHandle, int dwProcessId);
        [DllImport("kernel32.dll")]
        static extern bool ReadProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer, uint nSize, out int lpNumberOfBytesRead);
        [DllImport("kernel32.dll")]
        static extern bool WriteProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer, uint nSize, out int lpNumberOfBytesWritten);
        [DllImport("kernel32.dll")]
        static extern bool CloseHandle(IntPtr hObject);
        [DllImport("kernel32.dll")]
        static extern IntPtr VirtualAllocEx(IntPtr hProcess, IntPtr lpAddress, uint dwSize, uint flAllocationType, uint flProtect);
        [DllImport("kernel32.dll")]
        static extern bool VirtualFreeEx(IntPtr hProcess, IntPtr lpAddress, uint dwSize, uint dwFreeType);
        [DllImport("kernel32.dll")]
        static extern int IsDebuggerPresent();
        [DllImport("kernel32.dll")]
        static extern IntPtr GetCurrentProcess();
        [DllImport("kernel32.dll")]
        static extern bool CheckRemoteDebuggerPresent(IntPtr hProcess, ref bool bDebuggerPresent);
        [DllImport("psapi.dll")]
        static extern bool EnumProcessModulesEx(IntPtr hProcess, IntPtr lphModule, uint cb, out uint lpcbNeeded, uint dwFilterFlag);
        [DllImport("psapi.dll")]
        static extern uint GetModuleBaseName(IntPtr hProcess, IntPtr hModule, StringBuilder lpBaseName, uint nSize);
        [DllImport("psapi.dll")]
        static extern bool GetModuleInformation(IntPtr hProcess, IntPtr hModule, out MODULEINFO lpmodinfo, uint cb);
        [DllImport("kernel32.dll")]
        static extern bool IsWow64Process(IntPtr hProcess, out bool wow64Process);
        [DllImport("kernel32.dll")]
        static extern IntPtr VirtualQueryEx(IntPtr hProcess, IntPtr lpAddress, out MEMORY_BASIC_INFORMATION_EX lpBuffer, uint dwLength);
        [StructLayout(LayoutKind.Sequential)]
        struct MEMORY_BASIC_INFORMATION_EX
        {
            public IntPtr BaseAddress;
            public IntPtr AllocationBase;
            public uint AllocationProtect;
            public IntPtr RegionSize;
            public uint State;
            public uint Protect;
            public uint Type;
        }
        [DllImport("kernel32.dll", SetLastError = true)]
        static extern IntPtr CreateToolhelp32Snapshot(uint dwFlags, uint th32ProcessID);
        [DllImport("kernel32.dll", SetLastError = true)]
        static extern bool Module32First(IntPtr hSnapshot, ref MODULEENTRY32 lpme);
        [DllImport("kernel32.dll", SetLastError = true)]
        static extern bool Module32Next(IntPtr hSnapshot, ref MODULEENTRY32 lpme);

        const uint TH32CS_SNAPMODULE = 0x00000008;
        const uint TH32CS_SNAPMODULE32 = 0x00000010;

        [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Ansi)]
struct MODULEENTRY32
        {
            public uint dwSize;
            public uint th32ModuleID;
            public uint th32ProcessID;
            public uint GlbcntUsage;
            public uint ProccntUsage;
            public IntPtr modBaseAddr;
            public uint modBaseSize;
            public IntPtr hModule;
            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 256)]
            public string szModule;
            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)]
            public string szExePath;
        }

        [StructLayout(LayoutKind.Sequential)]
        struct MODULEINFO
        {
            public IntPtr lpBaseOfDll;
            public uint SizeOfImage;
            public IntPtr EntryPoint;
        }

const uint PROCESS_ALL_ACCESS = 0x1F0FFF;
        const uint PROCESS_QUERY_INFORMATION = 0x0400;
        const uint PROCESS_VM_READ = 0x0010;
        const uint MEM_COMMIT = 0x1000;
        const uint MEM_RESERVE = 0x2000;
        const uint PAGE_EXECUTE_READWRITE = 0x40;
        const uint MEM_RELEASE = 0x8000;

        IntPtr hProcess = IntPtr.Zero;
        bool bRunning = false;
        bool bStopping = false;
        bool silentMode = false;  // ★ 静默模式：自动激活时禁止弹窗，避免阻塞WorkerLoop
        string lastAAError = "";   // [AOB导出] 收集静默期的失败原因，供状态栏显示
        string connDiagInfo = "";    // [r3] 连接成功时的绿色状态栏文本，诊断结束后恢复
        string lastPtrStatus = "";   // [r3] 上次写入状态栏的记录诊断，用于去重（WorkerLoop 每100ms一轮）
        bool ptrHadProblem = false;  // [r3] 上一轮是否存在未解析记录
        bool targetIs32Bit = false;
        Thread workerThread;
__ANTI_THREAD_FIELD__
Dictionary<string, IntPtr> moduleCache = new Dictionary<string, IntPtr>(StringComparer.OrdinalIgnoreCase);
        Dictionary<string, uint> moduleSizeCache = new Dictionary<string, uint>(StringComparer.OrdinalIgnoreCase);
        // ★ 多子进程：单独缓存所有进程模块，仅用于AOB扫描
        Dictionary<string, IntPtr> allProcessModuleCache = new Dictionary<string, IntPtr>(StringComparer.OrdinalIgnoreCase);
        Dictionary<string, uint> allProcessModuleSizeCache = new Dictionary<string, uint>(StringComparer.OrdinalIgnoreCase);
        Process[] targetProcesses = new Process[0];
        int currentProcessIndex = -1;
        int totalProcessCount = 0;
        int totalModuleCount = 0;
        volatile bool bSwitchRequested = false;
__OBF_DECRYPT__
        TrainerEntry[] entries = new TrainerEntry[]
        {
__ENTRIES__
        };
        PanelEntry[] panels;
        Label lblStatus;
        Button btnStart;
        Button btnSwitch;
        Button btnGameLib;
        Button btnAbout;
        Panel mainPanel;
        List<GameLibEntry> gameLibData = new List<GameLibEntry>();

        class GameLibEntry
        {
            public string GameName;
            public string GameVersion;
            public string EntryData;
        }

        public MainForm()
        {
            this.Text = __TITLE_EXPR__;
             this.Width = 405;
            this.Height = Math.Min(125 + entries.Length * 30, 500);
            this.FormBorderStyle = FormBorderStyle.FixedSingle;
            this.StartPosition = FormStartPosition.CenterScreen;
            this.TopMost = true;
            this.MaximizeBox = false;
            this.ShowInTaskbar = true;
            try { this.Icon = CreateTrainerIcon(); } catch { }

            int y = 10;
            lblStatus = new Label();
            lblStatus.Text = "状态：等待启动";
            lblStatus.Left = 10; lblStatus.Top = y; lblStatus.Width = 400;
            lblStatus.ForeColor = Color.Gray;
            this.Controls.Add(lblStatus);

            y += 25;
            btnGameLib = new Button();
            btnGameLib.Text = "游戏库";
            btnGameLib.Left = 10; btnGameLib.Top = y;
            btnGameLib.Width = 70; btnGameLib.Height = 28;
            btnGameLib.Font = new Font(this.Font.FontFamily, 8, FontStyle.Bold);
            btnGameLib.BackColor = Color.FromArgb(50, 80, 120);
            btnGameLib.ForeColor = Color.White;
            btnGameLib.FlatStyle = FlatStyle.Flat;
            btnGameLib.Cursor = Cursors.Hand;
            btnGameLib.Click += BtnGameLib_Click;
            this.Controls.Add(btnGameLib);

            btnSwitch = new Button();
            btnSwitch.Text = "进程切换";
            btnSwitch.Left = 85; btnSwitch.Top = y;
            btnSwitch.Width = 80; btnSwitch.Height = 28;
            btnSwitch.Font = new Font(this.Font.FontFamily, 8, FontStyle.Bold);
            btnSwitch.BackColor = Color.FromArgb(60, 60, 60);
            btnSwitch.ForeColor = Color.White;
            btnSwitch.FlatStyle = FlatStyle.Flat;
            btnSwitch.Cursor = Cursors.Hand;
            btnSwitch.Enabled = false;
            btnSwitch.Click += BtnSwitch_Click;
            this.Controls.Add(btnSwitch);

            btnStart = new Button();
            btnStart.Text = "启动修改器";
            btnStart.Left = 170; btnStart.Top = y;
            btnStart.Width = 100; btnStart.Height = 28;
            btnStart.Font = new Font(this.Font.FontFamily, 8, FontStyle.Bold);
            btnStart.BackColor = Color.FromArgb(0, 120, 215);
            btnStart.ForeColor = Color.White;
            btnStart.FlatStyle = FlatStyle.Flat;
            btnStart.Cursor = Cursors.Hand;
            btnStart.Click += BtnStart_Click;
            this.Controls.Add(btnStart);

            btnAbout = new Button();
            btnAbout.Text = "关于";
            btnAbout.Left = 285; btnAbout.Top = y + 3;
            btnAbout.Width = 50; btnAbout.Height = 22;
            btnAbout.Font = new Font(this.Font.FontFamily, 7, FontStyle.Bold);
            btnAbout.BackColor = Color.FromArgb(192, 192, 192);
            btnAbout.ForeColor = Color.Black;
            btnAbout.FlatStyle = FlatStyle.Flat;
            btnAbout.Cursor = Cursors.Hand;
            btnAbout.Click += BtnAbout_Click;
            this.Controls.Add(btnAbout);

            y += 35;
            Panel panel = new Panel();
            mainPanel = panel;
            panel.Left = 5; panel.Top = y;
            panel.Width = this.ClientSize.Width - 10;
            panel.Height = this.ClientSize.Height - y - 5;
            panel.Anchor = AnchorStyles.Top | AnchorStyles.Bottom | AnchorStyles.Left | AnchorStyles.Right;
            panel.AutoScroll = true;
            panel.BorderStyle = BorderStyle.FixedSingle;
            this.Controls.Add(panel);

            __GAMELIB_INIT__

            panels = new PanelEntry[entries.Length];
__PANEL_ROWS__
        }

        void BuildRow(Panel parent, int idx, string desc, bool isAA, bool aaEnabled, string initVal)
        {
            PanelEntry pe = new PanelEntry();
            int y = idx * 30 + 5;

            pe.lblDesc = new Label();
            pe.lblDesc.Text = desc;
            pe.lblDesc.Left = 10; pe.lblDesc.Top = y + 3;
            pe.lblDesc.Width = 65;
            pe.lblDesc.AutoSize = false;
            parent.Controls.Add(pe.lblDesc);

            if (!isAA)
            {
                pe.lblCurrent = new Label();
                pe.lblCurrent.Text = "当前：??";
                pe.lblCurrent.Left = 80; pe.lblCurrent.Top = y + 3;
                pe.lblCurrent.Width = 100;
                pe.lblCurrent.ForeColor = Color.Blue;
                pe.lblCurrent.AutoSize = false;
                parent.Controls.Add(pe.lblCurrent);

                pe.txtValue = new TextBox();
                pe.txtValue.Text = initVal;
                pe.txtValue.Left = 185; pe.txtValue.Top = y;
                pe.txtValue.Width = 70;
                parent.Controls.Add(pe.txtValue);

                pe.chkFreeze = new CheckBox();
                pe.chkFreeze.Text = "锁定";
                pe.chkFreeze.Left = 260; pe.chkFreeze.Top = y + 3;
                pe.chkFreeze.AutoSize = true;
                parent.Controls.Add(pe.chkFreeze);

                pe.btnWrite = new Button();
                pe.btnWrite.Text = "修改";
                pe.btnWrite.Left = 310; pe.btnWrite.Top = y - 1;
                pe.btnWrite.Width = 50; pe.btnWrite.Height = 24;
                pe.btnWrite.Font = new Font(this.Font.FontFamily, 8, FontStyle.Bold);
                pe.btnWrite.Click += (s, e) => OnWriteValue(idx);
                parent.Controls.Add(pe.btnWrite);
            }
            else
            {
                pe.btnToggleAA = new Button();
                pe.btnToggleAA.Text = aaEnabled ? "已开启" : "已关闭";
                pe.btnToggleAA.Left = 80; pe.btnToggleAA.Top = y - 1;
                pe.btnToggleAA.Width = 80; pe.btnToggleAA.Height = 24;
                pe.btnToggleAA.BackColor = aaEnabled ? Color.LightGreen : Color.LightPink;
                pe.btnToggleAA.Enabled = false;
                parent.Controls.Add(pe.btnToggleAA);
            }
            panels[idx] = pe;
        }

int GetValueSize(int vt)
        {
            switch (vt)
            {
                case 0: return 1;
                case 1: return 2;
                case 2: return 4;
                case 3: return 8;  // vtQword
                case 4: return 4;  // vtSingle
                case 5: return 8;  // vtDouble
                default: return 4;
            }
        }

string FormatValue(byte[] buf, int vt)
        {
            try
            {
                switch (vt)
                {
                    case 0: return buf[0].ToString();
                    case 1: return BitConverter.ToUInt16(buf, 0).ToString();
                    case 2: return BitConverter.ToUInt32(buf, 0).ToString();
                    case 3: return BitConverter.ToUInt64(buf, 0).ToString();
                    case 4: return BitConverter.ToSingle(buf, 0).ToString("G6");
                    case 5: return BitConverter.ToDouble(buf, 0).ToString("G6");
                    default: return BitConverter.ToUInt32(buf, 0).ToString();
                }
            }
            catch { return "??"; }
        }

byte[] ParseValueBytes(string s, int vt)
        {
            try
            {
                s = s.Trim();
                switch (vt)
                {
                    case 0: return new byte[] { byte.Parse(s) };
                    case 1: return BitConverter.GetBytes(ushort.Parse(s));
                    case 2: return BitConverter.GetBytes(uint.Parse(s));
case 3: return BitConverter.GetBytes(ulong.Parse(s));
                    case 4: return BitConverter.GetBytes(float.Parse(s));
                    case 5: return BitConverter.GetBytes(double.Parse(s));
                    default: return BitConverter.GetBytes(uint.Parse(s));
                }
            }
            catch { return null; }
        }

bool ReadMem(IntPtr addr, byte[] buf, int size)
        {
            if (hProcess == IntPtr.Zero || addr == IntPtr.Zero) return false;
            int read;
            return ReadProcessMemory(hProcess, addr, buf, (uint)size, out read) && read == size;
        }

        bool WriteMem(IntPtr addr, byte[] buf, int size)
        {
            if (hProcess == IntPtr.Zero || addr == IntPtr.Zero) return false;
            int written;
            return WriteProcessMemory(hProcess, addr, buf, (uint)size, out written) && written == size;
        }

        void CheckAntiDebug()
        {
            if (IsDebuggerPresent() != 0)
                EmergencyExit();
            try
            {
                bool remoteDebug = false;
                CheckRemoteDebuggerPresent(GetCurrentProcess(), ref remoteDebug);
                if (remoteDebug)
                    EmergencyExit();
            }
            catch { }
        }

        void EmergencyExit()
        {
            try { if (hProcess != IntPtr.Zero) CloseHandle(hProcess); } catch { }
            Environment.Exit(0);
        }
__ANTI_MONITOR__
        int knownPID = __KNOWN_PID__;
        string targetProcessName = __PROC_EXPR__.Replace(".exe", "");

        Process[] FindAllTargetProcesses()
        {
            // ★ 增强匹配策略1：已知PID时，优先通过PID直接定位进程
            if (knownPID != 0)
            {
                try
                {
                    Process p = Process.GetProcessById(knownPID);
                    if (p != null && !p.HasExited)
                    {
                        // PID匹配成功，验证进程路径（如果可获取）
                        try
                        {
                            string pPath = p.MainModule != null ? (p.MainModule.FileName ?? "") : "";
                            if (!string.IsNullOrEmpty(pPath))
                            {
                                string pName = System.IO.Path.GetFileName(pPath);
                                if (!string.IsNullOrEmpty(pName))
                                    return new Process[] { p };
                            }
                        }
                        catch { }
                        // 路径验证失败时，仍信任PID匹配
                        return new Process[] { p };
                    }
                }
                catch { }
            }

            // ★ 增强匹配策略2：精确名称匹配
            Process[] procs = Process.GetProcessesByName(targetProcessName);
            
            // ★ 增强匹配策略3：模糊名称匹配（处理乱码/编码差异）
            List<Process> matches = new List<Process>();
            if (procs.Length == 0)
            {
                Process[] allProcs = Process.GetProcesses();
                foreach (Process proc in allProcs)
                {
                    try
                    {
                        if (proc.HasExited) continue;
                        string pName = (proc.ProcessName ?? "").ToLower();
                        string target = targetProcessName.ToLower();
                        if (pName.Contains(target) || target.Contains(pName))
                        {
                            matches.Add(proc);
                        }
                        else if (!string.IsNullOrEmpty(pName))
                        {
                            try
                            {
                                string filePath = proc.MainModule != null ? (proc.MainModule.FileName ?? "") : "";
                                if (!string.IsNullOrEmpty(filePath))
                                {
                                    string fileName = System.IO.Path.GetFileNameWithoutExtension(filePath).ToLower();
                                    if (fileName.Contains(target) || target.Contains(fileName))
                                        matches.Add(proc);
                                }
                            }
                            catch { }
                        }
                    }
                    catch { }
                }
                if (matches.Count > 0)
                    procs = matches.ToArray();
            }

            // ★ 增强匹配策略4：已知PID回退匹配
            if (procs.Length == 0 && knownPID != 0)
            {
                try
                {
                    Process p = Process.GetProcessById(knownPID);
                    if (p != null && !p.HasExited)
                    {
                        string pName = p.ProcessName ?? "";
                        if (pName.IndexOf(targetProcessName, StringComparison.OrdinalIgnoreCase) >= 0
                            || targetProcessName.IndexOf(pName, StringComparison.OrdinalIgnoreCase) >= 0)
                        {
                            procs = new Process[] { p };
                        }
                    }
                }
                catch { }
            }
            if (procs.Length == 0) return procs;
            Array.Sort(procs, delegate(Process a, Process b)
            {
                try
                {
                    long memA = a.WorkingSet64;
                    long memB = b.WorkingSet64;
                    return memB.CompareTo(memA);
                }
                catch { return 0; }
            });
            return procs;
        }

        void BuildModuleCache()
        {
            moduleCache.Clear();
            moduleSizeCache.Clear();
            if (hProcess == IntPtr.Zero || currentProcessIndex < 0 || currentProcessIndex >= targetProcesses.Length) return;
            Process target = targetProcesses[currentProcessIndex];
            int pid = target.Id;

            // 方法1：CreateToolhelp32Snapshot（最可靠，直接按进程ID枚举）
            try
            {
                IntPtr hSnap = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32, (uint)pid);
                if (hSnap != IntPtr.Zero && hSnap != new IntPtr(-1))
                {
                    MODULEENTRY32 me = new MODULEENTRY32();
                    me.dwSize = (uint)Marshal.SizeOf(typeof(MODULEENTRY32));
                    if (Module32First(hSnap, ref me))
                    {
                        do
                        {
                            if (!string.IsNullOrEmpty(me.szModule) && !moduleCache.ContainsKey(me.szModule))
                            {
                                moduleCache[me.szModule] = me.modBaseAddr;
                                moduleSizeCache[me.szModule] = me.modBaseSize;
                            }
                            me.dwSize = (uint)Marshal.SizeOf(typeof(MODULEENTRY32));
                        } while (Module32Next(hSnap, ref me));
                    }
CloseHandle(hSnap);
                }
            }
catch { }
            if (moduleCache.Count > 0) return;

            // 方法2：Process.Modules（.NET原生，64位跨进程可能失败）
            try
            {
                target.Refresh();
                foreach (ProcessModule mod in target.Modules)
                {
                    if (mod.ModuleName != null && !moduleCache.ContainsKey(mod.ModuleName))
                    {
                        moduleCache[mod.ModuleName] = mod.BaseAddress;
                        moduleSizeCache[mod.ModuleName] = (uint)mod.ModuleMemorySize;
                    }
                }
            }
            catch { }
            if (moduleCache.Count > 0) return;

            // 方法3：EnumProcessModulesEx（psapi备用）
            try
            {
                uint needed = 0;
                EnumProcessModulesEx(hProcess, IntPtr.Zero, 0, out needed, 3);
                if (needed > 0)
                {
                    int modCount = (int)(needed / IntPtr.Size);
                    IntPtr[] hMods = new IntPtr[modCount];
                    GCHandle gch = GCHandle.Alloc(hMods, GCHandleType.Pinned);
                    try
                    {
                        if (EnumProcessModulesEx(hProcess, gch.AddrOfPinnedObject(), needed, out needed, 3))
                        {
                            modCount = (int)(needed / IntPtr.Size);
                            for (int i = 0; i < modCount; i++)
                            {
                                IntPtr hMod = hMods[i];
                                if (hMod == IntPtr.Zero) continue;
                                StringBuilder sb = new StringBuilder(260);
                                GetModuleBaseName(hProcess, hMod, sb, 260);
                                string name = sb.ToString();
                                if (!string.IsNullOrEmpty(name) && !moduleCache.ContainsKey(name))
                                {
                                    MODULEINFO info;
                                    if (GetModuleInformation(hProcess, hMod, out info, (uint)Marshal.SizeOf(typeof(MODULEINFO))))
                                    {
                                        moduleCache[name] = info.lpBaseOfDll;
                                        moduleSizeCache[name] = info.SizeOfImage;
                                    }
                                }
                            }
                        }
                    }
                    finally { gch.Free(); }
                }
            }
catch { }
        }

void BuildAllProcessModuleCache()
        {
            allProcessModuleCache.Clear();
            allProcessModuleSizeCache.Clear();
            totalModuleCount = 0;
            foreach (var kv in moduleCache) { allProcessModuleCache[kv.Key] = kv.Value; }
            foreach (var kv in moduleSizeCache) { allProcessModuleSizeCache[kv.Key] = kv.Value; }
            if (hProcess != IntPtr.Zero)
            {
                try
                {
                    uint needed = 0;
                    if (EnumProcessModulesEx(hProcess, IntPtr.Zero, 0, out needed, 3) && needed > 0)
                    {
                        totalModuleCount += (int)(needed / IntPtr.Size);
                    }
                }
                catch { }
            }
            if (totalModuleCount == 0) totalModuleCount = moduleCache.Count;
            for (int pi = 0; pi < targetProcesses.Length; pi++)
            {
                if (pi == currentProcessIndex) continue;
                try
                {
                    Process cp = targetProcesses[pi];
                    if (cp.HasExited) continue;
                    IntPtr hChild = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, false, cp.Id);
                    if (hChild == IntPtr.Zero) continue;
                    try
                    {
                        uint needed = 0;
                        if (EnumProcessModulesEx(hChild, IntPtr.Zero, 0, out needed, 3) && needed > 0)
                        {
                            int modCount = (int)(needed / IntPtr.Size);
                            totalModuleCount += modCount;
                            IntPtr[] hMods = new IntPtr[modCount];
                            GCHandle gch = GCHandle.Alloc(hMods, GCHandleType.Pinned);
                            try
                            {
                                if (EnumProcessModulesEx(hChild, gch.AddrOfPinnedObject(), needed, out needed, 3))
                                {
                                    for (int mi = 0; mi < modCount; mi++)
                                    {
                                        if (hMods[mi] == IntPtr.Zero) continue;
                                        StringBuilder sb = new StringBuilder(260);
                                        GetModuleBaseName(hChild, hMods[mi], sb, 260);
                                        string mname = sb.ToString();
                                        if (!string.IsNullOrEmpty(mname) && !allProcessModuleCache.ContainsKey(mname))
                                        {
                                            MODULEINFO minfo;
                                            if (GetModuleInformation(hChild, hMods[mi], out minfo, (uint)Marshal.SizeOf(typeof(MODULEINFO))))
                                            {
                                                allProcessModuleCache[mname] = minfo.lpBaseOfDll;
                                                allProcessModuleSizeCache[mname] = minfo.SizeOfImage;
                                            }
                                        }
                                    }
                                }
                            }
                            finally { gch.Free(); }
                        }
                    }
                    finally { CloseHandle(hChild); }
                }
                catch { }
            }
        }

        IntPtr GetModuleBase(string modName)
        {
            if (string.IsNullOrEmpty(modName)) return IntPtr.Zero;
            if (moduleCache.ContainsKey(modName)) return moduleCache[modName];
            if (!modName.EndsWith(".exe", StringComparison.OrdinalIgnoreCase) &&
                !modName.EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
            {
                string withExe = modName + ".exe";
                if (moduleCache.ContainsKey(withExe)) return moduleCache[withExe];
                string withDll = modName + ".dll";
                if (moduleCache.ContainsKey(withDll)) return moduleCache[withDll];
            }
            if (modName.EndsWith(".exe", StringComparison.OrdinalIgnoreCase))
            {
                string noExe = modName.Substring(0, modName.Length - 4);
                if (moduleCache.ContainsKey(noExe)) return moduleCache[noExe];
            }
            if (modName.EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
            {
                string noDll = modName.Substring(0, modName.Length - 4);
                if (moduleCache.ContainsKey(noDll)) return moduleCache[noDll];
            }
            return IntPtr.Zero;
        }

        uint GetModuleSize(string modName)
        {
            if (string.IsNullOrEmpty(modName)) return 0;
            if (moduleSizeCache.ContainsKey(modName)) return moduleSizeCache[modName];
            if (!modName.EndsWith(".exe", StringComparison.OrdinalIgnoreCase) &&
                !modName.EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
            {
                string withExe = modName + ".exe";
                if (moduleSizeCache.ContainsKey(withExe)) return moduleSizeCache[withExe];
                string withDll = modName + ".dll";
                if (moduleSizeCache.ContainsKey(withDll)) return moduleSizeCache[withDll];
            }
            return 0;
        }

        string ResolvePointerChain(TrainerEntry entry, out long finalAddr)
        {
            finalAddr = 0;
            long baseAddr = 0;
            string diag = "";

            // ★ 数据段AOB解析路径(独立于代码段,优先级最高,找到即短路后续4级解析)
            if (!string.IsNullOrEmpty(entry.DataAOBPattern))
            {
                diag += string.Format("[数据段] 特征码: {0}, 偏移: 0x{1:X}\n", entry.DataAOBPattern, entry.DataAOBOffset);
                // 缓存有效 → 验证后直接用
                if (entry.DataSegBaseAddr != 0 && !entry.DataSegNeedsRescan)
                {
                    if (DataSegmentScanner.VerifyBaseAddr(hProcess, entry.DataSegBaseAddr, entry.DataAOBPattern))
                    {
                        baseAddr = entry.DataSegBaseAddr + entry.DataAOBOffset;
                        diag += string.Format("[数据段] 缓存有效: 0x{0:X} + 0x{1:X} = 0x{2:X}\n",
                            entry.DataSegBaseAddr, entry.DataAOBOffset, baseAddr);
                    }
                    else
                    {
                        entry.DataSegNeedsRescan = true;
                        diag += "[数据段] 缓存失效,需重扫\n";
                    }
                }
                // 缓存无效 → 全进程扫描
                if (baseAddr == 0 && entry.DataSegNeedsRescan)
                {
                    long scanned = DataSegmentScanner.Scan(hProcess, entry.DataAOBPattern);
                    if (scanned != 0)
                    {
                        entry.DataSegBaseAddr = scanned;
                        entry.DataSegNeedsRescan = false;
                        baseAddr = scanned + entry.DataAOBOffset;
                        diag += string.Format("[数据段] 扫描成功: 0x{0:X} + 0x{1:X} = 0x{2:X}\n",
                            scanned, entry.DataAOBOffset, baseAddr);
                    }
                    else
                    {
                        diag += "[数据段] 扫描失败!未找到特征码\n";
                        // ★ 扫描失败:阻止重复扫描,避免每100ms执行一次全进程扫描
                        //   游戏重启时ResetState()会将DataSegNeedsRescan重置为true
                        entry.DataSegNeedsRescan = false;
                    }
                }
                // ★ 数据段AOB路径成功:baseAddr已是最终地址(命中地址+偏移),无需后续指针链遍历
                // (原脚本设计中[dataAOB_targetPtr]+offset=目标地址,这里scanned+offset=目标地址,等价)
                // 不能走后续指针链遍历,否则会把目标地址处的数据值误当指针解引用
                if (baseAddr != 0)
                {
                    finalAddr = baseAddr;
                    diag += string.Format("[数据段] 最终地址: 0x{0:X}\n", finalAddr);
                    return diag;
                }
            }

// ★ 检查是否是alloc符号基址（如 hack+0xB → 用运行时alloc地址+偏移）
            if (!string.IsNullOrEmpty(entry.AllocSymbolName))
            {
                diag += string.Format("[指针链诊断] Alloc符号: {0}+0x{1:X}\n", entry.AllocSymbolName, entry.ModuleOffset);

                bool allocFound = false;
                for (int ei = 0; ei < entries.Length; ei++)
                {
                    if (entries[ei].AllocBlocks == null) continue;
                    for (int ai = 0; ai < entries[ei].AllocBlocks.Length; ai++)
                    {
                        if (string.Compare(entries[ei].AllocBlocks[ai].Name, entry.AllocSymbolName, true) == 0)
                        {
                            if (entries[ei].AllocBlocks[ai].NewAddr != IntPtr.Zero)
                            {
                                allocFound = true;
                                baseAddr = entries[ei].AllocBlocks[ai].NewAddr.ToInt64() + entry.ModuleOffset;
                                diag += string.Format("  → alloc块[{0}]: NewAddr=0x{1:X} + offset=0x{2:X} = baseAddr=0x{3:X}\n",
                                    entry.AllocSymbolName, entries[ei].AllocBlocks[ai].NewAddr.ToInt64(), entry.ModuleOffset, baseAddr);
                                break;
                            }
                            else
                            {
                                diag += string.Format("  → alloc块[{0}] NewAddr=0（AA脚本未激活！AAEnabled={1}）\n",
                                    entry.AllocSymbolName, entries[ei].AAEnabled);
                            }
                        }
                    }
                    if (allocFound) break;
                }
                if (!allocFound)
                {
                    diag += string.Format("  → 未找到名为[{0}]的alloc块！所有alloc块：\n", entry.AllocSymbolName);
                    for (int ei = 0; ei < entries.Length; ei++)
                    {
                        if (entries[ei].AllocBlocks != null && entries[ei].AllocBlocks.Length > 0)
                        {
                            for (int ai = 0; ai < entries[ei].AllocBlocks.Length; ai++)
                            {
                                diag += string.Format("    条目[{0}] AllocBlock: Name={1} NewAddr=0x{2:X}\n",
                                    ei, entries[ei].AllocBlocks[ai].Name, entries[ei].AllocBlocks[ai].NewAddr.ToInt64());
                            }
                        }
                    }
                }
            }

            if (baseAddr == 0 && !string.IsNullOrEmpty(entry.ModuleName))
            {
                IntPtr modBase = GetModuleBase(entry.ModuleName);
                if (modBase != IntPtr.Zero)
                {
                    baseAddr = modBase.ToInt64() + entry.ModuleOffset;
                    diag += string.Format("[指针链诊断] 模块基址: {0}=0x{1:X} + offset=0x{2:X} = baseAddr=0x{3:X}\n",
                        entry.ModuleName, modBase.ToInt64(), entry.ModuleOffset, baseAddr);
                }
else
                {
                    diag += string.Format("[指针链诊断] 模块未找到: {0}\n", entry.ModuleName);
                }
            }
            // ★ 检查是否是AOB扫描符号基址（如 INJECT+1000 → 用当前注入点地址+偏移）
            if (baseAddr == 0 && !string.IsNullOrEmpty(entry.ModuleName))
            {
                for (int ei = 0; ei < entries.Length; ei++)
                {
                    if (!entries[ei].IsAA) continue;
                    string aobSym = entries[ei].AOBSymbolName ?? "";
                    if (string.IsNullOrEmpty(aobSym))
                    {
                        var aobM = System.Text.RegularExpressions.Regex.Match(
                            entries[ei].AAScriptPreview ?? "",
                            @"aobscan(?:module)?\s*\(\s*(\w+)\s*,",
                            System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                        if (aobM.Success) aobSym = aobM.Groups[1].Value;
                    }
                    if (string.Equals(aobSym, entry.ModuleName, StringComparison.OrdinalIgnoreCase))
                    {
                        if (entries[ei].InjectAddress != IntPtr.Zero)
                        {
                            baseAddr = entries[ei].InjectAddress.ToInt64() + entry.ModuleOffset;
                            diag += string.Format("[指针链诊断] AOB符号: {0}=0x{1:X} + offset=0x{2:X} = baseAddr=0x{3:X}\n",
                                aobSym, entries[ei].InjectAddress.ToInt64(), entry.ModuleOffset, baseAddr);
                        }
                        else
                        {
                            // AOB符号存在但AA未激活，尝试直接用AOB扫描找地址
                            diag += string.Format("[指针链诊断] AOB符号{0}存在但AA未激活，InjectAddress=0\n", aobSym);
                        }
                        break;
                    }
                }
            }
            // ★ BaseResolvedAddr是CE生成时的固定地址，仅作最后回退（重启游戏后可能无效！）
            if (baseAddr == 0 && entry.BaseResolvedAddr != 0)
            {
                baseAddr = entry.BaseResolvedAddr;
                diag += string.Format("[指针链诊断] ?使用CE固定地址BaseResolvedAddr: 0x{0:X}（重启游戏后可能无效）\n", baseAddr);
            }
            if (baseAddr == 0)
            {
                diag += "[指针链诊断] 错误：无法确定基址！\n";
                diag += string.Format("  AllocSymbolName={0} ModuleName={1} BaseResolvedAddr=0x{2:X} AddrStr={3}\n",
                    entry.AllocSymbolName ?? "(null)", entry.ModuleName ?? "(null)", entry.BaseResolvedAddr, entry.AddrStr ?? "(null)");
                return diag;
            }

            long current = baseAddr;
            int ptrSize = targetIs32Bit ? 4 : 8;
            diag += string.Format("[指针链诊断] 开始遍历: baseAddr=0x{0:X}, 偏移数={1}, 指针大小={2}\n",
                baseAddr, entry.Offsets.Length, ptrSize);
            for (int i = 0; i < entry.Offsets.Length; i++)
            {
                byte[] ptrBuf = new byte[ptrSize];
                if (!ReadMem(new IntPtr(current), ptrBuf, ptrSize))
                {
                    diag += string.Format("  步骤{0}: 读取地址0x{1:X}失败！\n", i + 1, current);
                    return diag;
                }
                long ptrVal = 0;
                if (ptrSize == 4)
                    ptrVal = BitConverter.ToUInt32(ptrBuf, 0);
                else
                    ptrVal = BitConverter.ToInt64(ptrBuf, 0);
                if (ptrVal == 0)
                {
                    diag += string.Format("  步骤{0}: [0x{1:X}]=0（空指针！）\n", i + 1, current);
                    return diag;
                }
                long nextAddr = ptrVal + entry.Offsets[i];
                diag += string.Format("  步骤{0}: [0x{1:X}]=0x{2:X} + offset=0x{3:X} → 0x{4:X}\n",
                    i + 1, current, ptrVal, entry.Offsets[i], nextAddr);
                current = nextAddr;
            }
            finalAddr = current;
            diag += string.Format("[指针链诊断] 最终地址: 0x{0:X}\n", finalAddr);
            return diag;
        }

        // ★ 生成紧凑指针链显示字符串，用于UI面板红色标签
        void ResetAllAAStateAndUI()
        {
            for (int i = 0; i < entries.Length; i++)
            {
                entries[i].ResetState();
                if (panels[i] != null)
                {
                    if (entries[i].IsAA)
                    {
                        panels[i].btnToggleAA.Text = "已关闭";
                        panels[i].btnToggleAA.BackColor = Color.LightPink;
                    }
                }
            }
        }

        void ResetAllAA()
        {
            uint memProtectOld;
            for (int i = 0; i < entries.Length; i++)
            {
                TrainerEntry entry = entries[i];
                if (entry.IsAA && entry.AAEnabled)
                {
                    if (entry.InjectAddress != IntPtr.Zero && entry.OriginalCode != null)
                    {
                        if (MemoryProtector.UnprotectMemory(hProcess, entry.InjectAddress, entry.OriginalCode.Length, out memProtectOld))
                        {
                            WriteMem(entry.InjectAddress, entry.OriginalCode, entry.OriginalCode.Length);
                            MemoryProtector.ReprotectMemory(hProcess, entry.InjectAddress, entry.OriginalCode.Length, memProtectOld);
                        }
                    }
                    // ★ 释放所有alloc块（一次性分配的连续内存，只需释放一次）
                    int allocBlocksFreed = 0;
                    if (entry.AllocBlocks != null && entry.AllocBlocks.Length > 0)
                    {
                        // 只释放第一个块的NewAddr（即bigBlockAddr），其他块是同一块内存内的偏移
                        if (entry.AllocBlocks[0].NewAddr != IntPtr.Zero)
                        {
                            try { VirtualFreeEx(hProcess, entry.AllocBlocks[0].NewAddr, 0, MEM_RELEASE); } catch { }
                            allocBlocksFreed++;
                        }
                        foreach (var blk in entry.AllocBlocks)
                            blk.NewAddr = IntPtr.Zero;
                    }
                    // 旧方式释放（仅在未通过AllocBlocks释放时执行，防止Double-Free）
                    if (allocBlocksFreed == 0 && entry.AllocatedMem != IntPtr.Zero)
                    {
                        VirtualFreeEx(hProcess, entry.AllocatedMem, 0, MEM_RELEASE);
                    }
                    if (entry.ExtraAllocs != null)
                    {
                        foreach (IntPtr ea in entry.ExtraAllocs)
                        {
                            try { VirtualFreeEx(hProcess, ea, 0, MEM_RELEASE); } catch { }
                        }
                    }
                    entry.ResetState();
                }
            }
        }

        bool ConnectToProcess(int index)
        {
            if (index < 0 || index >= targetProcesses.Length) return false;
            Process target = targetProcesses[index];
            try { if (target.HasExited) return false; }
            catch { return false; }

            IntPtr h = OpenProcess(PROCESS_ALL_ACCESS, false, target.Id);
            if (h == IntPtr.Zero) return false;

            if (hProcess != IntPtr.Zero)
            {
                ResetAllAA();
                CloseHandle(hProcess);
            }
            hProcess = h;
            bRunning = true;
            currentProcessIndex = index;
            targetIs32Bit = false;
            try { IsWow64Process(hProcess, out targetIs32Bit); }
            catch { }

            BuildModuleCache();
            BuildAllProcessModuleCache();
            ResetAllAAStateAndUI();

            for (int i = 0; i < entries.Length; i++)
            {
                // ★ 数据段AOB条目:ModuleName="dataAOB_targetPtr"不是真实模块名,跳过BaseResolvedAddr更新
                //   否则GetModuleBase失败会将BaseResolvedAddr错误清零,导致数据AOB扫描失败时回退路径也无法工作
                if (!string.IsNullOrEmpty(entries[i].DataAOBPattern))
                {
                    continue;
                }
                if (!string.IsNullOrEmpty(entries[i].ModuleName))
                {
                    IntPtr modBase = GetModuleBase(entries[i].ModuleName);
                    if (modBase != IntPtr.Zero)
                    {
                        entries[i].BaseResolvedAddr = modBase.ToInt64() + entries[i].ModuleOffset;
                    }
                    else
                    {
                        entries[i].BaseResolvedAddr = 0;
                    }
                }
            }

            // ★★★ 自动激活所有AA脚本（指针链依赖alloc块的运行时地址）★★★
            //    重启游戏后，alloc块的NewAddr被重置为0
            //    指针链条目依赖AllocSymbolName→AllocBlock.NewAddr的映射
            //    所以必须先激活AA脚本，指针链才能解析到正确的运行时地址
            //    ★ OnToggleAA操作UI控件，必须通过Invoke在UI线程执行
            //    ★ 静默模式：不弹窗，避免阻塞WorkerLoop
            lastAAError = "";
            silentMode = true;
            for (int i = 0; i < entries.Length; i++)
            {
                if (entries[i].IsAA && !entries[i].AAEnabled)
                {
                    try
                    {
                        int idx = i; // 闭包捕获
                        if (this.InvokeRequired)
                            this.Invoke(new Action(() => OnToggleAA(idx)));
                        else
                            OnToggleAA(idx);
                    }
                    catch (Exception ex) { lastAAError = "自动激活异常：" + ex.Message; }
                    Thread.Sleep(100);
                }
            }
silentMode = false;
            // ★ 延迟等待：让游戏有时间执行注入点代码，确保alloc块数据已写入
            //    32位游戏某些注入点不是逐帧触发（如仅在特定事件时执行），需等待足够时间
            //    最长等待约10秒确保游戏至少触发一次注入代码
            for (int retry = 0; retry < 4; retry++) { Thread.Sleep(2500); }

            string pidHex = target.Id.ToString("X8");
            long memMB = 0;
            try { memMB = target.WorkingSet64 / (1024 * 1024); } catch { }
string diagInfo = string.Format("已连接 PID:0x{0} [{1}bit] 内存:{2}MB 模块数:{3} 进程:{4}/{5}",
                pidHex, targetIs32Bit ? "32" : "64", memMB, totalModuleCount, currentProcessIndex + 1, totalProcessCount);
            // [AOB导出] 自动激活失败不再静默：状态栏红色给出原因
            connDiagInfo = diagInfo;
            bool aaFailed = false;
            for (int i = 0; i < entries.Length; i++)
                if (entries[i].IsAA && !entries[i].AAEnabled) aaFailed = true;
            if (aaFailed)
            {
                string why = lastAAError;
                if (string.IsNullOrEmpty(why))
                    why = "AOB 未命中或注入点已被占用（CE 里的同一脚本是否仍勾选？请先完全退出 CE 再单独运行本修改器）";
                string one = why.Replace("\r", " ").Replace("\n", " ");
                if (one.Length > 150) one = one.Substring(0, 150);
                UpdateStatus("脚本自动激活失败：" + one, Color.Red);
            }
            else if (totalProcessCount > 1)
                UpdateStatus(diagInfo + "  ⚠ 检测到 " + totalProcessCount + " 个同名进程，当前连第 " + (currentProcessIndex + 1) + " 个；记录一直不刷新请点[进程切换]", Color.Orange);
            else UpdateStatus(diagInfo, Color.Green);
            return true;
        }

        // ★ 静默消息：自动激活模式下不弹窗，避免阻塞WorkerLoop
        void ShowMsg(string text, string caption, MessageBoxButtons buttons, MessageBoxIcon icon)
        {
            if (!silentMode)
                MessageBox.Show(text, caption, buttons, icon);
            else
                lastAAError = "[" + caption + "] " + text;   // [AOB导出] 静默期留痕，别让用户只看到"解析失败"
        }

        void OnToggleAA(int idx)
        {
            uint memProtectOld;
            if (idx < 0 || idx >= entries.Length) return;
            TrainerEntry entry = entries[idx];
            if (!entry.IsAA) return;
            // [AOB导出] CE 对含 '-' 等字符的模块名会返回带引号的名字，先剥掉再比对，
            // 否则 string.Equals(me.szModule, AOBModule) 全部失配，模块范围扫描不执行。
            if (!string.IsNullOrEmpty(entry.AOBModule))
                entry.AOBModule = entry.AOBModule.Trim().Trim('"');

            if (hProcess == IntPtr.Zero || !bRunning)
            {
                ShowMsg("未连接到游戏进程，请先启动修改器！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }

            if (entry.AAEnabled)
            {
                if (entry.InjectAddress != IntPtr.Zero && entry.OriginalCode != null)
                {
                    if (MemoryProtector.UnprotectMemory(hProcess, entry.InjectAddress, entry.OriginalCode.Length, out memProtectOld))
                    {
                        WriteMem(entry.InjectAddress, entry.OriginalCode, entry.OriginalCode.Length);
                        MemoryProtector.ReprotectMemory(hProcess, entry.InjectAddress, entry.OriginalCode.Length, memProtectOld);
                    }
                }
                // ★ 释放所有alloc块（新方式）
                int allocBlocksFreed = 0;
                if (entry.AllocBlocks != null && entry.AllocBlocks.Length > 0)
                {
                    // 只释放第一个块的NewAddr（即bigBlockAddr），其他块是同一块内存内的偏移
                    if (entry.AllocBlocks[0].NewAddr != IntPtr.Zero)
                    {
                        try { VirtualFreeEx(hProcess, entry.AllocBlocks[0].NewAddr, 0, MEM_RELEASE); } catch { }
                        allocBlocksFreed++;
                    }
                    foreach (var blk in entry.AllocBlocks)
                        blk.NewAddr = IntPtr.Zero;
                }
                // 旧方式释放（仅在未通过AllocBlocks释放时执行，防止Double-Free）
                if (allocBlocksFreed == 0 && entry.AllocatedMem != IntPtr.Zero)
                {
                    VirtualFreeEx(hProcess, entry.AllocatedMem, 0, MEM_RELEASE);
                }
                if (entry.ExtraAllocs != null)
                {
                    foreach (IntPtr ea in entry.ExtraAllocs)
                    {
                        try { VirtualFreeEx(hProcess, ea, 0, MEM_RELEASE); } catch { }
                    }
                }
                entry.ResetState();
                if (panels[idx] != null)
                {
                    panels[idx].btnToggleAA.Text = "已关闭";
                    panels[idx].btnToggleAA.BackColor = Color.LightPink;
                    panels[idx].lblCurrent.Text = "已还原原始指令";
                    panels[idx].lblCurrent.ForeColor = Color.Gray;
                }
                return;
            }

            if (string.IsNullOrEmpty(entry.AOBPattern))
            {
                ShowMsg(string.Format("该AA脚本无AOB特征码！\n模块: [{0}]\n脚本前100字: [{1}]",
                    entry.AOBModule,
                    entry.AAScriptPreview ?? "(null)"),
                    "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                return;
            }

            // 检查是否手动输入了注入地址
            IntPtr injectAddr = IntPtr.Zero;
            {
                List<long> moduleBases = new List<long>();
                List<uint> moduleSizes = new List<uint>();
                int pid = 0;
                try { pid = targetProcesses[currentProcessIndex].Id; } catch { }
                if (pid != 0)
                {
                    try
                    {
                        IntPtr hSnap = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32, (uint)pid);
                        if (hSnap != IntPtr.Zero && hSnap != new IntPtr(-1))
                        {
                            MODULEENTRY32 me = new MODULEENTRY32();
                            me.dwSize = (uint)Marshal.SizeOf(typeof(MODULEENTRY32));
                            if (Module32First(hSnap, ref me))
                            {
                                do
                                {
                                    if (string.Equals(me.szModule, entry.AOBModule, StringComparison.OrdinalIgnoreCase) ||
                                        string.Equals(me.szModule, entry.AOBModule + ".dll", StringComparison.OrdinalIgnoreCase) ||
                                        string.Equals(me.szModule, entry.AOBModule + ".exe", StringComparison.OrdinalIgnoreCase))
                                    {
                                        moduleBases.Add(me.modBaseAddr.ToInt64());
                                        moduleSizes.Add(me.modBaseSize);
                                    }
                                    me.dwSize = (uint)Marshal.SizeOf(typeof(MODULEENTRY32));
                                } while (Module32Next(hSnap, ref me));
                            }
                            CloseHandle(hSnap);
                        }
                    }
catch { }
                }
// ★ 单进程回退：用EnumProcessModulesEx搜索当前进程的模块
                if (moduleBases.Count == 0 && hProcess != IntPtr.Zero)
                {
                    try
                    {
                        uint needed = 0;
                        if (EnumProcessModulesEx(hProcess, IntPtr.Zero, 0, out needed, 3) && needed > 0)
                        {
                            int modCount = (int)(needed / IntPtr.Size);
                            IntPtr[] hMods = new IntPtr[modCount];
                            GCHandle gch = GCHandle.Alloc(hMods, GCHandleType.Pinned);
                            try
                            {
                                if (EnumProcessModulesEx(hProcess, gch.AddrOfPinnedObject(), needed, out needed, 3))
                                {
                                    modCount = (int)(needed / IntPtr.Size);
                                    for (int mi = 0; mi < modCount; mi++)
                                    {
                                        if (hMods[mi] == IntPtr.Zero) continue;
                                        StringBuilder sb = new StringBuilder(260);
                                        GetModuleBaseName(hProcess, hMods[mi], sb, 260);
                                        string mname = sb.ToString();
                                        if (string.Equals(mname, entry.AOBModule, StringComparison.OrdinalIgnoreCase) ||
                                            string.Equals(mname, entry.AOBModule + ".dll", StringComparison.OrdinalIgnoreCase) ||
                                            string.Equals(mname, entry.AOBModule + ".exe", StringComparison.OrdinalIgnoreCase))
                                        {
                                            MODULEINFO minfo;
                                            if (GetModuleInformation(hProcess, hMods[mi], out minfo, (uint)Marshal.SizeOf(typeof(MODULEINFO))))
                                            {
                                                long modBase = minfo.lpBaseOfDll.ToInt64();
                                                bool alreadyHave = false;
                                                foreach (long b in moduleBases) { if (b == modBase) { alreadyHave = true; break; } }
                                                if (!alreadyHave) { moduleBases.Add(modBase); moduleSizes.Add(minfo.SizeOfImage); }
                                            }
                                        }
                                    }
                                }
                            }
                            finally { gch.Free(); }
                        }
                    }
                    catch { }
                }
// ★ 最终回退：从moduleCache查找模块基址
                if (moduleBases.Count == 0)
                {
                    IntPtr modBase = GetModuleBase(entry.AOBModule);
                    if (modBase != IntPtr.Zero)
                    {
                        moduleBases.Add(modBase.ToInt64());
                        uint modSize = GetModuleSize(entry.AOBModule);
                        if (modSize == 0) modSize = 0x10000000;
                        moduleSizes.Add(modSize);
                    }
                }
// ★ 多子进程：用EnumProcessModulesEx搜索所有子进程的模块
                if (targetProcesses.Length > 1)
                {
                    for (int pi = 0; pi < targetProcesses.Length; pi++)
                    {
                        if (pi == currentProcessIndex) continue;
                        try
                        {
                            Process cp = targetProcesses[pi];
                            if (cp.HasExited) continue;
                            IntPtr hChild = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, false, cp.Id);
                            if (hChild == IntPtr.Zero) continue;
                            try
                            {
                                uint needed = 0;
                                if (EnumProcessModulesEx(hChild, IntPtr.Zero, 0, out needed, 3) && needed > 0)
                                {
                                    int modCount = (int)(needed / IntPtr.Size);
                                    IntPtr[] hMods = new IntPtr[modCount];
                                    GCHandle gch = GCHandle.Alloc(hMods, GCHandleType.Pinned);
                                    try
                                    {
                                        if (EnumProcessModulesEx(hChild, gch.AddrOfPinnedObject(), needed, out needed, 3))
                                        {
                                            modCount = (int)(needed / IntPtr.Size);
                                            for (int mi = 0; mi < modCount; mi++)
                                            {
                                                if (hMods[mi] == IntPtr.Zero) continue;
                                                StringBuilder sb = new StringBuilder(260);
                                                GetModuleBaseName(hChild, hMods[mi], sb, 260);
                                                string mname = sb.ToString();
                                                if (string.Equals(mname, entry.AOBModule, StringComparison.OrdinalIgnoreCase) ||
                                                    string.Equals(mname, entry.AOBModule + ".dll", StringComparison.OrdinalIgnoreCase) ||
                                                    string.Equals(mname, entry.AOBModule + ".exe", StringComparison.OrdinalIgnoreCase))
                                                {
                                                    MODULEINFO minfo;
                                                    if (GetModuleInformation(hChild, hMods[mi], out minfo, (uint)Marshal.SizeOf(typeof(MODULEINFO))))
                                                    {
                                                        long childBase = minfo.lpBaseOfDll.ToInt64();
                                                        bool alreadyHave = false;
                                                        foreach (long b in moduleBases) { if (b == childBase) { alreadyHave = true; break; } }
                                                        if (!alreadyHave) { moduleBases.Add(childBase); moduleSizes.Add(minfo.SizeOfImage); }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    finally { gch.Free(); }
                                }
                            }
                            finally { CloseHandle(hChild); }
                        }
                        catch { }
                    }
                }

if (moduleBases.Count == 0)
                {
                    ShowMsg(string.Format("无法定位模块：{0}\n模块缓存数：{1}", entry.AOBModule, moduleCache.Count), "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    return;
                }

                // === 第1步：解析AOB特征码 ===
                List<IntPtr> allMatches = new List<IntPtr>();
                while (entry.AOBPattern.Contains("  ")) entry.AOBPattern = entry.AOBPattern.Replace("  ", " ");
                string[] patParts = entry.AOBPattern.Trim().Split(new char[]{' '}, StringSplitOptions.RemoveEmptyEntries);
                byte[] pBytes = new byte[patParts.Length];
                bool[] pMask = new bool[patParts.Length];
                int validBytes = 0;
                for (int pi = 0; pi < patParts.Length; pi++)
                {
                    string part = patParts[pi].Trim();
                    if (part.Contains("?"))
                    {
                        pBytes[pi] = 0; pMask[pi] = false;
                    }
                    else
                    {
                        try { pBytes[pi] = Convert.ToByte(part, 16); pMask[pi] = true; validBytes++; }
                        catch { pBytes[pi] = 0; pMask[pi] = false; }
                    }
                }
                int pLen = patParts.Length;
                if (pLen == 0 || validBytes == 0)
                {
                    string parsedInfo = "";
                    for (int pi = 0; pi < patParts.Length; pi++)
                        parsedInfo += string.Format("[{0}]={1}(mask={2}) ", patParts[pi], pBytes[pi], pMask[pi]);
                    ShowMsg(string.Format("AOB特征码无效！\n原始模式: [{0}]\n分段数: {1}\n有效字节数: {2}\n解析详情: {3}\n\n特征码格式示例: 48 8B 05 ?? ?? ?? ??",
                        entry.AOBPattern, pLen, validBytes, parsedInfo),
                        "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    return;
                }

                // === 第2步：在模块范围内AOB扫描 ===
                byte[] scanBuf = new byte[65536];
                for (int mi = 0; mi < moduleBases.Count; mi++)
                {
                    long scanFrom = moduleBases[mi];
                    long scanTo = scanFrom + moduleSizes[mi];
                    // [AOB导出] aobscanregion：把扫描收窄到 模块基址+起止偏移 的小范围
                    if (entry.RegionEndOff > entry.RegionStartOff)
                    {
                        scanFrom = moduleBases[mi] + entry.RegionStartOff;
                        scanTo   = moduleBases[mi] + entry.RegionEndOff;
                    }
                    long sPos = scanFrom;
                    while (sPos + pLen <= scanTo)
                    {
                        int toRead = (int)Math.Min(scanBuf.Length, scanTo - sPos);
                        if (toRead < pLen) break;
                        int sRead;
                        if (!ReadProcessMemory(hProcess, new IntPtr(sPos), scanBuf, (uint)toRead, out sRead) || sRead < pLen)
                        {
                            sPos += 4096;
                            continue;
                        }
                        for (int si = 0; si <= sRead - pLen; si++)
                        {
                            bool ok = true;
                            for (int sj = 0; sj < pLen; sj++)
                            {
                                if (pMask[sj] && scanBuf[si + sj] != pBytes[sj]) { ok = false; break; }
                            }
                            if (ok)
                            {
                                allMatches.Add(new IntPtr(sPos + si));
                                if (allMatches.Count >= 64) break;
                            }
                        }
                        if (allMatches.Count >= 64) break;
                        sPos += sRead - pLen + 1;
                    }
                }

                // === 第3步：如果模块范围内未找到，使用VirtualQueryEx扫描全进程内存 ===
                if (allMatches.Count == 0)
                {
                    long queryAddr = 0x10000;
                    MEMORY_BASIC_INFORMATION_EX mbi2;
                    while (VirtualQueryEx(hProcess, new IntPtr(queryAddr), out mbi2, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION_EX))) != IntPtr.Zero)
                    {
                        if (mbi2.State == 0x1000 && (mbi2.Protect & 0x101) == 0)
                        {
                            long regionBase = mbi2.BaseAddress.ToInt64();
                            long regionSize = (long)mbi2.RegionSize;
                            if (regionSize > 0 && regionSize <= 512 * 1024 * 1024)
                            {
                                long sPos = regionBase;
                                long sEnd = regionBase + regionSize;
                                while (sPos + pLen <= sEnd)
                                {
                                    int toRead = (int)Math.Min(scanBuf.Length, sEnd - sPos);
                                    if (toRead < pLen) break;
                                    int sRead;
                                    if (!ReadProcessMemory(hProcess, new IntPtr(sPos), scanBuf, (uint)toRead, out sRead) || sRead < pLen)
                                    {
                                        sPos += 4096;
                                        continue;
                                    }
                                    for (int si = 0; si <= sRead - pLen; si++)
                                    {
                                        bool ok = true;
                                        for (int sj = 0; sj < pLen; sj++)
                                        {
                                            if (pMask[sj] && scanBuf[si + sj] != pBytes[sj]) { ok = false; break; }
                                        }
                                        if (ok)
                                        {
                                            allMatches.Add(new IntPtr(sPos + si));
                                            if (allMatches.Count >= 64) break;
                                        }
                                    }
                                    if (allMatches.Count >= 64) break;
                                    sPos += sRead - pLen + 1;
                                }
                            }
                        }
                        long nextAddr = mbi2.BaseAddress.ToInt64() + (long)mbi2.RegionSize;
                        if (nextAddr <= queryAddr) break;
                        queryAddr = nextAddr;
                    }
                }

                // === 第4步：结果处理 ===
                string diag = string.Format("=== AOB扫描结果 ===\n模块: {0}\n特征码: [{1}]\n模块实例数: {2}\n匹配总数: {3}\n\n",
                    entry.AOBModule, entry.AOBPattern, moduleBases.Count, allMatches.Count);
                for (int mbi = 0; mbi < moduleBases.Count; mbi++)
                {
                    diag += string.Format("模块实例{0}: 基址=0x{1:X} 大小=0x{2:X}\n", mbi + 1, moduleBases[mbi], moduleSizes[mbi]);
                }
                diag += "\n";
                for (int mi = 0; mi < Math.Min(allMatches.Count, 10); mi++)
                {
                    byte[] actual = new byte[Math.Min(pLen, 16)];
                    ReadMem(allMatches[mi], actual, actual.Length);
                    string hex = "";
                    for (int hi = 0; hi < actual.Length; hi++) hex += actual[hi].ToString("X2") + " ";
                    diag += string.Format("匹配[{0}]: 0x{1:X} = {2}\n", mi + 1, allMatches[mi].ToInt64(), hex.Trim());
                }

                if (allMatches.Count == 0)
                {
                    diag += "\n模块范围内和全进程内存均未找到该特征码！\n请确认游戏已加载目标模块，或手动输入注入地址。";
                    ShowMsg(diag, "AOB扫描失败", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    return;
                }

if (allMatches.Count == 1)
                {
                    injectAddr = allMatches[0];
                    diag += string.Format("\n使用匹配地址: 0x{0:X}", injectAddr.ToInt64());
                }
                else if (silentMode)
                {
                    // 静默自动激活时多个匹配，取首个（主进程模块优先）
                    injectAddr = allMatches[0];
                    diag += string.Format("\n多个匹配({0}个)，静默模式使用首个: 0x{1:X}", allMatches.Count, injectAddr.ToInt64());
                }
                else
                {
                    // 多个匹配，弹窗选择
                    Form selForm = new Form();
                    selForm.Text = "发现" + allMatches.Count + "个AOB匹配，请选择正确的注入地址";
                    selForm.Width = 520;
                    selForm.Height = 60 + Math.Min(allMatches.Count, 15) * 28 + 50;
                    selForm.StartPosition = FormStartPosition.CenterParent;
                    selForm.FormBorderStyle = FormBorderStyle.FixedDialog;
                    selForm.MaximizeBox = false; selForm.MinimizeBox = false; selForm.ShowInTaskbar = false;
                    ListBox selList = new ListBox();
                    selList.Left = 10; selList.Top = 10; selList.Width = 480;
                    selList.Height = Math.Min(allMatches.Count, 15) * 24;
                    for (int mi = 0; mi < allMatches.Count; mi++)
                    {
                        byte[] showB = new byte[Math.Min(pLen, 16)];
                        ReadMem(allMatches[mi], showB, showB.Length);
                        string hexShow = "";
                        for (int hi = 0; hi < showB.Length; hi++) hexShow += showB[hi].ToString("X2") + " ";
                        selList.Items.Add(string.Format("[{0}] 0x{1:X} = {2}", mi + 1, allMatches[mi].ToInt64(), hexShow.Trim()));
                    }
                    selList.SelectedIndex = 0;
                    selForm.Controls.Add(selList);
                    IntPtr selectedAddr = IntPtr.Zero;
                    Button selBtn = new Button();
                    selBtn.Text = "确定";
                    selBtn.Left = 210; selBtn.Top = selList.Top + selList.Height + 8;
                    selBtn.Width = 80; selBtn.Height = 28;
                    selBtn.Click += (s, e2) => {
                        if (selList.SelectedIndex >= 0 && selList.SelectedIndex < allMatches.Count)
                            selectedAddr = allMatches[selList.SelectedIndex];
                        selForm.Close();
                    };
                    selForm.Controls.Add(selBtn);
                    selForm.ShowDialog(this);
                    if (selectedAddr == IntPtr.Zero) return;
                    injectAddr = selectedAddr;
                    diag += string.Format("\n用户选择注入地址: 0x{0:X}", injectAddr.ToInt64());
                }
                ShowMsg(diag, "AOB扫描完成", MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
            entry.InjectAddress = injectAddr;

            int origInstrLen = entry.OrigInstrLen; // 实际原始指令长度
            int codeLen = Math.Max(origInstrLen, 5); // JMP补丁大小(至少5字节)
            byte[] originalCodeAtInject = new byte[codeLen]; // 读取完整patch用于还原
            if (!ReadMem(injectAddr, originalCodeAtInject, codeLen))
            {
                ShowMsg("读取原始代码失败！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                entry.ResetState();
                return;
            }
            // ★ 检查注入点是否已被其他程序Hook（首字节为E9表示已有JMP）
            if (originalCodeAtInject[0] == 0xE9)
            {
                ShowMsg(string.Format("注入点 0x{0:X} 已存在JMP指令！\n该地址可能已被CE或其他程序Hook。\n请先在CE中关闭该脚本，再使用修改器。", injectAddr.ToInt64()),
                    "警告", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                entry.ResetState();
                return;
            }
            entry.OriginalCode = originalCodeAtInject; // 保存完整codeLen字节用于还原

            // ★★★ 核心注入逻辑 ★★★
            byte[] customCode = entry.CustomCodeBytes;
            List<IntPtr> extraAllocs = new List<IntPtr>();
            IntPtr allocAddr = IntPtr.Zero;
            uint allocSize = 0;
            int customLen = 0;

            // ★ 模式检测：直接字节补丁（无alloc脚本）——直接写入注入地址，不创建代码洞
            if (!entry.IsAllocScript && entry.DirectPatchBytes != null && entry.DirectPatchBytes.Length > 0)
            {
                // 直接将补丁字节写入注入地址（类似CE中直接写db字节）
                if (!MemoryProtector.UnprotectMemory(hProcess, injectAddr, entry.DirectPatchBytes.Length, out memProtectOld))
                {
                    ShowMsg("无法解锁内存保护以写入补丁字节！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    entry.ResetState();
                    return;
                }
                if (!WriteMem(injectAddr, entry.DirectPatchBytes, entry.DirectPatchBytes.Length))
                {
                    MemoryProtector.ReprotectMemory(hProcess, injectAddr, entry.DirectPatchBytes.Length, memProtectOld);
                    ShowMsg("写入补丁字节失败！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    entry.ResetState();
                    return;
                }
                MemoryProtector.ReprotectMemory(hProcess, injectAddr, entry.DirectPatchBytes.Length, memProtectOld);
                entry.AAEnabled = true;
                if (panels[idx] != null)
                {
                    panels[idx].btnToggleAA.Text = "已开启";
                    panels[idx].btnToggleAA.BackColor = Color.LightGreen;
                    panels[idx].btnToggleAA.Enabled = false;
                }
                return;
            }

            // ★ 优先路径：使用CE预汇编的所有alloc块（最可靠，支持所有CE指令）
            if (entry.AllocBlocks != null && entry.AllocBlocks.Length > 0)
            {
                // ★ 步骤1：计算所有alloc块的总大小，一次性分配连续内存
                //    【关键】CE中多个alloc块是连续排列的，必须保持和CE相同的布局！
                //    例如CE中 alloc(hack,2048) 在 0x052F0000，alloc(hack2,2048) 在 0x052F0800
                //    hack2在hack+0x800处，所以运行时也必须保持相同偏移关系
                //    因此必须一次性分配所有块的总大小，然后按CE的布局偏移划分
                long injectBase = injectAddr.ToInt64();

                // ★ 计算所有alloc块在CE中的布局范围
                long ceBaseAddr = long.MaxValue;
                long ceEndAddr = 0;
                for (int bi = 0; bi < entry.AllocBlocks.Length; bi++)
                {
                    if (entry.AllocBlocks[bi].OrigAddr < ceBaseAddr)
                        ceBaseAddr = entry.AllocBlocks[bi].OrigAddr;
                    long blkEnd = entry.AllocBlocks[bi].OrigAddr + entry.AllocBlocks[bi].Size;
                    if (blkEnd > ceEndAddr) ceEndAddr = blkEnd;
                }
                uint totalAllocSize = (uint)(ceEndAddr - ceBaseAddr);
                // 页对齐
                totalAllocSize = (uint)(((long)totalAllocSize + 4095) & ~4095L);
                if (totalAllocSize < 4096) totalAllocSize = 4096;

                // ★★★ 在注入点附近分配一块连续内存 ★★★
                // ★ 用VirtualQueryEx扫描注入点附近内存，找到空闲区域精确分配
                //    比逐页尝试VirtualAllocEx更高效可靠
                IntPtr bigBlockAddr = IntPtr.Zero;
                {
                    long avoidStart = entry.LastAllocStart;
                    long avoidEnd = entry.LastAllocStart + entry.LastAllocSize;
                    // 先直接尝试在注入点所在64KB页分配
                    ulong preferredBase = (ulong)injectBase & ~(0x10000UL - 1);
                    if (preferredBase > 0x10000)
                    {
                        ulong tryBase = preferredBase;
                        if (avoidEnd > 0 && tryBase >= (ulong)avoidStart && tryBase < (ulong)avoidEnd)
                            tryBase = (ulong)avoidEnd & ~(0xFFFFUL);
                        if (tryBase > 0x10000)
                            bigBlockAddr = VirtualAllocEx(hProcess, new IntPtr((long)tryBase), totalAllocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                    }
                    
                    // 如果直接分配失败，用VirtualQueryEx扫描注入点附近寻找空闲区域
                    if (bigBlockAddr == IntPtr.Zero)
                    {
                        const uint MEM_FREE = 0x10000;
                        long rangeLimit = 0x7FFF0000L; // ±2GB
                        // 向上扫描
                        long scanUp = (long)preferredBase;
                        long scanDown = (long)preferredBase;
                        bool upDone = false, downDone = false;
                        
                        while (!upDone || !downDone)
                        {
                            // 向上扫描
                            if (!upDone)
                            {
                                MEMORY_BASIC_INFORMATION_EX mbi;
                                if (VirtualQueryEx(hProcess, new IntPtr(scanUp), out mbi, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION_EX))) != IntPtr.Zero)
                                {
                                    long regionStart = mbi.BaseAddress.ToInt64();
                                    long regionEnd = regionStart + mbi.RegionSize.ToInt64();
                                    
                                    if (mbi.State == MEM_FREE && mbi.RegionSize.ToInt64() >= totalAllocSize)
                                    {
                                        ulong tryAddr = (ulong)regionStart;
                                        tryAddr = (tryAddr + 0xFFFFUL) & ~(0xFFFFUL); // 64KB对齐
                                        if (avoidEnd > 0 && (long)tryAddr >= avoidStart && (long)tryAddr < avoidEnd)
                                            tryAddr = ((ulong)avoidEnd + 0xFFFFUL) & ~(0xFFFFUL);
                                        if (tryAddr + totalAllocSize <= (ulong)regionEnd)
                                        {
                                            bigBlockAddr = VirtualAllocEx(hProcess, new IntPtr((long)tryAddr), totalAllocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                                            if (bigBlockAddr != IntPtr.Zero) break;
                                        }
                                    }
                                    scanUp = regionEnd;
                                    if (scanUp - (long)preferredBase > rangeLimit) upDone = true;
                                }
                                else upDone = true;
                            }
                            // 向下扫描
                            if (!downDone && bigBlockAddr == IntPtr.Zero)
                            {
                                long downScan = scanDown - 0x10000;
                                if (downScan >= 0x10000 && (long)preferredBase - downScan <= rangeLimit)
                                {
                                    MEMORY_BASIC_INFORMATION_EX mbi;
                                    if (VirtualQueryEx(hProcess, new IntPtr(downScan), out mbi, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION_EX))) != IntPtr.Zero)
                                    {
                                        long regionStart = mbi.BaseAddress.ToInt64();
                                        long regionEnd = regionStart + mbi.RegionSize.ToInt64();
                                        
                                        if (mbi.State == MEM_FREE && mbi.RegionSize.ToInt64() >= totalAllocSize)
                                        {
                                            ulong tryAddr = (ulong)regionStart;
                                            tryAddr = (tryAddr + 0xFFFFUL) & ~(0xFFFFUL); // 64KB对齐
                                            if (avoidEnd > 0 && (long)tryAddr >= avoidStart && (long)tryAddr < avoidEnd)
                                                continue;
                                            if (tryAddr + totalAllocSize <= (ulong)regionEnd)
                                            {
                                                bigBlockAddr = VirtualAllocEx(hProcess, new IntPtr((long)tryAddr), totalAllocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                                                if (bigBlockAddr != IntPtr.Zero) break;
                                            }
                                        }
                                        scanDown = regionStart;
                                    }
                                    else downDone = true;
                                }
                                else downDone = true;
                            }
                        }
                    }
                    // 最终回退
                    if (bigBlockAddr == IntPtr.Zero)
                        bigBlockAddr = VirtualAllocEx(hProcess, IntPtr.Zero, totalAllocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                }

                if (bigBlockAddr == IntPtr.Zero)
                {
                    ShowMsg(string.Format("远程内存分配失败！总大小: {0} 字节", totalAllocSize), "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    entry.ResetState();
                    return;
                }

                // ★ 按CE布局偏移设置每个alloc块的NewAddr
                for (int bi = 0; bi < entry.AllocBlocks.Length; bi++)
                {
                    AllocBlock blk = entry.AllocBlocks[bi];
                    long offsetInBigBlock = blk.OrigAddr - ceBaseAddr;
                    blk.NewAddr = new IntPtr(bigBlockAddr.ToInt64() + offsetInBigBlock);
                    if (bi == 0) { allocAddr = blk.NewAddr; allocSize = totalAllocSize; }
                    else { extraAllocs.Add(blk.NewAddr); }
                }
                // ★ 验证：hack块的NewAddr必须等于bigBlockAddr+偏移（即代码洞内的正确位置）
                //    如果hack.NewAddr不等于bigBlockAddr + (hack.OrigAddr - ceBaseAddr)，指针链就会指向错误地址
                // 只需释放一次bigBlockAddr
                allocAddr = entry.AllocBlocks[0].NewAddr;
                allocSize = totalAllocSize;
                entry.LastAllocStart = bigBlockAddr.ToInt64();
                entry.LastAllocSize = totalAllocSize;
                // 清空extraAllocs，因为我们只分配了一块大内存
                extraAllocs.Clear();

                // ★ 步骤2：复制每个alloc块的字节并进行重定位
                long returnTarget = injectAddr.ToInt64() + codeLen;

                for (int bi = 0; bi < entry.AllocBlocks.Length; bi++)
                {
                    AllocBlock blk = entry.AllocBlocks[bi];
                    byte[] data = new byte[blk.Bytes.Length];
                    Array.Copy(blk.Bytes, data, data.Length);
                    long blkOrigAddr = blk.OrigAddr;
                    long blkNewAddr = blk.NewAddr.ToInt64();

                    if (!string.IsNullOrEmpty(entry.RipFixups))
                    {
                        string[] fixupList = entry.RipFixups.Split(new char[]{'|'}, StringSplitOptions.RemoveEmptyEntries);
                        foreach (string f in fixupList)
                        {
                            string[] parts = f.Split(':');
                            int fBi = int.Parse(parts[0]) - 1;
                            if (fBi != bi) continue;
                            int fOff = int.Parse(parts[1]);
                            int fLen = int.Parse(parts[2]);
                            string fType = parts[3];
                            string absStr = parts[4].StartsWith("0x") ? parts[4].Substring(2) : parts[4];
                            long absTarget = long.Parse(absStr, System.Globalization.NumberStyles.HexNumber);

long newTarget;
                            bool remappedByAlloc = false;

if (fType == "ri")
                            {
                                newTarget = injectAddr.ToInt64() + absTarget;
                            }
                            else if (fType == "d")
                            {
                                newTarget = absTarget;
                                if (entry.AllocBlocks != null)
                                {
                                    for (int bj = 0; bj < entry.AllocBlocks.Length; bj++)
                                    {
                                        AllocBlock tBlk = entry.AllocBlocks[bj];
                                        if (absTarget >= tBlk.OrigAddr && absTarget <= tBlk.OrigAddr + tBlk.Size)
                                        {
                                            newTarget = tBlk.NewAddr.ToInt64() + (absTarget - tBlk.OrigAddr);
                                            break;
                                        }
                                    }
                                }
                                // ★ ASLR修复：数据fixup也支持模块名+偏移重定位
                                if (parts.Length >= 7 && newTarget == absTarget)
                                {
                                    string dModName = parts[5];
                                    if (parts.Length > 7)
                                    {
                                        for (int pj = 6; pj < parts.Length - 1; pj++)
                                            dModName += ":" + parts[pj];
                                    }
                                    long dModOff = long.Parse(parts[parts.Length - 1], System.Globalization.NumberStyles.HexNumber);
                                    IntPtr dModBase = GetModuleBase(dModName);
                                    if (dModBase != IntPtr.Zero)
                                    {
                                        newTarget = dModBase.ToInt64() + dModOff;
                                    }
                                }
                                uint dVal = (uint)newTarget;
                                data[fOff] = (byte)(dVal & 0xFF);
                                data[fOff + 1] = (byte)((dVal >> 8) & 0xFF);
                                data[fOff + 2] = (byte)((dVal >> 16) & 0xFF);
                                data[fOff + 3] = (byte)((dVal >> 24) & 0xFF);
                                continue;
                            }
                            else
{
                                newTarget = absTarget;

                                if (entry.AllocBlocks != null)
                                {
                                    for (int bj = 0; bj < entry.AllocBlocks.Length; bj++)
                                    {
                                        AllocBlock tBlk = entry.AllocBlocks[bj];
                                        long effectiveSize = ((tBlk.Size + 4095) / 4096) * 4096;
                                        if (absTarget >= tBlk.OrigAddr && absTarget <= tBlk.OrigAddr + effectiveSize)
                                        {
                                            newTarget = tBlk.NewAddr.ToInt64() + (absTarget - tBlk.OrigAddr);
                                            remappedByAlloc = true;
                                            break;
                                        }
                                    }
}
                            }

                            // ★ ASLR修复：绝对地址未命中alloc块时，通过模块名+偏移重定位（32位和64位均支持）
                            if (parts.Length >= 7 && !remappedByAlloc)
                            {
                                string fixupModName = parts[5];
                                // 模块名可能包含冒号（极少数情况），故取parts[5..n-2]重建
                                if (parts.Length > 7)
                                {
                                    for (int pj = 6; pj < parts.Length - 1; pj++)
                                        fixupModName += ":" + parts[pj];
                                }
                                long fixupModOff = long.Parse(parts[parts.Length - 1], System.Globalization.NumberStyles.HexNumber);
                                IntPtr curModBase = GetModuleBase(fixupModName);
                                if (curModBase != IntPtr.Zero)
                                {
                                    newTarget = curModBase.ToInt64() + fixupModOff;
                                }
                            }

                            int relStart;
                            if (fType == "a" && fLen == 5 && (data[fOff] == 0xA1 || data[fOff] == 0xA3))
                            {
                                relStart = fOff + 1;
                            }
                            else if (fType == "a" || ((fType == "r" || fType == "ri") && fLen != 5 && !(fLen == 6 && data[fOff] == 0x0F)))
                            {
int modRMIdx = fOff + 1;
                                if (!targetIs32Bit && data[fOff] >= 0x40 && data[fOff] <= 0x4F) modRMIdx = fOff + 2;
                                relStart = modRMIdx + 1;
                            }
                            else
                            {
                                relStart = fOff + (fLen - 4);
                            }
                            if (relStart >= 0 && relStart + 3 < data.Length)
                            {
bool opcodeValid = false;
                                if (fLen == 5 && (data[fOff] == 0xE9 || data[fOff] == 0xE8)) opcodeValid = true;
                                else if (fLen == 5 && (data[fOff] == 0xA1 || data[fOff] == 0xA3)) opcodeValid = true;
                                else if (fLen == 6 && data[fOff] == 0x0F && data[fOff + 1] >= 0x80 && data[fOff + 1] <= 0x8F) opcodeValid = true;
                                else if (fLen == 2 && (data[fOff] == 0xEB || (data[fOff] >= 0x70 && data[fOff] <= 0x7F))) opcodeValid = true;
                                else if ((fType == "a" || fType == "ri" || fType == "r") && fLen >= 6)
                                {
                                    int modRMIdx = fOff + 1;
                                    if (!targetIs32Bit && data[fOff] >= 0x40 && data[fOff] <= 0x4F) modRMIdx = fOff + 2;
                                    if (modRMIdx < data.Length) { byte m = data[modRMIdx]; if (((m >> 6) & 3) == 0 && (m & 7) == 5) opcodeValid = true; }
                                }
                                if (!opcodeValid) continue;
                                if (fType == "sr")
                                {
                                    // 短跳转(EB/7x): 块内相对偏移不变，无需重定位
                                    // 仅验证目标仍在同一alloc块内
                                    continue;
                                }
                                else if (fType == "a")
                                {
                                    uint val = (uint)newTarget;
                                    data[relStart] = (byte)(val & 0xFF);
                                    data[relStart + 1] = (byte)((val >> 8) & 0xFF);
                                    data[relStart + 2] = (byte)((val >> 16) & 0xFF);
                                    data[relStart + 3] = (byte)((val >> 24) & 0xFF);
                                }
                                else
                                {
                                    long newInstrEnd = blkNewAddr + fOff + fLen;
                                    int newRel = (int)(newTarget - newInstrEnd);
                                    data[relStart] = (byte)(newRel & 0xFF);
                                    data[relStart + 1] = (byte)((newRel >> 8) & 0xFF);
                                    data[relStart + 2] = (byte)((newRel >> 16) & 0xFF);
                                    data[relStart + 3] = (byte)((newRel >> 24) & 0xFF);
                                }
                            }
                        }
                    }

// ★ 2c. 纯数据块清零：hack等无指令fixup的数据块由运行时代码写入
                    bool hasCodeFixup = false;
                    if (!string.IsNullOrEmpty(entry.RipFixups))
                    {
                        foreach (string f in entry.RipFixups.Split(new char[]{'|'}, StringSplitOptions.RemoveEmptyEntries))
                        {
                            string[] fp = f.Split(':');
                            if (fp.Length >= 4 && fp[3] != "d")
                            {
                                int fbi = int.Parse(fp[0]) - 1;
                                if (fbi == bi) { hasCodeFixup = true; break; }
                            }
                        }
                    }
                    if (!hasCodeFixup && bi > 0)
                    {
                        for (int zi = 0; zi < data.Length; zi++) data[zi] = 0;
                    }
                    // ★ 2d. 写入重定位后的alloc块数据
                    if (!WriteMem(blk.NewAddr, data, data.Length))
                    {
                        ShowMsg(string.Format("写入alloc块 {0} 数据失败！", blk.Name), "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                        // 回滚（一次性分配，只释放第一个块）
                        if (entry.AllocBlocks[0].NewAddr != IntPtr.Zero)
                        {
                            try { VirtualFreeEx(hProcess, entry.AllocBlocks[0].NewAddr, 0, MEM_RELEASE); } catch { }
                        }
                        foreach (var ablk in entry.AllocBlocks)
                            ablk.NewAddr = IntPtr.Zero;
                        entry.ResetState();
                        return;
                    }
                }
                customLen = 0;
                for (int bi = 0; bi < entry.AllocBlocks.Length; bi++)
                    customLen += entry.AllocBlocks[bi].Bytes.Length;
            }
            else if (entry.FullCaveBytes != null && entry.FullCaveBytes.Length > 0)
            {
                // ★ 回退路径A：使用旧的单块fullCaveBytes
                //    同样需要在注入点附近分配！
                int caveTotalLen = entry.FullCaveBytes.Length;
                allocSize = (uint)Math.Max(4096, caveTotalLen * 2);
                {
                    ulong preferredBase = (ulong)injectAddr.ToInt64() & ~(0x10000UL - 1); // 64KB对齐
                    if (preferredBase > 0x10000)
                        allocAddr = VirtualAllocEx(hProcess, new IntPtr((long)preferredBase), allocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                    if (allocAddr == IntPtr.Zero)
                    {
                        // 用VirtualQueryEx扫描注入点附近寻找空闲区域
                        const uint MEM_FREE = 0x10000;
                        long rangeLimit = 0x7FFF0000L;
                        long injectLong = (long)preferredBase;
                        long scanUp = injectLong, scanDown = injectLong;
                        bool upDone = false, downDone = false;
                        while (!upDone || !downDone)
                        {
                            if (!upDone)
                            {
                                MEMORY_BASIC_INFORMATION_EX mbi;
                                if (VirtualQueryEx(hProcess, new IntPtr(scanUp), out mbi, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION_EX))) != IntPtr.Zero)
                                {
                                    long rs = mbi.BaseAddress.ToInt64(), re = rs + mbi.RegionSize.ToInt64();
                                    if (mbi.State == MEM_FREE && mbi.RegionSize.ToInt64() >= allocSize)
                                    {
                                        ulong tryAddr = ((ulong)rs + 0xFFFFUL) & ~(0xFFFFUL);
                                        if (tryAddr + allocSize <= (ulong)re)
                                        {
                                            allocAddr = VirtualAllocEx(hProcess, new IntPtr((long)tryAddr), allocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                                            if (allocAddr != IntPtr.Zero) break;
                                        }
                                    }
                                    scanUp = re;
                                    if (scanUp - injectLong > rangeLimit) upDone = true;
                                }
                                else upDone = true;
                            }
                            if (!downDone && allocAddr == IntPtr.Zero)
                            {
                                long ds = scanDown - 0x10000;
                                if (ds >= 0x10000 && injectLong - ds <= rangeLimit)
                                {
                                    MEMORY_BASIC_INFORMATION_EX mbi;
                                    if (VirtualQueryEx(hProcess, new IntPtr(ds), out mbi, (uint)Marshal.SizeOf(typeof(MEMORY_BASIC_INFORMATION_EX))) != IntPtr.Zero)
                                    {
                                        long rs = mbi.BaseAddress.ToInt64(), re = rs + mbi.RegionSize.ToInt64();
                                        if (mbi.State == MEM_FREE && mbi.RegionSize.ToInt64() >= allocSize)
                                        {
                                            ulong tryAddr = ((ulong)rs + 0xFFFFUL) & ~(0xFFFFUL);
                                            if (tryAddr + allocSize <= (ulong)re)
                                            {
                                                allocAddr = VirtualAllocEx(hProcess, new IntPtr((long)tryAddr), allocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                                                if (allocAddr != IntPtr.Zero) break;
                                            }
                                        }
                                        scanDown = rs;
                                    }
                                    else downDone = true;
                                }
                                else downDone = true;
                            }
                        }
                    }
                    if (allocAddr == IntPtr.Zero)
                        allocAddr = VirtualAllocEx(hProcess, IntPtr.Zero, allocSize, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                }
                if (allocAddr == IntPtr.Zero)
                {
                    ShowMsg("远程内存分配失败！(预汇编模式)", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    entry.ResetState();
                    return;
                }

                byte[] caveData = new byte[caveTotalLen];
                Array.Copy(entry.FullCaveBytes, caveData, caveTotalLen);

                long returnTarget = injectAddr.ToInt64() + codeLen;
                long caveBase = allocAddr.ToInt64();

                if (!string.IsNullOrEmpty(entry.ReturnHereFixups))
                {
                    string[] fixupStrs = entry.ReturnHereFixups.Split(new char[]{','}, StringSplitOptions.RemoveEmptyEntries);
                    foreach (string fs in fixupStrs)
                    {
                        string[] fparts = fs.Split(':');
                        int off = int.Parse(fparts[0]);
                        int instrLen = int.Parse(fparts[1]);
                        long instrEnd = caveBase + off + instrLen;
                        int newRel = (int)(returnTarget - instrEnd);
                        int relStart = off + (instrLen - 4);
                        caveData[relStart] = (byte)(newRel & 0xFF);
                        caveData[relStart + 1] = (byte)((newRel >> 8) & 0xFF);
                        caveData[relStart + 2] = (byte)((newRel >> 16) & 0xFF);
                        caveData[relStart + 3] = (byte)((newRel >> 24) & 0xFF);
                    }
                }
                else
                {
                    long injBase = injectAddr.ToInt64();
                    for (int si = 0; si < caveTotalLen - 4; si++)
                    {
                        if (caveData[si] == 0xE9)
                        {
                            int oldRel = BitConverter.ToInt32(caveData, si + 1);
                            long jmpDest = caveBase + si + 5 + oldRel;
                            if (jmpDest >= injBase && jmpDest <= injBase + 4096)
                            {
                                int newRel = (int)(returnTarget - (caveBase + si + 5));
                                caveData[si + 1] = (byte)(newRel & 0xFF);
                                caveData[si + 2] = (byte)((newRel >> 8) & 0xFF);
                                caveData[si + 3] = (byte)((newRel >> 16) & 0xFF);
                                caveData[si + 4] = (byte)((newRel >> 24) & 0xFF);
                            }
                        }
                        else if (caveData[si] == 0x0F && si + 5 < caveTotalLen && caveData[si + 1] >= 0x80 && caveData[si + 1] <= 0x8F)
                        {
                            int oldRel = BitConverter.ToInt32(caveData, si + 2);
                            long jmpDest = caveBase + si + 6 + oldRel;
                            if (jmpDest >= injBase && jmpDest <= injBase + 4096)
                            {
                                int newRel = (int)(returnTarget - (caveBase + si + 6));
                                caveData[si + 2] = (byte)(newRel & 0xFF);
                                caveData[si + 3] = (byte)((newRel >> 8) & 0xFF);
                                caveData[si + 4] = (byte)((newRel >> 16) & 0xFF);
                                caveData[si + 5] = (byte)((newRel >> 24) & 0xFF);
                            }
                        }
                    }
                }

                if (!string.IsNullOrEmpty(entry.RipFixups))
                {
                    string[] fixupList = entry.RipFixups.Split(new char[]{'|'}, StringSplitOptions.RemoveEmptyEntries);
                    foreach (string f in fixupList)
                    {
                        string[] parts = f.Split(':');
                        int fBi = int.Parse(parts[0]) - 1;
                        if (fBi != 0) continue;
                        int fOff = int.Parse(parts[1]);
                        int fLen = int.Parse(parts[2]);
                        string fType = parts[3];
                        string absStr = parts[4].StartsWith("0x") ? parts[4].Substring(2) : parts[4];
                        long absTarget = long.Parse(absStr, System.Globalization.NumberStyles.HexNumber);

long newTarget;
                        bool remappedByAlloc = false;

if (fType == "ri")
                        {
                            newTarget = injectAddr.ToInt64() + absTarget;
                        }
                        else if (fType == "d")
                        {
                            newTarget = absTarget;
                            if (entry.AllocBlocks != null)
                            {
                                for (int bj = 0; bj < entry.AllocBlocks.Length; bj++)
                                {
                                    AllocBlock tBlk = entry.AllocBlocks[bj];
                                    if (absTarget >= tBlk.OrigAddr && absTarget <= tBlk.OrigAddr + tBlk.Size)
                                    {
                                        newTarget = tBlk.NewAddr.ToInt64() + (absTarget - tBlk.OrigAddr);
                                        break;
                                    }
                                }
                            }
                            // ★ ASLR修复：数据fixup也支持模块名+偏移重定位
                            if (parts.Length >= 7 && newTarget == absTarget)
                            {
                                string dModName = parts[5];
                                if (parts.Length > 7)
                                {
                                    for (int pj = 6; pj < parts.Length - 1; pj++)
                                        dModName += ":" + parts[pj];
                                }
                                long dModOff = long.Parse(parts[parts.Length - 1], System.Globalization.NumberStyles.HexNumber);
                                IntPtr dModBase = GetModuleBase(dModName);
                                if (dModBase != IntPtr.Zero)
                                {
                                    newTarget = dModBase.ToInt64() + dModOff;
                                }
                            }
                            uint dVal = (uint)newTarget;
                            caveData[fOff] = (byte)(dVal & 0xFF);
                            caveData[fOff + 1] = (byte)((dVal >> 8) & 0xFF);
                            caveData[fOff + 2] = (byte)((dVal >> 16) & 0xFF);
                            caveData[fOff + 3] = (byte)((dVal >> 24) & 0xFF);
                            continue;
                        }
                        else
{
                            newTarget = absTarget;

                            if (entry.AllocBlocks != null && entry.AllocBlocks.Length > 0)
                            {
                                AllocBlock firstBlk = entry.AllocBlocks[0];
                                long firstEffectiveSize = ((firstBlk.Size + 4095) / 4096) * 4096;
                                if (absTarget >= firstBlk.OrigAddr && absTarget < firstBlk.OrigAddr + firstEffectiveSize)
                                {
                                    newTarget = caveBase + (absTarget - firstBlk.OrigAddr);
                                    remappedByAlloc = true;
                                }
                                for (int bj = 1; bj < entry.AllocBlocks.Length; bj++)
                                {
                                    AllocBlock tBlk = entry.AllocBlocks[bj];
                                    long effectiveSize = ((tBlk.Size + 4095) / 4096) * 4096;
                                    if (absTarget >= tBlk.OrigAddr && absTarget <= tBlk.OrigAddr + effectiveSize)
                                    {
                                        newTarget = caveBase + (tBlk.OrigAddr - entry.AllocBlocks[0].OrigAddr) + (absTarget - tBlk.OrigAddr);
                                        remappedByAlloc = true;
                                        break;
                                    }
}
                            }

                            // ★ ASLR修复：绝对地址未命中alloc块时，通过模块名+偏移重定位（32位和64位均支持）
                            if (parts.Length >= 7 && !remappedByAlloc)
                            {
                                string fixupModName = parts[5];
                                if (parts.Length > 7)
                                {
                                    for (int pj = 6; pj < parts.Length - 1; pj++)
                                        fixupModName += ":" + parts[pj];
                                }
                                long fixupModOff = long.Parse(parts[parts.Length - 1], System.Globalization.NumberStyles.HexNumber);
                                IntPtr curModBase = GetModuleBase(fixupModName);
                                if (curModBase != IntPtr.Zero)
                                {
                                    newTarget = curModBase.ToInt64() + fixupModOff;
                                }
                            }
                        }

                        int relStart;
                        if (fType == "a" && fLen == 5 && (caveData[fOff] == 0xA1 || caveData[fOff] == 0xA3))
                        {
                            relStart = fOff + 1;
                        }
                        else if (fType == "a" || ((fType == "r" || fType == "ri") && fLen != 5 && !(fLen == 6 && caveData[fOff] == 0x0F)))
                        {
int modRMIdx = fOff + 1;
                            if (!targetIs32Bit && caveData[fOff] >= 0x40 && caveData[fOff] <= 0x4F) modRMIdx = fOff + 2;
                            relStart = modRMIdx + 1;
                        }
                        else
                        {
                            relStart = fOff + (fLen - 4);
                        }
                        if (fOff + fLen > caveData.Length) continue;
                        if (relStart >= 0 && relStart + 3 < caveData.Length)
                        {
bool opcodeValid = false;
                            if (fLen == 5 && (caveData[fOff] == 0xE9 || caveData[fOff] == 0xE8)) opcodeValid = true;
                            else if (fLen == 5 && (caveData[fOff] == 0xA1 || caveData[fOff] == 0xA3)) opcodeValid = true;
                            else if (fLen == 6 && caveData[fOff] == 0x0F && caveData[fOff + 1] >= 0x80 && caveData[fOff + 1] <= 0x8F) opcodeValid = true;
                            else if (fLen == 2 && (caveData[fOff] == 0xEB || (caveData[fOff] >= 0x70 && caveData[fOff] <= 0x7F))) opcodeValid = true;
                            else if ((fType == "a" || fType == "ri" || fType == "r") && fLen >= 6)
                            {
                                int modRMIdx = fOff + 1;
                                if (!targetIs32Bit && caveData[fOff] >= 0x40 && caveData[fOff] <= 0x4F) modRMIdx = fOff + 2;
                                if (modRMIdx < caveData.Length) { byte m = caveData[modRMIdx]; if (((m >> 6) & 3) == 0 && (m & 7) == 5) opcodeValid = true; }
                            }
                            if (!opcodeValid) continue;
                            if (fType == "sr") continue;
                            else if (fType == "a")
                            {
                                uint val = (uint)newTarget;
                                caveData[relStart] = (byte)(val & 0xFF);
                                caveData[relStart + 1] = (byte)((val >> 8) & 0xFF);
                                caveData[relStart + 2] = (byte)((val >> 16) & 0xFF);
                                caveData[relStart + 3] = (byte)((val >> 24) & 0xFF);
                            }
                            else
                            {
                                long newInstrEnd = caveBase + fOff + fLen;
                                int newRel = (int)(newTarget - newInstrEnd);
                                caveData[relStart] = (byte)(newRel & 0xFF);
                                caveData[relStart + 1] = (byte)((newRel >> 8) & 0xFF);
                                caveData[relStart + 2] = (byte)((newRel >> 16) & 0xFF);
                                caveData[relStart + 3] = (byte)((newRel >> 24) & 0xFF);
                            }
                        }
                    }
                }

                if (!WriteMem(allocAddr, caveData, caveData.Length))
                {
                    ShowMsg("写入代码洞数据失败！(预汇编模式)", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    VirtualFreeEx(hProcess, allocAddr, 0, MEM_RELEASE);
                    entry.ResetState();
                    return;
                }
                customLen = caveTotalLen;
}
            else
            {
// ★★★ AA引擎路径 — 直接解析脚本+汇编，绕过预编译重定位 ★★★
                string fullScript = entry.AAScriptPreview ?? "";
                if (string.IsNullOrEmpty(fullScript))
                {
                    ShowMsg("该AA脚本无脚本代码！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    entry.ResetState(); return;
                }
                string allocName; long asmAllocAddr; int asmAllocSz;
                byte[] asmCave = AAEngine.ExecuteScript(fullScript, injectAddr.ToInt64(),
                    entry.OrigInstrBytes, !targetIs32Bit,
                    out allocName, out asmAllocAddr, out asmAllocSz,
                    hProcess, MEM_COMMIT, MEM_RESERVE, PAGE_EXECUTE_READWRITE);
                if (asmCave == null || asmCave.Length == 0)
                {
                    ShowMsg("AA引擎：脚本汇编失败！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    entry.ResetState(); return;
                }
                allocAddr = new IntPtr(asmAllocAddr);
                allocSize = (uint)asmAllocSz;
                if (!WriteMem(allocAddr, asmCave, asmCave.Length))
                {
                    ShowMsg("AA引擎：写入代码洞失败！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    VirtualFreeEx(hProcess, allocAddr, 0, MEM_RELEASE); entry.ResetState(); return;
                }
                customLen = asmCave.Length;
                // 注册alloc块供指针链使用
                if (!string.IsNullOrEmpty(allocName))
                {
                    entry.AllocBlocks = new AllocBlock[] { new AllocBlock(allocName, 0, asmAllocSz, new byte[0]) };
                    entry.AllocBlocks[0].NewAddr = allocAddr;
                    entry.IsAllocScript = true;
                }
            }

            entry.AllocatedMem = allocAddr;
            entry.LastAllocStart = allocAddr.ToInt64();
            entry.LastAllocSize = (long)allocSize;
            entry.ExtraAllocs = extraAllocs;

            // 注入点JMP: 跳转到代码洞开头
            byte[] jmpPatch = new byte[codeLen];
            for (int i = 0; i < codeLen; i++) jmpPatch[i] = 0x90;
            long jmpFrom = injectAddr.ToInt64() + 5;
            long jmpTo = allocAddr.ToInt64();
            long rawRelOffset = jmpTo - jmpFrom;
            // ★ 关键检查：E9 JMP的32位有符号偏移必须在±2GB范围内
            if (rawRelOffset > 0x7FFFFFFF || rawRelOffset < -(long)0x80000000)
            {
                string rangeErr = string.Format(
                    "JMP偏移超出32位范围！\n\n注入点: 0x{0:X}\n代码洞: 0x{1:X}\n偏移: 0x{2:X} ({3})\n\n" +
                    "E9 JMP只有±2GB范围，代码洞必须在注入点附近分配。\n" +
                    "可能原因：VirtualAllocEx无法在注入点附近找到可用内存区域。\n\n" +
                    "建议：关闭其他占用内存的程序后重试。",
                    injectAddr.ToInt64(), allocAddr.ToInt64(), rawRelOffset, rawRelOffset > 0 ? "+2GB超出" : "-2GB超出");
                ShowMsg(rangeErr, "JMP范围错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                // 回滚：释放已分配的内存（一次性分配，只需释放第一个块）
                if (entry.AllocBlocks != null && entry.AllocBlocks.Length > 0)
                {
                    if (entry.AllocBlocks[0].NewAddr != IntPtr.Zero)
                    {
                        try { VirtualFreeEx(hProcess, entry.AllocBlocks[0].NewAddr, 0, MEM_RELEASE); } catch { }
                    }
                    foreach (var ablk in entry.AllocBlocks)
                        ablk.NewAddr = IntPtr.Zero;
                }
                else if (allocAddr != IntPtr.Zero)
                {
                    try { VirtualFreeEx(hProcess, allocAddr, 0, MEM_RELEASE); } catch { }
                }
                entry.ResetState();
                return;
            }
            int relOffset = (int)rawRelOffset;
            jmpPatch[0] = 0xE9;
            jmpPatch[1] = (byte)(relOffset & 0xFF);
            jmpPatch[2] = (byte)((relOffset >> 8) & 0xFF);
            jmpPatch[3] = (byte)((relOffset >> 16) & 0xFF);
            jmpPatch[4] = (byte)((relOffset >> 24) & 0xFF);

            // ★ 解锁注入点内存并写入JMP补丁
            if (!MemoryProtector.UnprotectMemory(hProcess, injectAddr, codeLen, out memProtectOld))
            {
                int err = Marshal.GetLastWin32Error();
                ShowMsg(string.Format("无法解锁内存保护！(错误码: 0x{0:X})\n地址: 0x{1:X}\n长度: {2}\n请确认没有试图修改系统保护区域。",
                    err, injectAddr.ToInt64(), codeLen), "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                VirtualFreeEx(hProcess, allocAddr, 0, MEM_RELEASE);
                entry.ResetState();
                return;
            }
            if (!WriteMem(injectAddr, jmpPatch, codeLen))
            {
                MemoryProtector.ReprotectMemory(hProcess, injectAddr, codeLen, memProtectOld);
                ShowMsg("写入补丁失败！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
                VirtualFreeEx(hProcess, allocAddr, 0, MEM_RELEASE);
                entry.ResetState();
                return;
            }
            MemoryProtector.ReprotectMemory(hProcess, injectAddr, codeLen, memProtectOld);

// ★ 验证写入结果：读回注入点字节确认JMP已写入
            byte[] verifyBuf = new byte[codeLen];
            bool jmpWritten = ReadMem(injectAddr, verifyBuf, codeLen) && (verifyBuf[0] == 0xE9);
            if (!jmpWritten)
            {
                string hexExpected = "", hexActual = "";
                for (int vi = 0; vi < codeLen; vi++) { hexExpected += jmpPatch[vi].ToString("X2") + " "; hexActual += verifyBuf[vi].ToString("X2") + " "; }
                ShowMsg(string.Format("JMP写入验证失败！\n地址: 0x{0:X}\n期望: {1}\n实际: {2}\n可能被反作弊保护还原。",
                    injectAddr.ToInt64(), hexExpected.Trim(), hexActual.Trim()), "警告", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                // ★ 回滚：JMP未生效，释放已分配内存并重置状态
                MemoryProtector.ReprotectMemory(hProcess, injectAddr, codeLen, memProtectOld);
                if (entry.AllocBlocks != null && entry.AllocBlocks.Length > 0)
                {
                    if (entry.AllocBlocks[0].NewAddr != IntPtr.Zero)
                    {
                        try { VirtualFreeEx(hProcess, entry.AllocBlocks[0].NewAddr, 0, MEM_RELEASE); } catch { }
                    }
                    foreach (var ablk in entry.AllocBlocks)
                        ablk.NewAddr = IntPtr.Zero;
                }
                else if (allocAddr != IntPtr.Zero)
                {
                    try { VirtualFreeEx(hProcess, allocAddr, 0, MEM_RELEASE); } catch { }
                }
                entry.ResetState();
                return;
            }

            entry.AAEnabled = true;
            if (panels[idx] != null)
            {
                panels[idx].btnToggleAA.Text = "已开启";
                panels[idx].btnToggleAA.BackColor = Color.LightGreen;
                panels[idx].btnToggleAA.Enabled = false;
            }
        }

        void OnWriteValue(int idx)
        {
            if (idx < 0 || idx >= entries.Length) return;
            if (hProcess == IntPtr.Zero || !bRunning)
            {
                MessageBox.Show("未连接到游戏进程，请先启动修改器！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }
            TrainerEntry entry = entries[idx];
            PanelEntry pe = panels[idx];
            string valStr = pe.txtValue.Text;
            byte[] valBytes = ParseValueBytes(valStr, entry.VType);
            if (valBytes == null)
            {
                MessageBox.Show("数值格式错误！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }
            long finalAddr;
            string ptrDiag = ResolvePointerChain(entry, out finalAddr);
            if (finalAddr == 0)
            {
                string tip = ptrDiag.IndexOf("空指针") >= 0
                    ? "【这不是故障】符号槽当前为 0，需要让游戏执行一次被 hook 的指令才有值。\n"                      + "教程第二关：点几次「打我」触发该指令；若仍无值，检查状态栏是否连到了正确的游戏进程。\n\n" : "";
                MessageBox.Show(tip + "完整诊断（可复制回贴）：\n\n" + ptrDiag, "地址解析诊断", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }
            IntPtr addr = new IntPtr(finalAddr);
            if (WriteMem(addr, valBytes, valBytes.Length))
            {
                pe.lblCurrent.Text = "当前：" + valStr;
            }
            else
            {
                MessageBox.Show("写入内存失败！", "错误", MessageBoxButtons.OK, MessageBoxIcon.Error);
            }
        }

        void BtnStart_Click(object sender, EventArgs e)
        {
            if (workerThread != null && workerThread.IsAlive)
            {
                bStopping = true;
                ResetAllAA();
                if (hProcess != IntPtr.Zero) CloseHandle(hProcess);
                hProcess = IntPtr.Zero;
                bRunning = false;
                btnStart.Text = "启动修改器";
                btnStart.BackColor = Color.FromArgb(0, 120, 215);
                btnSwitch.Enabled = false;
                UpdateStatus("状态：已停止", Color.Gray);
            }
            else
            {
                bStopping = false;
                bSwitchRequested = false;
                currentProcessIndex = -1;
                totalProcessCount = 0;
                workerThread = new Thread(WorkerLoop);
                workerThread.IsBackground = true;
                workerThread.Start();
__ANTI_THREAD_START__
                btnStart.Text = "停止修改器";
                btnStart.BackColor = Color.FromArgb(200, 50, 50);
                btnSwitch.Enabled = true;
                UpdateStatus("状态：等待连接...", Color.Orange);
            }
        }

        byte[] HexToBytes(string hex)
        {
            if (string.IsNullOrEmpty(hex)) return new byte[0];
            hex = hex.Replace(" ", "");
            if (hex.Length % 2 != 0) return new byte[0];
            byte[] result = new byte[hex.Length / 2];
            for (int i = 0; i < result.Length; i++)
                result[i] = Convert.ToByte(hex.Substring(i * 2, 2), 16);
            return result;
        }

        AllocBlock[] ParseAllocBlocks(string text)
        {
            if (string.IsNullOrEmpty(text)) return new AllocBlock[0];
            string[] parts = text.Split(',');
            List<AllocBlock> blocks = new List<AllocBlock>();
            foreach (string p in parts)
            {
                string[] f = p.Split(':');
                if (f.Length >= 4)
                {
                    string name = f[0];
                    long origAddr = long.Parse(f[1]);
                    int size = int.Parse(f[2]);
                    byte[] bytes = HexToBytes(f[3]);
                    blocks.Add(new AllocBlock(name, origAddr, size, bytes));
                }
            }
            return blocks.ToArray();
        }

        void LoadGameFromLib(GameLibEntry game)
        {
            if (game == null || string.IsNullOrEmpty(game.EntryData)) return;
            if (hProcess != IntPtr.Zero && bRunning)
            {
                ResetAllAA();
                CloseHandle(hProcess);
                hProcess = IntPtr.Zero;
                bRunning = false;
                moduleCache.Clear();
            }
            bSwitchRequested = false;
            currentProcessIndex = -1;
            string[] lines = game.EntryData.Split('\n');
            string procName = "";
            List<TrainerEntry> newEntries = new List<TrainerEntry>();
            foreach (string rawLine in lines)
            {
                string line = rawLine.Trim('\r');
                if (line.StartsWith("PROCESS:"))
                {
                    procName = line.Substring(8).Trim();
                    continue;
                }
                if (!line.StartsWith("ENTRY~")) continue;
                string[] f = line.Split('~');
                if (f.Length < 27) continue;
                try
                {
                    string desc = f[1];
                    string addrStr = f[2];
                    long resolvedAddr = long.Parse(f[3]);
                    long baseResolvedAddr = long.Parse(f[4]);
                    int vtype = int.Parse(f[5]);
                    long[] offsets = new long[0];
                    if (!string.IsNullOrEmpty(f[6]))
                    {
                        string[] offParts = f[6].Split(',');
                        List<long> offList = new List<long>();
                        foreach (string op in offParts)
                            offList.Add(long.Parse(op, System.Globalization.NumberStyles.HexNumber));
                        offsets = offList.ToArray();
                    }
                    string modName = f[7];
                    long modOff = long.Parse(f[8]);
                    bool isAA = f[9] == "1";
                    bool aaEnabled = f[10] == "1";
                    string aobPattern = isAA ? f[11] : "";
                    string aobModule = isAA ? f[12] : "";
                    byte[] origInstrBytes = isAA ? HexToBytes(f[13]) : new byte[0];
                    int origInstrLen = isAA ? int.Parse(f[14]) : 5;
                    byte[] customCodeBytes = isAA ? HexToBytes(f[15]) : new byte[0];
                    bool hasOriginalCode = isAA ? f[16] == "1" : true;
                    byte[] fullCaveBytes = isAA ? HexToBytes(f[17]) : new byte[0];
                    string returnHereFixups = isAA ? f[18] : "";
                    AllocBlock[] allocBlocks = isAA ? ParseAllocBlocks(f[19]) : new AllocBlock[0];
                    string ripFixups = isAA ? f[20] : "";
                    bool isAllocScript = isAA ? f[21] == "1" : false;
                    byte[] directPatchBytes = isAA ? HexToBytes(f[22]) : new byte[0];
                    string allocSymbolName = f[23];
                    string aobSymbolName = (f.Length > 24 && isAA) ? f[24] : "";
                    string initVal = (f.Length > 25) ? f[25] : "";
                    string dataAobPatternCS = (f.Length > 27) ? f[27] : "";  // ★ 新增:数据段AOB特征码
                    long dataAobOffsetCS = (f.Length > 28) ? long.Parse(f[28]) : 0;  // ★ 新增:数据段AOB偏移
                    TrainerEntry te = new TrainerEntry(desc, addrStr, resolvedAddr, baseResolvedAddr, vtype,
                        offsets, modName, modOff, isAA, aaEnabled,
                        aobPattern, aobModule, "", origInstrBytes, origInstrLen,
                        customCodeBytes, hasOriginalCode, fullCaveBytes, returnHereFixups,
                        allocBlocks, ripFixups,
                        isAllocScript, directPatchBytes,
                        allocSymbolName, aobSymbolName,
                        dataAobPatternCS, dataAobOffsetCS);
                    newEntries.Add(te);
                }
                catch { }
            }
            if (newEntries.Count == 0) return;
            entries = newEntries.ToArray();
            string cleanProcName = procName;
            int parenIdx = cleanProcName.IndexOf('(');
            if (parenIdx >= 0)
            {
                string inner = cleanProcName.Substring(parenIdx + 1);
                int dashIdx = inner.IndexOf('-');
                if (dashIdx >= 0)
                    cleanProcName = inner.Substring(dashIdx + 1).TrimEnd(')');
            }
            targetProcessName = cleanProcName.Replace(".exe", "");
            mainPanel.Controls.Clear();
            panels = new PanelEntry[entries.Length];
            for (int i = 0; i < entries.Length; i++)
            {
                BuildRow(mainPanel, i, entries[i].Desc, entries[i].IsAA, false, "");
            }
            this.Height = Math.Min(125 + entries.Length * 30, 500);
            if (workerThread != null && workerThread.IsAlive)
            {
                UpdateStatus("状态：切换中 - " + cleanProcName + " (" + entries.Length + "项)", Color.Orange);
            }
            else
            {
                bStopping = false;
                workerThread = new Thread(WorkerLoop);
                workerThread.IsBackground = true;
                workerThread.Start();
__ANTI_THREAD_START__
                btnStart.Text = "停止修改器";
                btnStart.BackColor = Color.FromArgb(200, 50, 50);
                btnSwitch.Enabled = true;
                UpdateStatus("状态：连接中 - " + cleanProcName + " (" + entries.Length + "项)", Color.Orange);
            }
        }

        void BtnGameLib_Click(object sender, EventArgs e)
        {
            if (gameLibData.Count == 0)
            {
                MessageBox.Show("游戏库为空，请先在生成工具中读取并存档数据。", "游戏库", MessageBoxButtons.OK, MessageBoxIcon.Information);
                return;
            }
            Form libForm = new Form();
            libForm.Text = "游戏库 - 双击选择游戏";
            libForm.Width = 310;
            libForm.Height = 370;
            libForm.StartPosition = FormStartPosition.Manual;
            Point btnScreen = btnGameLib.PointToScreen(new Point(0, btnGameLib.Height));
            libForm.Location = btnScreen;
            libForm.FormBorderStyle = FormBorderStyle.FixedDialog;
            libForm.MaximizeBox = false;
            libForm.MinimizeBox = false;
            libForm.ShowInTaskbar = false;
            libForm.BackColor = Color.White;
            libForm.TopMost = true;

            ListView lv = new ListView();
            lv.Left = 5; lv.Top = 5;
            lv.Width = 285; lv.Height = 295;
            lv.BackColor = Color.White;
            lv.ForeColor = Color.Black;
            lv.Font = new Font("Microsoft YaHei", 10);
            lv.BorderStyle = BorderStyle.FixedSingle;
            lv.View = View.Details;
            lv.FullRowSelect = true;
            lv.GridLines = true;
            lv.HeaderStyle = ColumnHeaderStyle.Nonclickable;
            lv.Columns.Add("编号", 40);
            lv.Columns.Add("游戏名称", 150);
            lv.Columns.Add("游戏版本", 75);
            for (int gi = 0; gi < gameLibData.Count; gi++)
            {
                ListViewItem lvi = new ListViewItem((gi + 1).ToString());
                string displayName = gameLibData[gi].GameName;
                int parenIdx = displayName.IndexOf('(');
                if (parenIdx >= 0)
                {
                    string inner = displayName.Substring(parenIdx + 1);
                    int dashIdx = inner.IndexOf('-');
                    if (dashIdx >= 0)
                        displayName = inner.Substring(dashIdx + 1).TrimEnd(')');
                }
                lvi.SubItems.Add(displayName);
                lvi.SubItems.Add(gameLibData[gi].GameVersion ?? "");
                lvi.Tag = gi;
                lv.Items.Add(lvi);
            }
            lv.DoubleClick += (s2, e2) =>
            {
                if (lv.SelectedItems.Count > 0)
                {
                    int idx = (int)lv.SelectedItems[0].Tag;
                    LoadGameFromLib(gameLibData[idx]);
                    libForm.Close();
                }
            };
            libForm.Controls.Add(lv);
            libForm.Deactivate += (s2, e2) => { libForm.Close(); };
            libForm.Show(this);
        }

        void BtnSwitch_Click(object sender, EventArgs e)
        {
            if (hProcess == IntPtr.Zero && !bRunning)
            {
                bSwitchRequested = true;
                UpdateStatus("状态：切换进程中...", Color.Orange);
                return;
            }
            ResetAllAA();
            if (hProcess != IntPtr.Zero) CloseHandle(hProcess);
            hProcess = IntPtr.Zero;
            bRunning = false;
            moduleCache.Clear();
            bSwitchRequested = true;
            UpdateStatus("状态：切换进程中...", Color.Orange);
        }

        static Icon CreateTrainerIcon()
        {
            int size = 64;
            Bitmap bmp = new Bitmap(size, size);
            using (Graphics g = Graphics.FromImage(bmp))
            {
                g.SmoothingMode = System.Drawing.Drawing2D.SmoothingMode.AntiAlias;
                g.Clear(Color.Transparent);
                int cx = size / 2;
                int cy = size / 2;
                int R = (int)(size * 0.46);
                int r = R / 2;
                int dotR = Math.Max((int)(R * 0.15), 1);
                g.FillEllipse(new SolidBrush(Color.FromArgb(30, 30, 30)), cx - R, cy - R, R * 2, R * 2);
                System.Drawing.Drawing2D.GraphicsPath whitePath = new System.Drawing.Drawing2D.GraphicsPath();
                using (whitePath)
                {
                whitePath.AddArc(cx - R, cy - R, R * 2, R * 2, 270, 180);
                whitePath.AddArc(cx - r, cy, r * 2, r * 2, 90, 180);
                whitePath.AddArc(cx - r, cy - R, r * 2, r * 2, 90, -180);
                g.FillPath(Brushes.White, whitePath);
                }
                g.FillEllipse(new SolidBrush(Color.FromArgb(30, 30, 30)), cx - dotR, cy - r - dotR, dotR * 2, dotR * 2);
                g.FillEllipse(Brushes.White, cx - dotR, cy + r - dotR, dotR * 2, dotR * 2);
                using (Pen outline = new Pen(Color.FromArgb(100, 100, 100), Math.Max(size / 64, 1)))
                {
                    g.DrawEllipse(outline, cx - R, cy - R, R * 2, R * 2);
                }
            }
            IntPtr hIcon = bmp.GetHicon();
            return Icon.FromHandle(hIcon);
        }

        void BtnAbout_Click(object sender, EventArgs e)
        {
            Form aboutForm = new Form();
            aboutForm.Text = "关于";
            aboutForm.Width = 380;
            aboutForm.Height = 320;
            aboutForm.StartPosition = FormStartPosition.CenterParent;
            aboutForm.FormBorderStyle = FormBorderStyle.FixedDialog;
            aboutForm.MaximizeBox = false;
            aboutForm.MinimizeBox = false;
            aboutForm.ShowInTaskbar = false;
            int ay = 15;
__SIGN_LABELS__
            Button btnClose = new Button();
            btnClose.Text = "关闭";
            btnClose.Left = 140; btnClose.Top = ay + 5;
            btnClose.Width = 80; btnClose.Height = 28;
            btnClose.Click += (s, ev) => aboutForm.Close();
            aboutForm.Controls.Add(btnClose);
            aboutForm.Show(this);
        }

        void UpdateStatus(string text, Color color)
        {
            if (this.InvokeRequired)
            {
                try { this.Invoke(new Action(() => UpdateStatus(text, color))); }
                catch { }
                return;
            }
            lblStatus.Text = text;
            lblStatus.ForeColor = color;
        }

        bool GetChecked(CheckBox chk)
        {
            if (chk.InvokeRequired)
            {
                try { return (bool)chk.Invoke(new Func<bool>(() => chk.Checked)); }
                catch { return false; }
            }
            return chk.Checked;
        }

        void WorkerLoop()
        {
            while (!bStopping)
            {
                try
                {
                    CheckAntiDebug();
                    if (!bRunning)
                    {
                        targetProcesses = FindAllTargetProcesses();
                        totalProcessCount = targetProcesses.Length;
                        if (targetProcesses.Length == 0)
                        {
                            UpdateStatus("状态：未找到游戏进程", Color.Red);
                            currentProcessIndex = -1;
                            Thread.Sleep(1000);
                            continue;
                        }
                        int targetIndex = 0;
                        if (bSwitchRequested)
                        {
                            bSwitchRequested = false;
                            targetIndex = (currentProcessIndex + 1) % targetProcesses.Length;
                        }
                        else
                        {
                            targetIndex = 0;
                            currentProcessIndex = -1;
                        }
                        if (ConnectToProcess(targetIndex))
                        {
                        }
                        else
                        {
                            bool connected = false;
                            for (int tryIdx = 0; tryIdx < targetProcesses.Length; tryIdx++)
                            {
                                if (tryIdx == targetIndex) continue;
                                if (ConnectToProcess(tryIdx))
                                {
                                    connected = true;
                                    break;
                                }
                            }
                            if (!connected)
                            {
                                UpdateStatus("状态：打开进程失败", Color.Red);
                            }
                        }
                        Thread.Sleep(1000);
                    }
                    else
                    {
                        bool processAlive = false;
                        if (currentProcessIndex >= 0 && currentProcessIndex < targetProcesses.Length)
                        {
                            try { processAlive = !targetProcesses[currentProcessIndex].HasExited; }
                            catch { processAlive = false; }
                        }
                        if (!processAlive)
                        {
                            ResetAllAA();
                            bRunning = false;
                            if (hProcess != IntPtr.Zero) CloseHandle(hProcess);
                            hProcess = IntPtr.Zero;
                            moduleCache.Clear();
                            currentProcessIndex = -1;
                            UpdateStatus("状态：游戏已退出", Color.Orange);
                            Thread.Sleep(1000);
                            continue;
                        }
                        bool anyProblem = false;   // [r3] 本轮是否有记录未解析
                        for (int i = 0; i < entries.Length; i++)
                        {
                            TrainerEntry entry = entries[i];
                            PanelEntry pe = panels[i];
                            if (pe == null) continue;
                            // ★ AA脚本条目：显示当前注入状态
                            if (entry.IsAA)
                            {
                                continue;
                            }
                            long finalAddr;
                            string ptrDiag = ResolvePointerChain(entry, out finalAddr);
                            if (finalAddr == 0)
                            {
                                anyProblem = true;
                                // [r3] 符号槽为 0 是 AOB 符号脚本的正常初始态：需要游戏执行到被 hook 的指令才写入
                                bool waiting = ptrDiag.IndexOf("空指针") >= 0;
                                bool allocGone = ptrDiag.IndexOf("NewAddr=0") >= 0 || ptrDiag.IndexOf("未找到名为") >= 0;
                                string rowTxt = waiting ? "等待触发" : (allocGone ? "符号未就绪" : "解析失败(见状态栏)");
                                try
                                {
                                    if (pe.lblCurrent.InvokeRequired)
                                        pe.lblCurrent.Invoke(new Action(() => pe.lblCurrent.Text = rowTxt));
                                    else
                                        pe.lblCurrent.Text = rowTxt;
                                }
                                catch { }
                                string shortReason;
                                if (waiting)
                                    shortReason = "⚠ 等待触发：请在游戏里执行被 hook 的那条指令（教程第二关点几次「打我」），符号槽才会写入地址";
                                else if (allocGone)
                                    shortReason = "⚠ 符号未就绪：AA 脚本没激活或符号槽缺失，请点上方 [AOB] 行的开关重新启用";
                                else if (ptrDiag.IndexOf("读取地址") >= 0)
                                    shortReason = "⚠ 读取符号槽失败：可能连错进程，请点[进程切换]选到正在玩的窗口";
                                else
                                    shortReason = "⚠ 地址未解析：" + ptrDiag.Replace("\r", " ").Replace("\n", " ");
                                if (shortReason.Length > 120) shortReason = shortReason.Substring(0, 120);
                                if (shortReason != lastPtrStatus)
                                {
                                    lastPtrStatus = shortReason;
                                    UpdateStatus(shortReason, waiting ? Color.Orange : Color.Red);
                                }
                                ptrHadProblem = true;
                                continue;
                            }
                            int sz = GetValueSize(entry.VType);
                            byte[] buf = new byte[sz];
                            if (ReadMem(new IntPtr(finalAddr), buf, sz))
                            {
                                string valStr = FormatValue(buf, entry.VType);
                                try
                                {
                                    if (pe.lblCurrent.InvokeRequired)
                                        pe.lblCurrent.Invoke(new Action(() => pe.lblCurrent.Text = "当前：" + valStr));
                                    else
                                        pe.lblCurrent.Text = "当前：" + valStr;
                                }
                                catch { }
                                if (GetChecked(pe.chkFreeze))
                                {
                                    string txtVal = pe.txtValue.Text;
                                    byte[] freezeBytes = ParseValueBytes(txtVal, entry.VType);
                                    if (freezeBytes != null)
                                        WriteMem(new IntPtr(finalAddr), freezeBytes, freezeBytes.Length);
                                }
                            }
                            else
                            {
                                try
                                {
                                    if (pe.lblCurrent.InvokeRequired)
                                        pe.lblCurrent.Invoke(new Action(() => pe.lblCurrent.Text = "当前：??"));
                                    else
                                        pe.lblCurrent.Text = "当前：??";
                                }
                                catch { }
                            }
                        }
                        // [r3] 所有记录都恢复解析成功后，状态栏从诊断恢复成绿色连接信息
                        if (!anyProblem && ptrHadProblem)
                        {
                            ptrHadProblem = false;
                            lastPtrStatus = "";
                            if (connDiagInfo != "") UpdateStatus(connDiagInfo, Color.Green);
                        }
                        Thread.Sleep(100);
                    }
                }
                catch
                {
                    Thread.Sleep(500);
                }
            }
            ResetAllAA();
            bRunning = false;
            if (hProcess != IntPtr.Zero) CloseHandle(hProcess);
            hProcess = IntPtr.Zero;
        }

        protected override void OnFormClosing(FormClosingEventArgs e)
        {
            bStopping = true;
            ResetAllAA();
            if (workerThread != null && workerThread.IsAlive)
                workerThread.Join(1000);
__ANTI_THREAD_STOP__
            base.OnFormClosing(e);
        }
    }
}
]=]

    code = exSafeReplace(code, "__ENTRIES__", entriesBlock)
    code = exSafeReplace(code, "__PANEL_ROWS__", panelBlock)
    code = exSafeReplace(code, "__GAMELIB_INIT__", "")
    code = exSafeReplace(code, "__PROC_EXPR__", procExpr)
    code = exSafeReplace(code, "__TITLE_EXPR__", titleExpr)
    code = exSafeReplace(code, "__KNOWN_PID__", tostring(knownPID))
    code = exSafeReplace(code, "__OBF_DECRYPT__", obfDecryptCode)
    code = exSafeReplace(code, "__ANTI_THREAD_FIELD__", antiThreadField)
    code = exSafeReplace(code, "__ANTI_THREAD_START__", antiThreadStart)
    code = exSafeReplace(code, "__ANTI_THREAD_STOP__", antiThreadStop)
    code = exSafeReplace(code, "__ANTI_MONITOR__", antiDebugCode)
    code = exSafeReplace(code, "__SIGN_LABELS__", signLabelsCode)
    return code
end

  -- CE VarType → EXE 模板里 TrainerEntry 的 vtype 数字
  local VT = { vtByte = 0, vtWord = 1, vtDword = 2, vtQword = 3, vtSingle = 4, vtDouble = 5,
               vtString = 6, vtByteArray = 7, vtBinary = 8 }

  -- [AOB导出] CE 的 getNameFromAddress 对含 '-' 等字符的模块名会返回带引号的名字
  -- （如 "Tutorial-x86_64.exe"），生成 AA 脚本时又包一层引号，出现 ""..."" 双引号。
  -- C# 侧用 string.Equals(真实模块名, AOBModule) 比对，必须在这里剥掉引号，
  -- 否则模块范围扫描 / aobscanregion 的起止偏移全部失效，退化成不可靠的全进程扫描。
  local function exNormModule(s)
    s = tostring(s or "")
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    s = s:gsub('^"', ''):gsub('"$', '')
    s = s:gsub("^'", ''):gsub("'$", '')
    return s
  end

  -- 从 lastExportData（generate 时的 o 表）组装契约；不解析脚本文本
  local function exBuildContract()
    if lastHwbpMode then
      return nil, "当前是「硬件断点模式」生成的脚本：没有代码洞和原字节固化信息，不能导出 EXE/DLL；取消勾选重新生成后再导出"
    end
    local o = lastExportData
    if type(o) ~= "table" then return nil, "还没有生成脚本，先点[生成脚本]" end
    local script = lastPlainScript
    if not script or script == "" then return nil, "明文脚本为空，先点[生成脚本]" end
    if not lastScript then return nil, "上一次生成失败（脚本为空），请重新生成" end

    -- [r4] 放开多 alloc：动态收集 [ENABLE] 段内所有独立 alloc(name, size[, near]) 语句。
    --   行首锚定（^%s*alloc）天然排除 dealloc( 与 // 注释行。
    --   C# 侧 OnToggleAA 用 AllocBlocks.Length 通用循环一次 bigBlock 连续分配、逐块按
    --   CE 布局偏移映射 NewAddr、跨块 RipFixups 重定位，天然支持任意块数；Lua 抓字节
    --   也是 for i=1,#allocNames 通用循环。因此这里不再按块数拒绝，改为全部收集。
    --   大小支持 0x../十进制/$../..；三参数 alloc(name,size,near) 就近分配也照样收集。
    local enableBody = script:match("%[ENABLE%](.-)%[DISABLE%]") or script
    local dynNames, dynSizes = {}, {}
    for rawLine in enableBody:gmatch("[^\r\n]+") do
      local nm, szRaw = rawLine:match("^%s*alloc%s*%(%s*([%w_]+)%s*,%s*([^,%)]+)")
      if nm then
        local t = exTrim(szRaw or "")
        local sz = 0x100
        if t:match("^0[xX]") then sz = tonumber(t:sub(3), 16) or 0x100
        elseif t:match("^%$") then sz = tonumber(t:sub(2), 16) or 0x100
        else sz = tonumber(t) or 0x100 end
        dynNames[#dynNames + 1] = nm
        dynSizes[#dynSizes + 1] = sz
      end
    end
    -- 兜底：极端情况下脚本里没解析出 alloc，仍保证代码洞 + 符号槽两块
    if #dynNames == 0 then
      dynNames = { o.memSym, o.baseSym }
      dynSizes = { 0x100, 8 }
    end

    local origBytes = {}
    for hb in tostring(o.hookHex or ""):gmatch("%x%x") do
      origBytes[#origBytes + 1] = tonumber(hb, 16)
    end
    if #origBytes == 0 then return nil, "取不到原指令字节（hookHex 为空）" end

    local regionStart, regionEnd = 0, 0
    local pattern
    if o.offHex then
      regionStart = tonumber(o.offHex, 16) or 0
      regionEnd   = tonumber(o.offStopHex, 16) or (regionStart + #origBytes + 16)
      pattern = o.hookHex                       -- region 模式：脚本本身用原指令字节作特征码
    else
      pattern = o.pattern or o.hookHex          -- module 模式：用加长后的唯一特征码
    end
    pattern = tostring(pattern):gsub("%s+", " "):gsub("^%s+", ""):gsub("%s+$", "")

    return {
      hookSym    = o.hookSym,
      baseSym    = o.baseSym,
      memSym     = o.memSym,
      aobPattern = pattern,
      aobModule  = exNormModule(o.module),
      origBytes  = origBytes,
      allocNames = dynNames,                    -- [r4] 全部 alloc 块，顺序与脚本一致，第一个是代码洞
      allocSizes = dynSizes,
      allocCount = #dynNames,
      regionStartOff = regionStart,
      regionEndOff   = regionEnd,
      desc       = tostring(o.desc or o.baseSym),
      recordType = o.recordType or "vtDword",
      script     = script,
    }
  end

  -- [r4] CE VarType → 中文类型名（列表显示用）
  local TYPE_NAME = { [0]="1字节", [1]="2字节", [2]="4字节", [3]="8字节", [4]="单浮点",
                      [5]="双浮点", [6]="字符串", [7]="字节数组", [8]="二进制", [11]="AA脚本" }

  -- [r4] 扫描 CE 地址列表的全部条目，映射成可直接生成 TrainerEntry 的 rows。
  --   移植原版 scanAddressList 的字段映射，裁掉 parseFullAAScript 文本解析 / dataAOB 协议，
  --   并增强「AOB 符号名」识别：静态地址用 BaseResolvedAddr、模块+偏移用 ModuleName+ModuleOffset、
  --   AOB 符号/自定义符号用 AllocSymbolName（用户约定指针基址填 AOB 符号名）。
  local function exScanAddressList(contract)
    local rows = {}
    local okAL, al = pcall(function() return getAddressList() end)
    if not okAL or not al then return rows end
    local count = al.Count or 0

    -- 当前契约登记的 alloc 符号名（小写集合）
    local symSet = {}
    local function addSym(s) if s and s ~= "" then symSet[tostring(s):lower()] = true end end
    addSym(contract.hookSym); addSym(contract.baseSym); addSym(contract.memSym)
    for _, n in ipairs(contract.allocNames or {}) do addSym(n) end

    for i = 0, count - 1 do
      local okMR, mr = pcall(function() return al.getMemoryRecord(i) end)
      if okMR and mr then
        local desc, addrStr, vtype, recType, offCount, curVal = "", "", 2, 2, 0, ""
        pcall(function() desc = tostring(mr.Description or "") end)
        pcall(function() addrStr = tostring(mr.Address or "") end)
        pcall(function() vtype = tonumber(mr.VarType) or tonumber(mr.Type) or 2 end)
        pcall(function() recType = tonumber(mr.Type) or vtype end)
        pcall(function() offCount = tonumber(mr.OffsetCount) or 0 end)
        pcall(function() curVal = tostring(mr.Value or "") end)
        local isAA = (recType == 11) or (recType == 14) or (vtype == 11)
        pcall(function() if type(vtAutoAssembler) == "number" then
          isAA = isAA or (recType == vtAutoAssembler) end end)

        -- 指针链偏移：CE 的 Offset[0] 是最后一级，需反转
        local offsets = {}
        if offCount > 0 then
          local tmp = {}
          for j = 0, offCount - 1 do
            local o = 0
            pcall(function() o = tonumber(mr.Offset[j]) or 0 end)
            tmp[#tmp + 1] = o
          end
          for j = #tmp, 1, -1 do offsets[#offsets + 1] = tmp[j] end
        end

        -- 地址串清洗：去掉 CE 给含 '-' 模块名加的引号、P-> 前缀
        local addrClean = tostring(addrStr)
        addrClean = addrClean:gsub('^"', ''):gsub('"%s*%+', '+'):gsub('"', '')
        addrClean = addrClean:gsub('^P%s*%-%s*>%s*', '')
        local modPart = addrClean:match("^([^+%s]+)") or ""
        local offPart = addrClean:match("%+(%S+)$") or ""
        local offNum = 0
        if offPart ~= "" then
          if offPart:match("^0[xX]") then offNum = tonumber(offPart) or 0
          else offNum = tonumber(offPart, 16) or tonumber(offPart) or 0 end
        end

        local allocSymbol, moduleName, moduleOffset, baseResolvedAddr = "", "", 0, 0
        local kind
        local isHexAddr = modPart ~= "" and modPart:match("^%x+$") ~= nil
        local isModule  = (modPart:match("%.[eEdD][xX][eE]$") ~= nil) or (modPart:match("%.[dD][lL][lL]$") ~= nil)
        local nativeMod = ""
        pcall(function() nativeMod = tostring(mr.ModuleName or "") end)
        if nativeMod ~= "" and not symSet[nativeMod:lower()] and not nativeMod:lower():match("^aob") then
          isModule = true
        end

        if symSet[modPart:lower()] then
          allocSymbol = modPart; moduleOffset = offNum; kind = "AOB符号"
        elseif isHexAddr and offPart == "" and #offsets == 0 then
          pcall(function() baseResolvedAddr = tonumber(getAddress(addrStr)) or 0 end)
          if baseResolvedAddr == 0 then
            pcall(function() baseResolvedAddr = tonumber(mr.CurrentAddress) or 0 end)
          end
          kind = "静态地址"
        elseif isModule then
          moduleName = modPart; moduleOffset = offNum; kind = "模块+偏移"
        elseif modPart ~= "" and not isHexAddr then
          -- 非十六进制、非模块 → 视作符号名（用户约定：指针基址填 AOB 符号名）
          allocSymbol = modPart; moduleOffset = offNum; kind = "符号记录"
        else
          pcall(function() baseResolvedAddr = tonumber(getAddress(addrStr)) or 0 end)
          kind = "静态地址"
        end
        if #offsets > 1 and kind ~= "AOB符号" and kind ~= "符号记录" then kind = "指针链" end
        if isAA then kind = "注入脚本" end   -- 对话框显示「[必需] 注入脚本」，AA 行不生成独立 entry

        local offDisp = "-"
        if #offsets > 0 then
          local p = {}
          for _, o in ipairs(offsets) do p[#p + 1] = string.format("%X", o) end
          offDisp = table.concat(p, " → ")
        elseif moduleOffset ~= 0 then
          offDisp = "+" .. string.format("%X", moduleOffset)
        end

        rows[#rows + 1] = {
          description = desc, addressStr = addrStr,
          currentAddr = 0, baseResolvedAddr = baseResolvedAddr,
          vtype = vtype, offsets = offsets,
          moduleName = moduleName, moduleOffset = moduleOffset,
          allocSymbol = allocSymbol,
          isAA = false, aaEnabled = false, aaParsed = {}, currentValue = curVal,
          dataAobPattern = "", dataAobOffset = 0,
          -- UI 元信息（下划线前缀，不进 C# 模板）
          _isAA = isAA, _kind = kind, _desc = desc, _addr = addrStr,
          _offDisp = offDisp, _typeDisp = TYPE_NAME[vtype] or ("类型" .. tostring(vtype)),
          _val = curVal, _checked = true,
        }
      end
    end
    return rows
  end

  -- [r4] 弹出「选择要生成的条目」勾选对话框；返回 rows 或 nil(取消)。
  --   AA 注入脚本行标注[必需]并锁定勾选：它是所有符号记录的前提，取消会产出必然失败的 EXE。
  local function exShowSelectDialog(contract, mode)
    local rows = exScanAddressList(contract)
    local dlg = createForm(false)
    dlg.Caption = (mode == "dll") and "选择要生成的条目 — 注入 DLL 导出"
      or "选择要生成的条目 — AOB 独立 EXE 导出"
    dlg.Width = 760
    dlg.Height = 540
    if type(poScreenCenter) ~= "nil" then dlg.Position = poScreenCenter end

    local lblTop = createLabel(dlg)
    lblTop.Caption = "勾选要生成进独立 EXE 的条目（默认全选）。[必需] 为 AOB 注入脚本，恒定包含；"
      .. "符号记录请填 AOB 符号名，模块+偏移 / 静态地址记录均可一起勾选。"
    lblTop.Left = 12 lblTop.Top = 10 lblTop.Width = 720 lblTop.Height = 34
    pcall(function() lblTop.WordWrap = true end)

    local lv = createListView(dlg)
    lv.Left = 12 lv.Top = 50 lv.Width = 720 lv.Height = 392
    lv.View = 3
    lv.Checkboxes = true
    lv.RowSelect = true
    lv.GridLines = true
    local cols = { {"来源", 96}, {"描述", 150}, {"地址", 190}, {"偏移", 96}, {"类型", 78}, {"当前值", 90} }
    for c = 1, #cols do
      lv.Columns.Add()
      lv.Columns[c - 1].Caption = cols[c][1]
      lv.Columns[c - 1].Width = cols[c][2]
    end

    local function fill()
      lv.Items.Clear()
      for _, r in ipairs(rows) do
        local it = lv.Items.Add()
        it.Checked = true
        it.Caption = r._isAA and ("[必需] " .. r._kind) or r._kind
        it.SubItems.Add(r._desc)
        it.SubItems.Add(r._addr)
        it.SubItems.Add(r._offDisp)
        it.SubItems.Add(r._typeDisp)
        it.SubItems.Add(r._val)
      end
    end
    fill()

    local confirmed = false
    local function applyChecks()
      for i = 0, lv.Items.Count - 1 do
        local r = rows[i + 1]
        if r then r._checked = (lv.Items[i].Checked == true) end
      end
      -- AA 注入脚本恒定包含
      for _, r in ipairs(rows) do if r._isAA then r._checked = true end end
    end

    local btnRefresh = createButton(dlg)
    btnRefresh.Caption = "刷新列表" btnRefresh.Left = 12 btnRefresh.Top = 452 btnRefresh.Width = 100 btnRefresh.Height = 30
    btnRefresh.OnClick = function()
      local fresh = exScanAddressList(contract)
      rows = fresh
      fill()
    end
    local btnAll = createButton(dlg)
    btnAll.Caption = "全选" btnAll.Left = 120 btnAll.Top = 452 btnAll.Width = 76 btnAll.Height = 30
    btnAll.OnClick = function() for i = 0, lv.Items.Count - 1 do lv.Items[i].Checked = true end end
    local btnNone = createButton(dlg)
    btnNone.Caption = "全不选" btnNone.Left = 204 btnNone.Top = 452 btnNone.Width = 76 btnNone.Height = 30
    btnNone.OnClick = function() for i = 0, lv.Items.Count - 1 do lv.Items[i].Checked = false end end
    local btnOK = createButton(dlg)
    btnOK.Caption = (mode == "dll") and "生成 DLL" or "生成独立 EXE" btnOK.Left = 484 btnOK.Top = 452 btnOK.Width = 140 btnOK.Height = 30
    btnOK.OnClick = function() applyChecks() confirmed = true dlg.close() end
    local btnCancel = createButton(dlg)
    btnCancel.Caption = "取消" btnCancel.Left = 632 btnCancel.Top = 452 btnCancel.Width = 100 btnCancel.Height = 30
    btnCancel.OnClick = function() dlg.close() end

    dlg.OnClose = function() return caFree end
    pcall(function() dlg.showModal() end)
    if not confirmed then return nil end
    return rows
  end

  -- TrainerEntry 组装：AA 注入脚本条目（负责注入）+ 勾选的记录。
  --   selectedRows == nil → 回退「契约 2 条」旧行为（供无 UI 的静态验证 / 兼容旧调用）。
  local function exMakeEntries(contract, parsed, selectedRows)
    -- 定位信息一律以契约为准，避免 aaParsed 被其它路径改写后与 region 配置不一致
    parsed.aobPattern    = contract.aobPattern
    parsed.aobModule     = contract.aobModule
    parsed.aobSymbolName = contract.hookSym
    local vt = VT[contract.recordType] or 2
    local aaEntry = {
      description = "[AOB] " .. contract.desc, addressStr = "", currentAddr = 0, baseResolvedAddr = 0,
      vtype = vt, offsets = {}, moduleName = "", moduleOffset = 0, allocSymbol = "",
      isAA = true, aaEnabled = true, aaParsed = parsed, currentValue = "",
      dataAobPattern = "", dataAobOffset = 0,
      regionStartOff = contract.regionStartOff, regionEndOff = contract.regionEndOff,
    }
    if selectedRows == nil then
      local recEntry = {
        description = contract.desc, addressStr = contract.baseSym, currentAddr = 0, baseResolvedAddr = 0,
        vtype = vt, offsets = { 0 }, moduleName = "", moduleOffset = 0,
        allocSymbol = contract.baseSym,          -- → ResolvePointerChain 的 AllocSymbolName 路径
        isAA = false, aaEnabled = false, aaParsed = {}, currentValue = "",
        dataAobPattern = "", dataAobOffset = 0,
      }
      return { aaEntry, recEntry }
    end
    local entries = { aaEntry }
    for _, r in ipairs(selectedRows) do
      if r._checked and not r._isAA then
        entries[#entries + 1] = {
          description = r.description, addressStr = r.addressStr,
          currentAddr = 0, baseResolvedAddr = r.baseResolvedAddr,
          vtype = r.vtype, offsets = r.offsets,
          moduleName = r.moduleName, moduleOffset = r.moduleOffset,
          allocSymbol = r.allocSymbol,
          isAA = false, aaEnabled = false, aaParsed = {}, currentValue = r.currentValue,
          dataAobPattern = "", dataAobOffset = 0,
        }
      end
    end
    return entries
  end

  local function exProcessInfo()
    local pid = 0
    pcall(function() pid = tonumber(getOpenedProcessID()) or 0 end)
    local name = ""
    pcall(function()
      local pl = getProcesslist()
      if pl then for k, v in pairs(pl) do if tonumber(k) == pid then name = tostring(v) break end end end
    end)
    if name == "" and type(lastExportData) == "table" then name = tostring(lastExportData.module or "") end
    if name == "" then name = "Trainer" end
    return name, pid
  end

  local function exCompile(csCode, procName)
    local csc = exFindCSC()
    if not csc then return nil, "未找到 csc.exe（需要 .NET Framework 4.x）" end
    local dir = exGetDesktop() .. "\\CE_Trainer_Output"
    exCreateDir(dir)
    local csPath = dir .. "\\trainer.cs"
    local manifestPath = dir .. "\\app.manifest"
    local errPath = dir .. "\\compile_errors.txt"
    local batPath = dir .. "\\compile.bat"
    local resultPath = dir .. "\\result.txt"
    local manifest = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><assembly xmlns="urn:schemas-microsoft-com:asm.v1" manifestVersion="1.0"><trustInfo xmlns="urn:schemas-microsoft-com:asm.v2"><security><requestedPrivileges xmlns="urn:schemas-microsoft-com:asm.v3"><requestedExecutionLevel level="asInvoker" uiAccess="false"/></requestedPrivileges></security></trustInfo></assembly>'
    if not exWriteFile(csPath, csCode, true) then return nil, "写入 trainer.cs 失败：" .. csPath end
    exWriteFile(manifestPath, manifest, false)
    local safe = procName:gsub("[^%w%.%-_]", "")
    if safe == "" or safe == ".exe" then safe = "Trainer" end
    if safe:lower():match("%.exe$") then safe = safe:sub(1, -5) end
    local exePath = dir .. "\\" .. safe .. ".exe"
    pcall(os.remove, resultPath) pcall(os.remove, exePath) pcall(os.remove, errPath)
    local cmd = '"' .. csc .. '" /nologo /optimize /platform:anycpu /target:winexe /unsafe /codepage:65001'
      .. ' /win32manifest:"' .. manifestPath .. '" /r:System.dll /r:System.Windows.Forms.dll /r:System.Drawing.dll'
      .. ' /out:"' .. exePath .. '" "' .. csPath .. '"'
    local bat = cmd .. ' > "' .. errPath .. '" 2>&1\r\nif %errorlevel%==0 echo OK > "' .. resultPath .. '"\r\n'
    if not exWriteFile(batPath, bat, false) then return nil, "写入 compile.bat 失败" end
    shellExecute(batPath, "", dir, 0)
    local ok = false
    for i = 1, 60 do
      sleep(1000)
      pcall(processMessages)
      local rf = io.open(resultPath, "r")
      if rf then local c = rf:read("*a") rf:close() if c and c:match("OK") then ok = true break end end
      local ef = io.open(exePath, "rb")
      if ef then ef:close() ok = true break end
    end
    pcall(os.remove, csPath) pcall(os.remove, batPath) pcall(os.remove, manifestPath) pcall(os.remove, resultPath)
    if ok then pcall(os.remove, errPath) return exePath, nil end
    local msg = "编译失败"
    local ef = io.open(errPath, "r")
    if ef then local c = ef:read("*a") ef:close() if c and #c > 0 then msg = msg .. "：" .. c:sub(1, 300) end end
    return nil, msg
  end

  function AOBEXE.onExport()
    log("============== [独立 EXE 导出] ==============")
    local contract, err = exBuildContract()
    if not contract then log("[EXE][错误] " .. tostring(err)) return end

    -- 前提：脚本已在 CE 里勾选激活（预汇编抓字节路径）
    local okAddr, inj = pcall(getAddress, contract.hookSym)
    if not okAddr or type(inj) ~= "number" or inj == 0 then
      log("[EXE][错误] 符号 " .. tostring(contract.hookSym) .. " 未注册：先把脚本[加到列表]并勾选激活，再点[生成独立 EXE]")
      return
    end
    log(string.format("[EXE] 注入点 %s = 0x%X（脚本已激活）", contract.hookSym, inj))
    if contract.regionEndOff > contract.regionStartOff then
      log(string.format("[EXE] 定位：aobscanregion %s+0x%X ~ +0x%X，特征码 [%s]",
        contract.aobModule, contract.regionStartOff, contract.regionEndOff, contract.aobPattern))
    else
      log(string.format("[EXE] 定位：aobscanmodule %s，特征码 [%s]", contract.aobModule, contract.aobPattern))
    end

    local okParse, parsed = pcall(exParseAOBScript, contract.script, contract)
    if not okParse then log("[EXE][错误] 预汇编解析异常：" .. tostring(parsed)) return end
    if not parsed.preAssembled or #parsed.allocBlocks < 1 then
      log(string.format("[EXE][错误] 预汇编抓字节失败（固化 %d 个 alloc 块）：确认脚本已勾选激活、aobscan 标签可读、原指令字节完整",
        #parsed.allocBlocks))
      return
    end
    log(string.format("[EXE] 已固化 %d 个 alloc 块 / 原指令 %d 字节 / returnhere 修复点 [%s]",
      #parsed.allocBlocks, parsed.origInstrLen, tostring(parsed.returnHereFixups or "")))
    if (contract.allocCount or 0) > 2 then
      log(string.format("[EXE] 脚本含 %d 个 alloc 块（附加选项已放开）：逐块固化 + 运行时逐块分配重定位；临时块若依赖未注册符号，请真机确认",
        contract.allocCount))
    end

    -- [r4] 弹出勾选列表：读取 CE 地址列表全部条目，用户选择后再生成为 EXE
    local okSel, selRows = pcall(exShowSelectDialog, contract)
    if not okSel then
      log("[EXE][错误] 打开条目选择窗口失败：" .. tostring(selRows) .. "；回退为「仅注入脚本 + 当前符号记录」")
      selRows = nil
    elseif selRows == nil then
      log("[EXE] 已取消（未选择任何条目，未生成 EXE）")
      return
    end

    local procName, pid = exProcessInfo()
    log(string.format("[EXE] 目标进程：%s（当前 PID %d）", procName, pid))
    local entries = exMakeEntries(contract, parsed, selRows)
    if selRows ~= nil then
      local nRec, nUnknown = 0, 0
      for _, r in ipairs(selRows) do
        if r._checked and not r._isAA then
          nRec = nRec + 1
          if r._kind == "符号记录" then nUnknown = nUnknown + 1 end
        end
      end
      log(string.format("[EXE] 已选择 %d 条记录（+1 条注入脚本），共 %d 个 TrainerEntry", nRec, #entries))
      if nUnknown > 0 then
        log(string.format("[EXE][注意] %d 条记录的地址是「契约符号之外」的符号名。本次只固化当前脚本的符号 [%s]；"
          .. "若这些符号来自别的脚本，独立 EXE 找不到对应 alloc 块会显示「符号未就绪」。请用当前脚本的符号名重建记录。",
          nUnknown, tostring(contract.baseSym)))
      end
    end
    local okCS, cs = pcall(exBuildCSharpCode, procName, 0, entries)
    if not okCS then log("[EXE][错误] 生成 C# 源码失败：" .. tostring(cs)) return end
    local _, left = cs:gsub("__[A-Z_]+__", "")
    if left > 0 then log("[EXE][错误] C# 模板残留 " .. left .. " 个未替换占位符，已中止") return end
    log(string.format("[EXE] C# 源码 %d 字节，开始编译（最长 60 秒）…", #cs))
    local outPath, cerr = exCompile(cs, procName)
    if not outPath then
      log("[EXE][错误] " .. tostring(cerr))
      log("[EXE] 排查：把 桌面\\CE_Trainer_Output\\compile_errors.txt 回贴")
      return
    end
    log("[EXE] 生成完成：" .. outPath)
    log("[EXE] 验收：完全退出 CE 后单独运行该 EXE，看记录当前值 / 改值 / 锁定是否生效")
    log("==============================================")
  end

  -- ============================================================
  -- [注入 DLL 导出模块] —— 原生 C++（cl / gcc 自动探测），不依赖 .NET
  -- ------------------------------------------------------------
  -- 与「独立 EXE」共用同一套前提：脚本必须已[加到列表]并勾选激活，
  -- 导出只固化 alloc 块字节与重定位信息，不在导出时重新汇编脚本。
  -- 产物：桌面\AOB_DLL_Output\<进程名>.cpp / .dll / build.bat
  -- ============================================================
  local CPP_BODY = [==[
// ============================================================================
//  AOB Hook DLL —— 由「AOB 符号脚本生成器」生成，注入目标进程后自动挂钩
@@SUMMARY@@
//
//  编译：见同目录 build.bat / 生成日志里的编译器提示
//  配置：与 DLL 同目录放 aob_dll.ini（可热改，每秒重读）
//          [0]                ; 条目序号
//          freeze=1           ; 1=持续写入 value
//          value=100          ; 十进制，或 0x 十六进制；浮点类型直接写小数
//  状态：同目录 aob_dll_status.txt（每秒刷新，可被外部工具轮询）
//  日志：OutputDebugString（DebugView 可看）
// ============================================================================
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <tlhelp32.h>
#include <psapi.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#ifdef _MSC_VER
#pragma comment(lib, "psapi.lib")
#pragma comment(lib, "kernel32.lib")
#pragma comment(lib, "user32.lib")
#endif

#define AOB_EXPORT extern "C" __declspec(dllexport)
#define AOB_MAXBLOCKS 8
#define AOB_MAXVALUES 32
#define AOB_MAXOFF 8
#define AOB_MAXFIX 512

// ---------------------------------------------------------------------------
// 生成时固化的数据
// ---------------------------------------------------------------------------
static const char* kTargetExe  = "@@TARGET@@";
static const char* kModuleName = "@@MODULE@@";
static const char* kGenTag     = "@@TAG@@";
static const int   kIs64       = @@IS64@@;

static const uint64_t kRegionStart = @@RSTART@@ULL;
static const uint64_t kRegionEnd   = @@REND@@ULL;
static const uint64_t kInjectRva   = @@RVA@@ULL;

static const int kOrigLen = @@ORIGLEN@@;
static const unsigned char kOrigBytes[] = { @@ORIGBYTES@@ };

static const int kPatLen = @@PATLEN@@;
static const unsigned char kPatBytes[] = { @@PATBYTES@@ };
static const unsigned char kPatMask[]  = { @@PATMASKS@@ };

struct AobBlock { const char* name; uint32_t ceOff; uint32_t size; };
static const AobBlock kBlocks[] = {
@@BLOCKS@@
};
static const int kBlockCount = @@BLOCKCOUNT@@;

static const int kCaveLen = @@CAVELEN@@;
static const unsigned char kCaveBytes[] = { @@CAVEBYTES@@ };

// 重定位项：把 CE 里代码洞的绝对/相对地址改成运行时新代码洞地址
enum { FIX_ABS = 0, FIX_INJ = 1, FIX_MOD = 2, FIX_BLOCK = 3 };
struct AobFix {
  uint32_t at;      // 字段在代码洞内的偏移
  uint32_t end;     // 所在指令结束偏移（算 rel 用）
  uint8_t  width;   // 1 = rel8，4 = rel32/绝对
  uint8_t  mode;    // FIX_ABS / FIX_INJ / FIX_MOD / FIX_BLOCK
  uint8_t  abs;     // 1 = 写绝对值，0 = 写相对偏移
  uint8_t  block;   // FIX_BLOCK 时的目标块序号
  uint64_t value;   // 绝对地址 / 注入点内偏移 / 模块内偏移 / 块内偏移
  const char* mod;  // FIX_MOD 时的模块名
};
static const AobFix kFixes[] = {
@@FIXES@@
};
static const int kFixCount = @@FIXCOUNT@@;

enum { VT_BYTE = 0, VT_WORD = 1, VT_DWORD = 2, VT_QWORD = 3,
       VT_SINGLE = 4, VT_DOUBLE = 5, VT_STRING = 6, VT_ARRAY = 7, VT_BINARY = 8 };
struct AobValue {
  const char* desc;
  const char* allocSym;   // 非空：基址 = 该 alloc 块 + modOff
  const char* modName;    // 非空：基址 = 模块基址 + modOff
  int64_t     modOff;
  uint64_t    fallback;   // 静态地址兜底
  int         vtype;
  int         nOff;
  int64_t     off[AOB_MAXOFF];
};
static const AobValue kValues[] = {
@@VALUES@@
};
static const int kValueCount = @@VALUECOUNT@@;

// ---------------------------------------------------------------------------
// 运行期状态
// ---------------------------------------------------------------------------
static HMODULE  g_hinst = 0;
static HANDLE   g_proc  = 0;
static int      g_self  = 0;
static volatile int g_stop = 0;
static volatile int g_active = 0;
static uint64_t g_modBase = 0, g_modSize = 0;
static uint64_t g_inject = 0, g_cave = 0, g_caveSize = 0;
static uint64_t g_blockBase[AOB_MAXBLOCKS];
static CRITICAL_SECTION g_cs;
static char     g_statusPath[MAX_PATH];
static char     g_iniPath[MAX_PATH];
static char     g_lastState[128] = "init";

struct ValueState { int freeze; int freezeLen; unsigned char freezeBuf[16]; };
static ValueState g_vs[AOB_MAXVALUES];

static int s_quietLog = 0;

static void logf(const char* fmt, ...) {
  if (s_quietLog) return;
  char buf[1024];
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(buf, sizeof(buf), fmt, ap);
  va_end(ap);
  OutputDebugStringA("[AOB] ");
  OutputDebugStringA(buf);
  OutputDebugStringA("\n");
}

static int ieq(const char* a, const char* b) {
  if (!a || !b) return 0;
  while (*a && *b) {
    char x = *a, y = *b;
    if (x >= 'A' && x <= 'Z') x = (char)(x - 'A' + 'a');
    if (y >= 'A' && y <= 'Z') y = (char)(y - 'A' + 'a');
    if (x != y) return 0;
    ++a; ++b;
  }
  return *a == 0 && *b == 0;
}

// ---------------------------------------------------------------------------
// 内存读写（本进程 / 跨进程统一入口）
// ---------------------------------------------------------------------------
static int memRead(uint64_t addr, void* buf, size_t n) {
  if (!addr || !n) return 0;
  if (g_self) { memcpy(buf, (const void*)(uintptr_t)addr, n); return 1; }
  SIZE_T got = 0;
  if (!ReadProcessMemory(g_proc, (LPCVOID)(uintptr_t)addr, buf, n, &got)) return 0;
  return got == n;
}

static int memWrite(uint64_t addr, const void* buf, size_t n) {
  if (!addr || !n) return 0;
  DWORD old = 0;
  int self = g_self;
  HANDLE h = self ? GetCurrentProcess() : g_proc;
  if (!VirtualProtectEx(h, (LPVOID)(uintptr_t)addr, n, PAGE_EXECUTE_READWRITE, &old)) {
    /* 有些页本来就 RW，保护修改失败也继续试写 */
  }
  int ok = 0;
  if (self) { memcpy((void*)(uintptr_t)addr, buf, n); ok = 1; }
  else {
    SIZE_T wrote = 0;
    ok = WriteProcessMemory(g_proc, (LPVOID)(uintptr_t)addr, buf, n, &wrote) && wrote == n;
  }
  DWORD tmp = 0;
  if (old) VirtualProtectEx(h, (LPVOID)(uintptr_t)addr, n, old, &tmp);
  FlushInstructionCache(h, (LPCVOID)(uintptr_t)addr, n);
  return ok;
}

// ---------------------------------------------------------------------------
// 模块定位
// ---------------------------------------------------------------------------
static uint64_t moduleBaseOf(const char* name) {
  if (!name || !name[0]) return 0;
  if (g_modBase && ieq(name, kModuleName)) return g_modBase;
  HMODULE m = 0;
  if (g_self) {
    m = GetModuleHandleA(name);
    if (!m && ieq(name, kModuleName)) m = GetModuleHandleA(NULL);
  } else {
    HMODULE mods[1024];
    DWORD need = 0;
    if (EnumProcessModulesEx(g_proc, mods, (DWORD)sizeof(mods), &need, LIST_MODULES_ALL)) {
      DWORD cnt = need / (DWORD)sizeof(HMODULE);
      if (cnt > 1024) cnt = 1024;
      for (DWORD i = 0; i < cnt; ++i) {
        char nm[MAX_PATH] = {0};
        if (GetModuleBaseNameA(g_proc, mods[i], nm, MAX_PATH) && ieq(nm, name)) { m = mods[i]; break; }
      }
    }
  }
  return (uint64_t)(uintptr_t)m;
}

static int moduleRangeOf(uint64_t base, uint64_t* sizeOut) {
  MODULEINFO info;
  memset(&info, 0, sizeof(info));
  HANDLE h = g_self ? GetCurrentProcess() : g_proc;
  if (!GetModuleInformation(h, (HMODULE)(uintptr_t)base, &info, sizeof(info))) return 0;
  *sizeOut = (uint64_t)info.SizeOfImage;
  return *sizeOut != 0;
}

static DWORD findProcessByName(const char* exe) {
  HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
  if (snap == INVALID_HANDLE_VALUE) return 0;
  PROCESSENTRY32 pe;
  memset(&pe, 0, sizeof(pe));
  pe.dwSize = sizeof(pe);
  DWORD pid = 0;
  if (Process32First(snap, &pe)) {
    do {
      if (ieq(pe.szExeFile, exe)) { pid = pe.th32ProcessID; break; }
    } while (Process32Next(snap, &pe));
  }
  CloseHandle(snap);
  return pid;
}

static int attachTarget(void) {
  HMODULE m = GetModuleHandleA(kModuleName);
  if (m) { g_self = 1; g_proc = GetCurrentProcess(); }
  else if (ieq(kModuleName, kTargetExe) && GetModuleHandleA(NULL)) {
    g_self = 1; g_proc = GetCurrentProcess(); m = GetModuleHandleA(NULL);
  }
  if (!g_self) {
    DWORD pid = findProcessByName(kTargetExe);
    if (!pid) { logf("找不到目标进程 %s，且本进程内也没有 %s", kTargetExe, kModuleName); return 0; }
    g_proc = OpenProcess(PROCESS_ALL_ACCESS, FALSE, pid);
    if (!g_proc)
      g_proc = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ | PROCESS_VM_WRITE | PROCESS_VM_OPERATION,
                          FALSE, pid);
    if (!g_proc) { logf("OpenProcess(%s, pid=%lu) 失败（权限不足？试管理员）", kTargetExe, (unsigned long)pid); return 0; }
    g_self = 0;
    uint64_t mb = moduleBaseOf(kModuleName);
    if (!mb) { logf("目标进程里找不到模块 %s", kModuleName); return 0; }
    g_modBase = mb;
    logf("跨进程模式：pid=%lu 模块=%s 基址=0x%llX", (unsigned long)pid, kModuleName,
         (unsigned long long)mb);
  } else {
    g_modBase = (uint64_t)(uintptr_t)m;
    logf("本进程模式：模块=%s 基址=0x%llX", kModuleName, (unsigned long long)g_modBase);
  }
  if (!moduleRangeOf(g_modBase, &g_modSize)) { logf("取模块大小失败"); return 0; }
  logf("模块范围 0x%llX - 0x%llX（%llu KB）", (unsigned long long)g_modBase,
       (unsigned long long)(g_modBase + g_modSize), (unsigned long long)(g_modSize / 1024));
  return 1;
}

// ---------------------------------------------------------------------------
// 特征码扫描（模块范围内，带通配）
// ---------------------------------------------------------------------------
static int scanPattern(uint64_t* hits, int maxHits) {
  int found = 0;
  uint64_t start = g_modBase + (kRegionStart ? kRegionStart : 0);
  uint64_t end = (kRegionEnd > kRegionStart) ? (g_modBase + kRegionEnd) : (g_modBase + g_modSize);
  if (end <= start || kPatLen <= 0) return 0;
  const size_t CHUNK = 0x100000;
  unsigned char* buf = (unsigned char*)malloc(CHUNK + 64);
  if (!buf) return 0;
  uint64_t pos = start;
  while (pos < end && found < maxHits) {
    size_t want = (size_t)((end - pos) < (uint64_t)CHUNK ? (end - pos) : (uint64_t)CHUNK);
    size_t gotLen = 0;
    if (g_self) { memcpy(buf, (const void*)(uintptr_t)pos, want); gotLen = want; }
    else {
      SIZE_T got = 0;
      if (ReadProcessMemory(g_proc, (LPCVOID)(uintptr_t)pos, buf, want, &got) && got == want) {
        gotLen = want;
      } else {
        /* 整块读失败（中间有不可读页）：拆成 4KB 逐页读到第一个空洞为止 */
        size_t pages = (want + 0xFFF) / 0x1000;
        size_t ok = 0;
        for (size_t pg = 0; pg < pages; ++pg) {
          SIZE_T g2 = 0;
          if (!ReadProcessMemory(g_proc, (LPCVOID)(uintptr_t)(pos + pg * 0x1000),
                                 buf + pg * 0x1000, 0x1000, &g2) || g2 == 0) break;
          ok = (pg + 1) * 0x1000;
        }
        gotLen = ok < want ? ok : want;
      }
    }
    if (gotLen >= (size_t)kPatLen) {
      for (size_t i = 0; i + (size_t)kPatLen <= gotLen; ++i) {
        int ok = 1;
        for (int j = 0; j < kPatLen; ++j) {
          if (kPatMask[j] && buf[i + (size_t)j] != kPatBytes[j]) { ok = 0; break; }
        }
        if (ok) {
          hits[found++] = pos + (uint64_t)i;
          if (found >= maxHits) break;
        }
      }
    }
    if (gotLen == 0) { pos += 0x1000; continue; }
    pos += (uint64_t)gotLen;
    if (pos + (uint64_t)kPatLen <= end) pos -= (uint64_t)(kPatLen - 1);
  }
  free(buf);
  return found;
}

// ---------------------------------------------------------------------------
// 在注入点附近分配（E9 只有 ±2GB）
// ---------------------------------------------------------------------------
static uint64_t allocNear(uint64_t nearAddr, uint64_t size) {
  const uint64_t GRAN = 0x10000ULL;
  const uint64_t LIMIT = 0x7FFE0000ULL;
  HANDLE h = g_self ? GetCurrentProcess() : g_proc;
  MEMORY_BASIC_INFORMATION mbi;
  uint64_t up = (nearAddr + GRAN - 1) & ~(GRAN - 1);
  uint64_t down = nearAddr & ~(GRAN - 1);
  uint64_t steps = LIMIT / GRAN;
  for (uint64_t d = 0; d <= steps; ++d) {
    for (int dir = 0; dir < 2; ++dir) {
      uint64_t cand;
      if (dir == 0) cand = up + d * GRAN;
      else { if (down < d * GRAN) continue; cand = down - d * GRAN; }
      if (!cand) continue;
      memset(&mbi, 0, sizeof(mbi));
      if (VirtualQueryEx(h, (LPCVOID)(uintptr_t)cand, &mbi, sizeof(mbi)) != sizeof(mbi)) continue;
      if (mbi.State != MEM_FREE) continue;
      if ((uint64_t)mbi.RegionSize < size) continue;
      LPVOID p = VirtualAllocEx(h, (LPVOID)(uintptr_t)cand, (SIZE_T)size,
                               MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
      if (p) return (uint64_t)(uintptr_t)p;
    }
  }
  LPVOID p = VirtualAllocEx(h, NULL, (SIZE_T)size, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  return (uint64_t)(uintptr_t)p;
}

// ---------------------------------------------------------------------------
// 代码洞重定位
// ---------------------------------------------------------------------------
static int findBlock(const char* name) {
  for (int i = 0; i < kBlockCount; ++i) if (ieq(kBlocks[i].name, name)) return i;
  return -1;
}

static int applyFixes(unsigned char* cave, uint64_t caveBase) {
  int bad = 0;
  for (int i = 0; i < kFixCount; ++i) {
    const AobFix& f = kFixes[i];
    uint64_t target = 0;
    if (f.mode == FIX_ABS) target = f.value;
    else if (f.mode == FIX_INJ) target = g_inject + f.value;
    else if (f.mode == FIX_MOD) {
      uint64_t mb = moduleBaseOf(f.mod);
      if (!mb) { logf("重定位失败：模块 %s 不在", f.mod ? f.mod : "?"); ++bad; continue; }
      target = mb + f.value;
    } else if (f.mode == FIX_BLOCK) {
      if (f.block >= (uint8_t)kBlockCount) { ++bad; continue; }
      target = g_blockBase[f.block] + f.value;
    }
    if (!target) { ++bad; continue; }
    if ((size_t)(f.at + f.width) > (size_t)kCaveLen) { ++bad; continue; }
    if (f.width == 1) {
      int64_t delta = (int64_t)target - (int64_t)(caveBase + f.end);
      if (delta < -128 || delta > 127) {
        logf("短跳超出 ±127（off=%u delta=%lld），该跳转会失效", (unsigned)f.at, (long long)delta);
        ++bad;
        continue;
      }
      cave[f.at] = (unsigned char)(delta & 0xFF);
    } else if (f.abs) {
      uint32_t v = (uint32_t)target;
      memcpy(cave + f.at, &v, 4);
    } else {
      int64_t delta = (int64_t)target - (int64_t)(caveBase + f.end);
      uint32_t v = (uint32_t)(delta & 0xFFFFFFFF);
      memcpy(cave + f.at, &v, 4);
    }
  }
  return bad;
}

// ---------------------------------------------------------------------------
// 挂钩 / 摘钩
// ---------------------------------------------------------------------------
static void uninstallHook(void) {
  EnterCriticalSection(&g_cs);
  if (g_active && g_inject) {
    memWrite(g_inject, kOrigBytes, (size_t)kOrigLen);
    logf("已还原注入点 0x%llX", (unsigned long long)g_inject);
  }
  g_active = 0;
  if (g_cave) {
    HANDLE h = g_self ? GetCurrentProcess() : g_proc;
    /* 别的线程可能正在代码洞里执行，稍等一下再释放，降低崩溃概率 */
    Sleep(20);
    VirtualFreeEx(h, (LPVOID)(uintptr_t)g_cave, 0, MEM_RELEASE);
    g_cave = 0;
  }
  for (int i = 0; i < AOB_MAXBLOCKS; ++i) g_blockBase[i] = 0;
  LeaveCriticalSection(&g_cs);
}

static int installHook(void) {
  if (g_active) return 1;
  if (kOrigLen < 5) { logf("原指令只有 %d 字节，不足 5 字节无法打补丁（生成器应已补齐）", kOrigLen); return 0; }
  if (kCaveLen <= 0) { logf("代码洞数据为空（kCaveLen=0），生成信息不完整"); return 0; }

  // 1) RVA 快路径
  uint64_t inject = 0;
  unsigned char cur[32];
  if (kInjectRva) {
    uint64_t cand = g_modBase + kInjectRva;
    if (memRead(cand, cur, (size_t)kOrigLen) && memcmp(cur, kOrigBytes, (size_t)kOrigLen) == 0)
      inject = cand;
  }
  // 2) 特征码扫描
  if (!inject) {
    uint64_t hits[16];
    int n = scanPattern(hits, 16);
    if (n <= 0) { logf("特征码未命中"); return 0; }
    if (n > 1) logf("特征码命中 %d 处，取第一处 0x%llX", n, (unsigned long long)hits[0]);
    inject = hits[0];
  }
  // 3) 校验原字节
  if (!memRead(inject, cur, (size_t)kOrigLen)) { logf("读注入点 0x%llX 失败", (unsigned long long)inject); return 0; }
  if (memcmp(cur, kOrigBytes, (size_t)kOrigLen) != 0) {
    if (cur[0] == 0xE9 || cur[0] == 0xEB)
      logf("注入点 0x%llX 已是跳转（%02X），可能 CE 里脚本还勾着，或本 DLL 已加载过",
           (unsigned long long)inject, cur[0]);
    else
      logf("注入点 0x%llX 字节不符：内存 %02X %02X %02X，期望 %02X %02X %02X",
           (unsigned long long)inject, cur[0], cur[1], cur[2],
           kOrigBytes[0], kOrigBytes[1], kOrigBytes[2]);
    return 0;
  }

  // 4) 大块尺寸 = CE 里各 alloc 块的布局总长，页对齐
  uint64_t total = 0;
  for (int i = 0; i < kBlockCount; ++i) {
    uint64_t e = (uint64_t)kBlocks[i].ceOff + (uint64_t)kBlocks[i].size;
    if (e > total) total = e;
  }
  if (!total) total = 0x1000;
  total = (total + 0xFFF) & ~0xFFFULL;
  if (total < 0x1000) total = 0x1000;

  // 5) 分配
  uint64_t caveBase = allocNear(inject, total);
  if (!caveBase) { logf("代码洞分配失败（%llu 字节）", (unsigned long long)total); return 0; }
  int64_t rel = (int64_t)caveBase - (int64_t)(inject + 5);
  if (rel > 0x7FFFFFFFLL || rel < -0x80000000LL) {
    logf("代码洞 0x%llX 距注入点超出 ±2GB，无法用 E9 跳转", (unsigned long long)caveBase);
    HANDLE h = g_self ? GetCurrentProcess() : g_proc;
    VirtualFreeEx(h, (LPVOID)(uintptr_t)caveBase, 0, MEM_RELEASE);
    return 0;
  }
  g_cave = caveBase;
  g_caveSize = total;
  g_inject = inject;
  for (int i = 0; i < kBlockCount && i < AOB_MAXBLOCKS; ++i)
    g_blockBase[i] = caveBase + (uint64_t)kBlocks[i].ceOff;

  // 6) 拷代码洞 + 重定位
  unsigned char* cave = (unsigned char*)malloc((size_t)(kCaveLen > 0 ? kCaveLen : 1));
  if (!cave) { uninstallHook(); return 0; }
  memcpy(cave, kCaveBytes, (size_t)kCaveLen);
  int bad = applyFixes(cave, caveBase);
  if (bad) logf("警告：%d 个重定位项没写成功", bad);
  int wrote = memWrite(caveBase, cave, (size_t)kCaveLen);
  free(cave);
  if (!wrote) { logf("写代码洞失败"); uninstallHook(); return 0; }

  // 7) 注入点补丁：E9 + NOP
  int codeLen = kOrigLen > 5 ? kOrigLen : 5;
  unsigned char patch[32];
  if (codeLen > (int)sizeof(patch)) { logf("覆盖长度 %d 超出上限", codeLen); uninstallHook(); return 0; }
  memset(patch, 0x90, sizeof(patch));
  patch[0] = 0xE9;
  int32_t r32 = (int32_t)(caveBase - (inject + 5));
  memcpy(patch + 1, &r32, 4);
  if (!memWrite(inject, patch, (size_t)codeLen)) { logf("写注入点失败"); uninstallHook(); return 0; }

  // 8) 回读校验
  unsigned char back[8] = {0};
  if (!memRead(inject, back, (size_t)codeLen) || back[0] != 0xE9) {
    logf("注入点回读校验失败（首字节 %02X），可能被保护还原；已写回原字节", back[0]);
    /* 先把原字节写回去：宁可不挂，也不能让游戏跳进已释放的代码洞 */
    memWrite(inject, kOrigBytes, (size_t)kOrigLen);
    uninstallHook();
    return 0;
  }

  g_active = 1;
  logf("挂钩完成：注入点 0x%llX → 代码洞 0x%llX（%d 字节覆盖，%d 个 alloc 块）",
       (unsigned long long)inject, (unsigned long long)caveBase, codeLen, kBlockCount);
  return 1;
}

// ---------------------------------------------------------------------------
// 值条目：解析地址 / 读写 / 冻结
// ---------------------------------------------------------------------------
static int valueSize(int vt) {
  switch (vt) {
    case VT_BYTE:   return 1;
    case VT_WORD:   return 2;
    case VT_DWORD:  return 4;
    case VT_QWORD:  return 8;
    case VT_SINGLE: return 4;
    case VT_DOUBLE: return 8;
    default:        return 8;
  }
}

static int resolveValue(int idx, uint64_t* out) {
  if (idx < 0 || idx >= kValueCount) return 0;
  const AobValue& v = kValues[idx];
  uint64_t base = 0;
  if (v.allocSym && v.allocSym[0]) {
    int bi = findBlock(v.allocSym);
    if (bi < 0 || bi >= AOB_MAXBLOCKS || !g_blockBase[bi]) return 0;
    base = g_blockBase[bi] + (uint64_t)v.modOff;
  } else if (v.modName && v.modName[0]) {
    uint64_t mb = moduleBaseOf(v.modName);
    if (!mb) return 0;
    base = mb + (uint64_t)v.modOff;
  } else if (v.fallback) {
    base = v.fallback;
  } else {
    return 0;
  }
  int ps = kIs64 ? 8 : 4;
  for (int i = 0; i < v.nOff; ++i) {
    uint64_t ptr = 0;
    if (ps == 4) {
      uint32_t p32 = 0;
      if (!memRead(base, &p32, 4)) return 0;
      ptr = (uint64_t)p32;
    } else {
      if (!memRead(base, &ptr, 8)) return 0;
    }
    if (!ptr) return 0;
    base = ptr + (uint64_t)v.off[i];
  }
  *out = base;
  return 1;
}

static int valueRead(int idx, unsigned char* buf, int cap) {
  uint64_t addr = 0;
  if (!resolveValue(idx, &addr)) return 0;
  int n = valueSize(kValues[idx].vtype);
  if (n > cap) n = cap;
  return memRead(addr, buf, (size_t)n) ? n : 0;
}

static int valueWrite(int idx, const unsigned char* buf, int len) {
  uint64_t addr = 0;
  if (!resolveValue(idx, &addr)) return 0;
  return memWrite(addr, buf, (size_t)len) ? 1 : 0;
}

static void doFreeze(void) {
  for (int i = 0; i < kValueCount; ++i) {
    if (!g_vs[i].freeze || !g_vs[i].freezeLen) continue;
    valueWrite(i, g_vs[i].freezeBuf, g_vs[i].freezeLen);
  }
}

// ---------------------------------------------------------------------------
// 值文本解析（INI 用）
// ---------------------------------------------------------------------------
static int parseValueText(const char* s, int vt, unsigned char* out, int cap) {
  while (*s == ' ' || *s == '\t') ++s;
  if (!*s) return 0;
  if (vt == VT_SINGLE) {
    float f = (float)strtod(s, NULL);
    if (cap < 4) return 0;
    memcpy(out, &f, 4);
    return 4;
  }
  if (vt == VT_DOUBLE) {
    double d = strtod(s, NULL);
    if (cap < 8) return 0;
    memcpy(out, &d, 8);
    return 8;
  }
  if (vt == VT_STRING) {
    size_t n = strlen(s);
    if (n > (size_t)cap) n = (size_t)cap;
    memcpy(out, s, n);
    return (int)n;
  }
  unsigned long long v = strtoull(s, NULL, 0);
  int n = valueSize(vt);
  if (n > cap) n = cap;
  for (int i = 0; i < n; ++i) out[i] = (unsigned char)((v >> (8 * i)) & 0xFF);
  return n;
}

// ---------------------------------------------------------------------------
// INI：与 DLL 同目录 aob_dll.ini，每秒重读
// ---------------------------------------------------------------------------
static void applyIni(void) {
  if (!g_iniPath[0]) return;
  HANDLE h = CreateFileA(g_iniPath, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE,
                         NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
  if (h == INVALID_HANDLE_VALUE) return;
  char data[8192];
  DWORD got = 0;
  int ok = ReadFile(h, data, (DWORD)sizeof(data) - 1, &got, NULL) ? 1 : 0;
  CloseHandle(h);
  if (!ok) return;
  data[got] = 0;

  int cur = -1;
  char* p = data;
  while (*p) {
    char* e = strchr(p, '\n');
    if (!e) e = p + strlen(p);
    char line[256];
    size_t n = (size_t)(e - p);
    if (n > sizeof(line) - 1) n = sizeof(line) - 1;
    memcpy(line, p, n);
    line[n] = 0;
    while (n > 0 && (line[n - 1] == '\r' || line[n - 1] == ' ' || line[n - 1] == '\t')) line[--n] = 0;
    char* s = line;
    while (*s == ' ' || *s == '\t') ++s;

    if (*s == '[') {
      int idx = atoi(s + 1);
      cur = (idx >= 0 && idx < kValueCount) ? idx : -1;
    } else if (*s == ';' || *s == '#' || *s == 0) {
      /* 注释 / 空行 */
    } else if (cur >= 0) {
      char* eq = strchr(s, '=');
      if (eq) {
        *eq = 0;
        char* key = s;
        char* val = eq + 1;
        char* ke = key + strlen(key);
        while (ke > key && (ke[-1] == ' ' || ke[-1] == '\t')) *--ke = 0;
        if (ieq(key, "freeze")) {
          int nf = (atoi(val) != 0);
          if (nf != g_vs[cur].freeze) {
            g_vs[cur].freeze = nf;
            logf("INI: 条目 %d freeze=%d", cur, nf);
          }
        } else if (ieq(key, "value")) {
          unsigned char buf[16];
          int len = parseValueText(val, kValues[cur].vtype, buf, (int)sizeof(buf));
          if (len > 0 && (len != g_vs[cur].freezeLen ||
                          memcmp(buf, g_vs[cur].freezeBuf, (size_t)len) != 0)) {
            memcpy(g_vs[cur].freezeBuf, buf, (size_t)len);
            g_vs[cur].freezeLen = len;
            logf("INI: 条目 %d value 已设为 %d 字节", cur, len);
          }
        }
      }
    }
    p = (*e) ? e + 1 : e;
  }
}

// ---------------------------------------------------------------------------
// 状态文件
// ---------------------------------------------------------------------------
static void writeStatus(const char* state) {
  if (!g_statusPath[0]) return;
  char buf[4096];
  int n = 0;
  n += snprintf(buf + n, sizeof(buf) - (size_t)n,
                "# AOB Hook DLL\nstate=%s\npid=%lu\nmodule=%s\nmodbase=0x%llX\nhook=0x%llX\ncave=0x%llX\ncount=%d\n",
                state, (unsigned long)GetCurrentProcessId(), kModuleName,
                (unsigned long long)g_modBase, (unsigned long long)g_inject,
                (unsigned long long)g_cave, kValueCount);
  for (int i = 0; i < kValueCount && n < (int)sizeof(buf) - 160; ++i) {
    uint64_t addr = 0;
    int ok = resolveValue(i, &addr);
    unsigned char v[8];
    int vn = ok ? valueRead(i, v, 8) : 0;
    unsigned long long hex = 0;
    for (int k = vn - 1; k >= 0; --k) hex = (hex << 8) | v[k];
    n += snprintf(buf + n, sizeof(buf) - (size_t)n,
                  "[%d]\nname=%s\naddr=0x%llX\nvalue=0x%llX\nvalid=%d\nfreeze=%d\n",
                  i, kValues[i].desc ? kValues[i].desc : "",
                  (unsigned long long)addr, hex, ok, g_vs[i].freeze);
  }
  HANDLE h = CreateFileA(g_statusPath, GENERIC_WRITE, FILE_SHARE_READ,
                         NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
  if (h == INVALID_HANDLE_VALUE) return;
  DWORD wrote = 0;
  WriteFile(h, buf, (DWORD)n, &wrote, NULL);
  CloseHandle(h);
}

// ---------------------------------------------------------------------------
// 路径初始化：DLL 所在目录，不可写则退回 %TEMP%
// ---------------------------------------------------------------------------
static void initPaths(void) {
  char dllPath[MAX_PATH] = {0};
  HMODULE self = 0;
  if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
                         (const char*)&initPaths, &self)) {
    GetModuleFileNameA(self, dllPath, MAX_PATH);
  }
  if (!dllPath[0]) GetModuleFileNameA(g_hinst, dllPath, MAX_PATH);
  char dir[MAX_PATH] = {0};
  size_t dn = strlen(dllPath);
  if (dn >= sizeof(dir)) dn = sizeof(dir) - 1;
  memcpy(dir, dllPath, dn);
  dir[dn] = 0;
  char* slash = strrchr(dir, '\\');
  if (slash) *slash = 0; else dir[0] = 0;

  int wrote = 0;
  if (dir[0]) {
    snprintf(g_statusPath, sizeof(g_statusPath), "%s\\aob_dll_status.txt", dir);
    snprintf(g_iniPath, sizeof(g_iniPath), "%s\\aob_dll.ini", dir);
    HANDLE h = CreateFileA(g_statusPath, GENERIC_WRITE, FILE_SHARE_READ, NULL,
                           OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (h != INVALID_HANDLE_VALUE) { CloseHandle(h); wrote = 1; }
    else { DeleteFileA(g_statusPath); }
  }
  if (!wrote) {
    char tmp[MAX_PATH] = {0};
    GetTempPathA(MAX_PATH, tmp);
    snprintf(g_statusPath, sizeof(g_statusPath), "%saob_dll_status.txt", tmp);
    snprintf(g_iniPath, sizeof(g_iniPath), "%saob_dll.ini", tmp);
    logf("DLL 目录不可写，状态/配置改到 %s", tmp);
  }
}

// ---------------------------------------------------------------------------
// 导出 API（供把 DLL 当引擎加载的宿主调用）
// ---------------------------------------------------------------------------
AOB_EXPORT int AOB_Start(void) {
  if (g_active) return 1;
  EnterCriticalSection(&g_cs);
  int ok = installHook();
  LeaveCriticalSection(&g_cs);
  return ok;
}

AOB_EXPORT void AOB_Stop(void) { uninstallHook(); }
AOB_EXPORT int  AOB_IsActive(void) { return g_active ? 1 : 0; }
AOB_EXPORT int  AOB_GetCount(void) { return kValueCount; }

AOB_EXPORT const char* AOB_GetName(int i) {
  if (i < 0 || i >= kValueCount) return "";
  return kValues[i].desc ? kValues[i].desc : "";
}

AOB_EXPORT unsigned long long AOB_GetAddress(int i) {
  uint64_t a = 0;
  return resolveValue(i, &a) ? (unsigned long long)a : 0ULL;
}

AOB_EXPORT int AOB_GetValue(int i, void* buf, int cap) {
  if (!buf || cap <= 0) return 0;
  return valueRead(i, (unsigned char*)buf, cap);
}

AOB_EXPORT int AOB_SetValue(int i, const void* buf, int len) {
  if (!buf || len <= 0) return 0;
  return valueWrite(i, (const unsigned char*)buf, len);
}

AOB_EXPORT int AOB_Freeze(int i, int on) {
  if (i < 0 || i >= kValueCount) return 0;
  if (on) {
    int n = valueRead(i, g_vs[i].freezeBuf, 8);
    if (n <= 0) return 0;
    g_vs[i].freezeLen = n;
  }
  g_vs[i].freeze = on ? 1 : 0;
  return 1;
}

AOB_EXPORT int AOB_FreezeWithValue(int i, const void* buf, int len) {
  if (i < 0 || i >= kValueCount || !buf || len <= 0 || len > 16) return 0;
  memcpy(g_vs[i].freezeBuf, buf, (size_t)len);
  g_vs[i].freezeLen = len;
  g_vs[i].freeze = 1;
  return 1;
}

AOB_EXPORT unsigned long long AOB_GetHookAddress(void) { return g_inject; }
AOB_EXPORT unsigned long long AOB_GetCaveAddress(void) { return g_cave; }

// ---------------------------------------------------------------------------
// 工作线程
// ---------------------------------------------------------------------------
static DWORD WINAPI WorkerProc(LPVOID) {
  logf("启动：%s", kGenTag);
  int attached = 0;
  int tries = 0;
  unsigned long long lastTry = 0, lastIni = 0, lastStat = 0;
  while (!g_stop) {
    unsigned long long now = GetTickCount64();
    /* 挂不上就隔 2 秒重试：注入到启动器时游戏可能还没起来；
       CE 里脚本还勾着时注入点已是 E9，等脚本关掉也能自动补上 */
    if (!g_active && now - lastTry >= 2000) {
      lastTry = now;
      if (!attached) {
        s_quietLog = (tries > 2);
        attached = attachTarget();
        s_quietLog = 0;
        if (!attached) {
          ++tries;
          if (tries <= 3 || tries % 15 == 0)
            logf("第 %d 次尝试失败：等待目标进程 %s / 模块 %s", tries, kTargetExe, kModuleName);
        }
      }
      if (attached && !g_active) {
        s_quietLog = (tries > 2);
        if (installHook()) {
          snprintf(g_lastState, sizeof(g_lastState), "active");
        } else {
          snprintf(g_lastState, sizeof(g_lastState), "failed: hook");
          ++tries;
          if (tries <= 3 || tries % 15 == 0)
            logf("第 %d 次尝试失败：挂钩未成功（详见上面的原因）", tries);
        }
        s_quietLog = 0;
      }
    }
    if (now - lastIni >= 1000) { lastIni = now; applyIni(); }
    if (g_active) doFreeze();
    if (now - lastStat >= 1000) {
      lastStat = now;
      writeStatus(g_active ? "active" : (tries ? g_lastState : "waiting"));
    }
    Sleep(100);
  }
  uninstallHook();
  logf("已退出并还原");
  return 0;
}

// ---------------------------------------------------------------------------
// DllMain
// ---------------------------------------------------------------------------
static volatile long g_inited = 0;

static void aobStartOnce(void) {
  if (InterlockedCompareExchange(&g_inited, 1, 0) != 0) return;
  InitializeCriticalSection(&g_cs);
  memset(g_blockBase, 0, sizeof(g_blockBase));
  initPaths();
  HANDLE t = CreateThread(NULL, 0, WorkerProc, NULL, 0, NULL);
  if (t) CloseHandle(t);
}

/* 静态构造先跑一遍：MinGW 的 dllcrt 自带 weak 的 DllMain，万一我们的符号没被
   链接上去，工作线程也照样能起来 */
struct AobBootstrap { AobBootstrap() { aobStartOnce(); } };
static AobBootstrap g_bootstrap;

extern "C" BOOL APIENTRY DllMain(HMODULE hinst, DWORD reason, LPVOID reserved) {
  (void)reserved;
  if (reason == DLL_PROCESS_ATTACH) {
    g_hinst = hinst;
    DisableThreadLibraryCalls(hinst);
    aobStartOnce();
  } else if (reason == DLL_PROCESS_DETACH) {
    g_stop = 1;
    if (g_active) uninstallHook();
  }
  return TRUE;
}
]==]

  -- ---------- 小工具 ----------
  local function dPatParse(s)
    local bytes, mask = {}, {}
    for tok in tostring(s or ""):gmatch("%S+") do
      tok = tok:upper()
      if tok == "??" or tok == "?" then
        bytes[#bytes + 1] = 0
        mask[#mask + 1] = 0
      elseif tok:match("^%x+$") and #tok % 2 == 0 then
        for i = 1, #tok, 2 do
          bytes[#bytes + 1] = tonumber(tok:sub(i, i + 1), 16)
          mask[#mask + 1] = 1
        end
      end
    end
    return bytes, mask
  end

  local function dByteListC(arr, fmt)
    local o = {}
    for i = 1, #arr do o[i] = string.format(fmt, arr[i]) end
    if #o == 0 then return "0" end
    return table.concat(o, ", ")
  end

  -- 把 CE 侧固化的重定位信息换算成「写在哪 / 写什么 / 目标怎么重算」
  -- mode：0=绝对 1=注入点内偏移 2=模块内偏移 3=代码洞块内偏移
  local function dCollectFixes(parsed, allocs, injAddr, is64, origLen)
    local cave = parsed.fullCaveBytes or {}
    local out, seen = {}, {}

    local function addFix(at, endOff, width, mode, absFlag, block, value, modName)
      if at < 0 or at + width > #cave then return end
      if seen[at] then return end
      seen[at] = true
      out[#out + 1] = { at = at, endOff = endOff, width = width, mode = mode,
                        abs = absFlag, block = block or 0, value = value, mod = modName }
    end

    local function mapTarget(absTarget, modName, modOff)
      for i, a in ipairs(allocs) do
        if absTarget >= a.origAddr and absTarget < a.origAddr + a.size then
          return 3, i - 1, absTarget - a.origAddr
        end
      end
      if injAddr and absTarget >= injAddr and absTarget <= injAddr + 64 then
        return 1, 0, absTarget - injAddr
      end
      if modName and modName ~= "" and modOff then return 2, 0, modOff end
      return 0, 0, absTarget
    end

    -- 1) 跳回注入点的那条 jmp（CE 侧单独记在 returnHereFixups）
    for off, len in tostring(parsed.returnHereFixups or ""):gmatch("(%d+):(%d+)") do
      off, len = tonumber(off), tonumber(len)
      addFix(off + (len - 4), off + len, 4, 1, 0, 0, math.max(origLen or 5, 5))
    end

    -- 2) 代码洞里所有需要重算的地址字段
    for one in tostring(parsed.ripFixups or ""):gmatch("[^|]+") do
      local parts = {}
      for p in one:gmatch("[^:]+") do parts[#parts + 1] = p end
      if #parts >= 5 then
        local bi = tonumber(parts[1])
        local off = tonumber(parts[2])
        local len = tonumber(parts[3])
        local typ = parts[4]
        local absTarget = tonumber((parts[5]:gsub("^0[xX]", "")), 16)
        local modName, modOff
        if #parts >= 7 then
          local np = {}
          for i = 6, #parts - 1 do np[#np + 1] = parts[i] end
          modName = table.concat(np, ":")
          modOff = tonumber(parts[#parts], 16)
        end
        if bi and off and len and absTarget then
          local blkOff = (allocs[bi] and allocs[bi].ceOff) or 0
          if typ == "d" then
            local mode, block, value = mapTarget(absTarget, modName, modOff)
            addFix(blkOff + off, blkOff + off + 4, 4, mode, 1, block, value, modName)
          elseif typ == "ri" then
            -- ri 的数值已经是「注入点内偏移」，不是绝对地址
            addFix(blkOff + off + (len - 4), blkOff + off + len, 4, 1, 0, 0, absTarget)
          else
            local b = cave[off + 1] or 0
            local at, width, absFlag
            if typ == "sr" or (len == 2 and (b == 0xEB or (b >= 0x70 and b <= 0x7F))) then
              at, width, absFlag = off + 1, 1, 0
            elseif len == 6 and b == 0x0F then
              at, width, absFlag = off + 2, 4, 0
            elseif len == 5 and (b == 0xE9 or b == 0xE8) then
              at, width, absFlag = off + 1, 4, 0
            elseif typ == "a" and len == 5 and (b == 0xA1 or b == 0xA3) then
              at, width, absFlag = off + 1, 4, 1
            else
              local modRM = off + 1
              if is64 and b >= 0x40 and b <= 0x4F then modRM = off + 2 end
              at, width, absFlag = modRM + 1, 4, (typ == "a") and 1 or 0
            end
            local mode, block, value = mapTarget(absTarget, modName, modOff)
            addFix(blkOff + at, blkOff + off + len, width, mode, absFlag, block, value, modName)
          end
        end
      end
    end
    return out
  end

  -- 插件数据 → C++ 模板所需的元数据
  local function exBuildCppMeta(contract, parsed, entries, proc, is64, injAddr, modBase, tag)
    local allocs, ceBase = {}, nil
    for _, b in ipairs(parsed.allocBlocks or {}) do
      local a = { name = b.name, origAddr = b.origAddr, size = b.size }
      allocs[#allocs + 1] = a
      if not ceBase or a.origAddr < ceBase then ceBase = a.origAddr end
    end
    if #allocs == 0 then return nil, "没有 alloc 块信息，确认脚本已在 CE 里勾选激活" end
    if #allocs > 8 then return nil, "alloc 块超过 8 个（模板上限），请拆脚本" end
    for _, a in ipairs(allocs) do a.ceOff = a.origAddr - ceBase end

    local patBytes, patMask = dPatParse(contract.aobPattern)
    if #patBytes == 0 then return nil, "特征码解析失败：" .. tostring(contract.aobPattern) end

    local cave = {}
    for i = 1, #(parsed.fullCaveBytes or {}) do cave[i] = parsed.fullCaveBytes[i] end
    if #cave == 0 then return nil, "代码洞字节为空（fullCaveBytes），预汇编抓字节没成功" end

    local vals = {}
    for _, e in ipairs(entries or {}) do
      if not e.isAA then
        local offs = {}
        for i = 1, math.min(#(e.offsets or {}), 8) do offs[i] = e.offsets[i] end
        vals[#vals + 1] = {
          desc = e.description or "", allocSym = e.allocSymbol or "",
          modName = e.moduleName or "", modOff = e.moduleOffset or 0,
          fallback = e.baseResolvedAddr or 0, vtype = e.vtype or 2,
          nOff = #offs, off = offs,
        }
        if #vals >= 32 then break end
      end
    end

    local fixes = dCollectFixes(parsed, allocs, injAddr, is64, #contract.origBytes)
    if #fixes > 512 then return nil, "重定位项超过 512 个（模板上限）" end

    local rva = 0
    if injAddr and modBase and injAddr > modBase then rva = injAddr - modBase end

    local summary = string.format(
      "//  目标进程 %s（%s 位）   模块 %s\n//  特征码 %s\n//  注入点 RVA 0x%X   原指令 %d 字节   代码洞 %d 字节   重定位 %d 项   记录 %d 条",
      proc or "?", is64 and "64" or "32", contract.aobModule or "?",
      contract.aobPattern or "?", rva, #contract.origBytes, #cave, #fixes, #vals)

    return {
      proc = proc, module = contract.aobModule, is64 = is64,
      regionStart = contract.regionStartOff or 0,
      regionEnd = contract.regionEndOff or 0,
      injectRva = rva,
      origBytes = contract.origBytes,
      patternBytes = patBytes, patternMask = patMask,
      allocs = allocs, cave = cave, fixups = fixes, values = vals,
      tag = tag, summary = summary,
    }
  end

  -- 元数据 → 完整 .cpp 源码
  local function exBuildCppSource(meta)
    local blocks = {}
    for _, b in ipairs(meta.allocs) do
      blocks[#blocks + 1] = string.format('  { "%s", 0x%X, 0x%X },', exEscapeCS(b.name), b.ceOff, b.size)
    end
    local fixes = {}
    for _, f in ipairs(meta.fixups) do
      fixes[#fixes + 1] = string.format(
        "  { %u, %u, %u, %u, %u, %u, 0x%XULL, %s },",
        f.at, f.endOff, f.width, f.mode, f.abs or 0, f.block or 0, f.value,
        (f.mod and f.mod ~= "") and ('"' .. exEscapeCS(f.mod) .. '"') or "0")
    end
    local values = {}
    for _, v in ipairs(meta.values) do
      local offs = {}
      for i = 1, 8 do offs[i] = tostring(v.off[i] or 0) .. "LL" end
      values[#values + 1] = string.format(
        '  { "%s", "%s", "%s", %dLL, 0x%XULL, %d, %d, { %s } },',
        exEscapeCS(v.desc), exEscapeCS(v.allocSym or ""), exEscapeCS(v.modName or ""),
        v.modOff or 0, v.fallback or 0, v.vtype, v.nOff, table.concat(offs, ", "))
    end

    local s = CPP_BODY
    s = exSafeReplace(s, "@@SUMMARY@@", meta.summary or "")
    s = exSafeReplace(s, "@@TARGET@@", exEscapeCS(meta.proc))
    s = exSafeReplace(s, "@@MODULE@@", exEscapeCS(meta.module))
    s = exSafeReplace(s, "@@TAG@@", exEscapeCS(meta.tag))
    s = exSafeReplace(s, "@@IS64@@", meta.is64 and "1" or "0")
    s = exSafeReplace(s, "@@RSTART@@", string.format("0x%X", meta.regionStart or 0))
    s = exSafeReplace(s, "@@REND@@", string.format("0x%X", meta.regionEnd or 0))
    s = exSafeReplace(s, "@@RVA@@", string.format("0x%X", meta.injectRva or 0))
    s = exSafeReplace(s, "@@ORIGLEN@@", tostring(#meta.origBytes))
    s = exSafeReplace(s, "@@ORIGBYTES@@", dByteListC(meta.origBytes, "0x%02X"))
    s = exSafeReplace(s, "@@PATLEN@@", tostring(#meta.patternBytes))
    s = exSafeReplace(s, "@@PATBYTES@@", dByteListC(meta.patternBytes, "0x%02X"))
    local masks = {}
    for i = 1, #meta.patternMask do masks[i] = meta.patternMask[i] == 1 and "1" or "0" end
    s = exSafeReplace(s, "@@PATMASKS@@", table.concat(masks, ", "))
    s = exSafeReplace(s, "@@BLOCKS@@", table.concat(blocks, "\n"))
    s = exSafeReplace(s, "@@BLOCKCOUNT@@", tostring(#meta.allocs))
    s = exSafeReplace(s, "@@CAVELEN@@", tostring(#meta.cave))
    s = exSafeReplace(s, "@@CAVEBYTES@@", dByteListC(meta.cave, "0x%02X"))
    s = exSafeReplace(s, "@@FIXES@@", table.concat(fixes, "\n"))
    s = exSafeReplace(s, "@@FIXCOUNT@@", tostring(#meta.fixups))
    s = exSafeReplace(s, "@@VALUES@@", table.concat(values, "\n"))
    s = exSafeReplace(s, "@@VALUECOUNT@@", tostring(#meta.values))
    local _, left = s:gsub("@@[A-Z_]+@@", "")
    if left > 0 then return nil, "模板残留 " .. left .. " 个占位符" end
    return s
  end

  -- ---------- 编译器探测 ----------
  local function exFindCXX(outDir)
    local batPath = outDir .. "\\find_compiler.bat"
    local resPath = outDir .. "\\find_compiler.txt"
    pcall(os.remove, resPath)
    local L = {
      "@echo off",
      "setlocal",
      'set "OUT=' .. resPath .. '"',
      'break > "%OUT%"',
      'set "VSWHERE=%ProgramFiles(x86)%\\Microsoft Visual Studio\\Installer\\vswhere.exe"',
      'if not exist "%VSWHERE%" set "VSWHERE=%ProgramFiles%\\Microsoft Visual Studio\\Installer\\vswhere.exe"',
      'set "VSPATH="',
      'if exist "%VSWHERE%" for /f "usebackq delims=" %%p in (`"%VSWHERE%" -latest -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath 2^>nul`) do set "VSPATH=%%p"',
      'if defined VSPATH if exist "%VSPATH%\\VC\\Auxiliary\\Build\\vcvars64.bat" >> "%OUT%" echo MSVC64^|%VSPATH%\\VC\\Auxiliary\\Build\\vcvars64.bat',
      'if defined VSPATH if exist "%VSPATH%\\VC\\Auxiliary\\Build\\vcvars32.bat" >> "%OUT%" echo MSVC32^|%VSPATH%\\VC\\Auxiliary\\Build\\vcvars32.bat',
    }
    local candidates = {
      "C:\\msys64\\mingw64\\bin\\g++.exe",
      "C:\\msys64\\ucrt64\\bin\\g++.exe",
      "C:\\msys64\\clang64\\bin\\g++.exe",
      "C:\\msys64\\mingw32\\bin\\g++.exe",
      "C:\\mingw64\\bin\\g++.exe",
      "C:\\mingw32\\bin\\g++.exe",
      "C:\\MinGW\\bin\\g++.exe",
      "C:\\TDM-GCC-64\\bin\\g++.exe",
      "C:\\TDM-GCC-32\\bin\\g++.exe",
      "C:\\Strawberry\\c\\bin\\g++.exe",
      "C:\\ProgramData\\chocolatey\\bin\\g++.exe",
    }
    for _, p in ipairs(candidates) do
      L[#L + 1] = 'if exist "' .. p .. '" >> "%OUT%" echo MINGW^|' .. p
    end
    -- mingw-w64 官方安装包是嵌套目录（...\<triplet>\mingw64\bin），递归找一下
    L[#L + 1] = 'for /r "C:\\Program Files\\mingw-w64" %%i in (g++.exe) do >> "%OUT%" echo MINGW^|%%i'
    L[#L + 1] = 'for /r "C:\\Program Files (x86)\\mingw-w64" %%i in (g++.exe) do >> "%OUT%" echo MINGW^|%%i'
    L[#L + 1] = 'for /f "delims=" %%i in (\'where g++.exe 2^>nul\') do >> "%OUT%" echo MINGW^|%%i'
    L[#L + 1] = 'if exist "C:\\Program Files\\LLVM\\bin\\clang++.exe" >> "%OUT%" echo CLANG^|C:\\Program Files\\LLVM\\bin\\clang++.exe'
    L[#L + 1] = '>> "%OUT%" echo END'

    if not exWriteFile(batPath, table.concat(L, "\r\n"), false) then
      return nil, "写编译器探测脚本失败"
    end
    pcall(shellExecute, batPath, "", outDir, 0)
    local text
    for _ = 1, 20 do
      sleep(300)
      pcall(processMessages)
      local f = io.open(resPath, "r")
      if f then
        local c = f:read("*a")
        f:close()
        if c and c:find("END", 1, true) then text = c break end
      end
    end
    pcall(os.remove, batPath)
    pcall(os.remove, resPath)
    if not text then return nil, "编译器探测超时（find_compiler.bat 没跑完）" end

    local tc = { msvc64 = nil, msvc32 = nil, mingw = {}, clang = nil }
    for line in text:gmatch("[^\r\n]+") do
      local kind, rest = line:match("^(%w+)|(.*)$")
      if kind == "MSVC64" then tc.msvc64 = rest
      elseif kind == "MSVC32" then tc.msvc32 = rest
      elseif kind == "MINGW" and rest ~= "" then
        local dup = false
        for _, p in ipairs(tc.mingw) do if p:lower() == rest:lower() then dup = true end end
        if not dup then tc.mingw[#tc.mingw + 1] = rest end
      elseif kind == "CLANG" then tc.clang = rest end
    end
    return tc
  end

  -- MinGW 的位数只能从路径判断（标准安装约定）
  local function mingwBits(p)
    local l = tostring(p or ""):lower()
    if l:find("mingw64", 1, true) or l:find("ucrt64", 1, true) or l:find("clang64", 1, true)
       or l:find("x86_64", 1, true) or l:find("tdm-gcc-64", 1, true) then return 64 end
    if l:find("mingw32", 1, true) or l:find("i686", 1, true) or l:find("tdm-gcc-32", 1, true)
       or l:find("c:\\mingw\\bin", 1, true) or l:find("strawberry", 1, true) then return 32 end
    return nil
  end

  local function exPickToolchain(tc, is64)
    local want = is64 and 64 or 32
    local mingws = tc.mingw or {}
    if want == 64 then
      if tc.msvc64 then return { kind = "msvc", vcvars = tc.msvc64 } end
    else
      if tc.msvc32 then return { kind = "msvc", vcvars = tc.msvc32 } end
    end
    -- 位数吻合的 MinGW 优先；位数未知的放第二档；位数相反的绝不用
    for _, p in ipairs(mingws) do
      if mingwBits(p) == want then return { kind = "mingw", gpp = p, bits = want } end
    end
    for _, p in ipairs(mingws) do
      if mingwBits(p) == nil then return { kind = "mingw", gpp = p, bits = want } end
    end
    return nil
  end

  local function exBuildBatFor(tc, srcPath, dllPath, errPath, resPath, is64)
    local L = { "@echo off" }
    if tc.kind == "msvc" then
      L[#L + 1] = 'call "' .. tc.vcvars .. '" >nul 2>&1'
      L[#L + 1] = string.format(
        'cl /nologo /LD /MT /O2 /GS- /EHsc /DNDEBUG "%s" /Fe:"%s" /link /DLL /SUBSYSTEM:WINDOWS /MACHINE:%s /NOLOGO psapi.lib kernel32.lib user32.lib > "%s" 2>&1',
        srcPath, dllPath, is64 and "X64" or "X86", errPath)
    else
      local flags = (is64 and tc.bits == 64) and "" or ""
      if not is64 and tc.bits == 64 then flags = " -m32" end
      L[#L + 1] = string.format(
        '"%s" -shared -O2 -s -static -static-libgcc%s -o "%s" "%s" -lpsapi -lkernel32 -luser32 > "%s" 2>&1',
        tc.gpp, flags, dllPath, srcPath, errPath)
    end
    L[#L + 1] = 'if errorlevel 1 (echo FAIL>"' .. resPath .. '") else (echo OK>"' .. resPath .. '")'
    return table.concat(L, "\r\n")
  end

  local function exCompileDll(srcPath, dllPath, dirPath, is64, tc)
    local errPath = dirPath .. "\\build_errors.txt"
    local batPath = dirPath .. "\\build.bat"
    local resPath = dirPath .. "\\build_result.txt"
    pcall(os.remove, resPath)
    pcall(os.remove, errPath)
    pcall(os.remove, dllPath)
    local bat = exBuildBatFor(tc, srcPath, dllPath, errPath, resPath, is64)
    if not exWriteFile(batPath, bat, false) then return nil, "写 build.bat 失败" end
    pcall(shellExecute, batPath, "", dirPath, 0)
    local ok = false
    for _ = 1, 120 do
      sleep(1000)
      pcall(processMessages)
      local rf = io.open(resPath, "r")
      if rf then
        local c = rf:read("*a")
        rf:close()
        if c and c:match("OK") then ok = true break end
        if c and c:match("FAIL") then break end
      end
      local df = io.open(dllPath, "rb")
      if df then df:close() ok = true break end
    end
    if ok then
      pcall(os.remove, batPath)
      pcall(os.remove, resPath)
      pcall(os.remove, errPath)
      return dllPath
    end
    local msg = "编译失败"
    local ef = io.open(errPath, "r")
    if ef then
      local c = ef:read("*a")
      ef:close()
      if c and #c > 0 then msg = msg .. "：" .. c:sub(1, 400) end
    end
    return nil, msg, errPath
  end

  -- 生成可双击的 build.bat：自己找编译器（MSVC → MinGW），编译同目录的 <名字>.cpp
  -- 没装编译器时也留一份，装好再双击即可；失败会 pause 让人看得到
  local function exWriteBuildBat(outDir, baseName, is64)
    local vcv = is64 and "vcvars64.bat" or "vcvars32.bat"
    local mach = is64 and "X64" or "X86"
    local m32 = is64 and "" or " -m32"
    local archName = is64 and "64" or "32"
    local pkg = is64 and "mingw-w64-x86_64-gcc" or "mingw-w64-i686-gcc"
    local L = {
      "@echo off",
      "chcp 65001 >nul",
      "setlocal",
      'cd /d "%~dp0"',
      'set "SRC=' .. baseName .. '.cpp"',
      'set "OUT=' .. baseName .. '.dll"',
      "echo === AOB Hook DLL 编译（目标 " .. archName .. " 位）===",
      "echo.",
      'if not exist "%SRC%" goto nosrc',
      "",
      'set "VSWHERE=%ProgramFiles(x86)%\\Microsoft Visual Studio\\Installer\\vswhere.exe"',
      'if not exist "%VSWHERE%" set "VSWHERE=%ProgramFiles%\\Microsoft Visual Studio\\Installer\\vswhere.exe"',
      'set "VSPATH="',
      'if exist "%VSWHERE%" for /f "usebackq delims=" %%p in (`"%VSWHERE%" -latest -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath 2^>nul`) do set "VSPATH=%%p"',
      'if not defined VSPATH goto mingw',
      'if not exist "%VSPATH%\\VC\\Auxiliary\\Build\\' .. vcv .. '" goto mingw',
      "echo [1/2] 用 MSVC 编译...",
      'call "%VSPATH%\\VC\\Auxiliary\\Build\\' .. vcv .. '" >nul 2>&1',
      'cl /nologo /LD /MT /O2 /GS- /EHsc /DNDEBUG "%SRC%" /Fe:"%OUT%" /link /DLL /SUBSYSTEM:WINDOWS /MACHINE:' .. mach .. ' /NOLOGO psapi.lib kernel32.lib user32.lib',
      "if not errorlevel 1 goto ok",
      "echo [MSVC] 没成功，继续试 MinGW...",
      "",
      ":mingw",
      "echo [2/2] 找 MinGW g++...",
      'set "GPP="',
    }
    local cands = {
      { "C:\\msys64\\mingw64\\bin\\g++.exe", 64 },
      { "C:\\msys64\\ucrt64\\bin\\g++.exe", 64 },
      { "C:\\msys64\\clang64\\bin\\g++.exe", 64 },
      { "C:\\mingw64\\bin\\g++.exe", 64 },
      { "C:\\TDM-GCC-64\\bin\\g++.exe", 64 },
      { "C:\\msys64\\mingw32\\bin\\g++.exe", 32 },
      { "C:\\mingw32\\bin\\g++.exe", 32 },
      { "C:\\MinGW\\bin\\g++.exe", 32 },
      { "C:\\TDM-GCC-32\\bin\\g++.exe", 32 },
      { "C:\\Strawberry\\c\\bin\\g++.exe", 32 },
    }
    local want = is64 and 64 or 32
    for _, c in ipairs(cands) do
      if c[2] == want then
        L[#L + 1] = 'if not defined GPP if exist "' .. c[1] .. '" set "GPP=' .. c[1] .. '"'
      end
    end
    L[#L + 1] = 'if not defined GPP for /f "delims=" %%i in (\'where g++.exe 2^>nul\') do if not defined GPP set "GPP=%%i"'
    L[#L + 1] = "if not defined GPP goto nocc"
    L[#L + 1] = 'echo 用: %GPP%'
    L[#L + 1] = '"%GPP%" -shared -O2 -s -static -static-libgcc' .. m32 .. ' -o "%OUT%" "%SRC%" -lpsapi -lkernel32 -luser32'
    L[#L + 1] = "if errorlevel 1 goto fail"
    L[#L + 1] = "goto ok"
    L[#L + 1] = ""
    L[#L + 1] = ":nosrc"
    L[#L + 1] = 'echo [错误] 找不到 %SRC%，把本文件和它放同一个目录'
    L[#L + 1] = "pause"
    L[#L + 1] = "exit /b 1"
    L[#L + 1] = ""
    L[#L + 1] = ":nocc"
    L[#L + 1] = "echo."
    L[#L + 1] = "echo [错误] 没找到 C++ 编译器。装一个再双击本脚本（任选其一）："
    L[#L + 1] = "echo   1. MSYS2: 装好后运行  pacman -S " .. pkg
    L[#L + 1] = "echo   2. VS / Build Tools: 勾选「使用 C++ 的桌面开发」"
    L[#L + 1] = "echo   3. WinLibs 免安装包: 解压后把 bin 目录加进 PATH"
    L[#L + 1] = "pause"
    L[#L + 1] = "exit /b 1"
    L[#L + 1] = ""
    L[#L + 1] = ":ok"
    L[#L + 1] = "echo."
    L[#L + 1] = "echo 编译成功: %OUT%"
    L[#L + 1] = "pause"
    L[#L + 1] = "exit /b 0"
    L[#L + 1] = ""
    L[#L + 1] = ":fail"
    L[#L + 1] = "echo."
    L[#L + 1] = "echo 编译失败，看上面的报错。"
    L[#L + 1] = "echo 若是 32/64 位工具链不匹配，就装 " .. archName .. " 位的编译器。"
    L[#L + 1] = "pause"
    L[#L + 1] = "exit /b 1"
    local p = outDir .. "\\build.bat"
    return exWriteFile(p, table.concat(L, "\r\n"), false), p
  end

  -- ---------- 导出入口 ----------
  function AOBEXE.onExportDll()
    log("============ [注入 DLL 导出（原生 C++）] ============")
    local contract, err = exBuildContract()
    if not contract then log("[DLL][错误] " .. tostring(err)) return end

    local okAddr, inj = pcall(getAddress, contract.hookSym)
    if not okAddr or type(inj) ~= "number" or inj == 0 then
      log("[DLL][错误] 符号 " .. tostring(contract.hookSym) .. " 未注册：先把脚本[加到列表]并勾选激活")
      return
    end
    log(string.format("[DLL] 注入点 %s = 0x%X", contract.hookSym, inj))

    local okParse, parsed = pcall(exParseAOBScript, contract.script, contract)
    if not okParse then log("[DLL][错误] 预汇编解析异常：" .. tostring(parsed)) return end
    if not parsed.preAssembled or #parsed.allocBlocks < 1 then
      log(string.format("[DLL][错误] 预汇编抓字节失败（%d 个 alloc 块）：确认脚本已勾选激活、原指令字节完整",
        #(parsed.allocBlocks or {})))
      return
    end
    log(string.format("[DLL] 已固化 %d 个 alloc 块 / 原指令 %d 字节 / 重定位源 [%s|%s]",
      #parsed.allocBlocks, parsed.origInstrLen,
      tostring(parsed.returnHereFixups or ""), tostring(parsed.ripFixups or "")))

    local okSel, selRows = pcall(exShowSelectDialog, contract, "dll")
    if not okSel then
      log("[DLL][错误] 打开条目选择窗口失败：" .. tostring(selRows))
      selRows = nil
    elseif selRows == nil then
      log("[DLL] 已取消（未生成 DLL）")
      return
    end

    local procName, pid = exProcessInfo()
    local is64 = targetIs64Bit()
    log(string.format("[DLL] 目标进程 %s（PID %d，%s 位）", procName, pid, is64 and "64" or "32"))

    local entries = exMakeEntries(contract, parsed, selRows)
    local modBase
    pcall(function() modBase = tonumber(getAddress(contract.aobModule)) or nil end)
    if not modBase then
      pcall(function()
        local list = enumModules()
        for _, m in ipairs(list or {}) do
          if m.Name and m.Name:lower() == tostring(contract.aobModule):lower() then
            modBase = tonumber(m.Address)
          end
        end
      end)
    end
    if not modBase then log("[DLL][提示] 取不到模块基址，注入点 RVA 快路径停用，只用特征码定位") end

    local meta, merr = exBuildCppMeta(contract, parsed, entries, procName, is64, inj, modBase,
      PLUGIN_VER .. " / " .. BUILD_STAMP)
    if not meta then log("[DLL][错误] " .. tostring(merr)) return end
    local src, serr = exBuildCppSource(meta)
    if not src then log("[DLL][错误] " .. tostring(serr)) return end
    log(string.format("[DLL] C++ 源码 %d 字节；重定位 %d 项，记录 %d 条，代码洞 %d 字节",
      #src, #meta.fixups, #meta.values, #meta.cave))

    local outDir = exGetDesktop() .. "\\AOB_DLL_Output"
    exCreateDir(outDir)
    local safe = tostring(procName):gsub("[^%w%.%-_]", "")
    if safe == "" or safe == ".exe" then safe = "AOB_Hook" end
    safe = safe:gsub("%.[eE][xX][eE]$", "")
    local srcPath = outDir .. "\\" .. safe .. ".cpp"
    local dllPath = outDir .. "\\" .. safe .. ".dll"
    if not exWriteFile(srcPath, src, false) then
      log("[DLL][错误] 写源码失败：" .. srcPath)
      return
    end
    log("[DLL] 源码已写：" .. srcPath)

    local tcs, tcerr = exFindCXX(outDir)
    if not tcs then
      log("[DLL][提示] " .. tostring(tcerr))
      local wb, batPath = exWriteBuildBat(outDir, safe, is64)
      log("[DLL] 源码已生成；装好编译器后双击 build.bat 就能编出 DLL")
      if wb then log("[DLL] 可双击的脚本：" .. batPath) end
      log("[DLL] 手动编译也行：")
      log('      cl /LD /MT /O2 /EHsc "' .. safe .. '.cpp" /link /DLL psapi.lib')
      log('      g++ -shared -O2 -static -o "' .. safe .. '.dll" "' .. safe .. '.cpp" -lpsapi')
      return
    end
    local tc = exPickToolchain(tcs, is64)
    if not tc then
      local anyFound = (tcs.msvc64 or tcs.msvc32 or tcs.clang or #(tcs.mingw or {}) > 0) and true or false
      if not anyFound then
        log("[DLL][错误] 这台机器上没有 C++ 编译器（cl.exe / g++.exe 都没找到）")
      else
        log(string.format("[DLL][错误] 现有编译器编不出 %s 位目标：", is64 and "64" or "32"))
        if tcs.msvc64 then log("      MSVC 64 位: " .. tcs.msvc64) end
        if tcs.msvc32 then log("      MSVC 32 位: " .. tcs.msvc32) end
        for _, p in ipairs(tcs.mingw) do log("      MinGW: " .. p) end
        if tcs.clang then log("      clang++: " .. tcs.clang) end
      end
      if is64 then
        log("[DLL] 需要 64 位工具集：vcvars64（VS/Build Tools）或 mingw64 版 g++")
      else
        log("[DLL] 需要 32 位工具集：vcvars32（VS/Build Tools）或 i686 版 g++（mingw32）")
      end
      log(string.format("[DLL] 推荐装 %s 位工具链（任选其一）：", is64 and "64" or "32"))
      log("      · MSYS2 + pacman -S " .. (is64 and "mingw-w64-x86_64-gcc" or "mingw-w64-i686-gcc"))
      log("      · WinLibs 免安装包（解压后把 bin 加进 PATH）")
      log("      · VS Build Tools：勾「使用 C++ 的桌面开发」")
      local wb, batPath = exWriteBuildBat(outDir, safe, is64)
      log("[DLL] 源码已生成；装好编译器后双击 build.bat 即可" .. (wb and ("（" .. batPath .. "）") or ""))
      return
    end
    log(string.format("[DLL] 编译器：%s %s", tc.kind, tc.vcvars or tc.gpp or ""))

    local out, cerr, errFile = exCompileDll(srcPath, dllPath, outDir, is64, tc)
    if not out then
      log("[DLL][错误] " .. tostring(cerr))
      if errFile then log("[DLL] 编译日志：" .. errFile) end
      local wb, batPath = exWriteBuildBat(outDir, safe, is64)
      if wb then
        log("[DLL] 已生成可双击的 build.bat（会自己找编译器并在出错时暂停）：" .. batPath)
      end
      return
    end
    log("[DLL] 生成完成：" .. out)
    log("[DLL] 用法：任意注入器把 DLL 注入 " .. procName .. "；")
    log("[DLL]       同目录 aob_dll.ini 控制值（[序号] freeze=1 / value=100），")
    log("[DLL]       aob_dll_status.txt 每秒刷新，可被外部工具轮询；日志看 DebugView")
    log("====================================================")
  end

  -- 供测试/调试：直接拿元数据出源码（不写盘）
  AOBEXE.buildCppMeta = exBuildCppMeta
  AOBEXE.buildCppSource = exBuildCppSource
  AOBEXE.writeBuildBat = exWriteBuildBat
  AOBEXE.findCXX = exFindCXX
  AOBEXE.pickToolchain = exPickToolchain
end

local function init()
  -- 启动即自报版本：打开生成器后 ⑤「结果输出」区第一行就能看到，
  -- 用来确认「当前跑的是不是刚替换的那个文件」
  log(string.format("[版本] AOB 符号脚本生成器 %s（构建 %s）已加载", PLUGIN_VER, BUILD_STAMP))
  log("[导出] 已内嵌两种产物：点底部[生成EXE]出 C# 修改器；[生成DLL]出原生注入 DLL")
  log("[提示] 两种导出都要求脚本已[加到列表]并勾选激活（导出只搬已固化的字节）")
  log("[提示] 反汇编选区右键「取选中代码」，或按 Ctrl+Shift+A 取指令")

  local ok = pcall(addContextMenu)
  if not ok then
    -- 注意：createTimer(owner, enabled) 第二参是「是否启用」，传 false 定时器永不触发。
    -- 这里先建后配再显式 Enabled=true，避免默认间隔内空跑。
    local t = createTimer(nil, false)
    if t then
      t.Interval = 800
      t.OnTimer = function()
        if pcall(addContextMenu) then t.destroy() end
      end
      t.Enabled = true
    end
  end
  -- 反汇编视图右键「取选中代码」：内存查看器窗体可能还没开，装不上就延时重试。
  -- 注意：addDisasmContextMenu 内部靠 tryCall 吞错并返回 false（不抛异常），
  -- 所以这里必须用它的返回值判断，不能用 pcall（否则“装不上”会被当成“成功”而放弃重试）。
  -- 再包一层 pcall：万一 createMenuItem / Items.add 抛异常，也要当作“没装上”去重试，别让 init 中断。
  local function tryInstallDisasmMenu()
    local okc, r = pcall(addDisasmContextMenu)
    return okc and (r == true)
  end
  -- 不在 init 里立刻访问内存查看器：CE 首次执行 Lua 时 Memory Viewer 往往还没建，
  -- 直接取窗体可能触发 access violation（官方论坛明确提过）。统一交给定时器，1 秒后再试。
  local t = createTimer(nil, false)
  if t then
    t.Interval = 1000
    t.OnTimer = function()
      if disasmMenuItem or tryInstallDisasmMenu() then t.destroy() end
    end
    t.Enabled = true         -- createTimer 第二参才是 enabled；必须显式打开，否则永不触发
  end
end

init()
