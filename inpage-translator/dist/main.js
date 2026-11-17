'use strict';

/**
 * 整页翻译插件 —— AiCode DSH 插件运行时。
 *
 * 架构（v2，2026-11-18 重构）：
 *   插件不直接操作浏览器，也不自己建模型句柄 —— 两条路都验证过走不通：
 *     - host.tools.execute 代执行 browser 工具拿不到活动标签页（evaluate 一直超时）；
 *     - host.model 句柄每插件限 16 个，auto 等虚拟模型一次翻译就展开超限。
 *
 *   现在只做一件事：把「翻译当前页」的任务派给当前工作区最近的 AI 会话。
 *   AI 会话里有真的 browser 工具和真的模型配置，由它完成取节点、翻译、回填。
 *   插件负责构造任务说明、维护进程内译文缓存，以及提供 diagnose 自检。
 *
 * 协议约定（AI 侧按此执行）：
 *   action=collect  → 取出页面待译节点
 *   action=translate → 把译文表回填到页面（参数 translations）
 *   action=restore  → 还原原文
 */

const readline = require('readline');

const {
  LANG_NAMES,
  squeeze,
} = require('./constants.js');
const { buildScript } = require('./page-script.js');
const { buildRelayMessage, relayToAiSession } = require('./relay.js');

// ------------------------------------------------------------------
// 宿主 JSON-RPC
// ------------------------------------------------------------------

let hostSeq = 0;
const hostPending = new Map();

function send(message) {
  process.stdout.write(JSON.stringify(message) + '\n');
}

function hostCall(method, params) {
  const id = 'host-' + (++hostSeq);
  return new Promise((resolve, reject) => {
    hostPending.set(id, { resolve, reject });
    send({ jsonrpc: '2.0', id, method, params: params || {} });
  });
}

// ------------------------------------------------------------------
// 配置（存 data://config.json）
// ------------------------------------------------------------------

const DEFAULT_CONFIG = {
  target: 'zh',
  mode: 'replace',
  maxChars: 0,
};

let configCache = null;

async function loadConfig() {
  if (configCache) return configCache;
  configCache = { ...DEFAULT_CONFIG };
  try {
    const res = await hostCall('host.fs.read', { path: 'data://config.json' });
    const parsed = JSON.parse(res.content);
    // 旧配置里的字段已废弃，读进来忽略即可
    configCache = { ...DEFAULT_CONFIG, ...parsed, engine: 'relay', providerId: '', model: '' };
  } catch (e) {
    // 没有配置文件就用默认值
  }
  return configCache;
}

async function saveConfig(patch) {
  const cur = await loadConfig();
  configCache = { ...cur, ...patch, engine: 'relay', providerId: '', model: '' };
  await hostCall('host.fs.write', {
    path: 'data://config.json',
    content: JSON.stringify(configCache, null, 2),
  });
  return configCache;
}

// ------------------------------------------------------------------
// 页面注入（仍走 browser 工具，但只用于状态查询；翻译本体交给 AI 会话）
// ------------------------------------------------------------------

/**
 * 调用内置浏览器工具。失败不抛 —— 状态查询只是锦上添花，翻译不依赖它。
 */
async function tryBrowser(action, args) {
  try {
    const res = await hostCall('host.tools.execute', {
      name: 'browser',
      arguments: { action, ...(args || {}) },
      timeoutMs: 15000,
    });
    if (res && res.status === 'success') return res.data;
    return null;
  } catch (e) {
    return null;
  }
}

function parseReport(value) {
  if (value === null || value === undefined) return null;
  if (typeof value === 'object') {
    if (value.detail !== undefined && value.detail !== null) {
      const inner = parseReport(value.detail);
      if (inner) return inner;
    }
    if (value.value !== undefined && value.value !== null) {
      const inner = parseReport(value.value);
      if (inner) return inner;
    }
    if (value.ok !== undefined || value.nodes !== undefined) return value;
    return null;
  }
  if (typeof value !== 'string') return null;
  try { return JSON.parse(value); } catch (e) { return null; }
}

async function runOnPage(action, extra) {
  const data = await tryBrowser('evaluate', { script: buildScript({ action, ...(extra || {}) }) });
  return parseReport(data);
}

// ------------------------------------------------------------------
// 译文缓存（进程内，按 目标语言 + 原文）
// ------------------------------------------------------------------

const CACHE_LIMIT = 4000;
const CACHE = new Map();

function cacheKey(target, text) {
  return `${target}\u0000${text}`;
}

function remember(target, text, value) {
  if (typeof value !== 'string' || value.trim() === '') return;
  const key = cacheKey(target, text);
  CACHE.delete(key);
  CACHE.set(key, value);
  while (CACHE.size > CACHE_LIMIT) {
    CACHE.delete(CACHE.keys().next().value);
  }
}

// ------------------------------------------------------------------
// 巡场：定期探测页面状态（只读，不干预）
// ------------------------------------------------------------------

const PATROL_INTERVAL = 5000;
let patrolTimer = null;
let patrolling = false;

async function patrolOnce() {
  if (patrolling) return;
  patrolling = true;
  try {
    const report = await runOnPage('ping');
    // 只探测，不做任何动作。翻译由 AI 会话驱动。
  } catch (e) {
    // 静默
  } finally {
    patrolling = false;
  }
}

function startPatrol() {
  if (patrolTimer) return;
  patrolTimer = setInterval(() => { void patrolOnce(); }, PATROL_INTERVAL);
  if (patrolTimer.unref) patrolTimer.unref();
}

function stopPatrol() {
  if (patrolTimer) clearInterval(patrolTimer);
  patrolTimer = null;
}

// ------------------------------------------------------------------
// 工具 handler
// ------------------------------------------------------------------

const handlers = {
  'tools.translatePage': async (args) => {
    startPatrol();

    const action = String((args && args.action) || 'translate');
    const cfg = await loadConfig();

    const opts = {
      target: (args && args.target) || cfg.target,
      mode: (args && args.mode) || cfg.mode,
      maxChars: args && args.maxChars !== undefined ? Number(args.maxChars) : cfg.maxChars,
    };

    if (action === 'status' || action === 'ping') {
      const report = await runOnPage('ping');
      return {
        ok: true,
        action,
        page: report ? { url: report.url, title: report.title, state: report.state, total: report.total, already: report.already } : null,
        config: { target: cfg.target, mode: cfg.mode },
        languages: LANG_NAMES,
        message: report
          ? '页面：' + (report.title || report.url)
          : '插件读不到浏览器页面（这正常）。翻译任务会派给 AI 会话，由它自己操作浏览器。',
      };
    }

    if (action === 'diagnose') {
      const checks = [];
      const probe = async (label, fn) => {
        const t0 = Date.now();
        try {
          const value = await fn();
          checks.push({ label, ok: true, ms: Date.now() - t0, value });
        } catch (e) {
          checks.push({ label, ok: false, ms: Date.now() - t0, error: String((e && e.message) || e) });
        }
      };

      await probe('会话列表', async () => {
        const res = await hostCall('host.chat.listSessions', { limit: 20 });
        return ((res && res.sessions) || []).map((s) => ({ id: s.id, title: s.title }));
      });

      await probe('browser.evaluate 最小探针', async () => {
        const d = await tryBrowser('evaluate', { script: '1+1' });
        return d;
      });

      await probe('页面状态探测', async () => {
        return await runOnPage('ping');
      });

      return {
        ok: true,
        action,
        checks,
        message: checks.map((c) => (c.ok ? 'OK ' : 'FAIL ') + c.label + ' (' + c.ms + 'ms)' + (c.error ? ' -> ' + c.error : '')).join('\n'),
      };
    }

    if (action === 'cleanup') {
      // v2 已无句柄可清，保留动作以兼容旧调用
      return { ok: true, action, message: 'v2 已不使用模型句柄，无需清理' };
    }

    if (action === 'restore') {
      const report = await runOnPage('restore');
      if (report && report.ok) {
        return { ok: true, action, restored: report.restored, message: '已还原 ' + (report.restored || 0) + ' 条' };
      }
      // 插件读不到页面：把还原任务也派给 AI 会话
      const relay = await relayToAiSession({
        target: opts.target, mode: opts.mode, nodes: [], task: 'restore',
      }, hostCall);
      return relay.ok
        ? { ok: true, action, relayed: true, message: relay.message }
        : { ok: false, action, error: relay.error };
    }

    // action === 'translate' / 'install'
    // 读一下页面（能读到就把节点带上，AI 少一步；读不到就完全交给 AI）
    let nodes = [];
    let pageUrl = '';
    let readError = null;
    try {
      const ping = await runOnPage('ping');
      if (ping && ping.url) pageUrl = ping.url;
    } catch (e) { /* 忽略 */ }

    try {
      const collected = await runOnPage('collect');
      if (collected && collected.ok) nodes = collected.nodes || [];
      else readError = (collected && collected.error) || null;
    } catch (e) {
      readError = String((e && e.message) || e);
    }

    const relay = await relayToAiSession({
      target: opts.target,
      mode: opts.mode,
      nodes,
      pageUrl,
      readError,
    }, hostCall);

    if (!relay.ok) {
      return { ok: false, action: 'translate', error: relay.error };
    }

    return {
      ok: true,
      action: 'translate',
      relayed: true,
      sent: nodes.length,
      message: relay.message + (nodes.length
        ? '（已附带 ' + nodes.length + ' 条节点，AI 直接翻译回填即可）'
        : '（插件读不到页面，AI 会自行打开并翻译）'),
    };
  },

  'hooks.boot': async () => {
    await loadConfig();
    startPatrol();
    return { ok: true, logs: ['整页翻译 v2：就绪（AI 会话代翻模式）'] };
  },

  'hooks.installed': async () => {
    await loadConfig();
    startPatrol();
    return { ok: true, logs: ['整页翻译 v2：巡场已启动（安装）'] };
  },

  'hooks.enabled': async () => {
    await loadConfig();
    startPatrol();
    return { ok: true, logs: ['整页翻译 v2：巡场已启动（启用）'] };
  },
};

// ------------------------------------------------------------------
// 消息循环
// ------------------------------------------------------------------

function handleRequest(id, method, params) {
  if (method !== 'tool.invoke' && method !== 'hook.invoke' && method !== 'ui.invoke') {
    send({ jsonrpc: '2.0', id, error: { code: 'METHOD_UNKNOWN', message: method } });
    return;
  }
  const handler = handlers[params.handler];
  if (typeof handler !== 'function') {
    send({ jsonrpc: '2.0', id, error: { code: 'HANDLER_NOT_FOUND', message: params.handler } });
    return;
  }
  Promise.resolve()
    .then(() => handler(params.args || {}))
    .then((result) => send({ jsonrpc: '2.0', id, result: result === undefined ? null : result }))
    .catch((error) => send({
      jsonrpc: '2.0',
      id,
      error: { code: 'PLUGIN_ERROR', message: String((error && error.message) || error) },
    }));
}

function handleResponse(id, message) {
  const pending = hostPending.get(id);
  if (!pending) return;
  hostPending.delete(id);
  if (message.error) pending.reject(new Error(message.error.message || 'host error'));
  else pending.resolve(message.result === undefined ? null : message.result);
}

readline.createInterface({ input: process.stdin }).on('line', (line) => {
  if (!line.trim()) return;
  let message;
  try {
    message = JSON.parse(line);
  } catch (e) {
    return;
  }
  if (message.method && message.id !== undefined) {
    handleRequest(message.id, message.method, message.params || {});
  } else if (message.method) {
    return;
  } else if (message.id !== undefined) {
    handleResponse(String(message.id), message);
  }
});

process.on('SIGTERM', stopPatrol);
process.on('SIGINT', stopPatrol);

module.exports = {
  squeeze,
  __parseReport: parseReport,
  __runOnPage: runOnPage,
  __loadConfig: loadConfig,
  __handlers: handlers,
  __CACHE: CACHE,
};
