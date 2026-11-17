'use strict';

/**
 * 翻译编排相关的常量与纯函数。
 * 移植自 dsh-inpage-translator 的 lib/constants.js，保留其分块、提示词与 JSON 解析逻辑。
 */

const DEFAULTS = {
  target: 'zh',
  mode: 'replace',
  maxChars: 0,
  chunkChars: 1200,
  chunkNodes: 40,
  concurrency: 3,
  llmTimeoutMs: 90000,
  adaptiveMinChars: 4000,
  adaptiveMaxChars: 24000,
};

const LANG_NAMES = {
  zh: '简体中文',
  'zh-TW': '繁體中文',
  en: 'English',
  ja: '日本語',
  ko: '한국어',
  ru: 'Русский',
  fr: 'Français',
  de: 'Deutsch',
  es: 'Español',
};

const MAX_OUTPUT_TOKENS = 8192;

/** 压缩空白：模型对多余空格敏感。 */
function squeeze(text) {
  return String(text == null ? '' : text).replace(/\s+/g, ' ').trim();
}

/**
 * 从模型输出里抠出 JSON 对象。
 * 模型有时会包一层 ```json，或在前后加话，所以先试整体解析，再试花括号截取。
 */
function extractJsonObject(raw) {
  const text = String(raw == null ? '' : raw).trim();
  if (!text) return null;

  const fenced = text.match(/```(?:json)?\s*([\s\S]*?)```/i);
  const candidates = [];
  if (fenced) candidates.push(fenced[1].trim());
  candidates.push(text);

  const first = text.indexOf('{');
  const last = text.lastIndexOf('}');
  if (first >= 0 && last > first) candidates.push(text.slice(first, last + 1));

  for (const candidate of candidates) {
    try {
      const parsed = JSON.parse(candidate);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) return parsed;
    } catch (e) {
      // 继续试下一个候选
    }
  }
  return null;
}

/**
 * 把模型返回的对象规整成 { index: text } 表。
 * 接受 { "0": "..." } 或 { "translations": { "0": "..." } } 或 { "0": { "text": "..." } }。
 */
function normalizeTranslations(parsed) {
  const table = {};
  if (!parsed || typeof parsed !== 'object') return table;

  let source = parsed;
  if (parsed.translations && typeof parsed.translations === 'object') source = parsed.translations;

  for (const key of Object.keys(source)) {
    const value = source[key];
    let text = '';
    if (typeof value === 'string') text = value;
    else if (value && typeof value === 'object') {
      if (typeof value.text === 'string') text = value.text;
      else if (typeof value.translated === 'string') text = value.translated;
      else if (typeof value.translation === 'string') text = value.translation;
    }
    if (text.trim() === '') continue;
    table[String(key)] = text;
  }
  return table;
}

/**
 * 把节点切成若干块。
 *
 * 两层限制：
 *   - 单块上限：chunkChars（字符）与 chunkNodes（条数），任一达到就切下一块；
 *   - 本次总额度：maxChars，超出部分丢弃并计数（dropped）。
 *
 * 去重发生在限额之前 —— 页面上重复的菜单/表头很多，去重后同样的额度能覆盖更大的页面。
 */
function chunkNodes(nodes, options) {
  const opts = { ...DEFAULTS, ...(options || {}) };
  const maxChars = Number(opts.maxChars) > 0 ? Number(opts.maxChars) : Infinity;
  const chunkChars = Math.max(100, Number(opts.chunkChars) || DEFAULTS.chunkChars);
  const chunkNodesLimit = Math.max(1, Number(opts.chunkNodes) || DEFAULTS.chunkNodes);

  const chunks = [];
  let current = [];
  let currentChars = 0;
  let accepted = 0;
  let totalChars = 0;
  let dropped = 0;
  let budgetUsed = 0;

  const flush = () => {
    if (current.length) {
      chunks.push(current);
      accepted += current.length;
    }
    current = [];
    currentChars = 0;
  };

  for (const node of nodes) {
    const text = squeeze(node && node.text);
    const index = Number(node && node.index);
    if (!text || !Number.isFinite(index)) continue;
    const len = text.length;
    totalChars += len;

    // 本次总额度已用完：后面的全部丢弃
    if (budgetUsed + len > maxChars) {
      dropped += 1;
      continue;
    }

    // 单块超限：先结掉当前块
    if (current.length && (currentChars + len > chunkChars || current.length >= chunkNodesLimit)) {
      flush();
    }

    // 单条本身就超过单块上限：切出来单独成块
    if (len > chunkChars) {
      if (current.length) flush();
      chunks.push([{ index, text }]);
      accepted += 1;
      budgetUsed += len;
      continue;
    }

    current.push({ index, text });
    currentChars += len;
    budgetUsed += len;
  }

  flush();

  return { chunks, accepted, dropped, totalChars };
}

/**
 * 构造送给模型的提示词。
 * 要求模型返回 JSON 对象，键是节点编号，值是译文。
 */
function buildPrompt(chunk, options) {
  const opts = { ...DEFAULTS, ...(options || {}) };
  const lang = LANG_NAMES[opts.target] || opts.target;
  const items = chunk.map((node) => `${node.index}\t${node.text}`).join('\n');

  const system = [
    'You are a professional translator that converts web page text into ' + lang + '.',
    'You will receive numbered lines in the form "<number>\\t<text>".',
    'Return a single JSON object mapping each number to its translation.',
    'Rules:',
    '- Output ONLY the JSON object, no prose, no markdown fences.',
    '- Keep every input number as a key. Do not add or drop numbers.',
    '- Translate meaning, not word by word. Keep names, identifiers, URLs and code untouched.',
    '- Preserve the original tone and formatting (line breaks, punctuation).',
    '- If a line is already in the target language, return it unchanged.',
    '- Never return an empty string.',
  ].join('\n');

  const user = [
    'Translate these lines into ' + lang + '.',
    '',
    items,
  ].join('\n');

  return { system, user };
}

module.exports = {
  DEFAULTS,
  LANG_NAMES,
  MAX_OUTPUT_TOKENS,
  squeeze,
  extractJsonObject,
  normalizeTranslations,
  chunkNodes,
  buildPrompt,
};
