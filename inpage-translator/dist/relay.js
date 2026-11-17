'use strict';

/**
 * 两跳方案：插件派任务给 AI 会话，由 AI 用 browser 工具完成页面注入与回填。
 *
 * 为什么需要这条路径：
 *   browser 工具是 AI 会话的能力，插件通过 host.tools.execute 代执行时，
 *   未必能拿到浏览器的活动标签页（表现为 evaluate 超时）。
 *   但 host.chat.sendMessage 可以直接给 AI 会话发消息，
 *   让 AI 自己调 browser 工具 —— 它有标签页，工具也走原生路径。
 *
 * 协议（插件 → AI）：
 *   插件把「本页待译节点 + 目标语言」写成一份 JSON 载荷，
 *   通过聊天消息交给 AI；AI 按约定调本插件的 translate_page 工具回填。
 *
 * 由于宿主文档未说明 browser 能否被插件代执行，本模块两种模式都支持：
 *   mode=direct  —— 插件直接调 browser（快，但要能拿到标签页）
 *   mode=relay   —— 插件派消息给 AI 会话（慢，但稳）
 */

const RELAY_TAG = '[整页翻译任务]';
const RELAY_TIMEOUT_MS = 180000;

/**
 * 构造交给 AI 的任务说明。
 * @param {object} payload {target, mode, nodes, pageUrl, readError, translations?}
 */
function buildRelayMessage(payload) {
  const lines = [];
  lines.push(RELAY_TAG + ' 请完成下面这个整页翻译任务。');
  lines.push('');
  lines.push('目标语言：' + (payload.target || 'zh'));
  lines.push('翻译方式：' + (payload.mode || 'replace'));
  lines.push('');

  const hasNodes = Array.isArray(payload.nodes) && payload.nodes.length > 0;
  const hasTranslations = payload.translations && Object.keys(payload.translations).length;

  if (payload.task === 'restore') {
    lines.push('任务：把浏览器当前页面还原成原文。');
    lines.push('调用插件工具 translate_page，action=restore 即可。');
  } else if (hasTranslations) {
    lines.push('任务：把下面的译文表回填到页面。');
    lines.push('调用插件工具 translate_page，action=translate，参数 translations 为下面这张表。');
    lines.push('');
    lines.push('译文表（JSON）：');
    lines.push(JSON.stringify(payload.translations));
  } else if (hasNodes) {
    lines.push('任务：把下面的节点翻译成' + (payload.target || 'zh') + '并回填到页面。');
    lines.push('');
    lines.push('第一步：调用插件工具 translate_page，action=translate，参数 translations 为「编号 -> 译文」的 JSON。');
    lines.push('第二步：把下面每个节点的文本翻译成' + (payload.target || 'zh') + '，得到编号与译文的对应关系。');
    lines.push('');
    lines.push('节点数据（JSON 数组，index 与 text）：');
    lines.push(JSON.stringify(payload.nodes));
  } else {
    lines.push('任务：翻译浏览器当前页面。');
    lines.push('');
    lines.push('第一步：用 browser 工具查看当前标签页（browser 的 listTabs 或 getText），确认页面内容。');
    lines.push('第二步：把页面上的可见文本翻译成' + (payload.target || 'zh') + '。');
    lines.push('第三步：调用插件工具 translate_page，action=collect，取出这一页的节点。');
    lines.push('第四步：把节点翻译成' + (payload.target || 'zh') + '，得到「编号 -> 译文」的对应关系。');
    lines.push('第五步：调用插件工具 translate_page，action=translate，把译文回填到页面。');
    if (payload.pageUrl) {
      lines.push('');
      lines.push('（插件读不到页面，参考地址：' + payload.pageUrl + '）');
    }
    if (payload.readError) {
      lines.push('（插件侧读取失败：' + payload.readError + '）');
    }
  }

  lines.push('');
  lines.push('完成后用一句话说明回填了多少条即可。');
  return lines.join('\n');
}

/**
 * 把任务派给最近的 AI 会话。
 *
 * @param {object} payload
 * @param {function} hostCall 宿主 JSON-RPC 调用函数
 * @returns {Promise<{ok:boolean, sessionId?:string, message?:string, error?:string}>}
 */
async function relayToAiSession(payload, hostCall) {
  let sessions = [];
  try {
    const res = await hostCall('host.chat.listSessions', { limit: 20 });
    sessions = (res && res.sessions) || [];
  } catch (e) {
    return { ok: false, error: '列会话失败：' + String((e && e.message) || e) };
  }

  if (sessions.length === 0) {
    return { ok: false, error: '当前工作区没有可用的 AI 会话，请先在聊天里发一条消息' };
  }

  // 用最近更新的会话
  const sorted = sessions.slice().sort((a, b) => {
    const ta = (a && (a.updatedAt || a.createdAt)) || 0;
    const tb = (b && (b.updatedAt || b.createdAt)) || 0;
    return tb - ta;
  });
  const target = sorted[0];
  const sessionId = target && (target.id || target.sessionId);
  if (!sessionId) return { ok: false, error: '会话列表里没有可用 id' };

  const text = buildRelayMessage(payload);
  try {
    await hostCall('host.chat.sendMessage', { sessionId, text });
  } catch (e) {
    return { ok: false, error: '发送消息失败：' + String((e && e.message) || e) };
  }
  return {
    ok: true,
    sessionId,
    message: '已把翻译任务派给 AI 会话（' + (target.title || sessionId) + '），它会在后台完成回填。',
  };
}

module.exports = { RELAY_TAG, RELAY_TIMEOUT_MS, buildRelayMessage, relayToAiSession };
