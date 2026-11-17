---
description: 当用户要求把网页翻译成中文、把当前页面内容翻译出来、或问「这个页面在讲什么」时使用。
---

用整页翻译插件把内置浏览器当前页面翻成中文。

## 怎么用

调用 `plugin__community_inpage_translator__translate_page`：

| 用户意图 | action |
| --- | --- |
| 「把这个页面翻成中文」 | `translate` |
| 「这个英文网页写了什么」 | `translate` |
| 「把页面恢复成原文」 | `restore` |
| 「翻译功能现在什么状态」 | `status` |
| 「翻译怎么不工作」 | `diagnose` |

默认 `action=translate`、`target=zh`、`mode=replace`。

## 工作方式（重要）

插件**不直接操作浏览器，也不自己调模型**。它做的是：

1. 插件收集当前页面的文本节点（打上 `data-aicode-ipt-node` 标记）
2. 插件把「翻译这些节点并回填」的任务派给当前工作区最近的 AI 会话
3. **你（AI 会话）** 调用插件的 `translate_page`，`action=translate`，参数 `translations` 带上
   「编号 → 译文」的 JSON，把译文写回页面
4. 插件把译文按编号写回各节点的 `textContent`

所以当收到 `[整页翻译任务]` 时，你要做的是：

- 读完任务里给的节点数据
- 翻译每个 `text`（保持 `index` 对应关系）
- 调用插件工具 `translate_page`，`action=translate`，把译文表传回去
- 用一句话说明回填了多少条

任务也可能由**用户点击页面上的「🈯 译」按钮**触发（插件巡场发现后派发）——
这时你同样收到 `[整页翻译任务]`，处理方式完全一样。

**注意**：搜索框里的查询语法（如 `is:pr state:open`）、代码标识符、
用户名和 URL 不该翻译 —— 翻译了反而不能用。保持原样。

## 已知边界

- GitHub 等 React 页面重渲染时可能覆盖译文，重翻一次即可
- 跨域 iframe 里的文字读不到
- 图片、canvas、输入框里的值不会被翻译
