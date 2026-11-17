'use strict';

/**
 * 页面侧脚本：装按钮 → 收集可译文本并打标 → 按标号回填译文/还原。
 *
 * 移植自 dsh-inpage-translator 的 lib/page-script.js，改动：
 *   1. 注入方式改为 browser 工具的 evaluate（仍是表达式字符串）；
 *   2. 属性前缀由 data-dsh-pt 改为 data-aicode-ipt，避免与原插件同页共存时冲突；
 *   3. **脚本压缩到最小** —— 宿主通过 WebView 通道传递脚本，过长可能撑爆通道。
 *
 * 两条铁律（沿用原插件）：
 *   1. 用内联样式，不用 <style> —— style 元素受页面 style-src CSP 约束；
 *   2. 文案用 textContent 写，不拼 HTML 字符串。
 */

const ATTRS = {
  rootId: 'aicode-ipt-root',
  skip: 'data-aicode-ipt-skip',
  node: 'data-aicode-ipt-node',
  orig: 'data-aicode-ipt-orig',
  trans: 'data-aicode-ipt-trans',
  req: 'data-aicode-ipt-req',
  mode: 'data-aicode-ipt-mode',
  lang: 'data-aicode-ipt-lang',
  state: 'data-aicode-ipt-state',
  pos: 'data-aicode-ipt-pos',
  drag: 'data-aicode-ipt-drag',
};

/**
 * 构造要注入页面的脚本表达式。
 * @param {object} req {action,target,mode,label,translations,message}
 * @returns {string}
 */
function buildScript(req) {
  const cfg = JSON.stringify(ATTRS);
  const reqJson = JSON.stringify(req || {});
  return `(function(){
var C=${cfg},R=${reqJson},H=320,T=10,K='aicode-ipt-pos';
function sv(){try{var v=JSON.parse(localStorage.getItem(K));return v&&typeof v=='object'?v:null}catch(e){return null}}
function ws(v){try{localStorage.setItem(K,JSON.stringify(v))}catch(e){}}
function fs(){var l=document.querySelectorAll('iframe,frame'),t=0,c=0,i;for(i=0;i<l.length;i++){t++;var s=false;try{s=!!(l[i].contentDocument&&l[i].contentDocument.body)}catch(e){}if(!s)c++}return{total:t,cross:c}}
try{
var b=document.body||document.documentElement;
if(!b)return JSON.stringify({ok:false,error:'no-body'});
var x=document.getElementById(C.root),pv=x?(x.getAttribute(C.state)||'idle'):'';
function cl(){var n=[],w=document.createTreeWalker(b,NodeFilter.SHOW_TEXT,{acceptNode:function(v){var p=v.parentElement;if(!p)return 0;if(p.closest('['+C.skip+']'))return 0;if(p.closest('script,style,noscript,template,textarea,select,svg,canvas'))return 0;var t=p.tagName;if(t=='SCRIPT'||t=='STYLE'||t=='NOSCRIPT'||t=='TEXTAREA'||t=='SELECT')return 0;if(p.hasAttribute('contenteditable'))return 0;if(p.getAttribute('aria-hidden')=='true')return 0;if((v.nodeValue||'').replace(/\\s+/g,' ').trim().length<2)return 0;return 1}}),i=0,e;while(w.nextNode()){e=w.currentNode.parentElement;if(!e||e.hasAttribute(C.node))continue;e.setAttribute(C.node,String(i));e.setAttribute(C.orig,e.textContent||'');n.push({index:i,text:(e.textContent||'').replace(/\\s+/g,' ').trim()});i++}return n}
function clb(o,l){var n=cl();return o>=n.length?[]:n.slice(o,o+l)}
function cm(){return document.querySelectorAll('['+C.node+']').length}
function ct(){return document.querySelectorAll('['+C.node+']['+C.trans+']').length}
function ap(t){var l=document.querySelectorAll('['+C.node+']'),h=0,i,e,k;for(i=0;i<l.length;i++){e=l[i];k=e.getAttribute(C.node);if(t&&Object.prototype.hasOwnProperty.call(t,k)){e.textContent=String(t[k]);e.setAttribute(C.trans,String(t[k]));h++}}return h}
function rs(){var l=document.querySelectorAll('['+C.node+']'),i,e;for(i=0;i<l.length;i++){e=l[i];if(e.hasAttribute(C.orig))e.textContent=e.getAttribute(C.orig);e.removeAttribute(C.trans)}return l.length}
function ss(r,s,h){r.setAttribute(C.state,s);var l=r.querySelector('[data-aicode-ipt-label]');if(l)l.textContent=s=='busy'?'…':(s=='done'?(h||'原'):(s=='error'?'!':(h||'译')));var n=r.querySelector('[data-aicode-ipt-note]');if(n){n.textContent=s=='error'?String(h||''):'';n.style.display=s=='error'?'inline':'none'}}
function pl(r){var q=r.getBoundingClientRect(),w=window.innerWidth||0,h=window.innerHeight||0;r.style.left=Math.max(0,Math.min(w-r.offsetWidth,q.left))+'px';r.style.right='auto';r.style.top=Math.max(0,Math.min(h-r.offsetHeight,q.top))+'px';r.style.bottom='auto';var p={left:Math.round(q.left),top:Math.round(q.top)};try{r.setAttribute(C.pos,JSON.stringify(p))}catch(e){}ws(p)}
function sp(r){var p=sv();if(!p)return false;var h=window.innerHeight||0;t=typeof p.top=='number'?Math.max(0,Math.min(h-r.offsetHeight,p.top)):0;if(typeof p.left=='number'){r.style.left=Math.max(0,p.left)+'px';r.style.right='auto';r.style.top=t+'px';r.style.bottom='auto';return true}return false}
function dg(r){if(r.getAttribute(C.drag)=='bound')return;r.setAttribute(C.drag,'bound');var h=null,ht=null,dr=false,mv=false,sc=false;
function dn(e){if(e.button!==undefined&&e.button!=0)return;var q=r.getBoundingClientRect();h={x:e.clientX,y:e.clientY,l:q.left,t:q.top};dr=false;mv=false;if(ht)clearTimeout(ht);ht=setTimeout(function(){if(!h)return;dr=true;sc=true;r.setAttribute(C.drag,'dragging');r.style.transition='none'},H);window.addEventListener('mousemove',mv2,true);window.addEventListener('mouseup',up,true)}
function mv2(e){if(!h)return;var dx=e.clientX-h.x,dy=e.clientY-h.y;if(!dr){if(Math.abs(dx)<=T&&Math.abs(dy)<=T)return;if(ht){clearTimeout(ht);ht=null}mv=true;dr=true;sc=true;r.setAttribute(C.drag,'dragging');r.style.transition='none'}e.preventDefault();e.stopPropagation();var w=window.innerWidth||0,i=window.innerHeight||0;r.style.left=Math.max(0,Math.min(w-r.offsetWidth,h.l+dx))+'px';r.style.top=Math.max(0,Math.min(i-r.offsetHeight,h.t+dy))+'px';r.style.right='auto';r.style.bottom='auto'}
function up(){window.removeEventListener('mousemove',mv2,true);window.removeEventListener('mouseup',up,true);if(ht){clearTimeout(ht);ht=null}if(dr){dr=false;r.setAttribute(C.drag,'bound');r.style.transition='left .16s ease, top .16s ease';pl(r);setTimeout(function(){sc=false},60)}else if(mv){sc=true;setTimeout(function(){sc=false},60)}h=null}
r.addEventListener('mousedown',dn,true);
r.addEventListener('click',function(e){if(sc){e.preventDefault();e.stopPropagation();return}e.preventDefault();e.stopPropagation();var s=r.getAttribute(C.state),q=r.getAttribute(C.req);if(s=='busy'||q=='pending'||q=='translating')return;r.setAttribute(C.req,s=='done'?'restore':'pending');var l=r.querySelector('[data-aicode-ipt-label]');if(l)l.textContent='…';if(s=='done')r.setAttribute(C.state,'idle');else r.setAttribute(C.state,'busy')},true)}
function bb(){var r=document.createElement('div');r.id=C.root;r.setAttribute(C.skip,'');r.setAttribute(C.state,'idle');r.style.cssText='position:fixed;right:16px;bottom:88px;z-index:2147483647;display:flex;align-items:center;gap:6px;padding:8px 12px;border-radius:999px;background:rgba(28,30,36,.92);color:#fff;font:13px/1 system-ui,sans-serif;cursor:pointer;box-shadow:0 6px 18px rgba(0,0,0,.35);border:1px solid rgba(255,255,255,.18);user-select:none;pointer-events:auto;touch-action:none';r.title='整页翻译：点一下翻译，按住可拖动';
var g=document.createElement('span');g.setAttribute('data-aicode-ipt-glyph','');g.textContent='\\uD83C\\uDDEF';g.style.cssText='font-size:14px;line-height:1';
var l=document.createElement('span');l.setAttribute('data-aicode-ipt-label','');l.textContent='译';
var n=document.createElement('span');n.setAttribute('data-aicode-ipt-note','');n.style.cssText='display:none;color:#ffb4b4;font-size:11px;max-width:180px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap';
r.appendChild(g);r.appendChild(l);r.appendChild(n);dg(r);return r}
var a=(R&&typeof R.action=='string')?R.action:'inspect';
if(!x){b.appendChild(bb());x=document.getElementById(C.root)}
var rt=x;
try{if(!rt.getAttribute(C.pos))sp(rt)}catch(e){}
if(a=='ping'||a=='probe')return JSON.stringify({ok:true,action:a,url:location.href,title:document.title,state:rt.getAttribute(C.state)||'idle',request:rt.getAttribute(C.req)||'',total:cm(),already:ct(),frames:fs(),bodyChars:(b.innerText||'').length});
if(a=='install'||a=='inspect'){if(pv==''||pv=='idle')ss(rt,'idle',(R&&R.label)||'译')}
else if(a=='collect'){var s=document.querySelectorAll('['+C.node+']'),i;for(i=0;i<s.length;i++){s[i].removeAttribute(C.node);s[i].removeAttribute(C.orig);s[i].removeAttribute(C.trans)}}
else if(a=='collectMore'){var o=(R&&R.offset)||0,l=(R&&R.limit)||40,nb=clb(o,l);return JSON.stringify({ok:true,action:a,nodes:nb,total:cm(),already:ct(),frames:fs()})}
else if(a=='translate'){rt.setAttribute(C.lang,(R&&R.target)||'zh');rt.setAttribute(C.mode,(R&&R.mode)||'replace');rt.setAttribute(C.req,'');var n2=ap(R&&R.translations);ss(rt,'done','原');return JSON.stringify({ok:true,action:a,applied:n2,state:rt.getAttribute(C.state),total:cm(),already:ct(),nodes:[]})}
else if(a=='restore'){rt.setAttribute(C.req,'');var n3=rs();ss(rt,'idle',(R&&R.label)||'译');return JSON.stringify({ok:true,action:a,restored:n3,state:'idle',total:cm(),already:0,nodes:[]})}
else if(a=='error'){ss(rt,'error',(R&&R.message)||'failed')}
var fr=cl();
return JSON.stringify({ok:true,action:a,state:rt.getAttribute(C.state),request:rt.getAttribute(C.req)||'',added:fr.length,nodes:fr,frames:fs(),total:cm(),already:ct()});}catch(e){return JSON.stringify({ok:false,error:String((e&&e.message)||e)})}
})()`;
}

module.exports = { ATTRS, buildScript };
