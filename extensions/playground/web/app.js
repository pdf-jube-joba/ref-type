const source = document.querySelector('#source');
const lines = document.querySelector('#lines');
const status = document.querySelector('#status');
const automatic = document.querySelector('#automatic');
const storageKey = 'ref-type-playground-source';
const example = String.raw`\module Playground {
  \definition identity: \forall (A: \Prop) -> A -> A :=
    \fun (A: \Prop) => \fun (x: A) => x;

  \infer identity;
  \eval identity;
}
`;

let revision = 0;
let timer;
let running = false;
let queued = false;

try {
  source.value = localStorage.getItem(storageKey) ?? example;
} catch {
  source.value = example;
}

function setStatus(text, state = '') {
  status.textContent = text;
  status.dataset.state = state;
}

function updatePosition() {
  const before = source.value.slice(0, source.selectionStart);
  const rows = before.split('\n');
  document.querySelector('#position').textContent = `行 ${rows.length} · 列 ${Array.from(rows.at(-1)).length + 1}`;
}

function updateEditor() {
  lines.textContent = Array.from({ length: source.value.split('\n').length }, (_, index) => index + 1).join('\n');
  lines.scrollTop = source.scrollTop;
  updatePosition();
}

function edited() {
  revision++;
  queued = false;
  clearTimeout(timer);
  updateEditor();
  try { localStorage.setItem(storageKey, source.value); } catch { /* Storage may be disabled. */ }
  setStatus('変更あり');
  if (automatic.checked) timer = setTimeout(run, 600);
}

function display(selector, messages, emptyText) {
  const element = document.querySelector(selector);
  element.textContent = messages.length ? messages.join('\n\n') : emptyText;
  element.classList.toggle('empty', !messages.length);
}

async function run() {
  clearTimeout(timer);
  if (running) {
    queued = true;
    return;
  }
  running = true;
  queued = false;
  const checkedRevision = revision;
  setStatus('チェック中…');
  try {
    const response = await fetch('/api/check', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ source: source.value }),
    });
    if (!response.ok) throw new Error(await response.text());
    const result = await response.json();
    if (revision !== checkedRevision) return;
    display('#diagnostics', result.diagnostics, 'エラーはありません。');
    display('#outputs', result.outputs, '出力はありません。');
    document.querySelector('#error-count').textContent = result.diagnostics.length;
    document.querySelector('#elapsed').textContent = `${result.elapsed_ms} ms`;
    setStatus(result.success ? 'チェック完了' : 'エラーあり', result.success ? 'success' : 'error');
  } catch (error) {
    if (revision !== checkedRevision) return;
    display('#diagnostics', [`サーバーとの通信に失敗しました。\n${error.message}`], '');
    display('#outputs', [], '出力はありません。');
    document.querySelector('#error-count').textContent = '1';
    document.querySelector('#elapsed').textContent = '';
    setStatus('通信エラー', 'error');
  } finally {
    running = false;
    if (queued) run();
  }
}

source.addEventListener('input', edited);
source.addEventListener('scroll', () => { lines.scrollTop = source.scrollTop; });
source.addEventListener('click', updatePosition);
source.addEventListener('keyup', updatePosition);
source.addEventListener('keydown', event => {
  if (event.key === 'Tab' && !event.shiftKey) {
    event.preventDefault();
    source.setRangeText('  ', source.selectionStart, source.selectionEnd, 'end');
    edited();
  }
});
document.addEventListener('keydown', event => {
  if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') {
    event.preventDefault();
    run();
  }
});
automatic.addEventListener('change', () => {
  clearTimeout(timer);
  queued = false;
  if (automatic.checked) run();
});
document.querySelector('#run').addEventListener('click', run);
updateEditor();
run();
