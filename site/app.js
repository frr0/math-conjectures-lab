"use strict";

const LEGEND = {
  "✅": ["lean", "Lean-verified"],
  "🟢": ["cas", "Computer-assisted"],
  "🟡": ["partial", "Partial Lean"],
  "⬜": ["partial", "Written only"],
};
const app = document.getElementById("app");
let DATA = null;
let filter = "all";

const esc = (s) => s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);

// Markdown + math: pull $...$ / $$...$$ out before marked (which would eat backslashes), render with KaTeX.
function renderMd(src, linkBase) {
  const math = [];
  const stash = (tex, display) => {
    math.push({ tex, display });
    return `@@MATH${math.length - 1}@@`;
  };
  // protect code spans first so `$` inside code stays literal
  const code = [];
  src = src.replace(/`[^`\n]+`/g, (m) => { code.push(m); return `@@CODE${code.length - 1}@@`; });
  src = src.replace(/\$\$([\s\S]+?)\$\$/g, (_, t) => stash(t, true));
  src = src.replace(/\$([^$\n]+?)\$/g, (_, t) => stash(t, false));
  src = src.replace(/@@CODE(\d+)@@/g, (_, i) => code[+i]);
  let html = marked.parse(src);
  html = html.replace(/@@MATH(\d+)@@/g, (_, i) => {
    const { tex, display } = math[+i];
    try { return katex.renderToString(tex, { displayMode: display, throwOnError: false }); }
    catch { return esc(tex); }
  });
  const div = document.createElement("div");
  div.innerHTML = html;
  div.querySelectorAll("a[href]").forEach((a) => {
    const h = a.getAttribute("href");
    if (!/^(https?:|#|mailto:)/.test(h)) a.href = linkBase + h;
  });
  return div.innerHTML;
}

function badge(b) {
  const [cls, label] = LEGEND[b] || ["partial", b];
  return `<span class="badge ${cls}">${b} ${label}</span>`;
}

function inline(s) { return renderMd(s.trim(), "#").replace(/^<p>|<\/p>\s*$/g, ""); }

function renderList() {
  const es = DATA.entries;
  const proved = es.filter((e) => /^Proved/i.test(e.outcome)).length;
  const disproved = es.filter((e) => /^Disproved/i.test(e.outcome)).length;
  const lean = es.filter((e) => e.badge === "✅").length;
  const shown = es.filter((e) => filter === "all" || (filter === "lean" ? e.badge === "✅"
    : filter === "proved" ? /^Proved/i.test(e.outcome) : /^Disproved/i.test(e.outcome)));
  const btn = (k, label) => `<button data-f="${k}" aria-pressed="${filter === k}">${label}</button>`;
  app.innerHTML = `
    <h1>Resolved conjectures</h1>
    <p class="muted">OEIS conjectures settled by proof or counterexample, checked in Python and Lean 4.</p>
    <div class="stats">
      <div><b>${es.length}</b>results</div><div><b>${proved}</b>proved</div>
      <div><b>${disproved}</b>disproved</div><div><b>${lean}</b>fully in Lean</div>
    </div>
    <div class="filters">${btn("all", "All")}${btn("proved", "Proved")}${btn("disproved", "Disproved")}${btn("lean", "✅ Lean")}</div>
    <ul class="list">${shown.slice().reverse().map((e) => `
      <li><a class="item" href="#/${e.slug}">
        <div class="row"><span class="t">${inline(e.title)}</span>${badge(e.badge)}</div>
        <div class="o">${inline(e.outcome)}</div>
      </a></li>`).join("")}</ul>`;
  app.querySelectorAll(".filters button").forEach((b) =>
    b.addEventListener("click", () => { filter = b.dataset.f; renderList(); }));
}

function renderEntry(e) {
  const gh = `https://github.com/${DATA.repo}`;
  const base = `${gh}/blob/${DATA.commit}/results/${e.slug}/`;
  const md = e.readme.replace(/^# .*\n/, "");
  const title = e.readme.match(/^# (.*)$/m);
  app.innerHTML = `
    <a class="back" href="#/">← All results</a>
    <h1>${title ? inline(title[1]) : esc(e.slug)}</h1>
    <div class="meta">${badge(e.badge)}
      <a href="${gh}/tree/${DATA.commit}/results/${e.slug}">results/${e.slug}</a>
      ${e.lean ? `<a href="${gh}/blob/${DATA.commit}/${e.lean}">${e.lean.split("/").pop()}</a>` : ""}
      ${e.updated ? `<span>updated ${e.updated}</span>` : ""}</div>
    <article class="doc">${renderMd(md, base)}</article>`;
  window.scrollTo(0, 0);
}

function route() {
  if (!DATA) return;
  const slug = location.hash.replace(/^#\/?/, "");
  const e = DATA.entries.find((x) => x.slug === slug);
  e ? renderEntry(e) : renderList();
}

fetch("data.json").then((r) => r.json()).then((d) => {
  DATA = d;
  const gh = `https://github.com/${d.repo}`;
  document.getElementById("repo-link").href = gh;
  document.getElementById("foot").innerHTML =
    `Built from <a href="${gh}/commit/${d.commit}"><code>${d.commit.slice(0, 7)}</code></a> · ` +
    `${esc(d.commit_subject)} · ${new Date(d.commit_date).toLocaleString()}`;
  route();
}).catch(() => { app.innerHTML = `<p class="muted">Could not load data.json.</p>`; });
window.addEventListener("hashchange", route);
