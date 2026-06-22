"use strict";

// Phase-cluster ordering + human labels (docs/CONJECTURES_FORMALIZATION_PLAN.md).
const CLUSTERS = [
  ["P1",  "Free wins — AACL clique cluster & Cheng–Keevash"],
  ["P9",  "Classic digraph core (Seymour, Caccetta–Häggkvist, …)"],
  ["P9b", "Maderian containment"],
  ["P2",  "Dichromatic core"],
  ["P3",  "Connectivity & Strong Arc Decompositions"],
  ["P10", "Packing & duality"],
  ["P4",  "Feedback arc set / degreewidth"],
  ["P5",  "Unavoidability"],
  ["P6",  "Heroes"],
  ["P11", "Colouring variants"],
  ["P7",  "Heavy bespoke (twin-width, H₂, 2-extremal)"],
  ["P12", "Structural width"],
  ["P8",  "Reals / Θ-growth envelopes"],
  ["G",   "General tournament theory (proved)"],
  ["?",   "Unclustered"],
];
const CLUSTER_LABEL = Object.fromEntries(CLUSTERS.map(c => c));
const CLUSTER_ORDER = Object.fromEntries(CLUSTERS.map((c, i) => [c[0], i]));

const STATUS_LABEL = {
  open: "open", proved: "proved", refuted: "refuted",
  disproved: "refuted", partial: "partial", solved: "solved", unknown: "open",
};

let DATA = [];           // all entries
const state = { q: "", status: new Set(), kind: new Set(), cluster: null };

const $ = sel => document.querySelector(sel);
const el = (tag, attrs = {}, ...kids) => {
  const n = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") n.className = v;
    else if (k === "html") n.innerHTML = v;
    else if (k.startsWith("on")) n.addEventListener(k.slice(2), v);
    else if (v != null) n.setAttribute(k, v);
  }
  for (const kid of kids) if (kid != null)
    n.append(kid.nodeType ? kid : document.createTextNode(kid));
  return n;
};
const esc = s => (s || "").replace(/[&<>]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));

function normStatus(s) { return STATUS_LABEL[s] || "open"; }

function badge(text, cls) { return el("span", { class: "badge " + cls }, text); }

function statusBadge(e) {
  const s = normStatus(e.status);
  return badge(s, "b-" + s);
}
function axiomBadge(e) {
  if (e.axiom_free) return badge("axiom-free ✓", "b-axiom");
  if (e.kind === "conjecture") return badge("formal statement only", "b-stated");
  return null;
}

// --- one entry card -------------------------------------------------------
function card(e) {
  const head = el("div", { class: "card-head", onclick: ev => {
      if (ev.target.tagName === "A") return;
      head.nextSibling.classList.toggle("collapsed");
    } },
    el("div", {},
      el("span", { class: "card-title" }, e.title), " ",
      el("span", { class: "card-id" }, e.id)),
    el("div", { class: "badges" },
      badge(e.kind, "b-kind"), statusBadge(e), axiomBadge(e)));

  const body = el("div", { class: "card-body" });

  // informal
  if (e.informal && e.informal.text) {
    const sec = el("div", { class: "sec" }, el("h4", {}, "Informal conjecture"),
      el("p", { class: "informal" }, e.informal.text));
    const src = e.informal.source || {};
    if (src.url || src.name || src.attribution) {
      const bits = [];
      if (src.attribution) bits.push(src.attribution);
      const where = src.url
        ? el("a", { href: src.url, target: "_blank", rel: "noopener" },
            src.name || "source")
        : (src.name ? document.createTextNode(src.name) : null);
      const line = el("div", { class: "src-link" }, "Source: ");
      if (src.attribution) line.append(src.attribution + (where ? " · " : ""));
      if (where) line.append(where);
      sec.append(line);
    }
    body.append(sec);
  }

  // decoded (informal reading of the formal; or "what this proof establishes")
  const grounding = e.kind === "grounding";
  const dh = el("h4", {}, grounding
    ? "What this proof establishes"
    : "Informal reading of the formal statement");
  if (!e.decoded_authored) dh.append(el("span", { class: "auto-tag" }, "auto — from doc-comment"));
  body.append(el("div", { class: "sec" }, dh, el("p", { class: "decoded" }, e.decoded || "—")));

  // formal verbatim (for grounding entries this is the lemma statement; the
  // full proof is at the GitHub line anchor)
  const f = e.formal;
  body.append(el("div", { class: "sec" },
    el("h4", {}, grounding ? "Lemma statement (Rocq) — proof at source" : "Formal statement (Rocq)"),
    el("pre", { class: "formal", html: esc(f.verbatim) }),
    el("div", { class: "formal-links" },
      el("a", { href: f.github_url, target: "_blank", rel: "noopener" },
        (grounding ? "Proof: " : "Source: ") + f.file + ":" + f.line),
      el("a", { href: f.coqdoc_url, target: "_blank", rel: "noopener" }, "coqdoc"))));

  // edges + specializes
  const edgeRows = [];
  const rel = (label, items, dir) => {
    for (const it of items) {
      const tgt = it.to || it.from;
      const known = DATA.some(x => x.id === tgt);
      const link = known
        ? el("a", { href: "#" + tgt }, tgt)
        : el("code", {}, tgt);
      edgeRows.push(el("div", { class: "edge" },
        el("span", { class: "rel" }, label),
        el("span", { class: "arrow" }, dir + " "), link,
        el("span", { class: "src-link" }, "  via " + it.thm)));
    }
  };
  const ed = e.edges || {};
  rel("implies", ed.implies || [], "→");
  rel("implied by", ed.implied_by || [], "←");
  rel("refutes", ed.refutes || [], "⊣");
  rel("refuted by", ed.refuted_by || [], "⊢");
  rel("equivalent to", ed.equiv || [], "↔");
  for (const sp of (e.specializes || [])) {
    const known = DATA.some(x => x.id === sp);
    edgeRows.push(el("div", { class: "edge" },
      el("span", { class: "rel" }, "proved instance of"),
      el("span", { class: "arrow" }, "⊑ "),
      known ? el("a", { href: "#" + sp }, sp) : el("code", {}, sp)));
  }
  if (edgeRows.length)
    body.append(el("div", { class: "sec" }, el("h4", {}, "Related statements"),
      el("div", { class: "edges" }, ...edgeRows)));

  // formal proofs that TEST this definition (reverse index)
  if (e.grounded_by && e.grounded_by.length) {
    const rows = el("div", { class: "edges" });
    for (const g of e.grounded_by)
      rows.append(el("div", { class: "edge" },
        el("span", { class: "rel" }, "tested by"),
        el("span", { class: "arrow" }, "✓ "),
        el("a", { href: "#" + g.id }, g.id),
        g.title ? document.createTextNode(" — " + g.title) : null));
    body.append(el("div", { class: "sec" },
      el("h4", {}, "Tested by (formal proofs)"), rows));
  }

  // (grounding entries:) the definitions/conjectures this proof validates
  if (e.grounds && e.grounds.length) {
    const rows = el("div", { class: "edges" });
    for (const gid of e.grounds) {
      const known = DATA.some(x => x.id === gid);
      rows.append(el("div", { class: "edge" },
        el("span", { class: "rel" }, "validates"),
        el("span", { class: "arrow" }, "⊨ "),
        known ? el("a", { href: "#" + gid }, gid) : el("code", {}, gid)));
    }
    body.append(el("div", { class: "sec" },
      el("h4", {}, "Validates (definitions tested)"), rows));
  }

  // free-form grounding notes (legacy)
  if (e.grounding && e.grounding.length) {
    const ul = el("ul", { class: "ground" });
    for (const g of e.grounding)
      ul.append(el("li", {}, el("code", {}, g.name), " — " + (g.gloss || "")));
    body.append(el("div", { class: "sec" }, el("h4", {}, "Grounding notes"), ul));
  }

  // faithfulness note
  if (e.faithfulness)
    body.append(el("div", { class: "sec" }, el("h4", {}, "Faithfulness note"),
      el("p", { class: "faith" }, e.faithfulness)));

  return el("section", { class: "card", id: e.id }, head, body);
}

// --- filtering ------------------------------------------------------------
function matches(e) {
  if (state.cluster && (e.cluster || "?") !== state.cluster) return false;
  if (state.status.size && !state.status.has(normStatus(e.status))) return false;
  if (state.kind.size && !state.kind.has(e.kind)) return false;
  if (state.q) {
    const hay = (e.id + " " + e.title + " " + (e.informal?.text || "") + " " +
      e.decoded).toLowerCase();
    if (!hay.includes(state.q)) return false;
  }
  return true;
}

function render() {
  const content = $("#content");
  content.innerHTML = "";
  const shown = DATA.filter(matches);
  if (!shown.length) { content.append(el("p", { class: "empty" }, "No entries match.")); return; }
  const groups = {};
  for (const e of shown) (groups[e.cluster || "?"] ||= []).push(e);
  const order = Object.keys(groups).sort(
    (a, b) => (CLUSTER_ORDER[a] ?? 99) - (CLUSTER_ORDER[b] ?? 99));
  for (const cl of order) {
    content.append(el("h3", { class: "clhead" },
      (CLUSTER_LABEL[cl] || cl), " ", el("span", { class: "clcode" }, "[" + cl + "]")));
    for (const e of groups[cl].sort((a, b) => a.title.localeCompare(b.title)))
      content.append(card(e));
  }
  // honour deep link after (re)render
  if (location.hash) { const t = document.getElementById(location.hash.slice(1)); if (t) t.scrollIntoView(); }
}

function buildSidebar() {
  // counts
  const byKind = k => DATA.filter(e => e.kind === k).length;
  $("#counts").append(
    el("div", { class: "stat" }, el("b", {}, String(DATA.length)), el("span", {}, "entries")),
    el("div", { class: "stat" }, el("b", {}, String(byKind("conjecture"))), el("span", {}, "conjectures")),
    el("div", { class: "stat" }, el("b", {}, String(byKind("proved-result"))), el("span", {}, "proved")),
    el("div", { class: "stat" }, el("b", {}, String(byKind("grounding"))), el("span", {}, "tests")),
    el("div", { class: "stat" }, el("b", {}, String(DATA.filter(e => e.axiom_free).length)), el("span", {}, "axiom-free")));

  // status + kind chips
  const mkChips = (host, key, values) => {
    for (const v of values) {
      const chip = el("span", { class: "chip", onclick: () => {
          state[key].has(v) ? state[key].delete(v) : state[key].add(v);
          chip.classList.toggle("on"); render();
        } }, v);
      host.append(chip);
    }
  };
  mkChips($("#filter-status"), "status", ["open", "proved", "refuted", "partial"]);
  mkChips($("#filter-kind"), "kind", ["conjecture", "proved-result", "grounding", "refutation"]);

  // cluster TOC
  const toc = $("#toc");
  const present = new Set(DATA.map(e => e.cluster || "?"));
  const allBtn = el("button", { class: "clbtn on", onclick: () => setCluster(null, allBtn) },
    el("span", {}, "All clusters"), el("span", { class: "n" }, String(DATA.length)));
  toc.append(allBtn);
  for (const [code, label] of CLUSTERS) {
    if (!present.has(code)) continue;
    const n = DATA.filter(e => (e.cluster || "?") === code).length;
    const btn = el("button", { class: "clbtn", onclick: () => setCluster(code, btn) },
      el("span", {}, label), el("span", { class: "n" }, String(n)));
    toc.append(btn);
  }
  function setCluster(code, btn) {
    state.cluster = code;
    toc.querySelectorAll(".clbtn").forEach(b => b.classList.remove("on"));
    btn.classList.add("on");
    render();
  }

  $("#search").addEventListener("input", e => {
    state.q = e.target.value.trim().toLowerCase(); render();
  });
}

fetch("registry.json")
  .then(r => r.json())
  .then(reg => {
    DATA = reg.entries || [];
    buildSidebar();
    render();
    document.body.append(el("footer", {},
      "Generated by ", el("code", {}, "scripts/build_correspondence.py"),
      " from ", el("code", {}, "docs/correspondence/registry.json"),
      ". Verbatim Rocq extracted from source; proved items machine-checked, axiom-free. ",
      el("a", { href: "../" }, "↑ blueprint"), " · ",
      el("a", { href: "../dependency_graph.html" }, "dependency graph")));
  })
  .catch(err => {
    $("#content").innerHTML =
      '<p class="empty">Could not load <code>registry.json</code>: ' + esc(String(err)) +
      '. Serve this folder over HTTP (e.g. <code>python3 -m http.server</code>).</p>';
  });

window.addEventListener("hashchange", () => {
  const t = document.getElementById(location.hash.slice(1));
  if (t) { const b = t.querySelector(".card-body"); if (b) b.classList.remove("collapsed"); t.scrollIntoView(); }
});
