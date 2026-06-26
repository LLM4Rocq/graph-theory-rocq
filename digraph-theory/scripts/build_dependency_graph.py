#!/usr/bin/env python3
"""Build the conjecture dependency graph from the Rocq formalization.

Scans theories/conjectures/*.v and extracts:
  NODES = every `Definition <name> : Prop := ...` (optionally with parameters
          before `: Prop`), i.e. statement-shaped Props that encode a
          conjecture / question / theorem-statement.
  EDGES = every theorem/lemma whose name matches one of
            <src>_implies_<dst>, <src>_equiv_<dst>, <a>_iff_<b>, <src>_refutes_<dst>
          Edge direction and kind are confirmed against the theorem TYPE:
            - the node-ids referenced in the type fix src -> dst,
            - a leading/embedded `~` on the dst marks a `refutes` edge,
            - `<->` marks an `equiv` edge.
          When the dst is not itself a named Definition (e.g. an inline
          bound), the edge is still emitted using the name-derived token.

Outputs (relative to repo root):
  docs/dependency_graph.json   { nodes:[...], edges:[...] }
  docs/dependency_graph.dot    Graphviz, clustered by source file
  docs/dependency_graph.svg    rendered if `dot` is on PATH
  site/dependency_graph.html   self-contained HTML view (inlined SVG +
                               edge table + nodes grouped by file)

stdlib only; uv-runnable: `uv run scripts/build_dependency_graph.py`
"""
import html as _html
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CONJ_DIR = os.path.join(ROOT, "theories", "conjectures")
DOCS = os.path.join(ROOT, "docs")
SITE = os.path.join(ROOT, "site")

# --- Definition <name> [params...] : Prop := ...
#   name is the first identifier; allow params between name and ': Prop'.
DEF_RE = re.compile(
    r"^\s*Definition\s+([A-Za-z_]\w*)\b[^:=]*?:\s*Prop\s*:=",
    re.MULTILINE,
)

# --- Theorem/Lemma/Corollary/Proposition <name> ... : <type> [Proof.|:= ...]
THM_HEAD_RE = re.compile(
    r"^\s*(?:Theorem|Lemma|Corollary|Proposition|Example)\s+([A-Za-z_]\w*)\b",
    re.MULTILINE,
)

# split a theorem name into src / dst around an edge keyword
EDGE_NAME_RE = re.compile(
    r"^(.*?)_(implies|equiv|iff|refutes)_(.*)$"
)


def strip_comments(text):
    """Remove (* ... *) Coq comments (handles nesting)."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text[i : i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i : i + 2] == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def build_html(graph, svg_text):
    """Render a self-contained HTML view from the graph dict + inline SVG.

    Pure HTML + inline CSS, no external dependencies. Reads only the
    already-built `docs/dependency_graph.json` (passed as `graph`) and the
    rendered SVG text (or None if `dot` was unavailable).
    """
    nodes = graph["nodes"]
    edges = graph["edges"]
    esc = _html.escape

    declared = {nd["id"] for nd in nodes}

    # nodes grouped by file
    by_file = {}
    for nd in nodes:
        by_file.setdefault(nd["file"], []).append(nd["id"])

    kind_counts = {k: sum(1 for e in edges if e["kind"] == k)
                   for k in ("implies", "equiv", "refutes")}

    kind_badge = {
        "implies": ('implies', '#1b5e20', '#e8f5e9'),
        "equiv": ('equiv', '#0d47a1', '#e3f2fd'),
        "refutes": ('refutes', '#b71c1c', '#ffebee'),
    }

    parts = []
    parts.append("<!DOCTYPE html>")
    parts.append('<html lang="en"><head>')
    parts.append('<meta charset="utf-8">')
    parts.append('<meta name="viewport" content="width=device-width, '
                 'initial-scale=1">')
    parts.append("<title>Conjecture dependency graph</title>")
    parts.append("""<style>
  :root { --fg:#1a1a1a; --muted:#666; --line:#ddd; --bg:#fff;
          --accent:#0d47a1; }
  * { box-sizing: border-box; }
  body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI",
         Roboto, Helvetica, Arial, sans-serif; color: var(--fg);
         background: var(--bg); margin: 0; padding: 1.5rem 2rem 4rem; }
  h1 { font-size: 1.6rem; margin: 0 0 .25rem; }
  h2 { font-size: 1.2rem; margin: 2.2rem 0 .6rem;
       border-bottom: 2px solid var(--line); padding-bottom: .25rem; }
  .sub { color: var(--muted); margin: 0 0 1rem; font-size: .9rem; }
  .counts { display: flex; flex-wrap: wrap; gap: .6rem; margin: 1rem 0; }
  .stat { border: 1px solid var(--line); border-radius: 8px;
          padding: .5rem .9rem; background: #fafafa; }
  .stat b { font-size: 1.3rem; display: block; }
  .stat span { color: var(--muted); font-size: .8rem;
               text-transform: uppercase; letter-spacing: .04em; }
  .graph-wrap { border: 1px solid var(--line); border-radius: 8px;
                padding: .5rem; overflow: auto; background: #fff; }
  .graph-wrap svg { max-width: 100%; height: auto; display: block; }
  table { border-collapse: collapse; width: 100%; font-size: .88rem; }
  th, td { text-align: left; padding: .45rem .6rem;
           border-bottom: 1px solid var(--line); vertical-align: top; }
  th { background: #f5f5f5; position: sticky; top: 0; }
  tr:hover td { background: #fbfbfb; }
  code, .mono { font-family: ui-monospace, SFMono-Regular, Menlo,
                Consolas, monospace; font-size: .85em; }
  .arrow { color: var(--muted); }
  .badge { display: inline-block; padding: .1rem .5rem; border-radius: 999px;
           font-size: .75rem; font-weight: 600; }
  .file-block { margin: 0 0 1.2rem; }
  .file-name { font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
               font-weight: 600; color: var(--accent); }
  ul.nodes { margin: .4rem 0 0; padding-left: 1.2rem; columns: 280px 3;
             list-style: square; }
  ul.nodes li { margin: .1rem 0; break-inside: avoid; }
  .inline-tag { color: var(--muted); font-style: italic; font-size: .78rem; }
  .legend { font-size: .85rem; color: var(--muted); margin: .4rem 0 0; }
  footer { margin-top: 3rem; color: var(--muted); font-size: .8rem;
           border-top: 1px solid var(--line); padding-top: 1rem; }
</style>""")
    parts.append("</head><body>")

    parts.append("<h1>Conjecture dependency graph</h1>")
    parts.append('<p class="sub">Statements (Definition&hellip;: Prop) and '
                 "the proved implies / equiv / refutes edges between them, "
                 "extracted from <code>theories/conjectures/*.v</code>. "
                 "Generated by "
                 "<code>scripts/build_dependency_graph.py</code> from "
                 "<code>docs/dependency_graph.json</code>.</p>")

    # --- counts ---
    parts.append('<div class="counts">')
    parts.append(f'<div class="stat"><b>{len(nodes)}</b><span>nodes</span>'
                 "</div>")
    parts.append(f'<div class="stat"><b>{len(edges)}</b><span>edges</span>'
                 "</div>")
    parts.append(f'<div class="stat"><b>{len(by_file)}</b>'
                 "<span>source files</span></div>")
    for k in ("implies", "equiv", "refutes"):
        parts.append(f'<div class="stat"><b>{kind_counts[k]}</b>'
                     f"<span>{k}</span></div>")
    parts.append("</div>")

    # --- graph ---
    parts.append("<h2>Graph</h2>")
    if svg_text:
        # inline the SVG; drop any XML/doctype prolog so it embeds cleanly
        body = svg_text
        idx = body.find("<svg")
        if idx > 0:
            body = body[idx:]
        parts.append('<div class="graph-wrap">')
        parts.append(body)
        parts.append("</div>")
        parts.append('<p class="legend">Solid black = implies &nbsp;|&nbsp; '
                     "blue (double) = equiv &nbsp;|&nbsp; red dashed = "
                     "refutes &nbsp;|&nbsp; dashed gray boxes = inline-bound "
                     "endpoints (not standalone Definitions).</p>")
    else:
        parts.append("<p><em>SVG not available (Graphviz <code>dot</code> "
                     "was not on PATH when the graph was built).</em></p>")

    # --- edge table ---
    parts.append("<h2>Edges</h2>")
    parts.append("<table><thead><tr>"
                 "<th>#</th><th>Source</th><th></th><th>Target</th>"
                 "<th>Kind</th><th>Theorem</th><th>File</th>"
                 "</tr></thead><tbody>")
    for i, e in enumerate(edges, 1):
        label, fg, bg = kind_badge.get(e["kind"], (e["kind"], "#333", "#eee"))
        arrow = "&#8596;" if e["kind"] == "equiv" else "&#8594;"
        def endp(x):
            tag = "" if x in declared else (
                ' <span class="inline-tag">(inline)</span>')
            return f'<code>{esc(x)}</code>{tag}'
        parts.append(
            "<tr>"
            f"<td>{i}</td>"
            f"<td>{endp(e['src'])}</td>"
            f'<td class="arrow">{arrow}</td>'
            f"<td>{endp(e['dst'])}</td>"
            f'<td><span class="badge" style="color:{fg};background:{bg}">'
            f"{esc(label)}</span></td>"
            f"<td><code>{esc(e['thm'])}</code></td>"
            f"<td><code>{esc(e['file'])}</code></td>"
            "</tr>"
        )
    parts.append("</tbody></table>")

    # --- nodes by file ---
    parts.append("<h2>Nodes by file</h2>")
    for fn in sorted(by_file):
        ids = sorted(by_file[fn])
        parts.append('<div class="file-block">')
        parts.append(f'<div class="file-name">{esc(fn)} '
                     f'<span class="inline-tag">({len(ids)})</span></div>')
        parts.append('<ul class="nodes">')
        for nid in ids:
            parts.append(f"<li><code>{esc(nid)}</code></li>")
        parts.append("</ul></div>")

    parts.append("<footer>Self-contained; no external dependencies. "
                 "Regenerate with "
                 "<code>uv run scripts/build_dependency_graph.py</code>."
                 "</footer>")
    parts.append("</body></html>")
    return "\n".join(parts)


def main():
    files = sorted(
        f for f in os.listdir(CONJ_DIR) if f.endswith(".v")
    )

    # node id -> file
    node_file = {}
    nodes = []
    # file -> cleaned source
    src_by_file = {}

    for fn in files:
        raw = open(os.path.join(CONJ_DIR, fn), encoding="utf-8").read()
        clean = strip_comments(raw)
        src_by_file[fn] = clean
        for m in DEF_RE.finditer(clean):
            name = m.group(1)
            if name in node_file:
                continue
            node_file[name] = fn
            nodes.append({"id": name, "file": fn, "kind": "statement"})

    node_ids = set(node_file)

    edges = []
    seen_edges = set()

    for fn in files:
        clean = src_by_file[fn]
        # find each theorem head; grab its type slice up to Proof/Qed/:=/Defined
        heads = list(THM_HEAD_RE.finditer(clean))
        for idx, hm in enumerate(heads):
            name = hm.group(1)
            em = EDGE_NAME_RE.match(name)
            if not em:
                continue
            keyword = em.group(2)
            name_src, name_dst = em.group(1), em.group(3)

            # type slice: from end of head to the first proof terminator
            start = hm.end()
            end = len(clean)
            if idx + 1 < len(heads):
                end = min(end, heads[idx + 1].start())
            slice_ = clean[start:end]
            term = re.search(r"\bProof\b|\bQed\b|\bDefined\b|\bAdmitted\b", slice_)
            if term:
                slice_ = slice_[: term.start()]

            # gather node-ids referenced in the type, in order of appearance
            refs = []
            for nm in re.finditer(r"[A-Za-z_]\w*", slice_):
                tok = nm.group(0)
                if tok in node_ids and (not refs or refs[-1][0] != tok):
                    refs.append((tok, nm.start()))

            # decide kind
            kind = {
                "implies": "implies",
                "equiv": "equiv",
                "iff": "equiv",
                "refutes": "refutes",
            }[keyword]
            if "<->" in slice_:
                kind = "equiv"
            negated = "~" in slice_

            # resolve src / dst
            src = dst = None
            if refs:
                src = refs[0][0]
                # prefer a distinct later ref as dst
                for tok, _pos in refs[1:]:
                    if tok != src:
                        dst = tok
                        break
            # fall back to name tokens when type didn't pin them down
            if src is None:
                src = name_src if name_src in node_ids else name_src
            if dst is None:
                dst = name_dst if name_dst in node_ids else name_dst

            if negated and kind == "implies":
                kind = "refutes"

            key = (src, dst, name)
            if key in seen_edges:
                continue
            seen_edges.add(key)
            edges.append(
                {
                    "src": src,
                    "dst": dst,
                    "thm": name,
                    "file": fn,
                    "kind": kind,
                }
            )

    os.makedirs(DOCS, exist_ok=True)
    graph = {"nodes": nodes, "edges": edges}
    json_path = os.path.join(DOCS, "dependency_graph.json")
    with open(json_path, "w", encoding="utf-8") as fh:
        json.dump(graph, fh, indent=2, ensure_ascii=False)
        fh.write("\n")

    # --- DOT ---
    def q(s):
        return '"' + s.replace('"', '\\"') + '"'

    by_file = {}
    for nd in nodes:
        by_file.setdefault(nd["file"], []).append(nd)

    lines = ["digraph conjecture_dependencies {", "  rankdir=LR;",
             "  node [shape=box, style=rounded, fontsize=10];",
             "  edge [fontsize=8];"]
    for i, fn in enumerate(sorted(by_file)):
        lines.append(f"  subgraph cluster_{i} {{")
        lines.append(f"    label={q(fn)}; style=filled; color=lightgrey;")
        for nd in by_file[fn]:
            lines.append(f"    {q(nd['id'])};")
        lines.append("  }")
    # nodes referenced by edges but not declared (inline-bound dsts/srcs)
    declared = set(node_ids)
    extra = set()
    for e in edges:
        for endp in (e["src"], e["dst"]):
            if endp not in declared:
                extra.add(endp)
    for x in sorted(extra):
        lines.append(f"  {q(x)} [style=dashed, color=gray50, "
                     f"fontcolor=gray40];")
    style = {
        "implies": "color=black",
        "equiv": "color=blue, dir=both, arrowtail=normal",
        "refutes": "color=red, style=dashed, arrowhead=tee",
    }
    for e in edges:
        attrs = style.get(e["kind"], "color=black")
        label = e["kind"] if e["kind"] != "implies" else ""
        lab = f', label={q(label)}' if label else ""
        lines.append(f"  {q(e['src'])} -> {q(e['dst'])} [{attrs}{lab}];")
    lines.append("}")
    dot_path = os.path.join(DOCS, "dependency_graph.dot")
    with open(dot_path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")

    svg_path = os.path.join(DOCS, "dependency_graph.svg")
    rendered = False
    if shutil.which("dot"):
        try:
            subprocess.run(
                ["dot", "-Tsvg", dot_path, "-o", svg_path],
                check=True,
            )
            rendered = True
        except subprocess.CalledProcessError as ex:
            print(f"dot failed: {ex}", file=sys.stderr)

    # --- HTML (self-contained view) ---
    svg_text = None
    if rendered and os.path.exists(svg_path):
        svg_text = open(svg_path, encoding="utf-8").read()
    html_doc = build_html(graph, svg_text)
    os.makedirs(SITE, exist_ok=True)
    html_path = os.path.join(SITE, "dependency_graph.html")
    with open(html_path, "w", encoding="utf-8") as fh:
        fh.write(html_doc)

    print(f"nodes: {len(nodes)}")
    print(f"edges: {len(edges)}")
    print(f"json : {json_path}")
    print(f"dot  : {dot_path}")
    print(f"svg  : {svg_path if rendered else '(not rendered; dot unavailable)'}")
    print(f"html : {html_path}")
    print(f"edge kinds: " + ", ".join(
        f"{k}={sum(1 for e in edges if e['kind']==k)}"
        for k in ("implies", "equiv", "refutes")))


if __name__ == "__main__":
    main()
