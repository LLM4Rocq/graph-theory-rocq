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

stdlib only; uv-runnable: `uv run scripts/build_dependency_graph.py`
"""
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

    print(f"nodes: {len(nodes)}")
    print(f"edges: {len(edges)}")
    print(f"json : {json_path}")
    print(f"dot  : {dot_path}")
    print(f"svg  : {svg_path if rendered else '(not rendered; dot unavailable)'}")
    print(f"edge kinds: " + ", ".join(
        f"{k}={sum(1 for e in edges if e['kind']==k)}"
        for k in ("implies", "equiv", "refutes")))


if __name__ == "__main__":
    main()
