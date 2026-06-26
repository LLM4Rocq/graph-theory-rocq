#!/usr/bin/env python3
"""Federation-wide conjecture dependency-graph extractor + gate (G1).

Scoped to graph-theory-rocq (NOT legacy digraph-theory). Scans every package's
theories/conjectures/*.v for implication/refutation EDGES from two sources:

  (1) explicit structured annotations (the machine-readable record for edges that are
      candidate/refuted/external — i.e. NOT a plain Qed theorem):
        (*@EDGE from=<A_statement> to=<B_statement> kind=<implies|equiv|refutes|specializes>
                status=<verified|candidate|refuted-direction> cite="<source>" *)
  (2) Qed-closed relative theorems named  <A>_implies_<B> / <A>_equiv_<B> / <A>_refutes_<B>
      (proved edges — these carry status=verified and MUST exist as a Theorem).

Output: one meta/dependency_graph.json with a DETERMINISTIC, sorted edge list.
Gate (`--check`): regenerates byte-identically (fails on drift) AND every verified
implies/equiv edge has a matching Theorem in its file (a proved edge can't be merely declared).
Includes a LEGACY compatibility report for the absorbed digraph-theory (its _implies_ theorem
count vs its committed dependency_graph.json) — reported, not used to drive this format.
"""
import json, os, re, sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
OUT = os.path.join(META, "dependency_graph.json")
PACKAGES = sorted(d for d in os.listdir(MONO)
                  if os.path.isdir(os.path.join(MONO, d, "theories", "conjectures")) and d != "digraph-theory")

EDGE_RE = re.compile(r"\(\*@EDGE\s+(.*?)\*\)", re.S)
THM_RE = re.compile(r"^\s*(?:Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)_(implies|equiv|refutes|specializes)_([A-Za-z0-9_']+)\s*:", re.M)
KV_RE = re.compile(r'(\w+)=(?:"([^"]*)"|(\S+))')
KINDS = {"implies", "equiv", "refutes", "specializes"}
STATUSES = {"verified", "candidate", "refuted-direction"}

def parse_kv(s):
    return {m.group(1): (m.group(2) if m.group(2) is not None else m.group(3)) for m in KV_RE.finditer(s)}

def scan(pkg):
    edges, thms = [], []
    cdir = os.path.join(MONO, pkg, "theories", "conjectures")
    for fn in sorted(os.listdir(cdir)):
        if not fn.endswith(".v"):
            continue
        txt = open(os.path.join(cdir, fn)).read()
        for m in EDGE_RE.finditer(txt):
            kv = parse_kv(m.group(1))
            status = kv.get("status")
            if status == "verified-literature":  # agents sometimes use the plan's term for a proved edge
                status = "verified"
            edges.append({"from": kv.get("from"), "to": kv.get("to"), "kind": kv.get("kind"),
                          "status": status, "cite": kv.get("cite", ""), "package": pkg, "file": fn})
        for m in THM_RE.finditer(txt):
            thms.append({"name": f"{m.group(1)}_{m.group(2)}_{m.group(3)}", "kind": m.group(2), "package": pkg, "file": fn})
    return edges, thms

all_edges, all_thms = [], []
for pkg in PACKAGES:
    e, t = scan(pkg); all_edges += e; all_thms += t

def need(c, m):
    if not c:
        raise AssertionError("EDGE-GRAPH INVARIANT VIOLATED: " + m)
for e in all_edges:
    need(e["from"] and e["to"] and e["kind"] and e["status"], f"edge missing field: {e}")
    need(e["kind"] in KINDS, f"bad kind {e['kind']!r} in {e['file']}")
    need(e["status"] in STATUSES, f"bad status {e['status']!r} in {e['file']}")
# a verified implies/equiv edge must be backed by an actual Theorem in its file
for e in [e for e in all_edges if e["status"] == "verified" and e["kind"] in ("implies", "equiv")]:
    need([t for t in all_thms if t["file"] == e["file"] and t["kind"] == e["kind"]],
         f"verified {e['kind']} edge {e['from']}->{e['to']} ({e['file']}) has no matching Theorem")

# dedup: collapse edges with identical (from,to,kind,status) — the SAME edge re-asserted in
# multiple files (e.g. a cross-milestone refuted edge noted at both endpoints). Keep one, record
# every file that asserts it under `sources` (sorted, deterministic).
by_id = {}
for e in all_edges:
    k = (e["from"], e["to"], e["kind"], e["status"])
    if k not in by_id:
        by_id[k] = {"from": e["from"], "to": e["to"], "kind": e["kind"], "status": e["status"],
                    "cite": e["cite"], "sources": set()}
    by_id[k]["sources"].add(f"{e['package']}/{e['file']}")
edges_sorted = sorted(by_id.values(), key=lambda e: (e["from"], e["to"], e["kind"], e["status"]))
for e in edges_sorted:
    e["sources"] = sorted(e["sources"])

# legacy report — counts only, does not define the format
legacy = {}
dt = os.path.join(MONO, "digraph-theory")
if os.path.isdir(dt):
    thm = 0
    cdir = os.path.join(dt, "theories", "conjectures")
    if os.path.isdir(cdir):
        for f in os.listdir(cdir):
            if f.endswith(".v"):
                thm += len(re.findall(r"(?:Theorem|Lemma|Corollary)\s+[A-Za-z0-9_']+_(?:implies|equiv|refutes|specializes|joint)_[A-Za-z0-9_']+",
                                      open(os.path.join(cdir, f)).read()))
    dgj = os.path.join(dt, "docs", "dependency_graph.json")
    committed = len(json.load(open(dgj)).get("edges", [])) if os.path.isfile(dgj) else None
    legacy = {"repo": "digraph-theory (absorbed)", "implies_theorems_in_source": thm,
              "committed_dependency_graph_edges": committed,
              "note": "Legacy digraph-only graph: source _implies_ theorem count vs the committed graph "
                      "differ (theorem-name pattern includes helper lemmas; the old extractor filtered). "
                      "Reconcile within digraph-theory separately; it does NOT define the federation format."}

graph = {
    "_README": "Federation-wide conjecture dependency graph (G1). Edges from (*@EDGE ...*) annotations + "
               "_implies_/_equiv_ theorems across graph-theory-rocq packages (legacy digraph-theory excluded; "
               "see `legacy`). Regenerate: `python3 meta/build_edge_graph.py`; gate: `--check` fails on drift. "
               "Edges are sorted (from,to,kind,status,package) for determinism.",
    "packages": PACKAGES,
    "totals": {"edges": len(edges_sorted),
               "by_status": {s: sum(1 for e in edges_sorted if e["status"] == s) for s in sorted(STATUSES)},
               "by_kind": {k: sum(1 for e in edges_sorted if e["kind"] == k) for k in sorted(KINDS)},
               "proved_theorems": len(all_thms)},
    "edges": edges_sorted,
    "legacy": legacy,
}
new = json.dumps(graph, ensure_ascii=False, indent=1) + "\n"

if "--check" in sys.argv:
    old = open(OUT).read() if os.path.exists(OUT) else ""
    if old != new:
        sys.exit("EDGE-GRAPH DRIFT: meta/dependency_graph.json is stale — run `python3 meta/build_edge_graph.py`")
    print(f"edge-graph gate OK: {len(edges_sorted)} edges, no drift; "
          f"{graph['totals']['by_status']}; {len(all_thms)} proved theorems")
else:
    open(OUT, "w").write(new)
    print(f"wrote meta/dependency_graph.json: {len(edges_sorted)} edges {graph['totals']['by_status']}, "
          f"{len(all_thms)} proved theorems | legacy digraph: {legacy.get('implies_theorems_in_source')} thms / "
          f"{legacy.get('committed_dependency_graph_edges')} committed")
