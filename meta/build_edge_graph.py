#!/usr/bin/env python3
"""Federation-wide conjecture dependency-graph extractor + gate (G1).

Scans every graph-theory-rocq package's theories/conjectures/*.v for @EDGE annotations, PLUS
the absorbed digraph-theory's @EDGE annotations that lie BETWEEN corpus nodes (its P9 rows are
part of the 227-corpus). Its legacy INTERNAL _implies_ theorems (short non-corpus node names)
are NOT federation edges and are excluded — only its edges, never its theorems.

  (1) explicit structured annotations (the machine-readable record for every edge):
        (*@EDGE from=<A_statement> to=<B_statement> kind=<implies|equiv|refutes|specializes>
                status=<verified|candidate|refuted-direction> [proof=<thm>] cite="<source>" *)
  (2) Qed-closed relative theorems named  <A>_implies_<B> / <A>_equiv_<B> / <A>_refutes_<B>,
      which BACK the verified edges (a verified edge names its theorem via proof=<name>).

Output: one meta/dependency_graph.json with a DETERMINISTIC, sorted edge list.
Gate (`--check`): regenerates byte-identically (fails on drift) AND every VERIFIED implies/equiv
edge names an existing proof= theorem in its file (right kind, endpoints consistent with from/to)
— a proved edge can't be merely declared, and a stale/mismatched annotation fails the endpoint
check. A LEGACY compatibility report for digraph-theory's own graph is included (reported only).
"""
import json, os, re, sys

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
sys.path.insert(0, META)
import corpus_registry as REG
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
            if not (kv.get("from") and kv.get("to")):
                import sys as _s; _s.stderr.write(f"skip malformed @EDGE (no from/to) in {fn} — likely prose\n")
                continue
            status = kv.get("status")
            if status == "verified-literature":  # agents sometimes use the plan's term for a proved edge
                status = "verified"
            edges.append({"from": kv.get("from"), "to": kv.get("to"), "kind": kv.get("kind"),
                          "status": status, "cite": kv.get("cite", ""), "proof": kv.get("proof", ""),
                          "package": pkg, "file": fn})
        for m in THM_RE.finditer(txt):
            thms.append({"name": f"{m.group(1)}_{m.group(2)}_{m.group(3)}", "kind": m.group(2), "package": pkg, "file": fn})
    return edges, thms

all_edges, all_thms = [], []
for pkg in PACKAGES:
    e, t = scan(pkg); all_edges += e; all_thms += t

# The absorbed digraph-theory's P9 rows ARE part of the 227 corpus, so its @EDGE annotations
# BETWEEN corpus nodes are federation edges. (Its legacy INTERNAL _implies_ theorems are NOT
# federation edges — they use short non-corpus node names — so we take digraph's EDGES only,
# never its theorems, and keep only edges whose both endpoints are corpus formal_names.)
# The endpoint domain is the UNION over every existing corpus manifest (opg + v2 once X0b lands)
# via corpus_registry — a v2-endpoint edge hosted in a digraph file must survive this filter.
corpus_nodes = REG.all_corpus_nodes()
if os.path.isdir(os.path.join(MONO, "digraph-theory", "theories", "conjectures")):
    dg_edges, _dg_thms = scan("digraph-theory")
    # Dropping is EXPECTED for legacy internal digraph edges, but an endpoint that follows the
    # corpus `*_statement` convention and is still unknown is suspicious (typo, or a row that
    # should exist in a manifest) — warn loudly instead of silently truncating the graph.
    for e in dg_edges:
        if e["from"] in corpus_nodes and e["to"] in corpus_nodes:
            all_edges.append(e)
            continue
        odd = [n for n in (e["from"], e["to"]) if n.endswith("_statement") and n not in corpus_nodes]
        if odd:
            sys.stderr.write(f"WARNING: digraph-hosted @EDGE dropped ({e['file']}): "
                             f"{e['from']} -> {e['to']} — corpus-looking non-corpus endpoint(s) "
                             f"{odd} (add the row to a manifest, or rename if internal)\n")

# Alias rows own no statements and may never be edge endpoints (plan §1.4): reject any edge
# touching a formal_name that belongs to an alias_of row (should not exist; fail loudly if it does).
ALIASES = REG.alias_formal_names()
for e in all_edges:
    bad = [n for n in (e["from"], e["to"]) if n in ALIASES]
    if bad:
        sys.exit(f"EDGE-GRAPH INVARIANT VIOLATED: edge {e['from']} -> {e['to']} ({e['file']}) uses "
                 f"alias-row endpoint(s) {bad}; point the edge at the canonical row "
                 f"({', '.join(str(ALIASES[n]) for n in bad)}) instead")

def need(c, m):
    if not c:
        raise AssertionError("EDGE-GRAPH INVARIANT VIOLATED: " + m)
for e in all_edges:
    need(e["from"] and e["to"] and e["kind"] and e["status"], f"edge missing field: {e}")
    need(e["kind"] in KINDS, f"bad kind {e['kind']!r} in {e['file']}")
    need(e["status"] in STATUSES, f"bad status {e['status']!r} in {e['file']}")
# a verified implies/equiv edge must name its backing Theorem (proof=<name>), and that EXACT
# theorem must exist in the edge's file with the right kind AND endpoints consistent with from/to
# (guards against a stale/mismatched annotation that a same-kind-in-file check would wave through).
STMT = "_statement"
def core(node):
    return node[:-len(STMT)] if node.endswith(STMT) else node
for e in [e for e in all_edges if e["status"] == "verified" and e["kind"] in ("implies", "equiv")]:
    pf = e.get("proof", "")
    need(pf, f"verified {e['kind']} edge {e['from']}->{e['to']} ({e['file']}) must carry proof=<theorem name>")
    need([t for t in all_thms if t["name"] == pf and t["file"] == e["file"] and t["kind"] == e["kind"]],
         f"verified edge proof theorem '{pf}' (kind {e['kind']}) not found in {e['file']}")
    a, sep, b = pf.partition(f"_{e['kind']}_")
    fc, tc = core(e["from"]), core(e["to"])
    need(sep and a and b and (a in fc or fc in a) and (b in tc or tc in b),
         f"verified edge proof '{pf}' endpoints inconsistent with {e['from']}->{e['to']}")

# dedup: collapse edges with identical (from,to,kind,status) — the SAME edge re-asserted in
# multiple files (e.g. a cross-milestone refuted edge noted at both endpoints). Keep one, record
# every file that asserts it under `sources` (sorted, deterministic).
by_id = {}
for e in all_edges:
    k = (e["from"], e["to"], e["kind"], e["status"])
    if k not in by_id:
        by_id[k] = {"from": e["from"], "to": e["to"], "kind": e["kind"], "status": e["status"],
                    "cite": e["cite"], "proof": e.get("proof", ""), "sources": set()}
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
    "_README": "Federation-wide conjecture dependency graph (G1). Edges from (*@EDGE ...*) annotations across "
               "graph-theory-rocq packages + the absorbed digraph-theory's @EDGEs BETWEEN corpus nodes; the "
               "endpoint domain is the union over every corpus manifest in meta/corpus_registry.py (opg + v2), "
               "so cross-corpus edges are first-class. Digraph's legacy internal theorems are not federation "
               "edges (see `legacy`); alias rows may never be endpoints. Verified edges name their backing "
               "theorem via proof=<name>. Regenerate: `python3 meta/build_edge_graph.py`; gate: `--check` fails "
               "on drift + validates verified-edge proofs. Sorted (from,to,kind,status) for determinism.",
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
