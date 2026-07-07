#!/usr/bin/env python3
"""Single source of truth for corpus routing (v2 plan meta/V2_FULL_CORPUS_PLAN.md §3, X0a).

One repo, several corpora. Each corpus owns a manifest + a legs-state overlay and has its
own gate invariants; a milestone phase code routes to exactly one corpus. The package→namespace
map (NS) and every manifest/overlay path live ONLY here — milestone_rows.py, check_milestone.py,
report_corpus_status.py, build_edge_graph.py and make_milestone_workflow.py import this module
instead of keeping private copies.

Corpora:
  opg — the frozen v1 OpenProblemGarden corpus (227 rows, statement-complete; release
        opg-v1.0.1-227-attempted). Invariants: exactly 227 rows, 0 todo.
  v2  — the growing graph-conjectures corpus (corpus tags arxiv/erdos/derived/arxiv-studied;
        manifest appears at milestone X0b). Invariants: overlay consistency only; todo rows
        are allowed until M-V2-STATEMENT-COMPLETE. Statement legs may reach `done` only with
        a complete source-verification tuple (see VERIFICATION_FIELDS).
"""
import json
import os
import re

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)

# package -> Rocq namespace (the only copy in the repo)
NS = {
    'chromatic-theory': 'Chromatic', 'hamiltonicity-theory': 'Hamilton', 'homomorphism-theory': 'Hom',
    'cycle-theory': 'Cycle', 'minor-theory': 'Minor', 'packing-theory': 'Packing',
    'reconstruction-theory': 'Reconstruction', 'hypergraph-theory': 'Hypergraph',
    'topological-graph-theory': 'Topological', 'graph-theory-misc': 'GTMisc',
    'spectral-graph-theory': 'Spectral', 'extremal-graph-theory': 'Extremal',
    'infinite-graph-theory': 'Infinite', 'digraph-theory': 'Digraph', 'graph-theory-base': 'GTBase',
}

# The source-verification tuple (plan §1.4/§2): a v2 row's statement leg may be `done` only when
# all of these are present AND source_verified_by != implemented_by. The convenience flag
# `source_verified` is derived from the tuple; gates check the tuple, never the flag.
VERIFICATION_FIELDS = ("source_locator", "source_hash", "source_verified_by", "source_verified_at")

CORPORA = {
    "opg": {
        "manifest": "opg_corpus_manifest.json",
        "overlay": "opg_legs_state.json",
        "subbatches": "subbatches.json",
        "frozen_total": 227,          # v1 is frozen: exactly 227 rows, 0 todo
        "requires_source_verification": False,
        # v1 phase codes: U1..U13, P0..P12 (digraph legacy + P9), D1..D7 — each optionally
        # carrying a subbatch-tag suffix (D2pr, D3cr, D4inf1, D6emb, and future U/P tags);
        # tags MUST start with their corpus's phase prefix so routing stays decidable.
        "phase_re": re.compile(r"^(U\d+\w*|P\d+\w*|D\d+\w*)$"),
    },
    "v2": {
        "manifest": "v2_corpus_manifest.json",
        "overlay": "v2_legs_state.json",
        "subbatches": "v2_subbatches.json",
        "frozen_total": None,         # growing corpus: todo allowed until statement-complete
        "requires_source_verification": True,
        # v2 phase codes (plan §4/§5): X0a..X0d, X1..X9 (+ subbatch tags), XE1.., T1..
        "phase_re": re.compile(r"^(X0[a-d]|X\d+\w*|XE\d+\w*|T\d+\w*)$"),
    },
}


def corpus_for_phase(phase):
    """Route a phase (or subbatch tag) to its corpus name. Exactly one corpus must claim it."""
    hits = [name for name, c in CORPORA.items() if c["phase_re"].match(phase)]
    if len(hits) != 1:
        raise SystemExit(f"corpus_registry: phase {phase!r} matches {hits or 'no'} corpus "
                         f"phase scheme(s); every phase code must route to exactly one corpus")
    return hits[0]


def manifest_path(corpus):
    return os.path.join(META, CORPORA[corpus]["manifest"])


def overlay_path(corpus):
    return os.path.join(META, CORPORA[corpus]["overlay"])


def subbatches_path(corpus):
    return os.path.join(META, CORPORA[corpus]["subbatches"])


def load_manifest(corpus, required=True):
    p = manifest_path(corpus)
    if not os.path.exists(p):
        if required:
            raise SystemExit(f"corpus_registry: manifest for corpus {corpus!r} not found at {p}"
                             + (" (v2 manifest is created by milestone X0b)" if corpus == "v2" else ""))
        return None
    return json.load(open(p))


def load_overlay(corpus, required=True):
    p = overlay_path(corpus)
    if not os.path.exists(p):
        if required:
            raise SystemExit(f"corpus_registry: overlay for corpus {corpus!r} not found at {p}")
        return None
    return json.load(open(p))


def existing_corpora():
    """Corpora whose manifest exists on disk (opg always; v2 from X0b onward)."""
    return [n for n in CORPORA if os.path.exists(manifest_path(n))]


def all_corpus_nodes():
    """Union of formal_names across every existing corpus manifest — the edge-endpoint domain.
    Rows without a formal_name (alias / parked / not-yet-classified v2 rows) contribute nothing."""
    nodes = set()
    for name in existing_corpora():
        for r in load_manifest(name)["rows"]:
            fn = r.get("formal_name")
            if fn:
                nodes.add(fn)
    return nodes


def alias_formal_names():
    """formal_names carried by rows that have alias_of set, across existing manifests.
    Invariant (plan §1.4): an alias row is never an edge endpoint or a statement owner —
    ideally it has NO formal_name at all; any that does is flagged so gates can reject it."""
    out = {}
    for name in existing_corpora():
        for r in load_manifest(name)["rows"]:
            if r.get("alias_of") and r.get("formal_name"):
                out[r["formal_name"]] = r["alias_of"]
    return out


def verification_tuple_errors(row):
    """Return a list of humane error strings if the row's source-verification tuple is
    incomplete or self-verified (empty list == tuple OK). Only meaningful for corpora with
    requires_source_verification. implemented_by is part of the contract: without it the
    second-reader distinctness check would be vacuously satisfiable."""
    errs = []
    for f in VERIFICATION_FIELDS + ("implemented_by",):
        if not row.get(f):
            errs.append(f"missing {f}")
    if row.get("source_verified_by") and row.get("implemented_by") \
            and row["source_verified_by"] == row["implemented_by"]:
        errs.append("source_verified_by == implemented_by (second reader required)")
    return errs
