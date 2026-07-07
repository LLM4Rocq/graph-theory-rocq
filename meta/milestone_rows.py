#!/usr/bin/env python3
"""Deterministic milestone-row loader/validator (the gate the workflow's args.rows must come from).

The area-milestone-pipeline workflow runs in a JS sandbox with NO filesystem access, so it cannot
read the manifest itself. This script does the canonical filter+validate and emits the rows to pass
as `args.rows`:

    python3 scripts/milestone_rows.py U1 chromatic-theory > /tmp/rows.json
    # then: Workflow({scriptPath: docs/area_milestone_pipeline.workflow.js,
    #                 args: {phase:"U1", repo:"chromatic-theory", base_ready:false, rows: <contents>}})

The phase code routes to its corpus via meta/corpus_registry.py (U*/P*/D* -> opg, X*/XE*/T* -> v2);
each corpus has its own manifest/overlay/subbatches files. With no args it lists every
(phase, repo) cell of every existing corpus. A phase that spans multiple repos (e.g. U13)
REQUIRES an explicit repo — the workflow generates ONE file per (phase,repo), never a mix.
"""
import json, sys, os, re
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import corpus_registry as REG

if len(sys.argv) < 2:
    print("corpus phase  repo                          n   (pass `<phase> <repo>` to emit rows)", file=sys.stderr)
    for corpus in REG.existing_corpora():
        rows = REG.load_manifest(corpus)["rows"]
        for (ph, repo), n in sorted(Counter((r.get("phase") or "-", r["repo"])
                                            for r in rows if r.get("repo")).items()):
            print(f"{corpus:6} {ph:5}  {repo:28}  {n}", file=sys.stderr)
    sys.exit(0)

phase = sys.argv[1]
repo = sys.argv[2] if len(sys.argv) > 2 else None
CORPUS = REG.corpus_for_phase(phase)
ROWS = REG.load_manifest(CORPUS)["rows"]
# In a frozen corpus every row has a phase; a missing one is a manifest regression that would
# otherwise silently drop the row from its milestone slice (and from gate coverage) — fail loudly.
# (v2 rows legitimately have phase=None until wave planning assigns them.)
if REG.CORPORA[CORPUS]["frozen_total"] is not None:
    _nophase = [r["slug"] for r in ROWS if not r.get("phase")]
    if _nophase:
        sys.exit(f"{len(_nophase)} {CORPUS} rows missing 'phase' (manifest regression): {_nophase[:5]}")
sel = [r for r in ROWS if r.get("phase") == phase and (repo is None or r["repo"] == repo)]
# sub-batch tags (per-corpus subbatches file): a tag resolves to a SLUG SUBSET of a real phase, so a
# large milestone (e.g. D2) runs in vocabulary chunks, each as its own <tag>.v file (overlay keeps
# real phase).
_subf = REG.subbatches_path(CORPUS)
SUBB = json.load(open(_subf)) if os.path.exists(_subf) else {}
if not sel and phase in SUBB and not phase.startswith("_"):
    _b = SUBB[phase]; _slugs = set(_b["slugs"])
    if repo is None: repo = _b.get("repo")
    sel = [r for r in ROWS if r["slug"] in _slugs and (repo is None or r["repo"] == repo)]

# alias rows never enter a milestone: they own no statement (plan §1.4). Parked rows carry no
# phase, so phase-selection already excludes them.
aliases = [r["slug"] for r in sel if r.get("alias_of")]
if aliases:
    print(f"-- excluding {len(aliases)} alias rows (alias_of set, no statement owed): "
          f"{aliases[:6]}", file=sys.stderr)
    sel = [r for r in sel if not r.get("alias_of")]
repos = sorted({r["repo"] for r in sel})

if not sel:
    sys.exit(f"no manifest rows for phase={phase} repo={repo} (corpus={CORPUS})")
if repo is None and len(repos) > 1:
    sys.exit(f"phase {phase} spans repos {repos}; pass an explicit repo (the workflow is one repo per run).")

# validation gate
names = [r["formal_name"] for r in sel]
assert all(names), "row without formal_name in slice (classify/assign before milestoning)"
assert len(names) == len(set(names)), "duplicate formal_name in slice"
assert all(re.match(r"^[A-Za-z_]\w*$", n) for n in names), "invalid Rocq formal_name in slice"
assert all(r.get("source_text") for r in sel), "row missing source_text (provenance)"

FIELDS = ["slug", "formal_name", "source_text", "source_propositions", "selected_proposition",
          "status", "status_semantics", "tier", "topic", "requires_planarity", "already_formalized",
          "rocq_idiom", "new_primitives"]
# v2 rows additionally carry identity + review + source-verification-tuple fields (plan §1.4);
# emitting them keeps check_milestone's verification gate and the workflow's audit steps fed.
V2_FIELDS = ["row_id", "corpus", "kind", "review_status", "review_date", "difficulty_tier",
             "alias_of", "parent", "disposition", "arxiv_id", "erdos_id", "license", "recovery",
             "source_locator", "source_hash", "source_excerpt", "implemented_by",
             "source_verified_by", "source_verified_at", "verification_note", "status_verified_at"]
fields = FIELDS + (V2_FIELDS if REG.CORPORA[CORPUS]["requires_source_verification"] else [])
out = [{k: r.get(k) for k in fields} for r in sel]
json.dump(out, sys.stdout, ensure_ascii=False)
print(f"\n-- emitted {len(out)} validated rows for phase={phase} repo={repo or repos[0]} (corpus={CORPUS})",
      file=sys.stderr)
