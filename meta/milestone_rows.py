#!/usr/bin/env python3
"""Deterministic milestone-row loader/validator (the gate the workflow's args.rows must come from).

The area-milestone-pipeline workflow runs in a JS sandbox with NO filesystem access, so it cannot
read the manifest itself. This script does the canonical filter+validate and emits the rows to pass
as `args.rows`:

    python3 scripts/milestone_rows.py U1 chromatic-theory > /tmp/rows.json
    # then: Workflow({scriptPath: docs/area_milestone_pipeline.workflow.js,
    #                 args: {phase:"U1", repo:"chromatic-theory", base_ready:false, rows: <contents>}})

With no args it lists every (phase, repo) cell. A phase that spans multiple repos (e.g. U13)
REQUIRES an explicit repo — the workflow generates ONE file per (phase,repo), never a mix.
"""
import json, sys, os, re
from collections import Counter

META = os.path.dirname(os.path.abspath(__file__))   # graph-theory-rocq/meta
m = json.load(open(f"{META}/opg_corpus_manifest.json"))
ROWS = m["rows"]

if len(sys.argv) < 2:
    print("phase  repo                          n   (pass `<phase> <repo>` to emit rows)", file=sys.stderr)
    for (ph, repo), n in sorted(Counter((r["phase"], r["repo"]) for r in ROWS).items()):
        print(f"{ph:5}  {repo:28}  {n}", file=sys.stderr)
    sys.exit(0)

phase = sys.argv[1]
repo = sys.argv[2] if len(sys.argv) > 2 else None
sel = [r for r in ROWS if r["phase"] == phase and (repo is None or r["repo"] == repo)]
repos = sorted({r["repo"] for r in sel})

if not sel:
    sys.exit(f"no manifest rows for phase={phase} repo={repo}")
if repo is None and len(repos) > 1:
    sys.exit(f"phase {phase} spans repos {repos}; pass an explicit repo (the workflow is one repo per run).")

# validation gate
names = [r["formal_name"] for r in sel]
assert len(names) == len(set(names)), "duplicate formal_name in slice"
assert all(re.match(r"^[A-Za-z_]\w*$", n) for n in names), "invalid Rocq formal_name in slice"
assert all(r.get("source_text") for r in sel), "row missing source_text (provenance)"

FIELDS = ["slug", "formal_name", "source_text", "source_propositions", "selected_proposition",
          "status", "status_semantics", "tier", "topic", "requires_planarity", "already_formalized",
          "rocq_idiom", "new_primitives"]
out = [{k: r.get(k) for k in FIELDS} for r in sel]
json.dump(out, sys.stdout, ensure_ascii=False)
print(f"\n-- emitted {len(out)} validated rows for phase={phase} repo={repo or repos[0]}", file=sys.stderr)
