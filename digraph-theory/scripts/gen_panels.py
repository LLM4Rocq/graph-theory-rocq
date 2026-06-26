#!/usr/bin/env python3
"""gen_panels.py — per-result closure panels (PLAN_WEB M21, used from M19).

For each catalog result, emit docs/web/panels/<result>.tex: the
"everything this statement needs" box — the result's def-blocks from
closure.json, in bottom-up reading order, as hyperlinks to the def-block
sections. Because the panels are generated from the same closure the CI
gate checks, a result page can never silently omit a definition.
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PANELS = ROOT / "docs" / "web" / "panels"

# Bottom-up reading order of the def-blocks (foundations first).
ORDER = [
    "def:arc", "def:dgiso", "def:oriented", "def:outdeg",
    "def:tournament", "def:transb", "def:C3", "def:subdel",
    "def:ltp", "def:backedge", "def:omegabar", "def:kcritical",
    "def:domination", "def:aut", "def:vt",
    "def:lexprod", "def:cayley", "def:AC",
    "def:T4family", "def:T5family",
    "def:dipath", "def:ell", "def:strong",
]


def main() -> None:
    closure = json.loads((ROOT / "docs/web/closure.json").read_text())
    cur = json.loads((ROOT / "docs/web/defblocks.json").read_text())
    blocks, cmap = cur["blocks"], cur["map"]
    assert set(ORDER) == set(blocks), \
        set(ORDER) ^ set(blocks)  # keep ORDER total

    PANELS.mkdir(parents=True, exist_ok=True)
    for result, r in closure.items():
        used = {cmap[c] for c in r["digraph"]}
        items = [b for b in ORDER if b in used]
        lines = ["\\begin{closurepanel}"]
        for b in items:
            lines.append(
                f"\\item \\hyperref[{b}]{{{blocks[b]['title']}}}"
                f" (\\S\\ref*{{{b}}})")
        lines.append(
            "\\item plus the standard finite-mathematics vocabulary "
            "of the Glossary (\\cref{ch:glossary})")
        lines.append("\\end{closurepanel}")
        (PANELS / f"{result}.tex").write_text("\n".join(lines) + "\n",
                                              encoding="utf-8")
    print(f"{len(closure)} panels -> {PANELS.relative_to(ROOT)}/")


if __name__ == "__main__":
    main()
