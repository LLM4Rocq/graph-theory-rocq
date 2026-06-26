#!/usr/bin/env python3
"""axiom_audit.py — verify every catalog result is axiom-free (M21).

Generates a probe file with `Print Assumptions` for each result of the
statement-audit catalog, compiles it against the built library, and
asserts one "Closed under the global context" per result. Run by the
site CI (the badge on every result page is this check).
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from statement_closure import CATALOG


def main() -> None:
    mods = sorted({Path(v).stem for v in CATALOG.values()})
    lines = [f"From Digraph Require Import {' '.join(mods)}."]
    lines += [f"Print Assumptions {r}." for r in CATALOG]
    with tempfile.TemporaryDirectory() as td:
        probe = Path(td) / "axiom_audit_probe.v"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        out = subprocess.run(
            ["rocq", "compile", "-R", str(ROOT / "theories"), "Digraph",
             str(probe)],
            capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit(f"probe failed to compile:\n{out.stdout}\n{out.stderr}")
    closed = (out.stdout + out.stderr).count("Closed under the global context")
    if closed != len(CATALOG):
        sys.exit(f"AXIOM AUDIT FAILED: {closed}/{len(CATALOG)} results "
                 f"closed under the global context\n{out.stdout}")
    print(f"axiom audit OK: {closed}/{len(CATALOG)} results axiom-free")


if __name__ == "__main__":
    main()
