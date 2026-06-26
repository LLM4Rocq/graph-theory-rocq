"""Sanity suite for statement_closure.py (PLAN_WEB M18).

Run:  python3 -m pytest scripts/test_statement_closure.py -q
(after `make` — the extractor reads the build's .glob files).
"""

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

import statement_closure as sc


def closures():
    cl = sc.Closure()
    return {r: cl.close(r, v) for r, v in sc.CATALOG.items()}


CLOSURES = closures()


def names(result):
    return set(CLOSURES[result]["digraph"])


def test_catalog_complete():
    """Every catalog result exists and has a nonempty statement."""
    for r, c in CLOSURES.items():
        assert c["statement"].strip(), r
        assert (ROOT / c["file"]).exists(), r


def test_unified_closure():
    """The headline's meaning chain reaches the arc relation."""
    need = {"kcritical", "omegabar", "omegab_at", "backedge",
            "backedge_rel", "ltp", "arc", "tournament",
            "sub_tournament", "del_tournament"}
    assert need <= names("conjecture_5_10_at_345")


def test_no_proof_leakage():
    """Statement closures never contain proof-only machinery."""
    proof_only = {"cidx", "key", "qk", "occ", "band", "dband", "sidx",
                  "kv", "kd", "qv", "qd", "realize", "coverage5",
                  "no_obstruction", "ckC", "ckB", "ckS", "kernel_full"}
    for r, c in CLOSURES.items():
        leaked = proof_only & set(c["digraph"])
        assert not leaked, (r, leaked)


def test_ck3_closure():
    need = {"orientedDigraph", "outdeg", "ell", "dipath", "arc"}
    assert need <= names("ck_conj1_delta3")
    assert "strongb" in names("no_short_strong3")


def test_k4_value_closure():
    need = {"omegabar", "lexprod", "AC", "ACset", "C3", "cayley"}
    assert need <= names("omegabar_T4")


def test_statement_text_is_statement():
    """Quoted statements stop before the proof script."""
    for r, c in CLOSURES.items():
        assert "Proof" not in c["statement"], r
        assert r in c["statement"], r


def test_check_gate_green():
    out = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "statement_closure.py"),
         "--check"], capture_output=True, text=True)
    assert out.returncode == 0, out.stdout + out.stderr


def test_every_block_used():
    """No orphan def-blocks: each block is the target of some mapped
    constant (keeps the curation honest in the other direction)."""
    cur = json.loads((ROOT / "docs/web/defblocks.json").read_text())
    used = set(cur["map"].values())
    orphans = set(cur["blocks"]) - used
    assert not orphans, orphans
