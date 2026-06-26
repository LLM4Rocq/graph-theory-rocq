#!/usr/bin/env python3
"""extract_quotes.py — generate the verbatim Rocq quote files (PLAN_WEB).

Every formal text shown on the site/PDF is *extracted from the current
source at build time*, never hand-copied:

  docs/web/quotes/result_<name>.tex   one per catalog result (statement)
  docs/web/quotes/block_<id>.tex      one per def-block quote anchor

Each file is a complete listings block plus a clickable source link
(\\rocqsource{file}{line}). Re-run after any library change; the PDF and
blueprint input these files.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import statement_closure as sc

QUOTES = ROOT / "docs" / "web" / "quotes"

# def-blocks whose anchor is HB syntax (mixin field / structure short
# name): quote an explicit, named span instead of a glob declaration.
HB_QUOTES = {
    "def:arc": ("theories/core/digraph.v",
                r"HB\.mixin Record HasArc.*?\n",
                r"Notation \"u --> v\".*?\n"),
    "def:oriented": ("theories/core/oriented.v",
                     r"HB\.mixin Record DiGraph_IsOriented.*?\}\.\n",
                     None),
    "def:tournament": ("theories/core/tournament.v",
                       r"HB\.mixin Record Oriented_IsTournament.*?\}\.\n",
                       None),
}


# Unicode in the source is rendered through listings' escapechar (`)
# as math — engine-independent (pdflatex chokes on combining chars in
# verbatim material). The library source contains no backtick in any
# quoted declaration.
UNICODE_MATH = {
    "ω̄": r"`$\bar\omega$`",
    "ω": r"`$\omega$`",
    "ℓ": r"`$\ell$`",
    "δ": r"`$\delta$`",
    "σ": r"`$\sigma$`",
    "κ": r"`$\kappa$`",
    "≥": r"`$\geq$`",
    "≤": r"`$\leq$`",
}


def listing(code: str, vrel: str, line: int) -> str:
    code = code.rstrip()
    assert "`" not in code, (vrel, line, "backtick in quoted code")
    for u, tex in UNICODE_MATH.items():
        code = code.replace(u, tex)
    assert all(ord(c) < 128 for c in code), \
        (vrel, line, {c for c in code if ord(c) >= 128})
    return (f"\\begin{{lstlisting}}[language=Rocq]\n{code}\n"
            f"\\end{{lstlisting}}\n"
            f"\\rocqsource{{{vrel}}}{{{line}}}\n")


def emit(stem: str, code: str, vrel: str, line: int) -> None:
    """Write both the LaTeX listing (PDF) and the raw code + source
    location (consumed by gen_blueprint.py for the website)."""
    (QUOTES / f"{stem}.tex").write_text(
        listing(code, vrel, line), encoding="utf-8")
    (QUOTES / f"{stem}.code").write_text(
        f"% {vrel}:{line}\n{code.rstrip()}\n", encoding="utf-8")


def decl_quote(cl: sc.Closure, vrel: str, name: str) -> tuple[str, int]:
    g = cl.glob_for(vrel)
    lo, hi, kind = g.statement_span(name)
    # back up to the introducing keyword on the same line
    bol = g.src.rfind(b"\n", 0, lo) + 1
    text = g.src[bol:hi].decode("utf-8")
    # The span runs to the *next* declaration's identifier, which can
    # drag in a partial following line and comments: keep only up to the
    # last line ending a Rocq sentence ('.').
    lines = text.splitlines()
    while lines and not lines[-1].rstrip().endswith("."):
        lines.pop()
    # drop a trailing coqdoc comment block that may sit between decls
    while lines and lines[-1].lstrip().startswith("(*"):
        lines.pop()
    return "\n".join(lines).rstrip(), g.line_of(lo)


def hb_quote(vrel: str, *patterns: str | None) -> tuple[str, int]:
    src = (ROOT / vrel).read_text(encoding="utf-8")
    chunks, first_line = [], None
    for pat in patterns:
        if pat is None:
            continue
        m = re.search(pat, src, re.S)
        if not m:
            sys.exit(f"extract_quotes: pattern {pat!r} not in {vrel}")
        chunks.append(m.group(0).rstrip())
        if first_line is None:
            first_line = src[:m.start()].count("\n") + 1
    return "\n".join(chunks), first_line or 1


def main() -> None:
    QUOTES.mkdir(parents=True, exist_ok=True)
    cl = sc.Closure()

    # 1. result statements
    for result, vrel in sc.CATALOG.items():
        g = cl.glob_for(vrel)
        lo, hi, _ = g.statement_span(result)
        bol = g.src.rfind(b"\n", 0, lo) + 1
        stmt = g.src[bol:hi].decode("utf-8").rstrip()
        if not stmt.endswith("."):
            stmt += "."
        emit(f"result_{result}", stmt, vrel, g.line_of(lo))

    # 2. def-block quotes ("HB" sentinel, or a list of declaration
    #    names / {file, name} pairs concatenated into one listing)
    cur = json.loads((ROOT / "docs/web/defblocks.json").read_text())
    for bid, b in cur["blocks"].items():
        if b.get("quote") is None:
            continue
        fid = bid.replace("def:", "")
        if b["quote"] == "HB":
            vrel, *pats = HB_QUOTES[bid]
            code, line = hb_quote(vrel, *pats)
        else:
            chunks, line, vrel = [], None, b["file"]
            for q in b["quote"]:
                qfile = q["file"] if isinstance(q, dict) else b["file"]
                qname = q["name"] if isinstance(q, dict) else q
                c, ln = decl_quote(cl, qfile, qname)
                chunks.append(c)
                if line is None:
                    line, vrel = ln, qfile
            code = "\n\n".join(chunks)
        emit(f"block_{fid}", code, vrel, line)

    n = len(list(QUOTES.glob("*.tex")))
    print(f"{n} quote files -> {QUOTES.relative_to(ROOT)}/")


if __name__ == "__main__":
    main()
