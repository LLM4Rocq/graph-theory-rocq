#!/usr/bin/env python3
"""gen_blueprint.py — generate the blueprint site chapters (PLAN_WEB M20).

Single source of truth: the PDF chapters (docs/web/chapters/) carry the
hand-written prose; closure.json carries the dependency structure;
docs/web/quotes/*.code carry the verbatim statements. This script
compiles all three into plasTeX-friendly chapters under blueprint/src/:

  bp_dictionary.tex   one \\begin{definition} per def-block
  bp_unified.tex,
  bp_families.tex,
  bp_paths.tex,
  bp_general.tex      one \\begin{theorem} per catalog result, with
                      \\uses{...} edges generated from closure.json
                      (the clickable dependency graph can never drift
                      from the audited closure).

Prose conversion: \\rocqinline@X@ -> \\code{X.}, \\cref -> \\ref list,
boxes -> bold-led paragraphs, \\input quote/panel lines dropped
(replaced by generated content).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from statement_closure import CATALOG, vfile_to_lib

CHAPTERS = ROOT / "docs" / "web" / "chapters"
QUOTES = ROOT / "docs" / "web" / "quotes"
OUT = ROOT / "blueprint" / "src"

# def-block -> def-block dependency edges (drawn in the graph).
DEF_USES = {
    "def:oriented": ["def:arc"],
    "def:outdeg": ["def:arc"],
    "def:tournament": ["def:oriented"],
    "def:transb": ["def:arc"],
    "def:C3": ["def:tournament"],
    "def:dgiso": ["def:arc"],
    "def:subdel": ["def:tournament"],
    "def:ltp": [],
    "def:backedge": ["def:tournament", "def:ltp"],
    "def:omegabar": ["def:backedge"],
    "def:kcritical": ["def:omegabar", "def:subdel"],
    "def:domination": ["def:tournament"],
    "def:aut": ["def:arc"],
    "def:vt": ["def:aut"],
    "def:lexprod": ["def:tournament"],
    "def:cayley": ["def:arc"],
    "def:AC": ["def:cayley", "def:tournament"],
    "def:T4family": ["def:lexprod", "def:AC", "def:C3"],
    "def:T5family": ["def:lexprod", "def:AC"],
    "def:dipath": ["def:arc"],
    "def:ell": ["def:dipath"],
    "def:strong": ["def:arc"],
}

TT_ESCAPE = str.maketrans({
    "_": r"\_", "&": r"\&", "%": r"\%", "#": r"\#", "$": r"\$",
    "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}",
})


def code(s: str) -> str:
    return r"\code{" + s.translate(TT_ESCAPE) + "}"


def convert_prose(t: str) -> str:
    """PDF-chapter prose -> plasTeX-friendly prose."""
    t = re.sub(r"\\rocqinline@([^@]*)@", lambda m: code(m.group(1)), t)
    t = re.sub(r"\\cref\{([^}]*)\}",
               lambda m: ", ".join(rf"\ref{{{x.strip()}}}"
                                   for x in m.group(1).split(",")), t)
    t = t.replace("\\S\\ref", "\\ref")
    t = re.sub(r"\\input\{[^}]*\}\n?", "", t)
    t = re.sub(r"\\label\{[^}]*\}\n?", "", t)
    # boxes -> bold-led inline paragraphs. NEVER \paragraph here: a
    # sectioning command inside a theorem-like environment makes plasTeX
    # close the environment early, leaving an empty unlabeled env that
    # shows up as an isolated auto-id node in the dependency graph.
    t = re.sub(r"\\begin\{decoded\}", r"\\par\\textbf{Decoded.} ", t)
    t = re.sub(r"\\end\{decoded\}", r"\\par", t)
    t = re.sub(r"\\begin\{faithnote\}",
               r"\\par\\textbf{Why this is the right definition.} ", t)
    t = re.sub(r"\\end\{faithnote\}", r"\\par", t)
    t = re.sub(r"\\begin\{trustbox\}", r"\\par\\textbf{Trust.} ", t)
    t = re.sub(r"\\end\{trustbox\}", r"\\par", t)
    t = t.replace("\\noindent\\textbf{Trust.}", "")
    t = t.replace("\\noindent", "")
    return t.strip()


def raw_quote(stem: str) -> tuple[str, str, str]:
    """(code, file, line) from a .code quote file."""
    txt = (QUOTES / f"{stem}.code").read_text(encoding="utf-8")
    head, _, body = txt.partition("\n")
    vrel, _, line = head[2:].rpartition(":")
    return body.rstrip(), vrel, line


def verb(stem: str) -> str:
    c, vrel, line = raw_quote(stem)
    gh = f"https://github.com/LLM4Rocq/digraph-theory/blob/main/{vrel}"
    return (f"\\begin{{verbatim}}\n{c}\n\\end{{verbatim}}\n"
            f"\\href{{{gh}\\#L{line}}}{{Source: "
            f"{code(vrel + ':' + line)}}}\n")


def parse_dictionary() -> dict[str, tuple[str, str]]:
    """def-block id -> (title, converted prose with quote inserted)."""
    src = (CHAPTERS / "ch_dictionary.tex").read_text(encoding="utf-8")
    out = {}
    parts = re.split(r"\\defblockhead\{", src)[1:]
    for part in parts:
        # title may contain braces (math) — match to the closing "}{id}"
        m = re.match(r"(.*?)\}\{(def:[A-Za-z0-9]+)\}\n", part, re.S)
        title, bid = m.group(1), m.group(2)
        body = part[m.end():]
        qm = re.search(r"\\input\{\.\./web/quotes/(block_\w+)\}", body)
        prose = convert_prose(body)
        quote_tex = verb(qm.group(1)) if qm else ""
        out[bid] = (title, quote_tex + "\n" + prose)
    return out


def parse_results() -> dict[str, tuple[str, str, str]]:
    """result -> (chapter, group title, converted decoded prose)."""
    out = {}
    for ch in ("ch_unified", "ch_families", "ch_paths", "ch_general"):
        src = (CHAPTERS / f"{ch}.tex").read_text(encoding="utf-8")
        groups = re.split(r"\\resulthead\{", src)[1:]
        for g in groups:
            m = re.match(r"(.*?)\}\{(\w+)\}\n", g, re.S)
            title = m.group(1)
            body = g[m.end():]
            results = re.findall(
                r"\\input\{\.\./web/quotes/result_(\w+)\}", body)
            dm = re.search(r"\\begin\{decoded\}(.*?)\\end\{decoded\}",
                           body, re.S)
            decoded = convert_prose(dm.group(1)) if dm else ""
            for i, r in enumerate(results):
                out[r] = (ch, title, decoded if i == 0 else "")
    return out


HEADERS = {
    "ch_unified": "The unified theorem: Conjecture 5.10 at $k = 3,4,5$",
    "ch_families": "The three critical families",
    "ch_paths": "Directed paths: the Cheng--Keevash results",
    "ch_general": "General tournament theory",
}


def main() -> None:
    closure = json.loads((ROOT / "docs/web/closure.json").read_text())
    cur = json.loads((ROOT / "docs/web/defblocks.json").read_text())
    blocks, cmap = cur["blocks"], cur["map"]
    OUT.mkdir(parents=True, exist_ok=True)

    # --- the dictionary chapter ---
    dico = parse_dictionary()
    missing = set(blocks) - set(dico)
    assert not missing, f"def-blocks without dictionary entry: {missing}"
    lines = ["% GENERATED by scripts/gen_blueprint.py — do not edit.",
             "\\chapter{The Dictionary: every definition you need}",
             "\\label{ch:dictionary}", ""]
    for bid, (title, content) in dico.items():
        uses = DEF_USES.get(bid, [])
        lines += [f"\\begin{{definition}}[{title}]",
                  f"  \\label{{{bid}}}"]
        if uses:
            lines.append(f"  \\uses{{{', '.join(uses)}}}")
        lines += ["  \\rocqok", "", content, "", "\\end{definition}", ""]
    (OUT / "bp_dictionary.tex").write_text("\n".join(lines) + "\n",
                                           encoding="utf-8")

    # --- the result chapters ---
    res = parse_results()
    missing = set(CATALOG) - set(res)
    assert not missing, f"catalog results without a page: {missing}"
    chapters: dict[str, list[str]] = {c: [] for c in HEADERS}
    emitted_titles: dict[str, set] = {c: set() for c in HEADERS}
    for r, vrel in CATALOG.items():
        ch, title, decoded = res[r]
        L = chapters[ch]
        if title not in emitted_titles[ch]:
            emitted_titles[ch].add(title)
            L += [f"\\section{{{title}}}", ""]
        uses = sorted({cmap[c] for c in closure[r]["digraph"]})
        fq = f"{vfile_to_lib(vrel)}.{r}"
        L += [f"\\begin{{theorem}}[{code(r)}]",
              f"  \\label{{res:{r}}}",
              f"  \\uses{{{', '.join(uses)}}}",
              f"  \\rocq{{{fq}}}",
              "  \\rocqok", "",
              verb(f"result_{r}"), ""]
        if decoded:
            L += [f"\\par\\textbf{{Decoded.}} {decoded}", ""]
        L += ["\\end{theorem}", ""]
    for ch, body in chapters.items():
        out = ["% GENERATED by scripts/gen_blueprint.py — do not edit.",
               f"\\chapter{{{HEADERS[ch]}}}",
               f"\\label{{bp:{ch}}}", ""] + body
        (OUT / f"bp_{ch.removeprefix('ch_')}.tex").write_text(
            "\n".join(out) + "\n", encoding="utf-8")
    print(f"blueprint chapters -> {OUT.relative_to(ROOT)}/ "
          f"({len(dico)} definitions, {len(res)} results)")


if __name__ == "__main__":
    main()
