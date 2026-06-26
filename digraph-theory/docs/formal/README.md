# The statement-audit companion (PDF)

`digraph_formal.pdf` lets a mathematician audit what exactly has been
machine-checked, without reading proofs or learning Rocq. One page per
headline result:

1. the **verbatim formal statement** (extracted from `theories/` at
   build time, GitHub-linked);
2. a *Decoded* box — the statement re-read as ordinary mathematics;
3. the *Everything this statement needs* panel — the complete list of
   definitions the statement transitively depends on, each explained
   in the Dictionary chapter with a faithfulness note;
4. trust notes (axiom audit, oracle cross-checks).

The panels and quotes are **generated from the compiled library**
(`scripts/statement_closure.py`, `scripts/extract_quotes.py`,
`scripts/gen_panels.py`) and the closure audit gate fails CI if any
definition in any statement's closure lacks a Dictionary entry, or if
a quote anchor disappears from the source. The full-catalog appendix
(`scripts/extract_catalog.py`) lists every named declaration in the
build chain.

Structure: Ch 1 primer (how to read a formal statement) · Ch 2 the
Dictionary (23 definition entries) · Ch 3 the unified theorem
(Conjecture 5.10 at k = 3, 4, 5; Question 5.9 failures) · Ch 4 the
three critical families · Ch 5 Cheng–Keevash path results · Ch 6
general tournament theory · App A glossary of MathComp primitives ·
App B full catalog.

The narrative chapters live in `../web/chapters/` and are shared with
the interactive blueprint site (see `docs/PLAN_WEB.md`).

## Build

```sh
cd docs/formal
make            # regenerates quotes/panels/catalog, runs the closure
                # gate, then pdflatex twice
```

Requires `pdflatex` with `listings`, `mdframed`, `hyperref`,
`cleveref`, plus a built library (the extractors read `*.glob`).
