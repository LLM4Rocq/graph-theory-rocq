# minor-theory (`coq-minor-theory` / `rocq-minor-theory`)

Area package of `graph-theory-rocq`. Namespace `Minor`. Phases: U7.
Conjectures: **6 core**
(see `meta/opg_corpus_manifest.json`, filter `repo==minor-theory`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed).

**Status: U7 LANDED (2026-06-26).** 6 minor/immersion statements (axiom-free, 9/9 grounding `Qed`,
`check_milestone U7` ACCEPTED) in `theories/conjectures/U7.v` — K₆-minor forcing, Seagull,
coloring-and-immersion, 2-regular-minor forcing (4 done); high-connectivity-no-Kₙ + Jørgensen
**G2-blocked** (abstract `is_planar`). Reuses coq-graph-theory `minor`/`'K_n` + base `regular`/`ceil_div`.
See `docs/AUDIT_NOTES.md`.
