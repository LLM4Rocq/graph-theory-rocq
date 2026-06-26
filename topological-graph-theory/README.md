# topological-graph-theory (`coq-topological-graph-theory` / `rocq-topological-graph-theory`)

Area package of `graph-theory-rocq`. Namespace `Topological`. Phases: D3, D6, U13.
Conjectures: **4 core** + 14 deferred
(see `meta/opg_corpus_manifest.json`, filter `repo==topological-graph-theory`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed). **Status: U13 (topological part) LANDED (2026-06-27).** 4 planar statements (axiom-free, 9/9
grounding `Qed`, `check_milestone` ACCEPTED) in `theories/conjectures/U13.v` — large-induced-forest,
earth-moon, square-of-planar colouring, degenerate colourings. **All 4 G2-blocked** (abstract
`is_planar`). Reuses base `Delta`/`graph_power` + `is_forest`. See `docs/AUDIT_NOTES.md`.
