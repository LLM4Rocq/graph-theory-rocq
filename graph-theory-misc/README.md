# graph-theory-misc (`coq-graph-theory-misc` / `rocq-graph-theory-misc`)

Area package of `graph-theory-rocq`. Namespace `GTMisc`. Phases: D7, U13.
Conjectures: **12 core** + 5 deferred
(see `meta/opg_corpus_manifest.json`, filter `repo==graph-theory-misc`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed). **Status: U13 (graph-theory-misc part) LANDED (2026-06-27).** 12 statements (axiom-free, 32/32
grounding `Qed`, `check_milestone` ACCEPTED, all 12 done) in `theories/conjectures/U13.v` — Moore(57),
graceful-tree, graph pebbling, book-thickness, shuffle-exchange/Beneš, gold-grabbing game, imbalance,
weighted/hexagonal colouring, degenerate-union, etc. See `docs/AUDIT_NOTES.md`.
