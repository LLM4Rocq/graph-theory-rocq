# hypergraph-theory (`coq-hypergraph-theory` / `rocq-hypergraph-theory`)

Area package of `graph-theory-rocq`. Namespace `Hypergraph`. Phases: U12.
Conjectures: **4 core**
(see `meta/opg_corpus_manifest.json`, filter `repo==hypergraph-theory`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed). **Status: U12 LANDED (2026-06-27).** 4 hypergraph statements (axiom-free, 33/33 grounding `Qed`,
`check_milestone U12` ACCEPTED) in `theories/conjectures/U12.v` — Frankl union-closed, Turán for
hypergraphs, critical k-forests, Ryser (τ ≤ (r−1)ν). Hypergraphs as `{set {set T}}` families; sole
dependency `base/`. See `docs/AUDIT_NOTES.md`.
