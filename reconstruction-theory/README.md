# reconstruction-theory (`coq-reconstruction-theory` / `rocq-reconstruction-theory`)

Area package of `graph-theory-rocq`. Namespace `Reconstruction`. Phases: U11.
Conjectures: **4 core**
(see `meta/opg_corpus_manifest.json`, filter `repo==reconstruction-theory`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed). **Status: U11 LANDED (2026-06-27).** 4 reconstruction statements (axiom-free, 19/19 grounding `Qed`,
`check_milestone U11` ACCEPTED) in `theories/conjectures/U11.v` — Reconstruction + edge/switching/tree
variants, all in the "decks equal up to iso ⟹ iso" form. See `docs/AUDIT_NOTES.md`.
