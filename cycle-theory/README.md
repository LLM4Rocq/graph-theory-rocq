# cycle-theory (`coq-cycle-theory` / `rocq-cycle-theory`)

Area package of `graph-theory-rocq`. Namespace `Cycle`. Phases: D1, U10, U6.
Conjectures: **14 core** + 15 deferred
(see `meta/opg_corpus_manifest.json`, filter `repo==cycle-theory`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed).

**Status: U6 LANDED (2026-06-26).** 11 cycle-cover/decomposition statements (axiom-free, 60/60
grounding `Qed`, `check_milestone U6` ACCEPTED) in `theories/conjectures/U6.v` — Cycle Double Cover
Conjecture + strong-5-CDC, faithful cycle covers, Eulerian/path decompositions, 3-decomposition.
Holds the federation's first **sound verified edge** (`faithful_cycle_covers ⟹ cycle_double_cover`).
See `docs/AUDIT_NOTES.md`.
