# packing-theory (`coq-packing-theory` / `rocq-packing-theory`)

Area package of `graph-theory-rocq`. Namespace `Packing`. Phases: U13, U9.
Conjectures: **15 core**
(see `meta/opg_corpus_manifest.json`, filter `repo==packing-theory`).

Layout (the digraph-theory template): `theories/{foundations,core,invariants,constructions,conjectures,applications}/`.
Depends only on `base/` (+ `digraph-theory/` if directed).

**Status: U9 LANDED (2026-06-26).** 13 packing/covering/transversal/partition statements (axiom-free,
29/29 grounding `Qed`, `check_milestone U9` ACCEPTED) in `theories/conjectures/U9.v` — Bollobás–
Eldridge–Catlin, triangle packing vs transversal, friendly/edge-connectivity partitions, Lovász path
removal, odd-cycle transversal, matching-cut, Kriesell, hypercube matchings, weak saturation, T-joins
(12 done); Jones **G2-blocked**. See `docs/AUDIT_NOTES.md` (incl. pending base-promotion candidates).
