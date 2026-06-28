# graph-theory-misc / D7 — algorithms & complexity audit notes

Deferred-tier milestone. **base_ready** run. Verified: compiles axiom-free, 31/31 grounding lemmas
`Qed`, `check_milestone D7 graph-theory-misc` → ACCEPTED (5/5 axiom-free). Algorithm/cost notions kept
deliberately **relational + abstract** (no machine/Turing model) per the agreed design.

## Leg state: 1 done, 4 PARTIAL — the abstract-model faithfulness limit
**Key finding (reviewed decision: mark partial):** math-predicate-only complexity, with no machine
model, can faithfully state **NP-hardness / lower bounds** (universal claims) but **NOT "∃ efficient
algorithm"** — because the abstract `algorithm` (a function) and its `cost` (a separate function) are
*decoupled*, so any existential-algorithm claim is satisfiable by `alg := the exact-answer function`
and `cost := 0`, i.e. **vacuously true**.

- **`complexity_of_the_h_factor` — DONE.** `NP_hard (hfactor_problem H a b)` for non-trivial H
  (`2 < #|H| ∧ connected [set: H]` — the H-hypothesis was auto-added by correct+ground). `NP_hard B`
  = *every* NP problem poly-reduces to B (a universal reduction claim) — genuinely non-vacuous.
- **`algorithm_for_graph_homomorphisms`, `approximation_ratio_for_maximum_edge_disjoint_paths`,
  `ptas_for_feedback_arc_set_in_tournaments`, `finding_k_edge_outerplanar_graph_embeddings` — PARTIAL.**
  All assert "∃ algorithm + cost bound", which is vacuously true in the decoupled abstract model (the
  auditor flagged `approximation_ratio` explicitly — its disjunction is provable via `alg := OPT`,
  `rho := 1 = o(√n)`). A faithful encoding needs computation↔cost coupling (a machine model, out of
  scope) or restructuring to a hardness/lower-bound direction. Recorded `partial`, not `done`.

## Reuse + design
Reused base `homs_to`/`is_hom` (Rows 1,3) and **`wagner_planar`** (the planar guard in Rows 2,5 — the
only available planarity notion; the embedding/face/outerplanar API is the deferred real planar layer,
so `edge_outerplanar` is a wagner_planar+layering PROXY). Abstract complexity vocab (`decides`,
`runs_in_time`, `poly_bounded`, `problem`/`poly_reduces`/`in_NP`/`NP_hard`) is area-local in D7.v;
shared across rows but in one file, so NOT extracted to a `foundations/algorithms.v` (no cross-file
reuse yet — extract if a 2nd graph-theory-misc complexity milestone appears). Nits (review, not fixed):
`walkb` re-implements base's `pathp`; `is_copy`/`H_factor` untagged; `H_factor` capitalization.

## Edges
2 refuted-direction records (ptas / approximation — the source's algorithmic claims do not give a
Qed-closed inter-node implication under these encodings). No verified/candidate edges forced.
