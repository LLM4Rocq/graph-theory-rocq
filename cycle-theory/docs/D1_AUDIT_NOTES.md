# cycle-theory / D1 — flows & tensions audit notes

First **deferred-tier** milestone. **base_ready** run; 3rd cycle-theory milestone (joins U6, U10).
Verified: compiles axiom-free, 25/25 grounding lemmas `Qed`, `check_milestone D1 cycle-theory` →
ACCEPTED. **Faithfulness: 15/15 OK, 0 flagged.** Leg state: **15 done, 0 blocked.**

## D1 — flow/tension conjectures
Integer nowhere-zero flows encoded combinatorially (`has_nz_kflow G k := ∃ conservative φ,
1 ≤ |φ e| ≤ k-1`), so the 3/4/5-flow + three-4-flows + Bouchet (bidirected `has_nz_biflow`) +
Jaeger (modular orientation) rows are axiom-free without reals. Rational/real machinery where the
source needs it: `has_nz_rflow`/`circular_flow_number_le` (over `rat`), `flow_poly : {poly int}` +
`flow_poly_eval` over `rat` (real-roots / half-integral-values rows), and a combinatorial-embedding
**face layer** (darts/`facemap`/`faces`/`fbound`/`local_tension`) for 5-local-tensions.

## Verified edge (sound + honest)
`jaegers_modular_orientation ⟹ three_flow` — `Theorem … : external_modular_orientation_to_flow_statement
-> jaegers_modular_orientation -> three_flow` (Qed). Verified relative to an **explicit named external
fact** (the standard mod-3-orientation ⇔ nowhere-zero-3-flow duality), disclosed, never `Admitted` —
the same pattern as petersen→berge. 5 candidate edges (3/4/5-flow chains, flow-poly, circular-flow).

## ⚠️ Import-order finding (record for future algebra D-phases)
Importing mathcomp `all_algebra`/`all_fingroup` **before** base **poisons** int/rat canonical structures
(ring numerals lose their order instance). **Correct order:** `all_boot` → `GraphTheory mgraph sgraph
treewidth` → `GTBase base` → `all_algebra all_fingroup`.

## Cross-area / de-dup candidates — PENDING your review (kept local, U9 pattern)
D1 re-inlined cycle-theory/U6's general multigraph connectivity (`mconnected`, `edge_connected`,
`cut`, `mdeg`, `is_circuit`, `bridgeless`) rather than importing U6, and adds `two_edge_connected`
(`[@MOVE-to-base]`). These are now in **U6 ∩ D1** (both cycle-theory). Per your "base only if reused
*outside* cycle-theory" rule they are NOT yet used outside this area, so the candidates to weigh are:
(a) a **cycle-theory foundations module** that U6/U10/D1 share (de-dup intra-area, not base);
(b) **D1 imports U6** (lightest); (c) **promote to base** (only if non-cycle reuse is expected soon).
Flow predicates (`has_nz_kflow`, conservation, orientation, flow_poly, face layer) stay
cycle-theory-local. Decision deferred to the promotion review.
