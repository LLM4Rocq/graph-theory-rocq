# Roadmap — deep layers (post statement-complete)

The corpus formalization goal is **complete**: 227/227 OpenProblemGarden rows attempted, 192 done as
axiom-free `Definition <name>_statement : Prop`, 18 partial, 17 blocked (see `meta/CORPUS_STATUS.md`).
The 35 partial/blocked rows are gated on three deep layers we deliberately did **not** build. Each is a
separate follow-up track; none should start before the v1.0 statement-complete release is frozen.

## Track A — Topological layer (unblocks ~12 + crossing totality)
Embeddings / faces / genus / surfaces / drawings / point-sets / combinatorial curvature, plus a
decidable planarity test so `crossing_number` becomes **total** (today it is a faithful planarization
invariant but the conjecture statements are vacuity-conditional on inhabitance — see
`topological-graph-theory/docs/D3_D6_AUDIT_NOTES.md`).
- Blocked/partial rows: the 10 D3+D6 geometry rows, the 4 D3 crossing rows (totality), the 2 surface
  rows (toroidal-Hamilton, plane-triangulation domination).
- Likely substrate: rotation systems (combinatorial embeddings) → Euler genus → faces; a decidable
  planar predicate to replace/strengthen `wagner_planar` for counting.
- **PROGRESS:** the orientable rotation-system layer (`foundations/embedding.v`, Wave 1) and the
  SIGNED layer (`foundations/signed_embedding.v` — general orientable-or-not maps, `orientable_map`,
  crosscap-scale `seuler_genus`) both EXIST, audited. Waves 1–2 landed grunbaum / curvature /
  toroidal-Hamilton / plane-triangulation / circular-embedding (all-surfaces form) / the 4 crossing
  rows. Remaining in this track: metric geometry (drawings, point-sets, great circles, obstacles),
  the embeds-in-N_k vocabulary for the non-orientable obstruction row, cr-on-S_i assembly for
  crossing_sequences, and hardening TODOs (Qed the flag-doubling mirror lemma; formalize
  emFs = 2·emF / the crosscap-scale compat).

## Track B — Infinite-combinatorics layer (unblocks 7 D4 partial)
Ends / Freudenthal-style end equivalence, infinite Hamiltonicity (topological double-ray cycles),
infinite-graph minors (branch sets over `iGraph`), and a careful ℵ₀-vs-cardinal neighbour comparison.
- Builds on the existing `infinite-graph-theory/foundations/igraph.v` carrier (Prop-edge `iGraph`).
- Rows: end_devouring_rays, hamiltonian_cycles_in_line_graphs / _in_powers, infinite_uniquely_hamiltonian,
  seymours_self_minor, unfriendly_partitions, strong_matchings_and_covers.
- Out of scope even then (genuine ℵ₁ / ZFC-independence / ℝ² / automorphism-universality): the 5 D4
  blocked rows.

## Track C — Computation-cost layer (unblocks 4 D7 algorithmic)
A lightweight cost model that COUPLES an abstract algorithm to its cost, so existential "∃ efficient
algorithm" claims are non-vacuous (today they are vacuously true under the decoupled abstract model —
see `graph-theory-misc/docs/D7_AUDIT_NOTES.md`). NP-hardness/lower-bound rows are already faithful
(`complexity_of_the_h_factor`).
- Rows: algorithm_for_graph_homomorphisms, approximation_ratio_for_maximum_edge_disjoint_paths,
  ptas_for_feedback_arc_set_in_tournaments, finding_k_edge_outerplanar_graph_embeddings.
- Design tension to resolve: a non-Turing cost coupling that stays statement-only.
- **PROGRESS (Track B landed):** `graph-theory-misc/foundations/complexity.v` — a deep-embedded total
  combinator language with one cost-metering interpreter (`no_zero_cost_program` Qed'd). The 4 positive
  rows retargeted and audited (3 breaks caught and fixed: EDP classical tautology, outerplanar
  constant-satisfier, h_factor refutable guard). Now: hom / EDP-improvement / PTAS done;
  k-edge-outerplanar remains partial (proxy notion). Hardening TODO: formalize the P-containment
  direction (Cobham-style) if ever needed.

## Invariants to preserve across all tracks
Axiom-free throughout (`Print Assumptions` clean); local-first vocabulary (promote to `base/` only when
≥2 areas reuse a finite invariant); faithfulness-audit + correct-and-ground before landing; update the
overlay + regenerate `meta/CORPUS_STATUS.md`; `make gate` green.
