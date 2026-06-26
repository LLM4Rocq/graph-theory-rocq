# topological-graph-theory — formalization audit notes

Per-statement decisions (keyed by `formal_name`). **base_ready** run; first milestone in the
`topological-graph-theory` area (namespace `Topological`); the graph-theory-misc + packing-theory
parts of U13 are separate sub-milestones. Verified: compiles axiom-free, 9/9 grounding lemmas `Qed`,
`check_milestone U13 topological-graph-theory` → ACCEPTED.

## U13 (topological) — 4 rows, ALL G2-BLOCKED
Every row is planarity-gated, so all four carry the abstract `is_planar : sgraph -> Prop` placeholder
and land **blocked** (graduate when the real planarity predicate lands at G2):
`large_induced_forest_in_a_planar_graph`, `earth_moon_problem`,
`colouring_the_square_of_a_planar_graph`, `degenerate_colorings_of_planar_graphs`.

## Base reuse
`Delta` (Δ) and **`graph_power`** (G² = the square, `graph_power G 2`) reused verbatim from base;
`is_forest` (induced forest) from coq-graph-theory; χ / `N(x)` from the base re-export. None redefined
— the manifest's "induced-forest", "graph-square", "max-degree" candidates all already existed.

## New primitives
- `union_of_two_planar` (thickness-2 / earth-moon: G is an edge-union of two planar layers over the
  same vertex set) — planar-specific, correctly area-local.
- `k_degenerate_on` / `k_degenerate` — **base candidates** (degeneracy is a general sparsity/colouring
  notion): untagged here; tag `[@MOVE-to-base]` and promote when a 2nd area needs degeneracy.
  `k_degenerate` (whole-graph) is currently defined-but-unused (only `k_degenerate_on` is used).

## Edges
None — no `implications_U13.v` (the four planar conjectures have no Qed-able relative implication;
they're G2-blocked anyway).
