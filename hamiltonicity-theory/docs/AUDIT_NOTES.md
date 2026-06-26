# hamiltonicity-theory — formalization audit notes

Per-statement formalization decisions (keyed by `formal_name`). Produced by the
`area-milestone-pipeline` QA workflow; **base_ready** run (imports `GTBase`, reuses base's
`regular` verbatim — cubic = `regular G 3`). Verified: compiles axiom-free, 24/24 grounding
lemmas `Qed`, `check_milestone U2 hamiltonicity-theory` → ACCEPTED 9/9 checks.

## U2 — hamiltonicity

### Leg state: 5 done, 4 BLOCKED (G2)
The 4 **planar** rows are **blocked** until the fourcolor spike (G2): they currently carry
planarity as an *abstract placeholder predicate*, which is **not a faithful encoding yet** —
do not treat them as landed statements.
- `barnettes_statement`, `decomposing_the_prism_of_a_3_connected_cubic_planar_statement`,
  `every_prism_over_a_3_connected_planar_graph_is_hamil_statement`,
  `every_4_connected_toroidal_graph_has_a_hamilton_cycl_statement`.
- **Why blocked (auditors flagged Barnette + prism-decomp explicitly):** the placeholder is
  written `forall (planar : sgraph -> Prop), planar G -> Concl`. Universally quantifying
  `planar` makes the statement **strictly stronger** than the conjecture — it can be
  instantiated with `planar := fun _ => True`, asserting `Concl` for *all* graphs (including
  non-planar / non-toroidal), which is generally false. So this is a deliberate placeholder,
  not the real statement.
- **G2 fix:** replace the placeholder with the genuine planarity (resp. toroidal-embedding)
  predicate from `coq-graph-theory-planar` (pulls `coq-fourcolor`); then these become faithful
  and graduate from `blocked`.

The 5 **non-planar** rows are faithful + axiom-free (`done`): vertex-transitive (Lovász),
Cayley-graph hamiltonicity, 4-connected-not-uniquely-hamiltonian, uniquely-hamiltonian,
line-graph hamiltonicity.

### New cross-area primitives tagged `[@MOVE-to-base]` (migrate when a 2nd area needs them)
`cartesian_product` (box product `□`, used for prisms), `line_graph`, `bipartite`, `edge_set`,
plus base-candidates `graph_automorphism`, `k_connected`. These are defined locally in `U2.v`
for now; per the federation protocol they move to `base/` once a second area requires them
(e.g. `cartesian_product`/`line_graph` are obvious next base additions). Area-specific
primitives (`hamiltonian_path`/`_cycle`, `is_hamiltonian`, `uniquely_hamiltonian`,
`hamilton_decomposition_into_two`, `vertex_transitive`, `cayley_graph`, `symmetric_set`,
`cycle_edges`) stay here. Minor: `edge_set` should also carry the `[@MOVE-to-base]` tag for
consistency with its siblings.

### Implications
No verified positive edges (the candidate edges — vertex-transitive↔Cayley (Lovász/Babai),
4-connected vs r-regular unique-Hamiltonicity (Sheehan), prism-ham ⟺ prism-decomposition — are
independent or unproven; recorded `candidate`, none asserted). No false edge forced through.
