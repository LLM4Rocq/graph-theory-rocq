# Track A / Wave 1 — 5 rows unblocked via the embedding foundation

> **Post-review corrections (adversarial Track-A review, 11 confirmed findings):** (1)
> `domination_in_plane_triangulations` gained the REQUIRED `connected [set: G]` guard — the unguarded
> form was **provably false** (disjoint triangles satisfy `planar_embedding`+`triangulation` under the
> truncated connected-map Euler formula yet need γ = n/3 > n/4). (2) `the_circular_embedding_conjecture`
> is **downgraded done → PARTIAL**: rotation systems capture exactly orientable embeddings
> (Heffter–Edmonds), so the Prop is the strictly stronger ORIENTABLE circular-embedding conjecture;
> full faithfulness needs signed rotation systems (non-orientable layer). (3) `grunbaums_conjecture`
> carries a status caveat: the general orientable form was refuted by Kochol (2009); encoding faithful
> to the OPG source, low-genus cases open. (4) `euler_genus`'s connected-only/truncation semantics are
> now documented at the definition site in `foundations/embedding.v`. Net Wave-1 outcome: **4 done +
> 1 partial** (was 5 done).

With the axiom-free combinatorial embedding foundation complete (`foundations/embedding.v`,
`embedding_exists : inhabited (embedding G)` making the predicates non-vacuous), the 5 rows that need
combinatorial topology (not metric geometry) are now faithfully statable and land **done**. All
`check_milestone` ACCEPTED, axiom-free, 3/3 faithfulness on D6emb + both cross-package rows verified.

## The 5 rows
- **grunbaums_conjecture** (topological/D6emb): triangulation E → the dual is 3-edge-colourable =
  ∃ `c : dart G -> 'I_3`, edge-invariant (`c d = c (edge_perm G d)`) with the 3 edges of every
  triangular face pairwise-distinct.
- **the_circular_embedding_conjecture** (topological/D6emb): `k_connected G 2` → ∃ embedding with every
  face boundary a cycle = `{in face_of E d &, injective (source)}` for every `d`.
- **what_is_the_largest_graph_of_positive_curvature** (topological/D6emb): `∃ Nmax, ∀ G E, connected /\
  planar_embedding /\ mindeg≥3 /\ positive_curvature /\ ~is_prism /\ ~is_antiprism -> #|G| <= Nmax`
  (the bounded-sup form). New local `antiprism` sgraph + `is_prism`/`is_antiprism` (reuse base
  `cartesian_product`/`cycle_graph`/`'K_2`/`≃`).
- **every_4_connected_toroidal_graph_has_a_hamilton_cycle** (hamiltonicity/U2): `∀ G, toroidal G ->
  k_connected G 4 -> is_hamiltonian G` (`toroidal = embeds_in_genus 1`). Replaced the old
  `∀ (toroidal : sgraph -> Prop)` placeholder (false under `True`).
- **domination_in_plane_triangulations** (packing/U13): `∃ n0, ∀ G E, planar_embedding E ->
  triangulation E -> n0<=#|G| -> is_domination_number G m -> m <= #|G| %/ 4`.

## Architecture
`hamiltonicity-theory` + `packing-theory` now depend on `topological-graph-theory` (acyclic:
base ← topological ← them) for the embedding predicates; `_CoqProject` + Makefile build order wired.
`is_prism`/`is_antiprism`/`antiprism` are area-local (positive-curvature classification).

## Still blocked after Wave 1 (need a *metric*-geometry or non-orientable layer, out of Track A's
## combinatorial-topology scope)
great_circles (spherical arrangement), small_universal_point_sets + obstacle_number (ℝ² point-sets /
visibility), consecutive_non_orientable_embedding_obstructions (non-orientable maps), drawing_disconnected
_graphs_on_surfaces + crossing_sequences (surface drawings / genus-crossing), plus the 4 D3 crossing
partials (totality) and the D4 infinite rows.
