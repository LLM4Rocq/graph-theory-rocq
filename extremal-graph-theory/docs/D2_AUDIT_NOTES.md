# extremal-graph-theory — D2 audit notes (run as 5 vocabulary sub-batches)

Deferred-tier milestone; first in the `extremal-graph-theory` area (namespace `Extremal`, 12th area).
Per the preflight, the 32 rows were split into 5 vocabulary sub-batches and run separately (keeping
faithfulness audits focused, avoiding one 32-statement primitive blob). Each batch is its own
`D2<tag>.v` module (overlay/manifest keep the real phase **D2**). All 5 `check_milestone` ACCEPTED,
axiom-free. **Leg state: 29 done, 3 partial.**

| batch | rows | result | vocabulary |
|---|---|---|---|
| D2chr | 9 | 8 done / 1 partial | fractional/list/circular/choosability χ (foundations/circular_colouring.v) |
| D2ram | 5 | 5 done | Ramsey / Erdős–Hajnal / induced (perfect, Cayley, isubgraph ⇀) |
| D2tur | 6 | 6 done | Turán / counting / **Sidorenko via finite hom_count** |
| D2pr  | 7 | 6 done / 1 partial | probabilistic/random via **exact rational expectations** (no prob. spaces) |
| D2str | 5 | 4 done / 1 partial | structural / hypergraph (poset-dim, geodesic, k-regular, eq-covering) |

## Notable faithful encodings (deferred-tier, no heavy machinery)
- **Sidorenko** (D2tur): finite `hom_count H G` (number of homomorphisms) ≥ the density bound — the
  discrete form, no graphon.
- **Random/probabilistic** (D2pr): EXACT rational expectations/proportions over the finite sample
  space — `Echi G = (Σ_{S⊆E} χ(G_S))/2^|E|` for E[χ(G_{1/2})]; `Pstar = #solvable/#profiles`;
  "almost all" via ε–N counting. No probability-space axioms.
- **Circular χ / choosability / fractional χ** (D2chr): a generic `(p,q)-colouring` layer in
  `foundations/circular_colouring.v` (parametric in adjacency — serves finite sgraphs AND the
  infinite orthogonality graph over an rcfType).

## The 3 partials (honest)
- `mixing_circular_colourings` (D2chr): M_c(G) is a real infimum; the rational-threshold encoding is
  an approximation.
- `covering_powers_of_cycles` (D2str): the `2k<n` guard admits `n=2k+1` where the statement is
  refutable — insufficient regime guard.
- `asymptotic_distribution_of_polyhedra` (D2pr): `polyhedralb` omits planarity (= 3-connected, not
  polyhedra). **Faithful fix available**: `polyhedralb := three_connb ∧ wagner_planar` (base has
  `wagner_planar`) — deferred to the reconciliation review.

## PENDING reconciliation review (base-reuse misses + cross-batch duplication)
Parallel batches independently introduced overlapping vocab + missed some base reuse:
- **base-reuse misses**: `k_connected` (D2str re-defined; base owns it), `edge_count`/`oedges`
  (D2tur+D2ram re-derive `#|E(G)|`), good-edge-labeling avg-degree (D2tur inlined; base has
  `average_degree_geq` → use `~ average_degree_geq`).
- **cross-batch dups**: `bipartite` (D2chr+D2tur), `cycle_graph` (D2str+D2pr), `edge_count` (D2tur+D2ram).
- **cross-area candidates** (`[@MOVE-to-base]`?): `cayley_graph` (undirected analogue of digraph-theory's),
  `strong_power` (strong product — NOT base's distance `graph_power`), `hom_count`, `clique_count`,
  `bipartite`. → consolidate into `extremal-graph-theory/foundations/` + selective base promotion,
  gated on the promotion review (local-first/U9 pattern).
