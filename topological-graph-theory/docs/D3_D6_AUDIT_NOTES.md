# topological-graph-theory — D3 + D6 preflight & audit notes

Deferred-tier topological campaign. **Strict classification** (no geometry→placeholder): of the 14
D3+D6 rows, **10 need the deferred topological/geometric layer** (drawings, surfaces, faces, genus,
non-orientable surfaces, point-sets, curvature) → **BLOCKED**; the **4 crossing-number rows** were
attempted via a faithful combinatorial `crossing_number` → **PARTIAL** (see vacuity note). D4 (infinite)
remains last. `check_milestone D3cr` ACCEPTED, axiom-free.

## crossing_number — a faithful planarization invariant (real contribution, kept)
`foundations/crossing.v`: `xsplit G a b c d` (one crossing resolution: delete independent edges a–b,
c–d, add a degree-4 crossing vertex on the `option G` carrier); `crossing_planar_in k G` (G planarized
by exactly k splits onto base's `wagner_planar`); `is_crossing_number G n` (least such k — the standard
planarization characterisation, hence faithful). Grounded: `crossing_number = 0 ⟺ wagner_planar` (both
ways), monotone under sub-relation, `is_crossing_number 'K_5` ⇒ `≥ 1` (K_5 not wagner_planar). Functional
(`is_crossing_number_uniq`). `hypercube d` = iterated base `cartesian_product` of `'K_2`
(`[@MOVE-to-base]`; base's `graph_power` is the distance-power, NOT the cartesian power, so not reusable).

## The 4 crossing rows → DONE (Wave 2: direct non-vacuous forms)
**Wave-2 upgrade (audited 5/5 clean: 4 per-row auditors + a vacuity skeptic with compiled refutation
probes):** the rows now assert the conjectures DIRECTLY — `is_crossing_number 'K_n (Guy)` /
`is_crossing_number (KB m n) (Zarankiewicz)` (achievability + minimality both part of the claim, no
inhabitance gate; Guy's `%/4` exact for all n), Albertson in sub-level form (`forall k achievable for
G, exists j <= k achievable for K_t` — robust to exactly-k non-monotonicity; the t=5 slice provably
carries four-colour-theorem strength), and the hypercube limit two-sided ε–N on achievable counts
(body ⟺ minimum-in-window, Qed-probed). The pre-Wave-2 text below records the original partial state.

### (historical) The 4 crossing rows → PARTIAL (vacuity, honest)
Each is the correct RELATIONAL encoding (`forall v, is_crossing_number G v -> v = …` / `… -> cr(G) ≥
cr('K_t)`), faithful given `is_crossing_number` is functional. **But `is_crossing_number G v` is not
provably inhabited for the non-planar regime** (n ≥ 5): totality (every graph HAS a crossing number)
needs the drawing/geometry existence fact the combinatorial model deliberately omits, and the exact
minimality (cr('K_n) ≥ formula) IS the open problem. So the implications are vacuity-conditional.
Per the bucket-3 rule (abstract invariant acceptable only WITH non-vacuity witnesses; if totality is
the hard part, mark partial), recorded **partial**, not done — the `crossing_number` primitive itself
is faithful + grounded; only inhabitance for non-planar graphs is missing. (Rows: cr('K_n)=Guy,
cr(KB m n)=Zarankiewicz, χ≥t→cr(G)≥cr('K_t), lim cr(Q_d)/4^d=5/32 via ε–N.)

## The 10 BLOCKED rows — which topological primitive each needs
| slug | ph | needs |
|---|---|---|
| 3_colourability_of_arrangements_of_great_circles | D3 | spherical arrangement geometry (great circles in general position) |
| are_different_notions_of_the_crossing_number_the_same | D3 | two distinct DRAWING semantics (pair-cr vs cr) — non-vacuous only with drawings |
| crossing_sequences | D3 | crossing-number-on-genus-i — genus/surface layer |
| drawing_disconnected_graphs_on_surfaces | D3 | optimal drawings on a surface Σ |
| obstacle_number_of_planar_graphs | D3 | obstacle/visibility geometry (the def is the hard part) |
| small_universal_point_sets_for_planar_graphs | D3 | point sets ⊂ ℝ² + straight-line embeddings |
| consecutive_non_orientable_embedding_obstructions | D6 | non-orientable surface embedding + minor-minimal obstructions |
| grunbaums_conjecture | D6 | triangulation of an orientable surface (rotation-system embedding) |
| the_circular_embedding_conjecture | D6 | surface embedding + face boundaries |
| what_is_the_largest_graph_of_positive_curvature | D6 | combinatorial curvature = needs face sizes (embedding) |

These stay blocked until a real topological layer (rotation systems / embeddings / genus / a decidable
planarity test) is built — a deliberate deferral, joining the 2 surface rows already blocked.

> **UPDATE (Wave 1 — the rotation-system layer now EXISTS,** `foundations/embedding.v`**):** of the
> table above, `grunbaums_conjecture` and `what_is_the_largest_graph_of_positive_curvature` are now
> **done**, and `the_circular_embedding_conjecture` is **partial** (orientable-only encoding — see
> `WAVE1_AUDIT_NOTES.md`); the two blocked surface rows outside this package (toroidal-Hamilton,
> plane-triangulation domination) are also done. The remaining rows of the table (drawings, point-sets,
> non-orientable obstructions, crossing sequences, great circles, obstacle number) still need metric
> geometry or a non-orientable layer and stay blocked.
