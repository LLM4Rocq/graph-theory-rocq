# topological-graph-theory — D3 + D6 preflight & audit notes

Deferred-tier topological campaign. **Strict classification** (no geometry→placeholder): of the 14
D3+D6 rows, **10 need the deferred topological/geometric layer** (drawings, surfaces, faces, genus,
non-orientable surfaces, point-sets, curvature) → **BLOCKED**; the **4 crossing-number rows** were
attempted via an axiom-free split-planarization model → **PARTIAL** (see proxy note). D4 (infinite)
remains last. `check_milestone D3cr` ACCEPTED, axiom-free.

## crossing_number — an axiom-free split-planarization proxy (real contribution, partial)
`foundations/crossing.v`: `xsplit G a b c d` (one crossing resolution: delete independent edges a–b,
c–d, add a degree-4 crossing vertex on the `option G` carrier); `crossing_planar_in k G` (G planarized
by exactly k splits onto base's `wagner_planar`); `is_crossing_number G n` (least such k in the split
model). Grounded: `crossing_number = 0 ⟺ wagner_planar` (both
ways), monotone under sub-relation, `is_crossing_number 'K_5` ⇒ `≥ 1` (K_5 not wagner_planar). Functional
(`is_crossing_number_uniq`). `hypercube d` = iterated base `cartesian_product` of `'K_2`
(`[@MOVE-to-base]`; base's `graph_power` is the distance-power, NOT the cartesian power, so not reusable).

## The 4 crossing rows → PARTIAL (readback/external-review proxy finding)
**Post-readback correction:** the Wave-2 direct forms removed the older vacuity problem, but the
definition still minimizes `xsplit` operations without carrying local drawing rotation/alternation
data at the new degree-4 crossing vertices.  The review in
`meta/FAITHFULNESS_READBACK_REVIEW_2026-07-07.md` therefore could not validate equivalence between
the split model and the drawing crossing number.  The four D3cr rows are now recorded as **partial**:
non-vacuous and useful, but explicitly a proxy until a drawing/rotation equivalence layer is built.

### (historical) The 4 crossing rows → PARTIAL (vacuity, honest)
The earlier concern was that each row used a RELATIONAL encoding (`forall v, is_crossing_number G v -> v = …` / `… -> cr(G) ≥
cr('K_t)`) over a functional split value. **But `is_crossing_number G v` is not
provably inhabited for the non-planar regime** (n ≥ 5): totality (every graph HAS a crossing number)
needs the drawing/geometry existence fact the combinatorial model deliberately omits, and the exact
minimality (cr('K_n) ≥ formula) IS the open problem. So the implications are vacuity-conditional.
Per the bucket-3 rule (abstract invariant acceptable only WITH non-vacuity witnesses; if totality is
the hard part, mark partial), recorded **partial**, not done.  The later readback review above found
the stronger proxy issue: even the direct non-vacuous split statements still need a drawing/rotation
equivalence layer. (Rows: cr('K_n)=Guy,
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

> **UPDATE 2 (signed layer — `foundations/signed_embedding.v`, audited 5/5 sound):** the
> rotation-system layer (`foundations/embedding.v`, Wave 1) made `grunbaums_conjecture` and
> `what_is_the_largest_graph_of_positive_curvature` **done**; the SIGNED layer (edge signatures =
> general orientable-or-not combinatorial maps, Mohar–Thomassen schemes) now makes
> `the_circular_embedding_conjecture` **done** too, in its intended all-surfaces generality.
> `consecutive_non_orientable_embedding_obstructions` stays blocked but the blocker narrowed to 4
> statement-level vocabulary items (embeds-in-N_k without orientable-scheme leakage, disconnected
> embeddability semantics, the K1 empty-map guard, proper-minor) — see the overlay note.
> `crossing_sequences`' blocker is also narrower than the table says: cr-on-S_i is assemblable from
> `xsplit` + `embeds_in_genus` (attemptable). The rest (drawings, point-sets, great circles, obstacle
> number) still need metric geometry and stay blocked.

> **UPDATE 3 (metric-geometry preflight — `foundations/geometry.v`, audited 3/3 SOUND):**
> the residual metric-geometry rows were preflighted under the strict "build only what one row
> justifies" rule. One primitive was justified and built: `orient` (the sign of a 2×2 determinant)
> over an abstract ordered field, with `between`/`seg_cross`/`seg_meet`/`straightline_planar`/
> `n_universal` derived from it (no metric, no Stdlib Reals → axiom-free). Outcome per row:
>
> | slug | outcome | why |
> |---|---|---|
> | small_universal_point_sets_for_planar_graphs | **DONE** | faithful `n_universal` over a real-closed field: injective placement, no vertex on a non-incident edge, independent edges never `seg_meet`. `forall R : rcfType` + Tarski–Seidenberg ⇒ equivalent to the ℝ² source (proof AND disproof transfer). No general-position side condition (the source imposes none). |
> | crossing_sequences | **PARTIAL** | built `foundations/crossing_genus.v`: `is_crossing_genus G i n` uses `k` `xsplit` resolutions landing in `embeds_in_genus i`. Statement = every strictly-decreasing-to-0 `seq nat` is realized by some CONNECTED graph's crossing sequence (orientable primary). `xsplit_connected` (machine-checked) keeps the Euler-genus side exact on connected split targets, but the inherited split model still lacks drawing rotation/alternation equivalence. Nonorientable twin (`semb_in_genus`) not built (scope). |
> | are_different_notions_of_the_crossing_number_the_same | partial candidate | pair-cr vs cr needs two DRAWING semantics; expressible as a proxy over the crossing/embedding layer, not the full ℝ² drawing space. |
> | consecutive_non_orientable_embedding_obstructions | partial candidate | non-orientable minor-minimal obstructions over the signed layer — proxy only (as recorded under UPDATE 2). |
> | 3_colourability_of_arrangements_of_great_circles | **BLOCKED** | genuine spherical arrangement geometry (great circles in general position on S²) — no finite `orient`-only proxy is faithful. |
> | drawing_disconnected_graphs_on_surfaces | **BLOCKED** | optimal drawings on an arbitrary surface Σ — continuous drawing space. |
> | obstacle_number_of_planar_graphs | **BLOCKED** | obstacle/visibility geometry over arbitrary closed sets — the definition itself is the hard part; no faithful finite-polygon proxy. |
>
> One row landed DONE from this preflight: small_universal_point_sets (new `orient`-only geometry
> foundation).  `crossing_sequences` landed as a PARTIAL orientable-primary split-genus proxy, built on
> the existing `xsplit` + `embeds_in_genus` — no new drawing primitive. The `orient`-only foundation is
> deliberately minimal (one row). The three BLOCKED rows stay blocked (real spherical / continuous /
> arbitrary-closed-set geometry). Infinite-combinatorics track is LAST.
>
> Residual caveats on the DONE row (recorded, none blocking — all `note`-severity in the 3/3-SOUND
> audit): (1) the `forall R : rcfType` ⇔ ℝ² equivalence rests on a METATHEORETIC Tarski–Seidenberg
> transfer (each fixed-`(c,n)` body is a first-order ordered-field sentence, field-independent across
> real-closed fields) — argued in the file comments, standard and correct, but not itself certified by
> the `.vo`; (2) `O(n)` is the all-`n` form `exists c, forall n` (equivalent to the textbook tail form
> since a finite universal set exists for each small `n`, absorbed into `c` via `max`); (3) `P : seq`
> counts size with multiplicity — at-least-as-strong as a distinct-point bound, since injectivity
> forces the `n` used points distinct; (4) `c` is chosen inside `forall R` so may formally depend on
> `R` — harmless because Tarski pins every `rcfType` to ℝ's truth; (5) the grounding lemma exercises
> only the edgeless `K1` case, so the `between`/`seg_meet` clauses are never driven by an actual edge
> in a checked-in lemma (`orient_unit`/`orient_id1`/`orient_id2` separately show the primitive has
> content) — a grounding-coverage limitation, not a statement defect.
