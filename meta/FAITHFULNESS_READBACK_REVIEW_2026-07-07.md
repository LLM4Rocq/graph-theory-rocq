# Faithfulness readback / review run - 2026-07-07

Scope: a targeted technique #5/#6 run over high-risk/load-bearing rows and
primitives, not a corpus-wide correspondence completion.  This does **not** mark
`correspondence` or `audit_page` legs done in `opg_legs_state.json`.

Method:

- Blind readback: one no-context reviewer saw only uncommented Rocq snippets plus
  a tiny notation glossary.  It did not inspect the OPG source or repo comments.
- Source-aware review proxy: two independent reviewers compared the selected
  Rocq definitions against `meta/opg_corpus_manifest.json` and the checked-in
  source files.
- Boundary: this is an independent-review proxy inside this session.  It is not a
  substitute for a real external domain-expert review.

Reviewed targets:

- `list_colourable_on`, `is_lambda`, `partial_list_coloring_0_statement`
- `strongly_colorable`, `strong_colorability_statement`
- `girth_geq`, `has_girth`, `wagner_planar`
- `subgraph_of_large_average_degree_and_large_average_d_statement`
- `crossing_planar_in`, `is_crossing_number`, D3 complete/complete-bipartite
  crossing-number statements
- `crossing_genus_in`, `is_crossing_genus`, `crossing_sequences_statement`
- `seg_meet`, `straightline_planar`, `n_universal`,
  `small_universal_point_sets_for_planar_graphs_statement`

## Blind-readback signals

The blind reader reconstructed the intended meaning of `Delta`, `girth_geq`,
partial list coloring, strong colorability, `wagner_planar`, crossing number,
crossing sequences, and universal point sets from definitions alone.

Useful blind concerns:

- `list_colourable_on` depends on the partial `option C` reading; source-aware
  review confirmed this is intentional and fixes the empty-palette corner.
- `wagner_planar` depends on `minor G H` direction; source-aware review confirmed
  the repo consistently uses "G contains H as a minor".
- `crossing_planar_in` / `is_crossing_number` read back as abstract edge-pair
  splitting, not a drawing-level crossing predicate.  Source-aware review
  promoted this to an open blocker below.
- `n_universal` uses `P : seq (pt R)`; existing D3 notes already record the
  multiplicity caveat, and source-aware review did not find it blocking.

## Fixes Applied

These findings were local statement/primitive bugs and were repaired in this run.

1. `has_girth` witness guard.
   Review found that `has_girth` required `ucycle c /\ size c = g` but did not
   repeat the genuine-cycle guard used by `girth_geq`.  The primitive now requires
   `2 < size c` in the witness half:
   `base/theories/base.v:264`.

2. Empty host graph in the average-degree/girth row.
   `average_degree_geq 'K_0 d` is fraction-free true, while the row demanded a
   nonempty subgraph.  The U13 statement now guards the host graph with
   `0 < #|G|` before applying `avgdeg_geq`:
   `graph-theory-misc/theories/conjectures/U13.v:150`.

3. Strong colorability at `r = 0`.
   The source defines strong `r`-colorability for positive `r`; the old row let
   nonempty edgeless graphs satisfy `strongly_colorable G 0` vacuously because no
   partition into nonempty blocks of size `<= 0` exists.  The row now states the
   non-degenerate case `0 < Delta G -> strongly_colorable G (2 * Delta G)`:
   `chromatic-theory/theories/conjectures/U4.v:273`.

## Open Findings

1. Crossing-number / crossing-genus split model.
   The D3 crossing layer defines `xsplit` by deleting two independent edges and
   adding a degree-4 vertex, then minimizing the number of such splits needed to
   reach `wagner_planar` or `embeds_in_genus`
   (`topological-graph-theory/theories/foundations/crossing.v:62`,
   `topological-graph-theory/theories/foundations/crossing.v:89`,
   `topological-graph-theory/theories/foundations/crossing_genus.v:113`).
   A drawing-level crossing planarization also carries local rotation/alternation
   data at each crossing vertex.  The current predicate has no such guard, so the
   review could not validate it as equivalent to drawing crossing number.

   Affected statements:

   - `the_crossing_number_of_the_complete_bipartite_graph_statement`
   - `the_crossing_number_of_the_complete_graph_statement`
   - `crossing_numbers_and_coloring_statement`
   - `the_crossing_number_of_the_hypercube_statement`
   - `crossing_sequences_statement` via `is_crossing_genus`

   Follow-up applied after this review: the four D3cr rows were downgraded to
   `statement = partial` with explicit proxy notes in `opg_legs_state.json` and
   `opg_corpus_manifest.json`.  The path back to `done` is still to build a
   drawing/rotation equivalence layer for the split model.

2. `crossing_sequences_statement` covers only the orientable half.
   The source includes the nonorientable "resp." variant.  The current formal row
   explicitly scopes itself to the orientable primary and leaves the
   nonorientable twin unbuilt.  This is already documented in
   `topological-graph-theory/theories/conjectures/D3xseq.v`, but the manifest
   idiom should expose the orientable-only restriction more directly.

## Source-Aware Verdicts

- SOUND after review: `partial_list_coloring_0_statement`, `list_colourable_on`,
  `is_lambda`, `girth_geq`, `wagner_planar` for finite simple graph planarity,
  and D3 geometry (`seg_meet`, `straightline_planar`, `n_universal`,
  `small_universal_point_sets_for_planar_graphs_statement`).
- REPAIRED in this run: `has_girth`, U13 average-degree/girth host graph,
  `strong_colorability_statement`.
- OPEN/BLOCKING REVIEW ITEM: the D3 crossing-number and crossing-genus split
  model needs a drawing/rotation equivalence to return the affected rows to
  `done`; the four D3cr rows have been downgraded to `partial`.
