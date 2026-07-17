# X171-X190 Faithfulness Audit

Date: 2026-07-15

Scope: the next 20 package-assigned, not-yet-landed v2 arXiv rows after X170,
skipping parked/out-of-scope rows and rows already reconciled in earlier waves
(`axv_1606_06011_00` through `axv_1704_00125_00`).

## Outcome

- 20 statement files authored and wired: X171-X190.
- 3 faithful `done` rows: X173, X178, X187.
- 17 honest `blocked` rows: X171, X172, X174-X177, X179-X186, X188-X190.
- No `partial` rows in this batch.

## Faithful Rows

- X173: fractional chromatic number bound for planar triangle-free graphs.
  Reuses X130's audited finite-graph fractional-colouring predicate, with the
  bound encoded exactly as `3n/(n+1)` and triangle-free as `girth_geq G 4`.
- X178: Bonamy-Perrett strengthening of Gallai path decomposition.  Encodes
  edge decompositions into at most `floor(|V|/2)` simple paths and encodes odd
  semi-cliques as graphs on `2k+1` vertices with at most `k-1` missing edges.
- X187: request-graph formulation for triangle-free planar graphs, tracked as
  faithful-to-refuted.  Equality/inequality request vertices, positive finite
  weights, proper 3-colourings, and a uniform positive rational satisfied
  fraction are explicit.  Natural weights are faithful for finite rational
  weights after clearing denominators.

## Blocked Rows

- X171/X172: need graph shortest-path metric lines, bridge counts, finite
  exceptional graph families, and bridge-to-path generation.
- X174: needs a faithful `K_t`-immersion relation and exact clique-count
  extremal maximum.
- X175: needs `K_t`-subdivision containment and a little-o exponential
  asymptotic layer.
- X176: needs cone crossing functions, crossing numbers, square-root/fractional
  powers, and little-o asymptotics.
- X177: needs the Scott-Seymour forest-of-lanterns class and long induced
  subdivisions.
- X179: needs kappa-/kappa-prime-maderian digraph definitions and directed
  subdivision containment.
- X180: needs the multitasker capacity model and asymptotic average-degree
  vocabulary.
- X181: needs clique chromatic number, `G(n,1/2)`, whp probability, logarithms,
  and asymptotic equality.
- X182: needs finite posets, cover graph planarity, height, and dimension.
- X183: needs weighted/unweighted list-flexibility; the file deliberately reuses
  the already-blocked X132 placeholder layer.
- X184: needs directed edge-connectivity and antisymmetric flows over `Z_5`.
- X185/X186: need Scott-Seymour widespreadness, multigraph support, local
  `chi_2`, and induced-subdivision containment.
- X188: needs the interactive sum-choice game and ordinary sum-choice number.
- X189: needs tree/path-decomposition objects, the rooted spaghetti condition,
  and bag-intersection width.
- X190: needs strongly sublinear separators and thin systems of overlays.

## Verification

The affected packages compiled axiom-free under the `~/.opam/digraph` switch:
chromatic, graph-theory-misc, minor, topological, packing, digraph, extremal,
and cycle.  Corpus gates and per-milestone gates were run after metadata
regeneration.

## 2026-07-16 Retarget Addendum

- X175 moved from `blocked` to `done` after the `GTBase.asymptotics`
  foundation was promoted.
- The retargeted statement defines `K_t`-subdivision containment concretely:
  injective branch vertices, simple paths between every branch pair, no branch
  vertex internal to a route, and pairwise internally vertex-disjoint routes.
- The `3^(2t/3+o(t)) n` upper envelope is now the rational-epsilon eventual
  integer form: for every epsilon `a/b > 0`, eventually
  `cliques^(3b) <= 3^((2b+3a)t) * n^(3b)`.
- Faithfulness boundary: the source-context lower-bound construction is known
  and not the open claim formalised here; the row records the conjectured
  matching upper envelope.

## 2026-07-16 Foundation Retarget Addendum

- X182 moved from `blocked` to `done` after `GTBase.posets` was promoted.
  Finite posets now have explicit carriers and orders, cover graphs are
  concrete `sgraph`s, height is bounded via finite chains, and dimension is
  represented by a realizer of linear extensions.  The row states the
  polynomial-in-height version for posets whose cover graph is `wagner_planar`.
- X183 moved from `blocked` to `done` after `GTBase.list_flexibility` was
  promoted.  It now uses base `k_degenerate` and the stronger weighted
  epsilon-flexibility branch for lists of size `d+1`.

## 2026-07-16 Graph Metric Retarget Addendum

- X171 moved from `blocked` to `done` after `GTBase.graph_metric` was promoted.
  The statement now uses shortest-path metric lines, bridge counts, and the
  bound `#|G| <= metric_line_count G + bridge_count G`.  The finite exceptional
  family is encoded by an order bound.
- X172 remains `blocked`, but its counterexample predicate is now grounded as
  `metric_line_count G + bridge_count G < #|G|` for connected graphs.  The
  missing foundation is specifically the repeated operation that replaces a
  bridge by an arbitrarily long path and the finite-generation closure under
  that operation.
- X174 moved from `blocked` to `done` by reusing the existing `U7` immersion
  relation.  The exact maximum statement is encoded as a universal upper bound
  for every `n`-vertex graph with no `K_t` immersion plus existence of a graph
  attaining `2^(t-2)(n-t+3)`.
