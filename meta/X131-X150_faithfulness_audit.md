# X131-X150 Faithfulness Audit

Date: 2026-07-15

Scope: the next standalone statement wave after X130, continuing the alphabetic
studies-slice walk. Two intervening manifest rows were intentionally skipped as
non-standalone statement targets: `std_erd_s_ne_et_il_conjecture_strong_chromatic_index`
is an alias of the existing OPG strong-edge-colouring row, and
`std_erd_s_problem_on_k_r_graphs` is an edge-anchor with an undefined paper-local
`(k,r)`-graph primitive.

## Outcome

- 20 statement files authored and wired: X131-X150.
- 11 faithful `done` rows: X131, X133-X137, X141, X142, X144, X146, X149.
- 9 honest `blocked` rows: X132, X138-X140, X143, X145, X147, X148, X150.
- No `partial` rows in this batch.

## Faithful Rows

- X131: duplicate Dvorak-Mnich fractional-colouring row, implemented as a synonym
  of the audited X130 statement to prevent drift.
- X133: K_s-free clique-minor growth; `K_s`-free is `omega < s`, `n/r` large
  enough is `N*r <= n`, and "polynomially larger" is a positive rational
  exponent cleared over `nat`.
- X134: squared spectral-energy bound is the same proposition as X6's audited
  `s+`/`s-` squared-sum bound.
- X135: Engbers homomorphism-count maximisation; hom counts use the existing
  finite-function idiom and fractional exponents are cleared by
  `D = 2*delta*(delta+1)`.
- X136: tournament Erdos-Hajnal; H-free is induced-free on tournaments, transitive
  subtournament is `transb (sub_tournament S)`, exponent is positive rational.
- X137: Erdos-Rado sunflower; finite r-uniform set families and k-petal common-core
  sunflower are defined directly.
- X141: zero forcing Cartesian product; local closure relation implements the
  unique-uncoloured-neighbour forcing rule and exact zero forcing numbers are
  relational.
- X142: neighbour-sum distinguishing edge colouring; proper edge colouring,
  positive colour sums, adjacent-vertex sum distinction, and the C5 exception are
  explicit.
- X144: Fox pure-pair conjecture; perfect graph and pure pair are direct, and
  `n^(1-o(1))` is the standard `forall epsilon > 0, eventually` rational form.
- X146: Geelen coarse Gallai; A-path endpoints are in A, internal vertices are
  outside A, distance uses closed `(d-1)`-balls, and the separator ball meets every
  A-path.
- X149: 4-chromatic planar fractional row; strict `chi_f > 3` is negated X130
  `chi_f <= 3`, with `wagner_planar` and `chi = 4`.

## Blocked Rows

- X132: weighted epsilon-flexibility of lists is absent; the file uses only the
  necessary choosability consequence for list sizes 5/4/3.
- X138: needs fixed-surface embeddability and clustered-colouring/component-size
  foundations.
- X139: needs polynomial-expansion/shallow-minor density and strong-colouring-number
  foundations.
- X140: needs multigraph edge multiplicity, random orientable embeddings,
  face-count expectation, and logarithmic asymptotics.
- X143: needs graphon/quasirandom forcing; the compiling file loudly marks the
  forcing predicate as a placeholder.
- X145: needs an asymptotic-dimension foundation for graph classes.
- X147: needs c-fat minor and quasi-isometry foundations.
- X148: needs the exact Bollobas two-family hypotheses and the
  Ahlswede-Khachatrian bound.
- X150: needs fixed-surface embeddability plus a polynomial-time computation model.

## Verification

All affected area packages compiled axiom-free under the `~/.opam/digraph` switch:
chromatic, minor, spectral, homomorphism, digraph, hypergraph, topological,
extremal, and graph-theory-misc. `make audit` / milestone gates are recorded in
the session transcript for this batch.

## 2026-07-16 Retarget Addendum

- X132 moved from `blocked` to `done` after `GTBase.list_flexibility` was
  promoted.
- The retargeted statement uses concrete weighted request/list-flexibility:
  arbitrary finite palettes, list assignments, natural request weights, proper
  list-colourings, and a rational `p/q` satisfied-weight inequality.
- The original planar, triangle-free, girth-at-least-five, and list-size
  `5/4/3` cases are preserved.
