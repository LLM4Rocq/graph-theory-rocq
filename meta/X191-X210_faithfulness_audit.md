# X191-X210 Faithfulness Audit

Date: 2026-07-16

Scope: the next 20 package-assigned, not-yet-landed v2 arXiv rows after X190,
skipping parked/out-of-scope rows and rows already reconciled in earlier waves
(`axv_1706_05642_00` through `axv_1803_10962_00`).

## Outcome

- 20 statement files authored and wired: X191-X210.
- 2 faithful `done` rows: X193, X204.
- 18 honest `blocked` rows: X191, X192, X194-X203, X205-X210.
- No `partial` rows in this batch.

## Faithful Rows

- X193: Harutyunyan-Le-Newman-Thomasse Conjecture 3.5.  Encodes
  directed-triangle-free digraphs by excluding `dicycle` witnesses of size 3,
  uses arc-stable sets for the independence number, and defines domination by
  selected vertices plus in-neighbours.  The polynomial bound is represented by
  an existential exponent `ell`.
- X204: Dvorak-Hu suspicion that `11/3` is not optimal for planar graphs without
  4- or 5-cycles.  Encodes the natural proposition as a uniform rational
  fractional-chromatic bound `p/q < 11/3`, using X130's fractional-colouring
  predicate, `wagner_planar`, and explicit no-cycle-length predicates.

## Blocked Rows

- X191: needs the exact dense-host, `K_m(t)`-maximizing, `H`-free setup from
  Proposition 1.4 and real/asymptotic `O(n^(2-delta))`.
- X192: needs polynomial-time additive approximation over proper minor-closed
  classes.
- X194: needs clustered chromatic number for minor-closed classes and treedepth.
- X195/X196: need the paper-local Ramsey `k`-nice family definition.
- X197/X202: need cops-and-robbers game/capture-time and genus cop-number
  foundations.
- X198: needs `col*`, `K_{t,m}`, and `I_{t-1}+P_m` obstruction families.
- X199: needs polynomial omega-expansion, weighted balanced separators, and the
  constant-size `M` conclusion.
- X200/X201: need minor-model Erdos-Posa packing/hitting machinery, treewidth
  lower bounds, vertex-disjoint subgraphs, and logarithmic thresholds.
- X203: needs separation choosability.
- X205: needs randomized distributed LOCAL-model round complexity.
- X206: needs real-valued `c`, real exponents, and list-chromatic minima.
- X207: needs Rodl theorem density parameters and the Erdos-Hajnal implication.
- X208: needs induced `P_t`-freeness, maximum independent set, and a polytime
  decision/optimization layer.
- X209: needs hypergraph maximum `r`-cuts, excess, extremal minima, and
  `Theta(sqrt m)` asymptotics.
- X210: needs single-conflict colouring, conflict assignments, Euler genus, and
  square-root genus thresholds.

## Verification

The affected packages compiled axiom-free under the `~/.opam/digraph` switch:
chromatic, digraph, extremal, graph-theory-misc, minor, topological, and
hypergraph.  Corpus gates and per-milestone gates were run after metadata
regeneration.

## 2026-07-16 Retarget Addendum

- X206 moved from `blocked` to `done`.  The real parameter `c > 1` is encoded
  by positive rationals `a/b > 1`; `chi_l(G) <= Delta/c` is the
  cross-multiplied choice-number inequality `a*m <= b*Delta(G)` for
  `is_choice_number G m`; and `omega(G) <= Delta^(1/f(c))` is encoded as
  `omega(G)^q <= Delta(G)` for a positive integer denominator exponent
  `q = f a b`.  This removes the previous real-exponent/list-chromatic-minimum
  blocker without changing the source quantifier shape.
- X209 moved from `blocked` to `done` after the `GTBase.asymptotics`
  foundation was promoted.
- The retargeted statement defines the missing hypergraph content directly:
  `k`-uniform finite hypergraphs, `r`-cuts as non-monochromatic edges under a
  colouring into `'I_r`, maximum `r`-cut size, denominator-scaled excess over
  the random-cut baseline, and the minimum scaled excess over all `m`-edge
  `k`-graphs.
- The `Theta(sqrt m)` claim is now encoded as
  `big_Theta_nat (fun m => excess m ^ 2) (fun m => m)`, which is the finite
  nat-valued square-root envelope.  Scaling by `r^(k-1)` is harmless for fixed
  `r,k`.
- Faithfulness boundary: the row is faithful-to-refuted; the source paper
  later disproves this plausible conjecture outside the small tight cases.
