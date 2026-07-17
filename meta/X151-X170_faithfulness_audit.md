# X151-X170 Faithfulness Audit

Date: 2026-07-15

Scope: the next 20 statement-owning v2 rows after X150, now in the arXiv slice
(`axv_0806_0178_00` through `axv_1605_07411_02`).

## Outcome

- 20 statement files authored and wired: X151-X170.
- 3 faithful `done` rows: X153, X158, X160.
- 17 honest `blocked` rows: X151, X152, X154-X157, X159, X161-X170.
- No `partial` rows in this batch.

## Faithful Rows

- X153: Conjecture 1.7 from arXiv:1302.2158.  Encodes the planar girth-5
  two-precoloured-short-cycles list-colouring obstruction with a bounded induced
  subgraph witness.  The source says "subgraph"; an induced subgraph on the same
  vertices is no loss for non-colourability because adding edges cannot create a
  colouring.
- X158: bounded queue number of planar graphs.  Defines q-queue layouts directly
  by a vertex order plus q edge queues with no nested edge pair in one queue;
  planarity uses the corpus `wagner_planar` facade.
- X160: density-zero constricting set.  Reuses X3's constricting-set vocabulary
  and adds a rational-epsilon asymptotic density-zero condition over decidable
  initial-segment counts.

## Blocked Rows

- X151: needs random graph `G(n,p)`, probability, chromatic-number distribution,
  and concentration interval foundations.
- X152/X154: need fixed-surface embeddability plus a polynomial-time
  4-colourability decision model.
- X155: needs identifying-code size, VC-dimension dichotomy, log-APX hardness,
  and approximation-algorithm foundations.
- X156: needs random block-stable graph classes, `R_n`, block trees `BT(R_n)`,
  and asymptotic probability bounds.
- X157: needs the true local-connectivity invariant (internally disjoint paths)
  and a computation model for deciding/finding k-colourings.
- X159: needs correspondence/DP-colouring assignments.
- X161: depends on paper-local `(2,phi)`-controlled graphs and internal Statement
  2.1.
- X162: needs periodic triangular-lattice graph families and Kempe-chain/WSK
  connectivity of q-colourings.
- X163: needs the intended graph-normality definition plus a `G(n,p)`/whp layer.
- X164: needs fixed-surface embeddings with precoloured boundary vertices and a
  linear-time output algorithm model.
- X165: needs Szeged-Wiener difference `eta(G)` and the exceptional families
  `K_n^2`, `K_n^{n-2}`.
- X166: needs digraph stability number, the directed k vertex-disjoint paths
  decision problem, and a shared complexity foundation.
- X167/X168: need spanning-tree polytopes and real/polyhedral extension
  complexity; X167 also needs fixed-surface embeddings.
- X169: needs token-sliding reconfiguration graphs, chordal clique-tree degree,
  and polytime decision machinery.
- X170: needs the actual `Or(P4)` family, exceptional orientations
  `P+(3)`/`P+(1,1,1)`, and the forbidden-orientation class.

## Verification

All affected packages compiled axiom-free under the `~/.opam/digraph` switch:
chromatic, packing, topological, graph-theory-misc, and digraph.  The milestone
gate and corpus audit were run after metadata regeneration.

