# Journal of the gap-repair round

## 2026-09-05 — preserve the current work and audit the claims

The round began from the isolated `graph-theory-rocq-next-proofs` worktree, preserving the six earlier formal resolutions and existing local changes. Baseline status, a patch, and the untracked-file list were saved before integration. Independent work used separate temporary staging directories; the parent agent retained control of target integration and the shared Rocq MCP session.

The nine MINOR_GAPS candidates were divided into three groups. Each group read the informal attack and verification report, then compared the claim with its primary paper and available Rocq definitions. The audit changed several interpretations before proof work began.

For the distributed-coloring candidates, equality in maximum average degree and complete components needed explicit handling. The LOCAL model also needed a real communication and round bound. The existing `X205` did not supply such a model. For frozen colorings, the finite counting argument survived the audit, but the later component-connectivity application needed `Delta>=3`.

For the separator candidate, primary-source inspection overturned the referee's padding objection: the paper already uses graphs with at most `n` vertices. The genuine repair was the bridge to its supremum definition of the exponent. For group flows, checking the odd-order branch revealed the correct uniform base `3/2`, leading to an explicit constant and a parallel-edge argument for graph orders two and three. For runsort, the proof gap was repaired with rank coupling, finite-grid empirical-distribution control, independent-window variance, and factorial truncation bounds.

For random faces, an off-by-one successor count and unstated finite thresholds needed correction; `X140` did not model the actual probability space. For planar precoloring, the weak-dual condition attributed to the paper was replaced by the paper's exact grid-map definition of viability. For deletion-induced cycles, the cited general theorem missed two small parameters, and the eventual construction depended on an external existence theorem.

These findings are recorded with primary-source links in the [repair audit](GAP_REPAIRS.md). Written repairs remain distinct from formal completions.

## 2026-09-05 — select concrete formal work

The team selected the complete finite counting inequality from `1811.12650__00` as the main theorem. It concerns actual finite graph colorings and could be proved with the existing GraphTheory and MathComp foundations. The separate record `1811.12650__01`, about a stronger logarithmic improvement, was not substituted for this claim.

The second formal task was the exact six-cycle viability step from `2312.13061__01`. It has a finite domain and an explicit integer-grid witness. The much larger arbitrary-parameter planar construction remained outside this certificate's scope.

The other seven candidates were retained as audited repair notes. No missing expander, flow, probability, distributed-algorithm, or hypohamiltonian theorem was introduced as an axiom to make a source claim appear complete.

## 2026-09-05 — build the frozen-coloring proof

The shared definitions use GraphTheory's finite simple graphs, actual adjacency and closed neighborhoods, finite-function colorings, and finite sets of proper and frozen colorings.

The local proof established that frozen colorings are injective on each closed neighborhood under the palette-size bound. Swapping colors on an edge preserves properness. The exact criterion for remaining frozen at a vertex is whether its closed neighborhood contains both swapped endpoints or neither. A separate module proved that the closed-neighborhood definition of frozen agrees with isolation under a proper one-vertex recoloring step.

The graph argument showed that every vertex of a connected noncomplete graph has a neighbor with a different closed neighborhood. Its contrapositive propagates equality of neighborhoods through the connected graph and forces a clique.

The multiplicity proof initially isolated generic facts about a missing color and the duplicated pair after a swap. It then normalized every inverse swap at a fixed nonfrozen vertex of the output. There are at most two possible inside endpoints. Local injectivity recovers the outside endpoint; a Boolean flag recovers the chosen root; swap involutivity recovers the original coloring. Encoding the preimage by two Booleans gives the bound four.

The final counting module partitions the actual domain of frozen-coloring/vertex pairs by their output coloring. Summing fibers of size at most four gives `n*F <= 4*(P-F)`, and the exact partition of proper colorings gives `(n+4)*F <= 4*P`. It also derives the finite quantitative consequence `k*F <= P` when `4*k <= n`.

The generic proof and its dependencies compiled successfully. Assumption readback reported `Closed under the global context`. Independent agents read the local, multiplicity, and global counting arguments for their mathematical meaning as well as their types. `rocqchk` checked the global counting module and its transitive dependencies. The final specialization uses the repository's actual maximum degree and the ordinal palette of `Delta+1` colors. A constructive greedy proof supplies a proper coloring, establishing positive proper-coloring count. The result is also transferred to the equivalent count of proper colorings isolated under one-vertex recoloring. The three source-facing bound theorems compiled and reported closed assumptions.

## 2026-09-05 — prove the viability certificate

The grid was implemented on integer pairs with all six permitted directed steps. Hue is the sum of coordinates modulo three, and color is the pair of coordinate parities. The domain is an actual six-vertex cycle with cyclic adjacency.

The explicit lift is `(0,0),(0,1),(1,2),(1,3),(1,2),(0,1)`. Finite proofs check every edge, hue, and color. An early tactic attempt used propositional automation after reduction; Boolean equality contradictions required `intuition congruence`. This was a proof-script adjustment, not a change in the mathematical witness.

The transformation `(x,y) -> (2-x,2-y)` supplies the opposite bipartition labeling while preserving parity colors. Both public viability theorems compile and have closed assumptions. The certificate proves the exact missing viability step. It proves none of the later embedding, distance, parity-of-degree, or short-walk-separation obligations of the full planar counterexample.

## 2026-09-05 — check scopes and prepare integration

The proposed repair checker uses a fixed list of source files, rebuilds them, compiles fresh explicit type checks, and inspects the assumptions of the public results. It passed on a clean temporary package containing the actual proof sources. Mutation tests exercised the checker against malformed or stale proof artifacts.

The deployment location is `chromatic-theory/theories/applications/gap_repairs/`. These artifacts have their own check and documentation. They do not change the nine source records into nine formal resolutions or provide faithfulness exemptions for `X205` or `X140`.

The consolidated report preserves the distinction among a complete finite theorem, a complete supporting certificate, and written mathematical repairs with remaining formal dependencies. The initial eight modules compiled in the native package during integration, and `make audit` passed. The previous six formal resolutions were then rebuilt and checked with their exact types and closed assumptions. The four source/journal hashes saved from the previous round were unchanged, as were the source manifest, resolution registry, and status reports.

The shared `rocq-evolve` MCP session was used for the graph-neighborhood and greedy-coloring arguments. The greedy proof was built by induction on a vertex list: bound the image of already colored neighbors strictly below the palette size, choose a missing color, update one vertex, and check the four endpoint cases. Native compilation was the final authority after interactive proof development. Separate staging namespaces needed distinct physical load paths; deployment under the common package namespace removed that temporary build issue.

## 2026-09-05 — final native verification

The integrated checker rebuilt all nine proof files and accepted ten exact theorem types with closed assumptions. The saved [assumption report](GAP_REPAIR_ASSUMPTIONS.txt) contains its fresh probe output. The invocation was `ROCQ_OPAM_SWITCH=rocq-tools python3 meta/check_gap_repairs.py --report meta/GAP_REPAIR_ASSUMPTIONS.txt`; the regular entry point is `ROCQ_OPAM_SWITCH=rocq-tools make gap-repairs`, which is also called by the full gate.

The standalone kernel checker accepted both `Chromatic.applications.gap_repairs.frozen_coloring_resolution` and `Chromatic.applications.gap_repairs.viable_boundary`, including their transitive dependencies, from the native package. `ROCQ_OPAM_SWITCH=rocq-tools make resolutions` accepted the six earlier complete resolutions, and `make audit` accepted the unchanged corpus metadata. The full corpus-wide `make gate` was not run in this round.

The checker was also exercised in isolated copies: an admitted source with an older timestamp than its compiled object was rejected, as was a closed theorem of the wrong type. The final source filter rejects admission, axiom, parameter, and conjecture declarations while allowing generalized section hypotheses. None of the deployed repair sources contains an admission or an axiom declaration.

The final files are in `graph-theory-rocq-next-proofs`, on branch `codex/formal-resolutions-next`, following the user's committed previous-round work at `3145717`. This round adds the nine proof modules, the checker, its assumption report, this journal, and the repair audit, with build and README entries. It leaves the six-entry resolution registry and source statuses unchanged. No commit or push was made in this round.
