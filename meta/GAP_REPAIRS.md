# Repairs and formal proof scope for nine MINOR_GAPS records

Date: 2026-09-05.

This round audited nine informal writeups against their primary sources and the available Rocq definitions. It produced a complete finite theorem about frozen graph colorings and a checked certificate for a six-cycle precoloring. The other repairs remain mathematical notes with explicit dependencies. A checked supporting lemma does not establish the full source conjecture.

The frozen-coloring result is

\[
(n+4)F\leq 4P,
\]

where `F` counts actual frozen proper colorings and `P` counts actual proper colorings of a connected noncomplete finite simple graph on `n` vertices. The generic theorem allows any finite palette at least as large as every closed neighborhood; the usual palette has `Delta+1` colors. The six-cycle result proves the source's exact definition of viability for one specified boundary precoloring, under either choice of its two hue labels.

Neither result, by itself, supplies a full formal proof of a Glauber-dynamics statement or of the arbitrary-parameter planar counterexample. They are checked as repair artifacts with their own scopes; this round does not turn all nine source records into formal resolutions.

| Record | Repair or correction | Formal result from this round |
| --- | --- | --- |
| `1802.05582__00` | Include equality in the maximum-average-degree bound and specify the LOCAL execution. | Written repair; distributed algorithms remain unformalized. |
| `1802.05582__01` | Handle complete components and make the block-tree growth and radius bounds explicit. | Written repair; the existing `X205` does not faithfully model the source. |
| `1811.12650__00` | Separate the finite count from the component-connectivity consequence, which needs `Delta>=3`. | Complete finite count and equivalence between frozen and isolated proper colorings. |
| `2001.09679__00` | Use the source's supremum definition. The referee's exact-size padding objection is inapplicable. | Written repair; the construction and asymptotic theory remain unformalized. |
| `2005.09767__00` | Handle orders two and three and extract an explicit common exponential constant. | Written repair conditional on the stated counting bounds and existence results. |
| `2106.14762__00` | Justify empirical convergence by rank coupling and truncated-window estimates. | Written probabilistic repair; no permuton formalization. |
| `2211.01032__02` | Correct an off-by-one denominator and state the finite thresholds. | Written repair; `X140` does not encode the required random embeddings. |
| `2312.13061__01` | Replace the unsupported weak-dual interpretation by an actual map to the paper's grid. | Exact viability certificate for the specified six-cycle. |
| `2505.24100__01` | Supply the two small cases outside the cited theorem's range. | Written repair and a concrete future construction route; no complete Rocq proof. |

## The frozen-coloring theorem and its limits

For a proper coloring, being frozen means that every color occurs in every closed neighborhood `N[v]`. The source's discussion of a unique nonfrozen recoloring component requires `Delta>=3`. That restriction belongs to the component theorem, not to the finite counting inequality. Connectedness and the exclusion of complete graphs remain essential. [Source, introduction](https://arxiv.org/html/1811.12650).

The formal proof uses finite functions from the library's actual graph vertices to a finite palette. Under the neighborhood-size bound, a frozen coloring is injective on each closed neighborhood. Exchanging the colors at the ends of an edge preserves properness. The result is nonfrozen exactly when the endpoints have different closed neighborhoods.

Every vertex of a connected noncomplete graph has a neighbor with a different closed neighborhood. Otherwise its closed neighborhood would be a complete connected component. Choose one such neighbor for each vertex, and switch each frozen coloring along the chosen edge. The domain contains exactly `n*F` pairs of a frozen coloring and a selected vertex; every output is a nonfrozen proper coloring.

Each output has at most four preimages. Fix a nonfrozen vertex of that output. An inverse switch has one endpoint inside its closed neighborhood and one outside. The inside endpoint is one of two vertices carrying the duplicated color. Its partner is recovered uniquely from the missing color and local injectivity. One further bit records which endpoint was the selected vertex. This gives an injection into `bool * bool`.

Thus `n*F <= 4*(P-F)`. Partitioning proper colorings into frozen and nonfrozen ones gives the displayed theorem. The proof takes no switching or multiplicity theorem as an unproved assumption. It also gives the finite quantitative consequence `k*F <= P` whenever `4*k <= n`.

The public generic results are `fc_frozen_count_bound` and `fc_frozen_count_quantitative`. The source-facing module [frozen_coloring_resolution.v](../chromatic-theory/theories/applications/gap_repairs/frozen_coloring_resolution.v) specializes the palette to the ordinals below `Delta(G)+1`, using the repository's actual `GTBase.base.Delta`. A constructive greedy-coloring proof establishes `fc_delta_proper_positive`, so the denominator in the probabilistic reading is positive. `fc_delta_frozen_count_bound` proves this positivity together with the exact count inequality, and `fc_delta_frozen_count_quantitative` proves the finite `k*F <= P` consequence. `fc_delta_isolated_count_bound` gives the same bound when the numerator counts proper colorings isolated under one-vertex recoloring.

The separate theorem `fc_frozen_isolated_iff` proves that a proper coloring is frozen exactly when it is isolated under actual one-vertex recoloring. It requires no degree bound.

A formal asymptotic or dynamic application still needs the relevant measure and convergence statements. For `Delta>=3`, the Feghali–Johnson–Paulusma component theorem would identify all nonfrozen proper colorings with one component. Markov-chain results would then be needed to state and prove the stationary or limiting distribution claim. Those external results are not imported as axioms here. A small frozen fraction gives no mixing-time estimate. Degree-two cycles show why the component assertion cannot be inferred without its additional hypothesis.

## `1802.05582__00`: equality and the LOCAL execution

The source task concerns `d`-list-coloring or finding a `(d+1)`-clique, for `d >= max(3,mad(G))`. Here `mad(G)` is the maximum average degree over subgraphs. The task is more precise than the catalog's degeneracy paraphrase. The source works in the synchronous LOCAL model with unique identifiers, known graph order, unrestricted messages, and free local computation. [Theorem 1.3 and the model description](https://arxiv.org/pdf/1802.05582).

At strict inequality, degeneracy gives the list-colorability promise. At equality, use the source's list version of Brooks' theorem when there is no `(d+1)`-clique. This covers the full parameter range.

For the distributed wrapper, let `H` consist of vertices of degree at least `d`. A maximal packing with mutual distances at least three has disjoint closed neighborhoods, each of size at least `d+1`. Its size is at most `n/(d+1)`. Assigning nearby vertices to packing centers gives a weak diameter bound `5n/(d+1)+4` for a component of `H`. Distances are measured in the original graph, so the permitted messages may travel outside `H`.

Use a common flooding radius and a fixed ordering of identifiers and color encodings. Each component can then perform the same exhaustive list-coloring search. Failure gives a clique certificate by the preceding existence alternative. No global announcement that every component is clique-free is needed. Once `H` is colored, each remaining vertex has at least one more available list color than its remaining degree. The residual list-coloring routine and the component searches use fixed time budgets computed from known parameters.

Balancing `O(n/d + polylog n)` with the source's `O(d^4 log^3 n)` bound yields `O(n^(4/5) log^(3/5) n + polylog n)`. This repairs the written reduction and execution details. A faithful formal proof still needs the LOCAL computation model, list-colorability theorem, and distributed subroutines.

## `1802.05582__01`: complete components and block-tree growth

The source includes list-coloring infeasibility and assumes `Delta>=3`. A `(Delta+1)`-clique in a graph of maximum degree `Delta` is an entire component. Gather that component and its lists, then choose the first proper list coloring by a shared exhaustive search or report infeasibility. Different lists can make such a component colorable, so it cannot simply be declared an obstruction. [Corollary 2.1 and its surrounding question](https://arxiv.org/pdf/1802.05582).

For the growth argument, choose `k=ceil(log_2(n+1))` and radius `R=2k+3`. Root the block-cut incidence tree at the center of the radius-`R` ball. A state consists of a vertex and its parent block. After removing complete components, the center has at least two branches. Every state can generate two descendant states within two additional graph steps: if only one child edge is available, it is a bridge, and its other endpoint has at least two remaining child edges. The block incidence tree keeps distinct descendant regions disjoint.

Generation `j` therefore has `2^j` distinct vertices at distance at most `2j-1`. Constructing generation `k` uses full-degree information only inside radius `2k-2`, strictly before the ball boundary. It would contain more than `n` vertices, giving the required contradiction. Fixed subroutine budgets and stronger per-subroutine error bounds make the union bound over layers explicit. The remaining argument still invokes degree choosability and a randomized MIS theorem.

The current `X205` is unsuitable for a source-level resolution. It puts lists of size `Delta+1` inside a palette with only `Delta+1` colors; its algorithm record imposes no locality requirement, and its round parameter does not constrain the result. A proof of that definition would not establish the requested distributed algorithm. Repair the model before registering such a proof.

## `2001.09679__00`: the exponent definition, with no padding gap

The primary source defines its separator profile using graphs with **at most** `n` vertices. The attack uses that same convention. The referee's objection based on an exact-`n` convention therefore does not apply. The source also defines `b_epsilon` as a supremum of universally forced lower exponents; the attack instead describes an infimum over witness-class upper bounds. [Source definitions and Corollary 2](https://arxiv.org/html/2001.09679v2).

For `0<epsilon<1/2`, put `a=1/(2 epsilon)-1`. The paper's lower bound with exponent `a` and a polylogarithmic loss implies every strictly smaller exponent `b<a`. Hence the source supremum is at least `a`. A hereditary witness class with the required separator profile and expansion `O(r^a)` excludes every universally forced exponent above `a`. Hence the supremum is at most `a`. This reasoning does not assert that the endpoint is attained in the defining set.

For the proposed block construction, choose graph orders with bounded consecutive ratios. Lower bounds at those orders extend to all orders by monotonicity of the source profile. No isolated-vertex padding is required. The construction still needs its grid-boundary and port estimates, expander existence, planar separators, surface estimates for minors, and shallow-minor localization. The target has no matching statement or sufficient asymptotic infrastructure. These dependencies remain explicit.

## `2005.09767__00`: small graphs and one exponential constant

The source's counting theorem uses base `(k-6)/2` for odd group order `k` and `(k-4)/2` for even order. For `k>=8`, the smallest base is `3/2`, attained at `k=9`; using base `2` uniformly would be incorrect. [Theorem 1.9 and Conjecture 1.10](https://arxiv.org/html/2005.09767).

Choose `c=(9/8)^(1/4)>1`. For graph order `n>=4`, minimum cut degree gives `m-n>=n/2`, so the quoted theorem gives

\[
N\geq \tfrac12(3/2)^{n/2}\geq c^n.
\]

For `n=2,3`, a 3-edge-connected multigraph has a parallel pair of nonloop edges. Starting from an avoiding flow, vary it by a circulation supported on that pair. At most two group parameters make an edge forbidden; the shifts are distinct. Thus `N>=k-2>=6>c^n`. Loops contribute no cut degree and do not invalidate this argument.

The same constant fits the attack's bounds for group orders six and seven because `c^12<3` and `c^4<7`. This completes the constant extraction conditional on those bounds. A full formal theorem still needs the external avoiding-flow existence theorem, the source's counting theorem, finite-field circulation dimensions, the polynomial support bound, and the Eulerian orientation lift. Also specify the one-vertex convention: a vacuously 3-edge-connected edgeless graph would defeat a `c^n` lower bound with `c>1`.

## `2106.14762__00`: a direct probabilistic explanation

The source already gives the runsort limit explicitly. Its open remark asks for a direct explanation of the density's independence from the horizontal coordinate. This is a request about proof method, rather than an unknown property of the displayed density. [The introductory remark on page 2](https://arxiv.org/pdf/2106.14762).

A detailed repair of the attack's convergence step uses ranks of independent continuous uniform variables. Ranking preserves every comparison and hence the starter chosen in a truncated run. The empirical distribution function converges uniformly in probability by a finite grid, Chebyshev's inequality at each grid point, and monotonicity between grid points. Uniform continuity then controls the effect of replacing uniform values by scaled ranks.

For a fixed window length `K+1`, disjoint windows are independent. If the test function has absolute value at most `B`, the variance of the average is at most `(2K+1)B^2/n`, and the left-boundary error is at most `2BK/n`. A truncation can fail only when `K+1` consecutive values are increasing, an event of probability `1/(K+1)!`. First let `n` grow at fixed `K`, then let `K` grow. This justifies the empirical convergence that the attack had sketched.

Its local density factors as `(1-z)exp(y-z)=r(z)exp(y-1)`, where `r(z)=(1-z)exp(1-z)`. Changing the first coordinate by its marginal distribution function explains horizontal uniformity before explicitly evaluating that function. Measure-theoretic pushforwards and the approximation of runsort positions still need full proofs. No finite-permutation bijection is claimed, and no probability or permuton theorem has been formalized in this round.

## `2211.01032__02`: random faces and a denominator correction

A faithful formulation fixes a positive density constant first, then comparison constants and an order threshold, then quantifies over the relevant simple graphs. The probability distribution must be independent uniform cyclic orders at vertices, with explicit face conventions. [Conjecture 9.3](https://arxiv.org/html/2211.01032v3).

The corrected successor count is

\[
d_u-\lfloor\theta d_u\rfloor-1\geq(1-\theta)\delta-1.
\]

The operative probability bound `2/delta` follows when `theta<=1/4` and `delta>=4`. Delete the intermediate bound `1/((1-theta)delta)`, which loses the final subtraction. State the other thresholds: `theta*delta>=2`, `theta*delta^2>=200`, and `delta>=8*sqrt(n)` at the steps where they are used. With positive linear density and `theta=1/sqrt(log n)`, they eventually hold.

The real formal work remains conditioning on exposed cyclic permutations, adaptive face exploration, weighted cycle counting, and spectral estimates. The target's `foundations/embedding.v` provides genuine darts, vertex rotations, and face permutations. Its `X140` instead stores an arbitrary natural face count and chooses a finite drawing family existentially. Those fields do not express uniform rotations or face orbits, so `X140` must not be used to claim this source result.

## `2312.13061__01`: the exact viability repair

The source defines viability by a map into an integer triangular grid that preserves edges, hues, and colors. A signed balance equation on a weak dual is not this definition unless an equivalence is proved. [Section 2 and Conjecture 4](https://arxiv.org/html/2312.13061v1).

The checked domain is an actual six-vertex cycle. Its boundary color sequence `(1,2,3,4,3,2)` is represented by the four parity pairs, and its hues alternate. The target grid permits steps `±(1,0)`, `±(0,1)`, and `±(1,1)`; its hue is `(x+y) mod 3`, and its color is `(x mod 2,y mod 2)`. The formal witness is

\[
(0,0),(0,1),(1,2),(1,3),(1,2),(0,1).
\]

In [viable_boundary.v](../chromatic-theory/theories/applications/gap_repairs/viable_boundary.v), theorems `six_cycle_precoloring_viable` and `six_cycle_precoloring_viable_swapped` prove preservation of every edge and both labels, including the opposite bipartition labeling. Their assumptions are closed.

The full refutation must still construct the proposed family for every separation parameter at boundary length six and prove its plane embedding, independent apex set, bipartite deletion, even internal degrees, selected faces, distances, and nonseparation by short walks. The source constrains the selected faces and permits the extra long face used by the example. The certificate establishes no strengthened version requiring all other bounded faces to be quadrilaterals, and it is not a formal negation of Conjecture 4.

## `2505.24100__01`: repair the small cases and choose a construction

The cited Theorem 1.6 starts at `t>=5`. Observation 1.5 in the same source supplies the missing cases: the 12-vertex icosahedron for `t=3` and the 25-vertex Cartesian product of two five-cycles for `t=4`. Their required properties still need finite certificates. [Theorem 1.6 and Observation 1.5](https://arxiv.org/html/2505.24100v2).

The target already has a precise statement, `Extremal.conjectures.X60.induced_saturation_even_cycle_polynomial_size_statement`, using actual edge deletion and induced cycles. Its documented interpretation replaces the source's undefined `H` by `C_(2t-2)`.

The attack's general construction uses the line graph of a cubic hypohamiltonian graph. A complete proof needs the line-graph cycle correspondence and an all-order existence theorem; citing the [hypohamiltonian spectrum paper](https://arxiv.org/pdf/1608.07164) is not a Rocq proof of that dependency.

A concrete alternative is [Choi's explicit construction](https://arxiv.org/html/2608.24202), posted on 2026-08-25. It uses `8q` vertices for `q>=3`. Formalizing its induced-cycle exclusion and its two edge-deletion witness cases, with `q=t-2`, would cover `t>=5`. Adding the two checked small graphs would give the polynomial bound `f(t)=8t`. This is a future route, not a completed theorem. A proof using it must preserve that attribution and must not claim the informal attack's sharper `3t-3` bound.

## Reproduction and future registration

The repair modules use Rocq 9.1.1 from the `rocq-tools` switch, matching the existing library artifacts. Their deployment directory is `chromatic-theory/theories/applications/gap_repairs/`. Run `ROCQ_OPAM_SWITCH=rocq-tools make gap-repairs` to rebuild the listed sources, check explicit theorem types in a fresh probe, and inspect their assumptions. All nine source modules passed the native repair checker, with ten exact public theorem checks and closed assumptions; see the [assumption report](GAP_REPAIR_ASSUMPTIONS.txt). Both final modules and their transitive dependencies passed standalone `rocqchk` from the native package.

Any future source-resolution entry should name the exact complete theorem and all of its hypotheses. The frozen-count result can support a later dynamic development, and the viability certificate can support a later planar construction. Neither supplies the missing external theorem or arbitrary-parameter construction by itself. The inaccurate `X205` and `X140` representations need faithful replacements before they can serve as source-resolution targets.
