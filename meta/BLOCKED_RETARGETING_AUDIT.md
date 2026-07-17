# Blocked-retargeting faithfulness audit (2026-07-17)

Independent adversarial audit of the **72 rows** the 2026-07-16 pass (`meta/BLOCKED_RETARGETING_FOUNDATIONS.md`) unblocked (`blocked -> done`) by retargeting each formerly-blocked conjecture to a finite witness surface. Method: 4 foundation-fidelity readers + one adversarial second reader per row (machine-refuting suspects), workflow `wf_63f4702e`.

## Verdict

**48 DEFECT, 5 PROXY, 17 FAITHFUL** (+ X90 spot-checked faithful). The pass's `0 blocked / 377 v2-done` headline was FALSE: ~63% of the unblocked rows are weaker-than-conjecture, trivially-true, mis-quantified, or **provably false**. Restored to an honest state (legs-only reclassification, retargeted `.v` files kept but honestly re-labelled):

- **v2: 330 done - 9 partial - 39 blocked** (was 377/1/0).
- **OPG: 208 done - 12 partial - 7 blocked** (was 215/12/0). All 7 OPG rows re-blocked.

## Foundation fidelity

- `GTBase.finite_graph`: all primitives FAITHFUL, incl. a genuine `fg_whp` (ratio->1). BUT `fg_event_at_least_ratio` is a single-space constant-ratio threshold, NOT a whp notion -- the misuse vector for the **X125 collapse** (`forall family, exists good, ratio>=9/10 /\ good subset P` collapses to 'ALL objects satisfy P').
- `GTBase.surface`: `surface_embedding` (rotation system) FAITHFUL; but `clustered_chromatic_at_most` and `surface_embeddable_with_boundary` are **machine-confirmed vacuous**, and **crossing number is not modelled at all** (surface != crossing) -- `D3D6_unblocked.v` misuses `surface_*` for it.
- `GTBase.complexity`: cost-coupled `prog`/`pcost` core FAITHFUL (X90/X166/X208 good); the GTMisc **D7 `in_NP`/`NP_hard` layer is decoupled/lightweight** (satisfiable by `fun _ => 0`).
- `GTBase.graph_metric`/`asymptotics`: FAITHFUL, but contain **no** asymptotic-dimension / shallow-minor / bounded-expansion primitive -- coarse-geometry rows assemble ad-hoc (weakening risk).

## Per-row verdicts

| row | verdict | new leg | biggest defect |
|---|---|---|---|
| X124 | DEFECT | blocked | Biggest risk: the "bounded merge-width" ANTECEDENT is a trivially-satisfiable witness surface that does zero restricting work, so the implication coll |
| X125 | DEFECT | blocked | Biggest faithfulness risk = the X125 quantifier-collapse (mis-quantified "almost all"), and it resolves against the row: x125_almost_all quantifies `f |
| X138 | DEFECT | blocked | Biggest faithfulness risk: the conclusion primitive `clustered_chromatic_at_most G 2 := exists c, clustered_colouring G 2 c` existentially binds the c |
| X139 | DEFECT | blocked | Biggest faithfulness risk: x139_scol_at_most drops the defining constraint of the STRONG colouring number. x139_strong_reach_set ord r v = [set u / gr |
| X140 | DEFECT | blocked | Biggest faithfulness risk: the "expected number of faces of a uniformly random orientable embedding" is encoded so that ALL of its content is free/pro |
| X143 | DEFECT | blocked | Biggest risk = trivially-satisfiable witness surface (X125-family mis-quantification, machine-confirmed). Source: Skokan-Thoma "A is forcing iff bipar |
| X148 | DEFECT | blocked | Biggest risk: the surface encodes the WRONG extremal object and is outright false, not the open conjecture. The source (Scott–Wilmer, verifying Gerbne |
| X155 | DEFECT | blocked | Biggest risk = the assembled dichotomy is provably FALSE, and it resolves against faithfulness: the statement is `forall C hereditary, (A1 /\ A2) \/ ( |
| X156 | DEFECT | blocked | Biggest faithfulness risk: the `f`-hypothesis `forall N, exists n, N<=n /\ N<=f n` encodes "f unbounded (limsup=∞)", NOT the conjecture's "f tends to  |
| X162 | DEFECT | blocked | Biggest faithfulness risk: the retargeted statement is TRIVIALLY TRUE and captures none of the WSK ergodicity conjecture — it holds for every finite g |
| X164 | DEFECT | blocked | Biggest faithfulness risk = a missing-precondition over-strengthening that makes the row provably FALSE (a witness-collapse cousin of X125). Source (a |
| X166 | DEFECT | blocked | see below |
| X167 | DEFECT | blocked | Biggest faithfulness risk = vacuous witness surface / trivially-true collapse, and it fully realizes. The conjecture (Aprile-Fiorini) is that the EXTE |
| X168 | DEFECT | blocked | Biggest faithfulness risk: the extension-complexity notion is not modelled at all, making the statement vacuous. `x168_spanning_tree_polytope_xc G fac |
| X169 | DEFECT | blocked | Biggest faithfulness risk: the decided predicate is not TS_k connectivity. x169_ts_step (X169.v:31-36) constrains only #/B/==k, b∉A, a--b, B==(A:\a):/ |
| X170 | DEFECT | blocked | Biggest faithfulness risk: the exceptional-set predicate is mis-encoded, making the statement FALSE (not merely a weaker proxy). Source Conjecture 5 e |
| X174 | DEFECT | partial | Biggest faithfulness risk: a nat-subtraction ordering bug, not a lightweight-surface or almost-all mis-quantification. The primitives are all faithful |
| X176 | DEFECT | blocked | Biggest risk = a double weakening that makes the surface miss the open conjecture entirely, so no faithful proxy survives. (1) MIS-QUANTIFIED EXTREMAL |
| X177 | DEFECT | blocked | Biggest faithfulness risk: the word "induced" — the crux of the entire Chudnovsky–Scott–Seymour "Induced subgraphs of graphs with large chromatic numb |
| X179 | DEFECT | blocked | Biggest faithfulness risk = mis-encoded k-strong-connectivity premise, and it does NOT resolve: x179_k_vertex_strongly_connected G k := (forall S, #/S |
| X180 | DEFECT | blocked | Biggest faithfulness risk (confirmed): mis-quantification + vacuous witness, same collapse family as the known-BROKEN X125 but on the "constant indepe |
| X181 | DEFECT | partial | Biggest faithfulness risk: the conjecture is an EQUALITY chi_c(G(n,1/2)) = (1/2+o(1))log2 n whp, but the encoding captures only the UPPER half. The wh |
| X183 | DEFECT | blocked | Biggest faithfulness risk = a fatal mis-quantification of list size that makes the retargeted Prop provably FALSE rather than the open conjecture. The |
| X184 | DEFECT | partial | Biggest faithfulness risk: the defining ANTISYMMETRY property is entirely absent, so the row does not encode the conjecture's object. `x184_z5_antisym |
| X185 | DEFECT | blocked | Biggest risk: WRONG TARGET OBJECT. Scott-Seymour Conj 1.8 ("every multigraph H is widespread") requires that bounded-omega, large-chi graphs contain a |
| X186 | DEFECT | blocked | Biggest faithfulness risk: the load-bearing "induced" qualifier of Conjecture 1.10 ("some INDUCED subgraph of G is a subdivision of J") is entirely ab |
| X188 | DEFECT | blocked | Biggest faithfulness risk: the interactive-sum-choice-number encoding does not model chi_ISC at all. The game's `x188_add_colour` (foundation-local, d |
| X189 | DEFECT | blocked | Biggest faithfulness risk: the conjecture's defining "spaghetti" hypothesis — for each vertex v, the bags containing v form a DIRECTED PATH from the r |
| X190 | DEFECT | blocked | Biggest risk = trivially-satisfiable witness surface (LIGHTWEIGHT/BROKEN 'thin system of overlays'), and it fully realizes: the conclusion x190_thin_s |
| X191 | DEFECT | blocked | Biggest faithfulness risk = FINITENESS COLLAPSE (foundation flag B) and it does NOT resolve. The conjecture's entire content is quantitative: the o(n^ |
| X194 | DEFECT | blocked | Biggest risk = clustering-constant mis-quantification (the flagged BROKEN clustered_chromatic_at_most-in-conclusion pattern, same family as X138/X125) |
| X195 | DEFECT | blocked | Biggest risk: the surface does not encode "k-nice" and is outright FALSE, so no weaker true statement survives. The paper's k-nice = the k-COLOUR Rams |
| X196 | DEFECT | blocked | Biggest risk = mis-quantification / lightweight-witness, and it fires on the load-bearing quantifier. The whole content of Conj 1.5 is that "k-nice" h |
| X197 | DEFECT | blocked | Biggest faithfulness risk: the top statement does NOT say capt3(G) > n. Foundation primitives: wagner_planar (base.v) = FAITHFUL planarity; the cops/r |
| X198 | DEFECT | blocked | Biggest risk = mis-quantification of the clustered/star coloring number col⋆: the paper (arXiv:1710.02727 lines 91-111) defines col⋆(G)≤t as "∃C≥1 suc |
| X199 | DEFECT | blocked | Biggest faithfulness risk = the statement is not merely a weakening but is provably FALSE, so it can never be `done`. Source (Dvořák 1710.03117) is ab |
| X202 | DEFECT | blocked | Biggest risk: the two-sided asymptotic c(g)=g^{1/2+o(1)} (upper AND lower, for both orientable c and nonorientable ec) is rendered as a ONE-SIDED, wro |
| X203 | DEFECT | blocked | Biggest faithfulness risk: the statement is trivially FALSE (refutable), so it cannot encode an open conjecture. In chromatic-theory/theories/conjectu |
| X205 | DEFECT | blocked | Biggest risk = the conjecture's ENTIRE subject (round complexity of a randomized DISTRIBUTED list-colouring algorithm, and whether it avoids the poly- |
| X207 | DEFECT | blocked | Biggest faithfulness risk = trivially-true (Foundation WATCH: nat-subtraction / mis-encoded density disjunction), and it resolves against the statemen |
| X210 | DEFECT | blocked | Biggest faithfulness risk = dropped positivity of the constants, and it resolves against the statement: the source needs "C, C' > 0" (context even not |
| are_different_notions_of_the_c | DEFECT | blocked | Biggest faithfulness risk: the pair-cr side of the equality is a fully decorative, trivially-satisfiable record, which collapses the statement into a  |
| characterizing_aleph_0_aleph_1 | DEFECT | blocked | Biggest risk: the top-level statement is a pure tautology, not the conjecture. Source asks the OPEN problem "Characterize the (aleph_0,aleph_1)-graphs |
| consecutive_non_orientable_emb | DEFECT | blocked | Biggest faithfulness risk: the embeddability primitive is a fake witness surface (surface.v foundation note: no non-orientable-embedding predicate exi |
| drawing_disconnected_graphs_on | DEFECT | blocked | Biggest faithfulness risk: the conclusion is a claim purely about `sd_component_image`, a FREE unconstrained relation `{set G}->nat->Prop` living in t |
| highly_arc_transitive_two_ende | DEFECT | blocked | Biggest faithfulness risk = the paper-local "tile" surface in D4_unblocked.v (the iDigraph/darc/darc_irr/highly_arc_transitive core in D4inf4.v is fai |
| obstacle_number_of_planar_grap | DEFECT | blocked | Biggest faithfulness risk: the "obstacle number" is not modelled at all — the entire visibility-vs-adjacency constraint is replaced by a tautology, so |
| three_colourability_of_arrange | DEFECT | ? | Biggest faithfulness risk (machine-confirmed): the great_circle_arrangement record is a vacuous witness surface. gca_graph is an ARBITRARY sgraph — no |
| X147 | PROXY | partial | Biggest faithfulness risk: the conclusion x147_quasi_isometric_to_H_minor_free (X147.v:22-32) is strictly weaker than a quasi-isometry, so it does not |
| X150 | PROXY | partial | Biggest risk: the "embeddable in a fixed surface" hypothesis is modelled by surface_embeddable surface G (= exists rotation system E, surface_euler_ge |
| X152 | PROXY | partial | Biggest faithfulness risk = the surface model, which is load-bearing here: the Class is `surface_embeddable surface G` (GTBase.surface, WATCH-flagged  |
| X154 | PROXY | partial | Biggest risk: could be trivially-true if the class had no χ>4 members (then Pconst(Dnat 1) decides it) — resolved NO: for positive genus the class con |
| X209 | PROXY | partial | Biggest risk = a minimality mis-quantification in the extremal-min helper: X209.v line 41 reads `forall (T' : finType) (E' : {set {set T}}) (y : nat), |
| X128 | FAITHFUL | done | Biggest faithfulness risk was a finiteness-collapse of the single-graph `x128_expansion_bounded G p` predicate (graph_metric family invariant); it RES |
| X132 | FAITHFUL | done | Biggest faithfulness risk was that the new GTBase.list_flexibility primitive (not in the phase-1 verdict list) might over- or under-strengthen the "(w |
| X145 | FAITHFUL | done | Biggest faithfulness risk was the foundation note's FINITENESS-COLLAPSE trap (asymptotic dimension over one finite sgraph is vacuously 0) — it resolve |
| X151 | FAITHFUL | done | Biggest faithfulness risk was the constant-ratio-as-asymptotic-proxy mode (fixed a/b gap looking like the X125 mis-quantification). It resolves: "not  |
| X157 | FAITHFUL | done | Biggest risk was trivial-satisfiability of the positive "exists polytime algorithm" claim, but it resolves cleanly: the surface is built on the COUPLE |
| X159 | FAITHFUL | done | Biggest faithfulness risk was that the retargeting note claims an "axiom-free finite witness formulation" — but the actual statement (planar_no_cycles |
| X161 | FAITHFUL | done | Biggest risk: the control primitive being a lightweight proxy for Scott–Seymour's "(2,φ)-controlled". It is NOT a proxy — it matches the paper verbati |
| X163 | FAITHFUL | done | Biggest faithfulness risk was the X125-style almost-all/whp mis-quantification collapse; it does NOT apply here. The "with high probability" is encode |
| X165 | FAITHFUL | done | Biggest faithfulness risk was that the 2026-07-16 "retargeting to a finite witness surface" had swapped the open conjecture for a proxy — but X165.v i |
| X171 | FAITHFUL | done | Biggest faithfulness risk is the modelling of "there is a finite set of graphs F0" as an order bound: `exists N, forall connected G, N < #/G/ -> (pend |
| X172 | FAITHFUL | done | Biggest risk: the reflexive constructor x172_generated_by_bridge_replacement G G plus an existential seed could trivialize the claim by picking seed = |
| X175 | FAITHFUL | done | Biggest faithfulness risk was a mis-quantified asymptotic (X125 collapse) or a fractional-exponent fudge; both resolve cleanly. The statement is foral |
| X182 | FAITHFUL | done | Biggest faithfulness risk = STRENGTH MISMATCH: the statement encodes the POLYNOMIAL height-bound (exists C d, dim <= C*(h+1)^d) while the source's hea |
| X192 | FAITHFUL | done | Biggest faithfulness risk was accidental trivial-truth via the complexity foundation (failure mode 1: trivial Class/Spec) plus a constant-output short |
| X200 | FAITHFUL | done | Biggest faithfulness risk is whether the retarget quietly weakened "planar H + O(k log k) Erdos-Posa" into a trivially-satisfiable finite surface; it  |
| X201 | FAITHFUL | done | Biggest faithfulness risk was the log-factor bound: f depends only on r, so it cannot fudge the k-dependence, meaning the k*log(k+1) shape must be exa |
| X208 | FAITHFUL | done | Biggest faithfulness risk was the complexity foundation's "trivial Class/Spec" collapse (a constant/cheap program satisfying polytime_outputs_graph_on |

Rows kept `done` (genuinely faithful use of the new foundations): X90, X128, X132, X145, X151, X157, X159, X161, X163, X165, X171, X172, X175, X182, X192, X200, X201, X208.

## Note

Reclassification is **legs-only**: the retargeted `.v` statements still compile axiom-free (gate-clean) but their statement legs are now `blocked`/`partial` with this audit as the record. A faithful re-encoding of the blocked rows remains future work; some ARE achievable on the real foundations (e.g. X125 via `fg_whp`, crossing rows need a genuine drawing/crossing layer).

