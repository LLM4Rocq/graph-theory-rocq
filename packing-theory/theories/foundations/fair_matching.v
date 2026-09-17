(** * Packing.foundations.fair_matching — Conjecture 1.15 of arXiv:1611.03196

    This file proves [bipartite_matching_underrepresentation_llm_statement],
    [bipartite_matching_underrepresentation_llm2_statement] (the same with the
    sharper constant actually obtained) and [bipartite_matching_underrepresentation]
    of [Packing.conjectures.X15], i.e. Conjecture 1.15 of

      R. Aharoni, N. Alon, E. Berger, M. Chudnovsky, D. Kotlar, M. Loebl,
      R. Ziv, "Fair representation by independent sets", arXiv:1611.03196,

    with the explicit constant [c(m) <= 32(m+1)^3] claimed by the LLM attack the
    statement refers to:

      for every [m] there is a [c(m) <= 32(m+1)^3] such that, for every
      bipartite graph [G] with [Delta G > 0] and any sets of edges
      [E_1, ..., E_m], there is a matching [S] of [G] with

        |S| >= |E(G)| / Delta G - c(m)    and    |S :&: E_i| <= ceil(|E_i| / Delta G).

    The two halves are easy separately and hard together: a maximum matching
    gives the first (this is [x15_big_matching], König's theorem), and the empty
    matching gives the second.  The point is one matching doing both.

    ** THE PROOF, IN ENGLISH

    Throughout, [D := Delta G] is the maximum degree, and the *statistics* of a
    matching [M] are the [m+1] numbers [|M|], [|M :&: E_1|], ..., [|M :&: E_m|]
    ([zstat] below).  The theorem asks for a matching whose statistics are close
    to the averages [|E(G)|/D, |E_1|/D, ..., |E_m|/D]: at least the first of
    them, at most each of the others.

    *** Step 1 — the edges are [D] matchings.

    [G] is bipartite, so by König's line-colouring theorem ([chi' = Delta]) its
    edges can be coloured with [D] colours in such a way that each colour class
    is a matching:
    [ClassicalLemmas.konig.line_colouring.line_colouring_E].  Call the classes
    [M_1, ..., M_D] ([cls] below).  Every edge gets exactly one colour
    ([cls_uniq]), so every one of the [m+1] statistics is additive over the
    classes ([cls_partition]).  In other words the vector of averages that the
    theorem is aiming at is *exactly the average of the [D] statistic vectors*
    of [M_1, ..., M_D].  If matchings could be averaged, we would be done.

    *** Step 2 — only [m+2] of them are needed.

    Carathéodory's theorem in dimension [m+1]: an average of [D] points of
    [Q^(m+1)] is a convex combination of at most [m+2] of them.  Formalized as
    [ClassicalLemmas.caratheodory.caratheodory.caratheodory_nat], in the form
    with the denominators cleared: there are natural weights [a_j], at most
    [m+2] of them nonzero, with
    [(sum_j a_j z(M_j)) * D = (sum_j z(M_j)) * (sum_j a_j)] in every coordinate.
    So it is enough to be able to average *few* matchings with *prescribed*
    weights.

    *** Step 3 — averaging two matchings, by splitting a necklace.

    This is where the topology enters.  Given matchings [A] and [B], one wants a
    matching [C] contained in [A :|: B] whose statistics are the averages of
    those of [A] and of [B].  Exactly that is impossible; what is proved
    ([matching_halving], below) is

      |A| + |B| <= 2|C| + (16m+28)   and   2|C :&: E_i| <= |A :&: E_i| + |B :&: E_i| + (8m+16),

    i.e. the average up to an additive [O(m)] that does not depend on [G].
    That construction, and the mixing of step 4, are the only parts of the
    argument that are not classical lemmas; they are the two sections "Step 3"
    and "Step 4" below.

    The construction: in the symmetric difference [A △ B] every vertex meets at
    most one edge of [A] and at most one edge of [B], so the relation "these two
    edges share a vertex" has degree at most two — the classical fact that the
    union of two matchings is a union of paths and even cycles.  Because [G] is
    bipartite that relation can be *oriented*: it becomes a partial injection
    [nxt] ([ClassicalLemmas.konig.paths2]), whose orbits linearise [A △ B] into
    blocks in which consecutive edges are exactly the meeting ones.

    Choosing [C] means choosing, for each edge of that linear order, whether to
    keep it.  Make a necklace of it: each edge contributes [m+1] beads, one per
    statistic, and the *type* of a bead records both which of [A], [B] the edge
    belongs to and which statistic it serves — [2(m+1)] types in all.  Alon's
    Splitting Necklace Theorem for two thieves
    ([ClassicalLemmas.necklace.necklace.splitting_necklace_seq] at [q = 2])
    hands each of two thieves *exactly half* of every type, using at most
    [2(m+1)] cuts.  Give each edge to the thief of its first bead and keep the
    edges of [A] belonging to thief 0 and the edges of [B] belonging to thief 1:
    every statistic is then halved on the nose.

    What can go wrong is that two kept edges share a vertex.  Such a pair is
    consecutive in a block and has two different thieves, so it sits at one of
    the [<= 2(m+1)] cuts, or at the wrap-around of a block that is not
    monochromatic — of which there are as many as cuts again.  Hence [O(m)]
    conflicts; deleting one edge per conflict restores a matching, changes every
    statistic by [O(m)] only, and changes it *downwards*, which is the harmless
    direction for the [m] upper bounds.

    *** Step 4 — from halving to arbitrary weights.

    The write-up being followed would now invoke a *prescribed-ratio* splitting
    theorem.  We only have the equal-share one, so an arbitrary weight is
    reached by a *chain of halvings along a binary expansion*: with
    [y_(L+1) := B] and [y_j := (P_j + y_(j+1))/2], where [P_j] is [A] or [B]
    according to the [j]-th bit of the desired ratio, [y_1] is the desired
    mixture of [A] and [B] up to [2^(-L)].  The error of a halving is the
    *average* of the errors of its two inputs plus a constant, so along such a
    chain it obeys [e <= e/2 + c] and never exceeds [2c], however many bits are
    used.  That is what keeps the final constant independent of the denominators
    coming out of step 2.  All of this is done with every quantity scaled by the
    common denominator, so that only natural numbers occur
    ([realisesN], below); the [<= m+2] matchings of step 2 are then mixed in
    one at a time ([mix_dyadic], then [mix_list]).

    *** Step 5 — trimming, and the constant.

    Feeding the colour classes selected in step 2 to [mix_list] and undoing the
    scaling gives [approx_fair_core]: a matching [C] with

      |E(G)|/D <= |C| + Bmix m   and   |C :&: E_i| <= |E_i|/D + Bmix m,
      where [Bmix m = (m+1)(16m+29)],

    which is [x15_approx_fair m (Bmix m)] ([x15_approx_fair_proof]).  The upper
    bounds are still off by [Bmix m] and the conjecture wants them exact, so
    edges are deleted from [C], one at a time, out of the classes that exceed
    their ceiling ([trim_exists]).  Each deletion costs one unit of size and
    removes one unit of excess, and the total excess is at most [m * Bmix m], so
    the size bound degrades from [Bmix m] to [(m+1) * Bmix m]
    ([x15_approx_fair_instance]).  As [Bmix m <= 32(m+1)^2] ([Bmix_le]), the
    constant obtained is

      c(m) = (m+1) * Bmix m = (m+1)^2 (16m+29) <= 32(m+1)^3,

    which is [x15_llm_proof].  The trimming step is stated for an arbitrary
    error as [x15_trim_instance], so the constant can also be read off exactly
    rather than through [32(m+1)^3]: that sharper reading is [x15_llm2_proof],
    with [c(m) = (m+1)^2 (16m+29)] — a factor [m+1] below the attack's claim.
    Forgetting the bound on [c] altogether gives Conjecture 1.15 itself,
    [bipartite_matching_underrepresentation].

    The case [m = 0] needs none of this: a maximum matching does it
    ([x15_approx_fair0], [x15_llm_instance0]).

    ** POSSIBLE FUTURE IMPROVEMENTS: c(m) from Theta(m^3) down to Theta(m log m)

    The constant [c(m) = (m+1)^2 (16m+29)] is a product of three factors [m],
    two of which the argument above does not really need.

      (a) the per-class error of one halving is [Theta(m)]: it is the term
          [4 * cuts_seq a] of [Chalf_stat], coming from
          [Dc], the number of edges whose class-[l] bead was given
          to a different thief from their head bead — and the thief of the edge
          is that of its head bead ([thj]).  [Dc_cuts] only bounds
          it by the number of cuts, [cuts_seq a <= 2m+3];
      (b) the [<= m+2] matchings of step 2 are mixed in a linear chain, so
          [mix_list] accumulates [(size s).-1 = Theta(m)] halving errors;
      (c) trimming turns a per-class error [B_class] into a size loss
          [m * B_class] ([x15_trim_instance]).

    *** (a) is spurious: delete the edges that straddle a cut.

    Each edge owns a *contiguous* block of [m+1] beads of the necklace
    ([beadty], blocks of constant size [m.+1]), so an edge can
    disagree with itself only if a cut falls strictly inside its own block;
    blocks of distinct edges are disjoint, hence at most [cuts_seq a] edges are
    not unanimous.  Deleting them — exactly as the conflicting edges
    [Psrc] are already deleted — costs at most [cuts_seq a] more
    in *size*, where [Theta(cuts_seq a)] is being paid anyway
    ([Chalf_size] is [4 + 8 * cuts_seq a]); in exchange every kept
    edge is unanimous, so each class count is its exact fair half up to the
    padding of the type counts, and the error of [Chalf_stat] drops from
    [4 + 4 * cuts_seq a = 8m + 16] to the constant [4].  [matching_halving]
    would then read

      |A| + |B| <= 2|C| + (20m + 34)   and   2|C :&: W i| <= |A :&: W i| + |B :&: W i| + 4.

    To exploit that asymmetry, [realisesN] has to carry two error budgets
    (one for the size, one for the classes) instead of one, and
    [x15_trim_instance] to be read with those two: [B_size = (m+1)(20m+35)],
    [B_class = 5(m+1)], hence

      c(m) = B_size + m * B_class = (m+1)(25m+35) = Theta(m^2),

    against [Theta(m^3)] today — for a change localized to the selection and to
    the three counting lemmas [Chalf_stat], [Chalf_size], [SelC_le] of step 3,
    plus a mechanical two-budget refactor of step 4.

    *** (b) is reducible to Theta(log m): mix along a balanced tree.

    [mix_dyadic] gives [e <= max (e_A) (e_B) + eh], so mixing the
    [k <= m+2] matchings as a *balanced binary tree* (splitting the list in
    halves) instead of folding them one at a time costs [ceil(log2 k) * (eh+1)]
    in place of [(k-1) * (eh+1)].  Together with (a) this gives
    [B_size = O(m log m)], [B_class = O(log m)], hence [c(m) = O(m log m)].

    *** Theta(m log m) is the floor for this technique.

    One halving must lose [Theta(m)] in size: splitting [m+1] statistics exactly
    needs [Omega(m)] cuts, and at a cut the selected edge of [A] and the selected
    edge of [B] may share a vertex, forcing a deletion.  And iterated halving of
    [k] matchings costs the sum, over the internal nodes of the mixing tree, of
    the weight of the subtree below — that sum is an expected code length, hence
    at least the entropy of the weight distribution, i.e. [Omega(log k)] for
    uniform weights (Huffman).  So no arrangement of halvings goes below
    [Omega(m log m)].

    Reaching [Theta(m)] — the [c(m) = m/2] that [AABCKLZ16] suggests — needs a
    different argument.  The natural discrepancy route does not work either:
    every edge lies in at most [m] of the classes, so Beck-Fiala would give
    discrepancy below [m], but its proof relaxes constraints once they hold few
    floating variables, and the vertex constraints of a matching cannot be
    relaxed at all.  That is presumably why Conjecture 1.15 is still open.

    ** CONTENTS

    Vocabulary and elementary facts:
    - [x15_edge_setE], [matching_x15], [x15_matching_sub] : the local X15
      vocabulary of [X15.v] is the coq-graph-theory vocabulary ([E(G)],
      [matching]), so the library's König/Hall infrastructure applies verbatim;
    - [edges_leq_cover] : a vertex cover [V] bounds [#|E(G)| <= #|V| * Delta G];
    - [x15_big_matching] : a bipartite [G] with [Delta G > 0] has a matching of
      size at least [#|E(G)| %/ Delta G] (König min-cover = max-matching);
    - [x15_small_instance] : instances with [#|E(G)| %/ Delta G <= c] are
      settled by [S = set0].

    The reduction (step 5 and the bookkeeping of the constant):
    - [trim_exists] : per-class ceilings can be enforced by deletions, at a cost
      equal to the total excess;
    - [x15_trim_instance] : hence a [B]-approximately fair matching yields an
      exactly fair one, of size within [(m+1)*B] of the target;
    - [x15_approx_fair] : the additive-error form of the conjecture;
    - [x15_approx_fair_instance], [x15_approx_fair_llm] : [x15_approx_fair] with
      error [32(m+1)^2] implies the [32(m+1)^3] statement of X15;
    - [x15_approx_fair0], [x15_llm_instance0] : the case [m = 0].

    Step 3, halving two matchings along the necklace of their symmetric
    difference:
    - [cuts_seq_flatten], [conflict_count], [cyc_le] : counting the cuts along
      the blocks of [ClassicalLemmas.konig.paths2];
    - [beadty], [cs], [cs_even] : the necklace, one bead per (edge, statistic);
    - [thj], [sel], [Csel], [Psrc], [Chalf] : the selection, and the deletion of
      the conflicting edges;
    - [Chalf_matching], [Chalf_stat], [Chalf_size] : what it is worth;
    - [matching_halving] : the halving lemma.

    Step 4, interpolating several matchings:
    - [realisesN], [eh] : the scaled error bookkeeping;
    - [mix_half], [mix_dyadic] : one halving, and the chain of halvings that
      realises an arbitrary dyadic ratio at no extra cost;
    - [mix_list] : the convex combination of a list of matchings.

    The approximate fair matching (steps 1 to 4):
    - [cls], [cls_uniq], [cls_partition] : the colour classes of a line
      colouring and their additivity;
    - [zstat], [sum_zstat] : the statistics, and their averages;
    - [approx_fair_core] : the matching produced by Carathéodory + mixing;
    - [Bmix], [Bmix_le] : the constant;
    - [x15_approx_fair_proof] : [x15_approx_fair m (Bmix m)].

    The conjecture:
    - [x15_llm_proof] : [bipartite_matching_underrepresentation_llm_statement],
      with the constant [32(m+1)^3] claimed by the attack;
    - [x15_llm2_proof] : [bipartite_matching_underrepresentation_llm2_statement],
      the same with the constant actually obtained, [(m+1)^2 (16m+29)];
    - [bipartite_matching_underrepresentation] : Conjecture 1.15.

    ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    models Claude Opus 5 and (for the first sections) Claude Opus 4.8, between
    11 and 16 September 2026.  Rocq was driven interactively.  The
    rocq-mcp-evolve MCP server of the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools), is used throughout this
    repository for that purpose and is gratefully acknowledged; for the last
    sections its cached project configuration predated the move of
    classical-lemmas into subdirectories, so goals were read instead from a
    small [rocq repl] harness and files recompiled with [rocq c].  Every error
    that recurred, together with the tactic that fixed it, is recorded in
    tactics-playbook.md at the root of the repository.  Nothing is admitted:
    [Print Assumptions] on the results of this file answers "Closed under the
    global context".

    ESTIMATED TOKEN COST FOR THIS FILE.  About 1.69M tokens, of which 670k
    output: 703k (224k) for the vocabulary, the König bound and the reduction,
    11-14 September; 464k (222k) for step 3, 345k (166k) for step 4 and 174k
    (58k) for the assembly, 15-16 September.  Not counted here: the
    classical-lemmas files this one rests on, about 0.3M tokens for
    konig/paths2.v and konig/line_colouring.v, 0.16M for caratheodory/ and 3.9M
    for necklace/.  Method: as in ClassicalLemmas.necklace.necklace — for every
    assistant message of the Claude Code session, input + cache-creation +
    output tokens (the tokens processed anew, excluding the cached conversation
    that is re-read at each turn), charged to the file the message's tool calls
    were acting on.

    SOURCES.

      [AABCKLZ16]  R. Aharoni, N. Alon, E. Berger, M. Chudnovsky, D. Kotlar,
             M. Loebl, R. Ziv, "Fair representation by independent sets",
             arXiv:1611.03196.  Conjecture 1.15 is the target; it is stated in
             packing-theory/theories/conjectures/X15.v.

      [A87]  N. Alon, "Splitting necklaces", Advances in Mathematics 63 (1987)
             247-253, formalized in this repository as
             [ClassicalLemmas.necklace.necklace.splitting_necklace_seq]
             (through Meunier's simplotopal Tucker lemma); used at [q = 2] in
             step 3.

      [LLM]  The proof sketch attacked here,
             https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md
             (five steps: line colouring, Carathéodory, interpolation of two
             matchings, iterated interpolation, trimming), referenced from the
             comment on [bipartite_matching_underrepresentation_llm_statement]
             in X15.v.

      DEVIATION FROM [LLM].  Step 3 of [LLM] invokes a *prescribed-ratio*
      continuous splitting theorem (its Lemma 1, Hobby-Rice style): for any
      ratio theta, a union of O(r) intervals carrying exactly a theta-share of
      r measures.  That statement does not follow from the equal-share
      Splitting Necklace Theorem with a number of cuts independent of theta:
      reading theta = a/q off a q-splitting costs t(q-1) cuts, so the error
      would grow with the denominator.  Here every interpolation is instead a
      halving (theta = 1/2), which is exactly
      [necklace.splitting_necklace_seq] at [q = 2], and an arbitrary ratio is
      realised by a chain of halvings along the binary expansion of a dyadic
      approximation, as described in step 4 above.  The result is the same
      theorem with a better constant.

    WHAT CORRESPONDS TO WHAT.

      - the vocabulary of [AABCKLZ16] Conj. 1.15 versus that of
        coq-graph-theory  -> [x15_edge_setE], [matching_x15],
                             [x15_matching_sub]
      - [LLM] step 1, König line colouring, instantiated at the colour classes
                          -> [cls], [cls_uniq], [cls_partition]
      - [LLM] step 2, Carathéodory, instantiated at the statistics
                          -> [zstat], [sum_zstat]
      - [LLM] step 3, the interpolation of two matchings, from [A87] at [q = 2]
                          -> [beadty], [cs_even], [thj], [sel], [Chalf],
                             [Chalf_stat], [Chalf_size], [matching_halving]
      - [LLM] step 4, the iterated interpolation, by chains of halvings along
        binary expansions rather than by the prescribed-ratio Lemma 1
                          -> [realisesN], [eh], [mix_half], [mix_dyadic],
                             [mix_list]
      - the mixing of the colour classes, and the passage from the scaled error
        bound back to the averages |E(G)|/D and |E_i|/D
                          -> [approx_fair_core], [Bmix]
      - bookkeeping with no counterpart in [LLM]: the cut counting needed to
        pass between the flat necklace, the blocks of
        [ClassicalLemmas.konig.paths2] and the edge sets
                          -> [cuts_seq_cat], [cuts_seq_flatten],
                             [cuts_seq_subseq], [conflict_count], [Dc_cuts]
      - [LLM] step 5, trimming, and the final assembly
                          -> [trim_exists], [x15_trim_instance],
                             [x15_approx_fair_instance],
                             [x15_approx_fair_proof], [x15_llm_proof],
                             [x15_llm2_proof],
                             [bipartite_matching_underrepresentation]
      - the constant: one halving costs 8m+14 (scaled: [eh] = 16m+28), a chain
        costs at most twice that, and at most m+1 chains are needed, so
        [Bmix m] = (m+1)(16m+29) <= 32(m+1)^2 and c(m) = (m+1)[Bmix m] =
        (m+1)^2(16m+29) <= 32(m+1)^3, the constant claimed by [LLM] and stated
        in X15.v                  -> [Bmix_le], [x15_llm2_proof]
      - with no counterpart in [LLM]: [edges_leq_cover], [x15_big_matching]
        (the case m = 0, and the sanity check that the size bound alone is
        König's theorem), [x15_small_instance] *)

From GTBase Require Export base.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From Packing Require Import X15.
From Stdlib Require Import Lia.
From ClassicalLemmas Require Import necklace.necklace konig.paths2
                                    konig.line_colouring
                                    caratheodory.caratheodory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Bridging the X15 vocabulary with coq-graph-theory *********************)

Lemma x15_edge_setE (G : sgraph) : x15_edge_set G = E(G).
Proof.
apply/setP => e; apply/idP/idP.
- rewrite in_set => /existsP [x /existsP [y /andP [xy /eqP ->]]].
  by rewrite in_edges.
- case/edgesP => x [y [-> xy]]; rewrite in_set.
  by apply/existsP; exists x; apply/existsP; exists y; rewrite xy eqxx.
Qed.

Lemma matching_x15 (G : sgraph) (M : {set {set G}}) :
  matching M -> x15_matching M.
Proof.
case=> M1 M2; split.
  by apply/subsetP => e /M1; rewrite x15_edge_setE.
move=> v; apply/card_le1_eqP => e1 e2.
rewrite !inE => /andP [e1M ve1] /andP [e2M ve2].
exact: (M2 _ _ e2M e1M v ve2 ve1).
Qed.

Lemma x15_matching_sub (G : sgraph) (M M' : {set {set G}}) :
  M' \subset M -> x15_matching M -> x15_matching M'.
Proof.
move=> sub [H1 H2]; split; first exact: subset_trans sub H1.
move=> v; apply: leq_trans (H2 v); apply: subset_leq_card.
by apply/subsetP => e; rewrite !inE => /andP [eM ve]; rewrite (subsetP sub) ?ve.
Qed.

(** ** A vertex cover bounds the number of edges ****************************)

Lemma leq_card_bigcup (I T : finType) (P : pred I) (F : I -> {set T}) :
  #|\bigcup_(i | P i) F i| <= \sum_(i | P i) #|F i|.
Proof.
elim/big_rec2: _ => [|i n U _ leUn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU (F i) U).1) ?leq_add2l.
Qed.

Lemma set2C (T : finType) (x y : T) : [set x; y] = [set y; x].
Proof. by apply/setP => z; rewrite !inE orbC. Qed.

Lemma edges_leq_cover (G : sgraph) (V : {set G}) :
  vcover V -> #|E(G)| <= #|V| * Delta G.
Proof.
move=> covV.
move/(vcoverP V): (covV) => covP.
have sub : E(G) \subset \bigcup_(v in V) [set [set v; y] | y in N(v)].
  apply/subsetP => e /edgesP [x [y [-> xy]]].
  case: (covP _ _ xy) => [xV|yV]; apply/bigcupP.
  - by exists x => //; apply/imsetP; exists y => //; rewrite in_opn.
  - exists y => //; apply/imsetP; exists x; first by rewrite in_opn sgP.
    by rewrite set2C.
apply: leq_trans (subset_leq_card sub) _.
apply: leq_trans (leq_card_bigcup _ _) _.
rewrite -[X in _ <= X]sum_nat_const.
apply: leq_sum => v _.
apply: leq_trans (leq_imset_card _ _) _.
exact: leq_bigmax.
Qed.

(** ** König: a matching of size at least ⌊|E(G)|/Δ(G)⌋ *********************)

Theorem x15_big_matching (G : sgraph) :
  bipartite G -> 0 < Delta G ->
  exists M : {set {set G}},
    x15_matching M /\ #|x15_edge_set G| %/ Delta G <= #|M|.
Proof.
move=> [f fP] dpos.
have bipA : bipartition [set x : G | f x].
  move=> x y xy; rewrite !inE; move: (fP _ _ xy).
  by case: (f x) (f y) => [] [].
have covT : @vcover G setT by apply/vcoverP => x y _; left; rewrite inE.
have smV := @argmin_smallest _ (@vcover G) setT covT.
set V := [arg min_(B < setT | vcover B) #|B|] in smV.
have [M mM defM] := min_vcover_matching bipA smV.
exists M; split; first exact: matching_x15.
rewrite x15_edge_setE -defM -(mulnK #|V| dpos).
by apply: leq_div2r; apply: edges_leq_cover; case: smV.
Qed.

(** ** Enforcing per-class ceilings by deletion *****************************)

Section Trim.
Variables (T : finType) (m : nat) (E : 'I_m -> {set T}) (q : 'I_m -> nat).

Definition trim_excess (C : {set T}) := \sum_(i < m) (#|C :&: E i| - q i).

Lemma trim_exists (C : {set T}) :
  exists C' : {set T},
    [/\ C' \subset C,
        forall i : 'I_m, #|C' :&: E i| <= q i &
        #|C| <= #|C'| + trim_excess C].
Proof.
have key (a b : nat) : b < a -> (a.-1 - b).+1 <= a - b.
  by case: a => // a; rewrite ltnS => hb; rewrite subSn.
have [n] := ubnP (trim_excess C); elim: n C => [C|n IH C]; first by rewrite ltn0.
rewrite ltnS => leC.
have [allok|] := boolP [forall i : 'I_m, #|C :&: E i| <= q i].
  by exists C; split; [exact: subxx | exact: (forallP allok) | exact: leq_addr].
rewrite negb_forall => /existsP [i]; rewrite -ltnNge => hi.
have /card_gt0P [e emem] : 0 < #|C :&: E i| by apply: leq_ltn_trans hi.
have eC : e \in C by move: emem; rewrite inE => /andP [].
have cardD (j : 'I_m) : (C :\ e) :&: E j = (C :&: E j) :\ e.
  by rewrite setIC setIDA setIC.
have cardi : #|(C :\ e) :&: E i| = (#|C :&: E i|).-1.
  by rewrite cardD (cardsD1 e (C :&: E i)) emem.
have dec : trim_excess (C :\ e) < trim_excess C.
  rewrite /trim_excess (bigD1 i) //= [X in _ < X](bigD1 i) //= -addSn.
  apply: leq_add; first by rewrite cardi; exact: key.
  apply: leq_sum => j _; apply: leq_sub2r; apply: subset_leq_card.
  by rewrite cardD; exact: subD1set.
have [C' [sub' ok' big']] := IH (C :\ e) (leq_trans dec leC).
exists C'; split.
- exact: subset_trans sub' (subD1set _ _).
- exact: ok'.
- have step : #|C :\ e| + 1 <= #|C'| + trim_excess (C :\ e) + 1.
    by rewrite leq_add2r.
  rewrite (cardsD1 e C) eC add1n -addn1.
  apply: leq_trans step _.
  by rewrite -addnA addn1 leq_add2l.
Qed.

End Trim.

(** ** The X15 statement, instance by instance ******************************)

Definition x15_llm_instance (m : nat) : Prop :=
  exists c : nat,
    c <= 32 * (m + 1)^3 /\
    forall (G : sgraph) (E : 'I_m -> {set {set G}}),
      bipartite G ->
      0 < Delta G ->
      x15_edge_family E ->
      exists S : {set {set G}},
        x15_matching S /\
        (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
        forall i : 'I_m,
          #|S :&: E i| <= ceil_div #|E i| (Delta G).

Lemma x15_llm_instanceE :
  (forall m : nat, x15_llm_instance m) <->
  bipartite_matching_underrepresentation_llm_statement.
Proof. by []. Qed.

(** The additive-error form: a matching within [B] of the target size whose
    class intersections exceed their ceilings by at most [B].  This is exactly
    (3)+(4) of the LLM write-up, i.e. what the necklace-splitting/Carathéodory
    interpolation argument is supposed to deliver. *)
Definition x15_approx_fair (m B : nat) : Prop :=
  forall (G : sgraph) (E : 'I_m -> {set {set G}}),
    bipartite G ->
    0 < Delta G ->
    x15_edge_family E ->
    exists C : {set {set G}},
      x15_matching C /\
      (#|x15_edge_set G| %/ Delta G <= #|C| + B)%N /\
      forall i : 'I_m, #|C :&: E i| <= ceil_div #|E i| (Delta G) + B.

(** Step 5 of the LLM proof, for an arbitrary additive error [B]: a matching
    that is [B]-approximately fair yields an *exactly* fair one, of size still
    within [(m+1)*B] of the target.  One deletion removes one unit of excess and
    costs one unit of size, and the total excess is at most [m*B]. *)
Theorem x15_trim_instance (m B : nat) (G : sgraph) (E : 'I_m -> {set {set G}}) :
  (exists C : {set {set G}},
     x15_matching C /\
     (#|x15_edge_set G| %/ Delta G <= #|C| + B)%N /\
     forall i : 'I_m, #|C :&: E i| <= ceil_div #|E i| (Delta G) + B) ->
  exists S : {set {set G}},
    x15_matching S /\
    (#|x15_edge_set G| %/ Delta G <= #|S| + (m + 1) * B)%N /\
    forall i : 'I_m, #|S :&: E i| <= ceil_div #|E i| (Delta G).
Proof.
move=> [C [mC [sC fC]]].
have [S [subS okS bigS]] :=
  @trim_exists _ m E (fun i => ceil_div #|E i| (Delta G)) C.
exists S; split; first exact: x15_matching_sub subS mC.
split; last exact: okS.
have hexc : trim_excess E (fun i => ceil_div #|E i| (Delta G)) C <= m * B.
  rewrite /trim_excess (_ : m * B = \sum_(i < m) B); last first.
    by rewrite big_const_ord iter_addn_0 mulnC.
  by apply: leq_sum => i _; rewrite leq_subLR; apply: fC.
apply: leq_trans sC _.
rewrite mulnDl mul1n addnA leq_add2r.
exact: leq_trans bigS (leq_add (leqnn _) hexc).
Qed.

Theorem x15_approx_fair_instance (m : nat) :
  x15_approx_fair m (32 * (m + 1)^2) -> x15_llm_instance m.
Proof.
set B := 32 * (m + 1)^2 => hyp.
exists ((m + 1) * B); split.
  by rewrite /B mulnCA expnS.
move=> G E bipG dpos famE.
exact: x15_trim_instance (hyp G E bipG dpos famE).
Qed.

Corollary x15_approx_fair_llm :
  (forall m : nat, x15_approx_fair m (32 * (m + 1)^2)) ->
  bipartite_matching_underrepresentation_llm_statement.
Proof. by move=> H m; apply: x15_approx_fair_instance. Qed.

(** ** The unconditional case [m = 0] ***************************************)

Lemma x15_approx_fair0 (B : nat) : x15_approx_fair 0 B.
Proof.
move=> G E bipG dpos _.
have [M [mM sM]] := x15_big_matching bipG dpos.
exists M; split => //; split => [|i]; first exact: leq_trans sM (leq_addr _ _).
by have := ltn_ord i; rewrite ltn0.
Qed.

(** Small instances are trivial: the empty matching already works as soon as
    the target [#|E(G)| %/ Δ(G)] is below the additive allowance [c].  Hence any
    attack on the general case may assume the instance is large. *)
Lemma x15_small_instance (G : sgraph) (m : nat)
    (E : 'I_m -> {set {set G}}) (c : nat) :
  #|x15_edge_set G| %/ Delta G <= c ->
  exists S : {set {set G}},
    x15_matching S /\
    (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
    forall i : 'I_m, #|S :&: E i| <= ceil_div #|E i| (Delta G).
Proof.
move=> hc; exists set0; split; last split.
- split; first exact: sub0set.
  move=> v; apply: leq_trans (leq0n 1).
  rewrite leqn0 cards_eq0; apply/eqP; apply/setP => e.
  by rewrite !inE /=.
- by rewrite cards0.
- by move=> i; rewrite set0I cards0.
Qed.

Theorem x15_llm_instance0 : x15_llm_instance 0.
Proof. exact/x15_approx_fair_instance/x15_approx_fair0. Qed.


(** * Step 3: halving two matchings with the Splitting Necklace Theorem ******)

(** Everything up to [matching_halving] is independent of the X15 vocabulary:
    it is the interpolation of two matchings of a bipartite graph, through the
    necklace of their symmetric difference.  See step 3 of the header. *)

(** ** Counting changes in a sequence *)

Lemma bool_tri (Q : eqType) (y w z : Q) : (y != z) <= (y != w) + (w != z).
Proof.
case hyw : (y == w); first by rewrite (eqP hyw) /= add0n.
case hwz : (w == z); first by rewrite -(eqP hwz) /=; case: (y == w).
by rewrite /=; case: (y == z).
Qed.

Lemma cuts_seq_cons_le (Q : eqType) (y w : Q) (s : seq Q) :
  cuts_seq (y :: s) <= cuts_seq (y :: w :: s).
Proof.
case: s => [|z s]; first by rewrite cuts_seq_cons2 /=.
rewrite !cuts_seq_cons2 [X in _ <= X]addnA leq_add2r.
exact: bool_tri.
Qed.

Lemma cuts_seq_sub (Q : eqType) (s2 s1 : seq Q) :
  subseq s1 s2 -> forall y : Q, cuts_seq (y :: s1) <= cuts_seq (y :: s2).
Proof.
elim: s2 s1 => [|w s2 IH] s1.
  by move/eqP => -> y.
case: s1 => [_ y|x s1]; first by rewrite /cuts_seq /=.
rewrite [subseq _ _]/=; case: eqP => [hxw hs y|hne hs y].
  by rewrite hxw !cuts_seq_cons2 leq_add2l; apply: IH.
by apply: (leq_trans (IH _ hs y)); exact: cuts_seq_cons_le.
Qed.

Lemma cuts_seq_subseq (Q : eqType) (s1 s2 : seq Q) :
  subseq s1 s2 -> cuts_seq s1 <= cuts_seq s2.
Proof.
case: s1 => [|x s1] //.
elim: s2 => [|y s2 IH] //.
rewrite [subseq _ _]/=; case: eqP => [hxy hs|hne hs].
  by rewrite hxy; apply: cuts_seq_sub.
by apply: (leq_trans (IH hs)); exact: leq_cuts_seq_behead.
Qed.

Lemma cuts_seq_cat (Q : eqType) (s t : seq Q) :
  cuts_seq s + cuts_seq t <= cuts_seq (s ++ t).
Proof.
elim: s => [|x s IH]; first by rewrite /cuts_seq /= add0n.
case: s IH => [_|y s IH].
  have -> : cuts_seq [:: x] = 0 by [].
  by rewrite add0n cat_cons cat0s; exact: (leq_cuts_seq_behead (x :: t)).
by rewrite cat_cons !cuts_seq_cons2 -addnA leq_add2l.
Qed.

Lemma cuts_seq_flatten (Q : eqType) (ss : seq (seq Q)) :
  \sum_(s <- ss) cuts_seq s <= cuts_seq (flatten ss).
Proof.
elim: ss => [|s ss IH]; first by rewrite big_nil.
rewrite big_cons /=.
by apply: leq_trans (cuts_seq_cat s (flatten ss)); rewrite leq_add2l.
Qed.

(** ** Cyclic versus linear changes along a block *)

Lemma const_iota (Q : eqType) (g : nat -> Q) (n : nat) :
  count (fun k => (k.+1 < n) && (g k != g k.+1)) (iota 0 n) = 0 ->
  forall j, j < n -> g j = g 0.
Proof.
move=> h0 j; elim: j => [//|j IH hj].
have hj' : j < n by apply: ltn_trans hj.
have hnh : ~~ has (fun k => (k.+1 < n) && (g k != g k.+1)) (iota 0 n).
  by rewrite has_count h0 ltnn.
move: (hasPn hnh j); rewrite mem_iota /= add0n hj' => /(_ isT).
rewrite negb_and hj /= negbK => /eqP h.
by rewrite -h IH.
Qed.

Lemma cyc_le (Q : eqType) (g : nat -> Q) (n : nat) : 0 < n ->
  count (fun k => g k != g (k.+1 %% n)) (iota 0 n)
    <= 2 * count (fun k => (k.+1 < n) && (g k != g k.+1)) (iota 0 n).
Proof.
move=> hn.
have hsplit : iota 0 n = iota 0 n.-1 ++ [:: n.-1].
  by rewrite -{1}(prednK hn) -addn1 iotaD /= add0n.
set Pl := (fun k => (k.+1 < n) && (g k != g k.+1)).
set Pc := (fun k => g k != g (k.+1 %% n)).
have hlin : count Pl (iota 0 n) = count Pl (iota 0 n.-1).
  by rewrite hsplit count_cat /Pl /= (prednK hn) ltnn /= add0n addn0.
have hcyc : count Pc (iota 0 n) = count Pl (iota 0 n.-1) + (g n.-1 != g 0).
  rewrite hsplit count_cat; congr (_ + _).
    apply: eq_in_count => k; rewrite mem_iota /= add0n => hk.
    have hk1 : k.+1 < n by rewrite -(prednK hn) ltnS.
    by rewrite /Pc /Pl modn_small // hk1.
  by rewrite /= /Pc (prednK hn) modnn addn0.
rewrite hlin hcyc.
case: (boolP (g n.-1 != g 0)) => [hne|hne]; last by rewrite /= addn0 leq_pmull.
have h1 : 1 <= count Pl (iota 0 n.-1).
  rewrite lt0n; apply/eqP => h0.
  have hc0 : count Pl (iota 0 n) = 0 by rewrite hlin h0.
  have hlt : n.-1 < n by rewrite ltn_predL.
  by move: hne; rewrite (const_iota hc0 hlt) eqxx.
by rewrite mul2n -addnn leq_add2l.
Qed.

Lemma cuts_seq_map_nth (T Q : eqType) (x0 : T) (th : T -> Q) (b : seq T) :
  cuts_seq (map th b)
  = count (fun k => (k.+1 < size b) && (th (nth x0 b k) != th (nth x0 b k.+1)))
          (iota 0 (size b)).
Proof.
rewrite (cuts_seq_nth (th x0)) size_map.
apply: eq_in_count => k; rewrite mem_iota /= add0n => hk.
case: (ltnP k.+1 (size b)) => hk1 //=.
by rewrite !(nth_map x0).
Qed.

(** ** Conflicts of a selection sit at the cuts *)

Section Conflicts.
Variables (G : sgraph) (f : G -> bool) (A B : {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis mA : matching A.
Hypothesis mB : matching B.

Lemma conflict_count (th : {set G} -> bool) (P : pred {set G}) :
  (forall e, P e -> [/\ e \in SS A B, nxt f A B e != set0 &
                        th e != th (nxt f A B e)]) ->
  count P (bl f A B) <= 2 * cuts_seq (map th (bl f A B)).
Proof.
move=> hP.
have hblock (b : seq {set G}) : b \in blocks f A B ->
    count P b <= 2 * cuts_seq (map th b).
  move=> hb.
  have hn : 0 < size b by exact: (block_size hb).
  have hbe : b = [seq nth set0 b j | j <- iota 0 (size b)].
    by rewrite map_nth_iota0 // take_size.
  rewrite {1}hbe count_map.
  rewrite (@eq_in_count _ _ (fun k => (k < size b) && P (nth set0 b k))); last first.
    by move=> k; rewrite mem_iota /= add0n => ->.
  apply: (leq_trans (_ : _ <=
    count (fun k => th (nth set0 b k) != th (nth set0 b (k.+1 %% size b)))
          (iota 0 (size b)))).
    apply: sub_count => k /= /andP[hk hPk].
    have [hSS hn0 hth] := hP _ hPk.
    by rewrite -(block_nth bipf mA mB hb hk) (sigma_nxt hn0).
  apply: (leq_trans (cyc_le _ hn)).
  by rewrite leq_pmul2l // (cuts_seq_map_nth set0).
rewrite /bl count_flatten sumnE big_map.
apply: (leq_trans (_ : _ <= \sum_(b <- blocks f A B) (2 * cuts_seq (map th b)))).
  rewrite big_seq_cond [X in _ <= X]big_seq_cond.
  by apply: leq_sum => b /andP[hb _]; exact: hblock.
rewrite -big_distrr /= leq_pmul2l //.
rewrite map_flatten -(big_map (fun b => map th b) xpredT (fun s : seq bool => cuts_seq s)).
exact: cuts_seq_flatten.
Qed.

End Conflicts.

(** ** Counting over a sequence cut into blocks of constant size *)

Lemma count_iota_blocks (Q : pred nat) (N c : nat) :
  count Q (iota 0 (N * c)) = \sum_(j < N) count (fun l => Q (j * c + l)) (iota 0 c).
Proof.
elim: N => [|N IH]; first by rewrite mul0n big_ord0.
rewrite big_ord_recr /= -IH mulSn addnC iotaD count_cat; congr (_ + _).
by rewrite add0n -{1}(addn0 (N * c)) iotaDl count_map.
Qed.

Lemma count_iota_sum (Q : pred nat) (n : nat) :
  count Q (iota 0 n) = \sum_(j < n) (Q j : nat).
Proof.
rewrite -(big_mkord xpredT (fun j => (Q j : nat))) /index_iota subn0.
exact: sum_count.
Qed.

Lemma count_iota_split (Q : pred nat) (n p : nat) :
  count Q (iota 0 (n + p)) = count Q (iota 0 n) + count (fun i => Q (n + i)) (iota 0 p).
Proof.
rewrite iotaD count_cat; congr (_ + _).
by rewrite add0n -{1}(addn0 n) iotaDl count_map.
Qed.

(** Plain arithmetic, discharged by [lia] after translating [ssrnat] to the
    stdlib operations. *)

Lemma halving_arith_le (S Zt Zf Xf Xt K : nat) :
  S + Zt = Zf + Xt ->
  2 * Zf <= Xf + (1 + 2 * K) ->
  Xt <= 2 * Zt + (3 + 2 * K) ->
  2 * S <= Xf + Xt + (4 + 4 * K).
Proof.
move=> hid /leP h1 /leP h2; apply/leP.
by move: hid h1 h2; rewrite -!plusE -!multE => *; lia.
Qed.

Lemma halving_arith_ge (S Zt Zf Xf Xt K : nat) :
  S + Zt = Zf + Xt ->
  Xf <= 2 * Zf + (3 + 2 * K) ->
  2 * Zt <= Xt + (1 + 2 * K) ->
  Xf + Xt <= 2 * S + (4 + 4 * K).
Proof.
move=> hid /leP h1 /leP h2; apply/leP.
by move: hid h1 h2; rewrite -!plusE -!multE => *; lia.
Qed.

Lemma ZYD_arith (Z Y X D K : nat) :
  2 * Y <= X + 1 -> X <= 2 * Y + 3 -> Z <= Y + D -> Y <= Z + D -> D <= K ->
  (2 * Z <= X + (1 + 2 * K)) && (X <= 2 * Z + (3 + 2 * K)).
Proof.
move=> /leP h1 /leP h2 /leP h3 /leP h4 /leP h5; apply/andP.
move: h1 h2 h3 h4 h5; rewrite -!plusE -!multE => *.
by split; apply/leP; lia.
Qed.

Lemma count_split (T : eqType) (s : seq T) (P Q : pred T) :
  count P s = count (fun e => P e && Q e) s + count (fun e => P e && ~~ Q e) s.
Proof.
elim: s => [//|x s IH] /=; rewrite IH.
case: (P x) => /=; last by rewrite !add0n.
by case: (Q x) => /=; rewrite ?add0n ?addSn ?addnS.
Qed.

Lemma card_seq_count (T : finType) (s : seq T) (S : {set T}) (P : pred T) :
  uniq s -> (forall x, (x \in s) = (x \in S)) ->
  #|[set x in S | P x]| = count P s.
Proof.
move=> hu hs.
have -> : [set x in S | P x] = [set x in [seq y <- s | P y]].
  by apply/setP => x; rewrite !inE mem_filter hs andbC.
by rewrite cardsE -size_filter; apply/card_uniqP; apply: filter_uniq.
Qed.

Lemma count_nth_iota (T : eqType) (x0 : T) (s : seq T) (P : pred T) :
  count (fun i => P (nth x0 s i)) (iota 0 (size s)) = count P s.
Proof.
have he : s = [seq nth x0 s i | i <- iota 0 (size s)].
  by rewrite map_nth_iota0 // take_size.
by rewrite [in RHS]he count_map.
Qed.

Lemma diff_count (Q : eqType) (g : nat -> Q) (r : nat) :
  ((g 0 != g r) : nat) <= count (fun i => g i != g i.+1) (iota 0 r).
Proof.
case: (posnP (count (fun i => g i != g i.+1) (iota 0 r))) => [h0|]; last first.
  by move=> hgt; apply: leq_trans hgt; exact: leq_b1.
suff -> : g 0 = g r by rewrite eqxx.
have hcst : forall j, j <= r -> g j = g 0.
  elim=> [//|j IH hj].
  have hj' : j < r by [].
  have hnh : ~~ has (fun i => g i != g i.+1) (iota 0 r).
    by rewrite has_count h0.
  move: (hasPn hnh j); rewrite mem_iota /= add0n hj' => /(_ isT).
  by rewrite negbK => /eqP h; rewrite -h IH // ltnW.
by rewrite hcst.
Qed.

Lemma count_iota_le (Q : pred nat) (r1 r2 : nat) :
  r1 <= r2 -> count Q (iota 0 r1) <= count Q (iota 0 r2).
Proof.
move=> h12; rewrite -(subnKC h12) iotaD count_cat leq_addr //.
Qed.

Lemma sum_ord_count (T : eqType) (x0 : T) (s : seq T) (Q : pred T) :
  \sum_(j < size s) (Q (nth x0 s j) : nat) = count Q s.
Proof.
rewrite -(big_mkord xpredT (fun j => (Q (nth x0 s j) : nat))).
rewrite -(big_nth x0 xpredT (fun x => (Q x : nat))) /=.
by rewrite sum_count.
Qed.

(** ** Halving two matchings *)

Section Halving.
Variables (G : sgraph) (f : G -> bool) (A B : {set {set G}}) (m : nat).
Variable W : 'I_m -> {set {set G}}.
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis mA : matching A.
Hypothesis mB : matching B.

Local Notation es := (bl f A B).
Local Notation N := (size (bl f A B)).
Local Notation t := (#|{: bool * 'I_m.+1}|.+1).

(** The [m.+1] statistics: the total number of edges, and the [m] classes. *)
Definition wpred (l : 'I_m.+1) (e : {set G}) : bool :=
  if unlift ord0 l is Some k then e \in W k else true.

Local Notation TT := (bool * 'I_m.+1)%type.

Lemma card_TT : #|{: TT}| = 2 * m.+1.
Proof. by rewrite card_prod card_bool card_ord. Qed.

Definition tix (s : bool) (l : 'I_m.+1) : 'I_t :=
  widen_ord (leqnSn _) (enum_rank (s, l)).
Definition tnull : 'I_t := ord_max.

Lemma tixE (s s' : bool) (l l' : 'I_m.+1) :
  (tix s l == tix s' l') = (s == s') && (l == l').
Proof.
rewrite -xpair_eqE; apply/idP/idP.
  by move/eqP/(congr1 val) => /= /val_inj/enum_rank_inj ->.
by move/eqP => [-> ->].
Qed.

Lemma tix_null (s : bool) (l : 'I_m.+1) : (tix s l == tnull) = false.
Proof.
apply/negbTE/negP => /eqP/(congr1 val) /=.
by move/eqP; rewrite -[X in _ == X]/(#|{: TT}|) ltn_eqF // ltn_ord.
Qed.

Definition sd (e : {set G}) : bool := e \in B.

Definition beadty (p : nat) : 'I_t :=
  let e := nth set0 es (p %/ m.+1) in
  let l := inord (p %% m.+1) : 'I_m.+1 in
  if wpred l e then tix (sd e) l else tnull.

Definition creal : seq 'I_t := [seq beadty p | p <- iota 0 (N * m.+1)].
Definition padding : seq 'I_t := [seq k <- enum 'I_t | odd (count (pred1 k) creal)].
Definition cs : seq 'I_t := creal ++ padding.

Lemma size_creal : size creal = N * m.+1.
Proof. by rewrite size_map size_iota. Qed.

Lemma nth_creal (p : nat) : p < N * m.+1 -> nth tnull creal p = beadty p.
Proof.
move=> hp; rewrite (nth_map 0) ?size_iota // nth_iota //.
Qed.

Lemma beadty_block (j l : nat) : l < m.+1 ->
  beadty (j * m.+1 + l) =
  (let e := nth set0 es j in
   if wpred (inord l) e then tix (sd e) (inord l) else tnull).
Proof.
move=> hl; rewrite /beadty divnMDl // modnMDl.
by rewrite (divn_small hl) (modn_small hl) addn0.
Qed.

Lemma padding_uniq : uniq padding.
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Lemma count_padding (k : 'I_t) :
  count (pred1 k) padding = (odd (count (pred1 k) creal) : nat).
Proof.
by rewrite count_uniq_mem ?padding_uniq // mem_filter mem_enum andbT.
Qed.

Lemma cs_even (k : 'I_t) : 2 %| count (pred1 k) cs.
Proof.
by rewrite /cs count_cat count_padding dvdn2 oddD oddb addbb.
Qed.

(** Positions of the necklace. *)

Lemma count_pair_pos (T Q : eqType) (x0 : T) (y0 : Q) (k : T) (j : Q)
    (c : seq T) (u : seq Q) :
  size u = size c ->
  count_pair k j c u
  = count (fun p => (nth x0 c p == k) && (nth y0 u p == j)) (iota 0 (size c)).
Proof.
move=> hsz; rewrite /count_pair.
have hz : size (zip c u) = size c by rewrite size_zip hsz minnn.
have hzip : zip c u = [seq nth (x0, y0) (zip c u) p | p <- iota 0 (size c)].
  by rewrite -hz map_nth_iota0 // take_size.
rewrite {1}hzip count_map; apply: eq_in_count => p _ /=.
by rewrite nth_zip.
Qed.

Lemma size_cs : size cs = N * m.+1 + size padding.
Proof. by rewrite /cs size_cat size_creal. Qed.

Lemma nth_cs (p : nat) : p < N * m.+1 -> nth tnull cs p = beadty p.
Proof. by move=> hp; rewrite /cs nth_cat size_creal hp nth_creal. Qed.


Lemma count_block_tix (j : nat) (s : bool) (l : 'I_m.+1) :
  count (fun l' => beadty (j * m.+1 + l') == tix s l) (iota 0 m.+1)
  = (wpred l (nth set0 es j) && (sd (nth set0 es j) == s) : nat).
Proof.
rewrite (@eq_in_count _ _
   (fun l' => (l' == val l) &&
              (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)))); last first.
  move=> l'; rewrite mem_iota /= add0n => hl'.
  rewrite beadty_block //.
  case: (altP (l' =P val l)) => [hl'e|hne] /=.
    rewrite hl'e inord_val.
    case: (boolP (wpred l (nth set0 es j))) => hw /=.
      by rewrite tixE eqxx andbT.
    by rewrite eq_sym tix_null.
  have hvi : val (@inord m l') = l' by exact: (inordK hl').
  have hii : inord l' != l by apply: contra hne => /eqP <-; rewrite hvi.
  case: (boolP (wpred (inord l') (nth set0 es j))) => hw /=.
    by rewrite tixE (negbTE hii) andbF.
  by rewrite eq_sym tix_null.
case: (boolP (wpred l (nth set0 es j) && (sd (nth set0 es j) == s))) => hX.
  rewrite (@eq_count _ _ (pred1 (val l))); last by move=> l' /=; rewrite andbT.
  by rewrite count_uniq_mem ?iota_uniq // mem_iota /= add0n ltn_ord.
rewrite (@eq_count _ _ pred0); last by move=> l' /=; rewrite andbF.
by rewrite count_pred0.
Qed.

Lemma count_creal_tix (s : bool) (l : 'I_m.+1) :
  count (pred1 (tix s l)) creal
  = count (fun e => wpred l e && (sd e == s)) es.
Proof.
rewrite /creal count_map count_iota_blocks.
rewrite (eq_bigr (fun j : 'I_N =>
   (wpred l (nth set0 es j) && (sd (nth set0 es j) == s) : nat))); last first.
  by move=> j _; exact: count_block_tix.
exact: (sum_ord_count set0 es (fun e => wpred l e && (sd e == s))).
Qed.


Lemma pos_lt (j l' : nat) : j < N -> l' < m.+1 -> j * m.+1 + l' < N * m.+1.
Proof.
move=> hj hl'.
apply: (leq_trans (_ : j * m.+1 + l' < j.+1 * m.+1)).
  by rewrite mulSn addnC ltn_add2r.
by rewrite leq_mul2r hj orbT.
Qed.

Lemma count_block_tix_gen (j : nat) (s : bool) (l : 'I_m.+1) (R : nat -> bool) :
  count (fun l' => (beadty (j * m.+1 + l') == tix s l) && R (j * m.+1 + l'))
        (iota 0 m.+1)
  = (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
     && R (j * m.+1 + val l) : nat).
Proof.
rewrite (@eq_in_count _ _
   (fun l' => (l' == val l) &&
      (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
       && R (j * m.+1 + val l)))); last first.
  move=> l'; rewrite mem_iota /= add0n => hl'.
  rewrite beadty_block //.
  case: (altP (l' =P val l)) => [hl'e|hne] /=.
    rewrite hl'e inord_val.
    case: (boolP (wpred l (nth set0 es j))) => hw /=.
      by rewrite tixE eqxx andbT.
    by rewrite eq_sym tix_null.
  have hvi : val (@inord m l') = l' by exact: (inordK hl').
  have hii : inord l' != l by apply: contra hne => /eqP <-; rewrite hvi.
  case: (boolP (wpred (inord l') (nth set0 es j))) => hw /=.
    by rewrite tixE (negbTE hii) andbF.
  by rewrite eq_sym tix_null.
case: (boolP (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
              && R (j * m.+1 + val l))) => hX.
  rewrite (@eq_count _ _ (pred1 (val l))); last by move=> l' /=; rewrite andbT.
  by rewrite count_uniq_mem ?iota_uniq // mem_iota /= add0n ltn_ord.
rewrite (@eq_count _ _ pred0); last by move=> l' /=; rewrite andbF.
by rewrite count_pred0.
Qed.

Lemma count_pos_tix (s : bool) (l : 'I_m.+1) (R : nat -> bool) :
  count (fun p => (nth tnull cs p == tix s l) && R p) (iota 0 (N * m.+1))
  = \sum_(j < N) ((wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
                   && R (j * m.+1 + val l)) : nat).
Proof.
rewrite count_iota_blocks; apply: eq_bigr => j _.
rewrite -(count_block_tix_gen j s l R); apply: eq_in_count => l'.
by rewrite mem_iota /= add0n => hl'; rewrite nth_cs // pos_lt.
Qed.


Lemma nth_cs_pad (i : nat) : nth tnull cs (N * m.+1 + i) = nth tnull padding i.
Proof.
by rewrite /cs nth_cat size_creal ltnNge leq_addr /= addKn.
Qed.

Section WithSplit.
Variable a : seq 'I_2.
Hypothesis size_a : size a = size cs.
Hypothesis share_a : forall (k : 'I_t) (j : 'I_2),
  count_pair k j cs a = count (pred1 k) cs %/ 2.

Definition bth (p : nat) : 'I_2 := nth ord0 a p.

Definition Xc (s : bool) (l : 'I_m.+1) : nat :=
  count (fun e => wpred l e && (sd e == s)) es.
Definition Yc (s : bool) (l : 'I_m.+1) : nat :=
  \sum_(j < N) ((wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
                 && (bth (j * m.+1 + val l) == ord0)) : nat).

Lemma pad_le1 (k : 'I_t) (R : nat -> bool) :
  count (fun i => (nth tnull cs (N * m.+1 + i) == k) && R i)
        (iota 0 (size padding)) <= 1.
Proof.
apply: (leq_trans (_ : _ <= count (fun i => nth tnull cs (N * m.+1 + i) == k)
                             (iota 0 (size padding)))).
  by apply: sub_count => i /=; case/andP.
have -> : count (fun i => nth tnull cs (N * m.+1 + i) == k)
                (iota 0 (size padding)) = count (pred1 k) padding.
  rewrite (@eq_in_count _ _ (fun i => nth tnull padding i == k)); last first.
    by move=> i _ /=; rewrite nth_cs_pad.
  exact: (count_nth_iota tnull padding (pred1 k)).
by rewrite count_padding; case: (odd _).
Qed.

Lemma share_bounds (s : bool) (l : 'I_m.+1) :
  (2 * Yc s l <= Xc s l + 1) && (Xc s l <= 2 * Yc s l + 3).
Proof.
pose R := fun p : nat => bth p == ord0.
have hcp : count_pair (tix s l) ord0 cs a
         = Yc s l + count (fun i => (nth tnull cs (N * m.+1 + i) == tix s l)
                                    && R (N * m.+1 + i))
                          (iota 0 (size padding)).
  rewrite (count_pair_pos tnull ord0) // size_cs count_iota_split; congr (_ + _).
  by rewrite /Yc; exact: (count_pos_tix s l (fun p => bth p == ord0)).
have hc : count (pred1 (tix s l)) cs = Xc s l + count (pred1 (tix s l)) padding.
  by rewrite /cs count_cat count_creal_tix.
have hpA := pad_le1 (tix s l) (fun i => R (N * m.+1 + i)).
have hpX : count (pred1 (tix s l)) padding <= 1.
  by rewrite count_padding; case: (odd _).
move: (share_a (tix s l) ord0); rewrite hcp hc => heq.
set PA := count _ _ in heq hpA.
set PX := count (pred1 (tix s l)) padding in heq hpX.
apply/andP; split.
  apply: (leq_trans (_ : _ <= 2 * (Yc s l + PA))).
    by rewrite leq_pmul2l // leq_addr.
  rewrite heq.
  apply: (leq_trans (_ : _ <= Xc s l + PX)); last by rewrite leq_add2l.
  by rewrite {2}(divn_eq (Xc s l + PX) 2) mulnC leq_addr.
apply: (leq_trans (_ : _ <= Xc s l + PX)); first by rewrite leq_addr.
rewrite {1}(divn_eq (Xc s l + PX) 2) -heq mulnDl -addnA.
apply: leq_add; first by rewrite mulnC.
have -> : 3 = 2 + 1 by [].
apply: leq_add.
  by rewrite -{2}[2]mul1n leq_mul2r hpA orbT.
by rewrite -ltnS ltn_mod.
Qed.

(** The thief of an edge is the thief of its first bead; it differs from the
    thief of its [l]-th bead only for edges whose block is cut. *)

Definition Dc (l : 'I_m.+1) : nat :=
  \sum_(j < N) ((bth (j * m.+1) != bth (j * m.+1 + val l)) : nat).

Lemma Dc_cuts (l : 'I_m.+1) : Dc l <= cuts_seq a.
Proof.
pose Q := fun p => (p.+1 < size a) && (bth p != bth p.+1).
have hsz : N * m.+1 <= size a by rewrite size_a size_cs leq_addr.
have hcut : cuts_seq a = count Q (iota 0 (size a)) by rewrite (cuts_seq_nth ord0).
apply: (leq_trans (_ : _ <= count Q (iota 0 (N * m.+1)))); last first.
  by rewrite hcut; apply: count_iota_le.
rewrite count_iota_blocks /Dc.
apply: leq_sum => j _.
apply: (leq_trans (_ : _ <= count (fun i => bth (j * m.+1 + i)
                                         != bth (j * m.+1 + i.+1)) (iota 0 (val l)))).
  rewrite -{1}(addn0 (j * m.+1)).
  exact: (diff_count (fun i => bth (j * m.+1 + i)) (val l)).
apply: (leq_trans (_ : _ <= count (fun i => bth (j * m.+1 + i)
                                         != bth (j * m.+1 + i.+1)) (iota 0 m))).
  by apply: count_iota_le; rewrite -ltnS ltn_ord.
rewrite (@eq_in_count _ _ (fun i => Q (j * m.+1 + i))); last first.
  move=> i; rewrite mem_iota /= add0n => hi.
  have hlt : j * m.+1 + i.+1 < size a.
    by apply: leq_trans hsz; apply: pos_lt; rewrite ?ltn_ord.
  by rewrite /Q -addnS hlt.
by apply: count_iota_le.
Qed.

(** The thief of an edge, and the selection it defines. *)

Definition thj (j : nat) : bool := bth (j * m.+1) == ord0.
Definition thE (e : {set G}) : bool := thj (index e es).
Definition sel (e : {set G}) : bool := if e \in A then thE e else ~~ thE e.

Definition Zc (s : bool) (l : 'I_m.+1) : nat :=
  \sum_(j < N) ((wpred l (nth set0 es j) && (sd (nth set0 es j) == s) && thj j) : nat).

Lemma Zc_Yc_le (s : bool) (l : 'I_m.+1) : Zc s l <= Yc s l + Dc l.
Proof.
rewrite /Zc /Yc /Dc -big_split /=; apply: leq_sum => j _.
case: (boolP (wpred l (nth set0 es j) && (sd (nth set0 es j) == s))) => hP /=; last by [].
rewrite /thj; case: (altP (bth (j * m.+1) =P ord0)) => h1 /=; last by [].
case: (altP (bth (j * m.+1 + val l) =P ord0)) => h2 /=; first by [].
by rewrite h1 eq_sym h2.
Qed.

Lemma Yc_Zc_le (s : bool) (l : 'I_m.+1) : Yc s l <= Zc s l + Dc l.
Proof.
rewrite /Zc /Yc /Dc -big_split /=; apply: leq_sum => j _.
case: (boolP (wpred l (nth set0 es j) && (sd (nth set0 es j) == s))) => hP /=; last by [].
rewrite /thj; case: (altP (bth (j * m.+1 + val l) =P ord0)) => h2 /=; last by [].
case: (altP (bth (j * m.+1) =P ord0)) => h1 /=; first by [].
by rewrite h2 h1.
Qed.

Lemma thE_nth (j : nat) : j < N -> thE (nth set0 es j) = thj j.
Proof.
by move=> hj; rewrite /thE index_uniq // (uniq_bl bipf mA mB).
Qed.

Lemma Zc_count (s : bool) (l : 'I_m.+1) :
  Zc s l = count (fun e => wpred l e && (sd e == s) && thE e) es.
Proof.
rewrite /Zc -(sum_ord_count set0 es (fun e => wpred l e && (sd e == s) && thE e)).
by apply: eq_bigr => j _; rewrite thE_nth.
Qed.

Lemma map_thE_es : [seq thE e | e <- es] = [seq thj j | j <- iota 0 N].
Proof.
have hes : es = [seq nth set0 es j | j <- iota 0 N].
  by rewrite map_nth_iota0 // take_size.
rewrite {1}hes -map_comp; apply/eq_in_map => j.
by rewrite mem_iota /= add0n => hj; rewrite /= thE_nth.
Qed.

Lemma cuts_thE : cuts_seq [seq thE e | e <- es] <= cuts_seq a.
Proof.
pose Q := fun p => (p.+1 < size a) && (bth p != bth p.+1).
have hsz : N * m.+1 <= size a by rewrite size_a size_cs leq_addr.
have hcut : cuts_seq a = count Q (iota 0 (size a)) by rewrite (cuts_seq_nth ord0).
rewrite map_thE_es (cuts_seq_map_nth 0) size_iota.
rewrite (@eq_in_count _ _ (fun k => (k.+1 < N) && (thj k != thj k.+1))); last first.
  move=> k; rewrite mem_iota /= add0n => hk.
  case: (boolP (k.+1 < N)) => hk1 /=; last by [].
  by rewrite !nth_iota // ?add0n //; apply: ltn_trans hk1.
apply: (leq_trans (_ : _ <= count Q (iota 0 (N * m.+1)))); last first.
  by rewrite hcut; apply: count_iota_le.
rewrite [X in X <= _]count_iota_sum count_iota_blocks.
apply: leq_sum => j _.
case: (boolP (j.+1 < N)) => hj1 /=; last by [].
apply: (leq_trans (_ : _ <= ((bth (j * m.+1) != bth (j * m.+1 + m.+1)) : nat))).
  rewrite /thj (_ : j.+1 * m.+1 = j * m.+1 + m.+1); last by rewrite mulSnr.
  case: (altP (bth (j * m.+1) =P bth (j * m.+1 + m.+1))) => [heq|hne].
    by rewrite heq eqxx.
  exact: leq_b1.
apply: (leq_trans (_ : _ <= count (fun i => bth (j * m.+1 + i)
                                         != bth (j * m.+1 + i.+1)) (iota 0 m.+1))).
  rewrite -{1}(addn0 (j * m.+1)).
  exact: (diff_count (fun i => bth (j * m.+1 + i)) m.+1).
rewrite (@eq_in_count _ _ (fun i => Q (j * m.+1 + i))) //.
move=> i; rewrite mem_iota /= add0n => hi.
have hlt : j * m.+1 + i.+1 < size a.
  apply: leq_trans hsz.
  apply: (leq_ltn_trans (_ : j * m.+1 + i.+1 <= j.+1 * m.+1)).
    by rewrite mulSnr leq_add2l.
  by rewrite ltn_mul2r /= hj1.
by rewrite /Q -addnS hlt.
Qed.

(** The selected edges, minus those that start a conflict. *)

Definition Csel : {set {set G}} := [set e in SS A B | sel e].
Definition Psrc : {set {set G}} :=
  [set e in SS A B | sel e && ((nxt f A B e != set0) && (nxt f A B e \in Csel))].
Definition Chalf : {set {set G}} := (A :&: B) :|: (Csel :\: Psrc).

Lemma mem_Csel (e : {set G}) : (e \in Csel) = (e \in SS A B) && sel e.
Proof. by rewrite inE. Qed.

Lemma mem_Psrc (e : {set G}) :
  (e \in Psrc) = (e \in SS A B) &&
     (sel e && ((nxt f A B e != set0) && (nxt f A B e \in Csel))).
Proof. by rewrite inE. Qed.

Lemma sel_opp (e : {set G}) :
  e \in SS A B -> nxt f A B e != set0 -> sel e -> sel (nxt f A B e) ->
  thE e != thE (nxt f A B e).
Proof.
move=> /SSP/orP[he|he] hn hs hsn.
  have hnB := nxt_SA he hn.
  have hnA' : nxt f A B e \notin A.
    by move: (proj1 (andP hnB)); rewrite inE => /andP[].
  move: hs; rewrite /sel (SA_A he) => hs.
  move: hsn; rewrite /sel (negbTE hnA') => hsn.
  by rewrite hs; move: hsn; case: (thE (nxt f A B e)).
have hnA := nxt_SB he hn.
have heA : e \notin A by move: he; rewrite inE => /andP[].
move: hs; rewrite /sel (negbTE heA) => hs.
move: hsn; rewrite /sel (SA_A (proj1 (andP hnA))) => hsn.
by rewrite hsn; move: hs; case: (thE e).
Qed.

Lemma card_Psrc : #|Psrc| <= 2 * cuts_seq a.
Proof.
pose P := fun e : {set G} => (e \in SS A B) &&
   (sel e && ((nxt f A B e != set0) && (nxt f A B e \in Csel))).
have -> : #|Psrc| = count P es.
  rewrite (@card_seq_count _ es (SS A B) _ (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
  apply: eq_in_count => e; rewrite (mem_bl bipf mA mB) => he.
  by rewrite /P he.
apply: (leq_trans (_ : _ <= 2 * cuts_seq [seq thE e | e <- es])); last first.
  by rewrite leq_pmul2l //; exact: cuts_thE.
apply: (conflict_count bipf mA mB) => e /andP[he /andP[hs /andP[hn hin]]].
split=> //.
by apply: sel_opp => //; move: hin; rewrite mem_Csel => /andP[].
Qed.

(** Set-theoretic bookkeeping. *)

Lemma Csel_SS (e : {set G}) : e \in Csel -> e \in SS A B.
Proof. by rewrite mem_Csel => /andP[]. Qed.

Lemma AB_SS (e : {set G}) : e \in A :&: B -> e \notin SS A B.
Proof.
rewrite inE => /andP[hA hB]; apply/negP => /SSP/orP[]; rewrite inE.
  by move=> /andP[]; rewrite hB.
by move=> /andP[]; rewrite hA.
Qed.

Lemma Chalf_matching : matching Chalf.
Proof.
have hsub : forall e, e \in Chalf -> (e \in A) || (e \in B).
  move=> e; rewrite inE => /orP[|].
    by rewrite inE => /andP[-> _].
  rewrite inE => /andP[_ /Csel_SS /SSP/orP[/SA_A ->|/SB_B ->]] //.
  by rewrite orbT.
split.
  move=> e /hsub /orP[hA|hB].
    by case: mA => hs _; exact: (hs _ hA).
  by case: mB => hs _; exact: (hs _ hB).
move=> e1 e2 h1 h2 v hv1 hv2.
case: (e1 =P e2) => // hne.
have hne1 : e1 != e2 by apply/eqP.
have key : forall x y : {set G}, x \in Chalf -> y \in Chalf -> x != y ->
    v \in x -> v \in y -> (x \in A :&: B) -> x = y.
  move=> x y hx hy hxy hvx hvy hxAB.
  have hxA : x \in A by move: hxAB; rewrite inE => /andP[].
  have hxB : x \in B by move: hxAB; rewrite inE => /andP[].
  case/orP: (hsub _ hy) => hym.
    by case: mA => _ hu; apply: (hu _ _ hxA hym v).
  by case: mB => _ hu; apply: (hu _ _ hxB hym v).
case: (boolP (e1 \in A :&: B)) => h1AB; first exact: (key e1 e2).
case: (boolP (e2 \in A :&: B)) => h2AB.
  by apply/esym; apply: (key e2 e1) => //; rewrite eq_sym.
have hC1 : e1 \in Csel :\: Psrc by move: h1; rewrite inE (negbTE h1AB).
have hC2 : e2 \in Csel :\: Psrc by move: h2; rewrite inE (negbTE h2AB).
have hin1 : e1 \in Csel by move: hC1; rewrite inE => /andP[_].
have hin2 : e2 \in Csel by move: hC2; rewrite inE => /andP[_].
have hnp1 : e1 \notin Psrc by move: hC1; rewrite inE => /andP[].
have hnp2 : e2 \notin Psrc by move: hC2; rewrite inE => /andP[].
have hs1 : e1 \in SS A B by exact: Csel_SS.
have hs2 : e2 \in SS A B by exact: Csel_SS.
have hsel1 : sel e1 by move: hin1; rewrite mem_Csel => /andP[].
have hsel2 : sel e2 by move: hin2; rewrite mem_Csel => /andP[].
exfalso.
case/orP: (meetP bipf mA mB hs1 hs2 hne1 hv1 hv2) => /eqP hnx.
  by move: hnp1; rewrite mem_Psrc hs1 hsel1 hnx hin2 (SS_neq0 mA mB hs2).
have hne2 : e2 != e1 by rewrite eq_sym.
by move: hnp2; rewrite mem_Psrc hs2 hsel2 hnx hin1 (SS_neq0 mA mB hs1).
Qed.

Lemma Chalf_sub : Chalf \subset A :|: B.
Proof.
apply/subsetP => e; rewrite inE => /orP[|].
  by rewrite !inE => /andP[-> _].
rewrite inE => /andP[_ /Csel_SS /SSP/orP[hs|hs]].
  by rewrite inE (SA_A hs).
by rewrite inE (SB_B hs) orbT.
Qed.

(** Counting the selection. *)

Lemma sel_esE (e : {set G}) : e \in es -> sel e = (if sd e then ~~ thE e else thE e).
Proof.
rewrite (mem_bl bipf mA mB) => /SSP/orP[he|he]; rewrite /sel.
  have -> : sd e = false by move: he; rewrite /sd inE => /andP[/negbTE].
  by rewrite (SA_A he).
have -> : sd e by rewrite /sd (SB_B he).
by have -> : (e \in A) = false by apply/negbTE; move: he; rewrite inE => /andP[].
Qed.


Lemma SelC_id (l : 'I_m.+1) :
  count (fun e => sel e && wpred l e) es + Zc true l = Zc false l + Xc true l.
Proof.
have hpred1 : {in es, (fun e => (sel e && wpred l e) && ~~ sd e)
                   =1 (fun e => wpred l e && (sd e == false) && thE e)}.
  move=> e he /=; rewrite (sel_esE he).
  by case: (sd e); case: (thE e); case: (wpred l e).
have hpred2 : {in es, (fun e => (sel e && wpred l e) && ~~ ~~ sd e)
                   =1 (fun e => wpred l e && (sd e == true) && ~~ thE e)}.
  move=> e he /=; rewrite (sel_esE he).
  by case: (sd e); case: (thE e); case: (wpred l e).
rewrite (count_split es (fun e => sel e && wpred l e) (fun e => ~~ sd e)).
rewrite (eq_in_count hpred1) (eq_in_count hpred2) -Zc_count -addnA.
congr (_ + _).
rewrite addnC Zc_count /Xc.
by rewrite (count_split es (fun e => wpred l e && (sd e == true)) (fun e => thE e)).
Qed.

Lemma Xc_split (l : 'I_m.+1) : Xc false l + Xc true l = count (wpred l) es.
Proof.
rewrite /Xc (count_split es (wpred l) (fun e => sd e)) addnC.
congr (_ + _); apply: eq_count => e /=.
  by case: (sd e); rewrite ?andbT ?andbF.
by case: (sd e); rewrite ?andbT ?andbF.
Qed.

(** The two halving estimates. *)

Lemma Zc_bounds (s : bool) (l : 'I_m.+1) :
  (2 * Zc s l <= Xc s l + (1 + 2 * cuts_seq a))
  && (Xc s l <= 2 * Zc s l + (3 + 2 * cuts_seq a)).
Proof.
have /andP[h1 h2] := share_bounds s l.
apply: (ZYD_arith h1 h2 (Zc_Yc_le s l) (Yc_Zc_le s l) (Dc_cuts l)).
Qed.

Lemma SelC_le (l : 'I_m.+1) :
  2 * count (fun e => sel e && wpred l e) es
  <= count (wpred l) es + (4 + 4 * cuts_seq a).
Proof.
have /andP[h1f _] := Zc_bounds false l.
have /andP[_ h2t] := Zc_bounds true l.
rewrite -Xc_split.
exact: (halving_arith_le (SelC_id l) h1f h2t).
Qed.

Lemma SelC_ge (l : 'I_m.+1) :
  count (wpred l) es
  <= 2 * count (fun e => sel e && wpred l e) es + (4 + 4 * cuts_seq a).
Proof.
have /andP[_ h2f] := Zc_bounds false l.
have /andP[h1t _] := Zc_bounds true l.
rewrite -Xc_split.
exact: (halving_arith_ge (SelC_id l) h2f h1t).
Qed.

(** Cardinalities. *)

Lemma card_setI_P (X : {set {set G}}) (P : pred {set G}) :
  [set e in X | P e] = X :&: [set e | P e].
Proof. by apply/setP => e; rewrite !inE. Qed.

Lemma card_split (P : pred {set G}) :
  #|[set e in A | P e]| + #|[set e in B | P e]|
  = 2 * #|[set e in A :&: B | P e]| + count P es.
Proof.
have hA : #|[set e in A | P e]|
        = #|[set e in A :&: B | P e]| + #|[set e in SA A B | P e]|.
  have -> : [set e in A :&: B | P e] = [set e in A | P e] :&: B.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  have -> : [set e in SA A B | P e] = [set e in A | P e] :\: B.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  by rewrite cardsID.
have hB : #|[set e in B | P e]|
        = #|[set e in A :&: B | P e]| + #|[set e in SB A B | P e]|.
  have -> : [set e in A :&: B | P e] = [set e in B | P e] :&: A.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  have -> : [set e in SB A B | P e] = [set e in B | P e] :\: A.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  by rewrite cardsID.
have hSS : count P es = #|[set e in SA A B | P e]| + #|[set e in SB A B | P e]|.
  rewrite -(@card_seq_count _ es (SS A B) P (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
  have -> : [set e in SS A B | P e]
          = [set e in SA A B | P e] :|: [set e in SB A B | P e].
    by apply/setP => e; rewrite !inE -andb_orl.
  rewrite cardsU.
  have -> : [set e in SA A B | P e] :&: [set e in SB A B | P e] = set0.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  by rewrite cards0 subn0.
by rewrite hA hB hSS -!plusE -!multE; lia.
Qed.

Lemma memsetP (X : {set {set G}}) (P : pred {set G}) (e : {set G}) :
  (e \in [set x in X | P x]) = (e \in X) && P e.
Proof. by rewrite inE. Qed.

Lemma card_Chalf (P : pred {set G}) :
  #|[set e in Chalf | P e]|
  = #|[set e in A :&: B | P e]| + #|[set e in Csel :\: Psrc | P e]|.
Proof.
have hmem : forall e, (e \in Chalf) = (e \in A :&: B) || (e \in Csel :\: Psrc).
  by move=> e; rewrite /Chalf inE.
have -> : [set e in Chalf | P e]
        = [set e in A :&: B | P e] :|: [set e in Csel :\: Psrc | P e].
  by apply/setP => e; rewrite memsetP hmem in_setU !memsetP andb_orl.
rewrite cardsU.
have -> : [set e in A :&: B | P e] :&: [set e in Csel :\: Psrc | P e] = set0.
  apply/setP => e; rewrite in_setI !memsetP in_set0 in_setD.
  case: (boolP ((e \in A) && (e \in B))) => hab /=; last by [].
  have hab' : e \in A :&: B by rewrite in_setI.
  have -> : (e \in Csel) = false.
    by apply/negbTE; apply: contra (AB_SS hab') => /Csel_SS.
  by rewrite andbF andbF.
by rewrite cards0 subn0.
Qed.

Lemma card_Csel_count (P : pred {set G}) :
  #|[set e in Csel | P e]| = count (fun e => sel e && P e) es.
Proof.
have -> : [set e in Csel | P e] = [set e in SS A B | sel e && P e].
  by apply/setP => e; rewrite !memsetP andbA.
exact: (@card_seq_count _ es (SS A B) (fun e => sel e && P e)
                        (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
Qed.

Lemma card_Chalf_le (P : pred {set G}) :
  #|[set e in Chalf | P e]|
  <= #|[set e in A :&: B | P e]| + count (fun e => sel e && P e) es.
Proof.
rewrite card_Chalf -card_Csel_count leq_add2l.
apply: subset_leq_card; apply/subsetP => e.
rewrite memsetP in_setD => /andP[/andP[_ hc] hP].
by rewrite memsetP hc hP.
Qed.

Lemma card_Chalf_ge (P : pred {set G}) :
  #|[set e in A :&: B | P e]| + count (fun e => sel e && P e) es
  <= #|[set e in Chalf | P e]| + #|Psrc|.
Proof.
rewrite card_Chalf -card_Csel_count -addnA leq_add2l.
apply: (leq_trans (_ : _ <= #|[set e in Csel :\: Psrc | P e] :|: Psrc|)).
  apply: subset_leq_card; apply/subsetP => e.
  rewrite memsetP => /andP[hc hP].
  case: (boolP (e \in Psrc)) => hp; first by rewrite in_setU hp orbT.
  by rewrite in_setU memsetP in_setD hp hc hP.
apply: (leq_trans (leq_card_setU _ _).1) => //.
Qed.

(** The two halving estimates, in terms of cardinalities. *)

Lemma Chalf_stat (l : 'I_m.+1) :
  2 * #|[set e in Chalf | wpred l e]|
  <= #|[set e in A | wpred l e]| + #|[set e in B | wpred l e]|
     + (4 + 4 * cuts_seq a).
Proof.
rewrite card_split.
move/leP: (card_Chalf_le (wpred l)) => h1; move/leP: (SelC_le l) => h2.
by apply/leP; move: h1 h2; rewrite -!plusE -!multE => *; lia.
Qed.

Lemma wpred0 (e : {set G}) : wpred ord0 e = true.
Proof. by rewrite /wpred unlift_none. Qed.

Lemma set_wpred0 (X : {set {set G}}) : [set e in X | wpred ord0 e] = X.
Proof. by apply/setP => e; rewrite memsetP wpred0 andbT. Qed.

Lemma Chalf_size : #|A| + #|B| <= 2 * #|Chalf| + (4 + 8 * cuts_seq a).
Proof.
have hsplit := card_split (wpred ord0).
have h1 := card_Chalf_ge (wpred ord0).
move: hsplit h1; rewrite !set_wpred0 => hsplit h1.
move/leP: h1 => h1; move/leP: (SelC_ge ord0) => h2; move/leP: card_Psrc => h3.
apply/leP; move: hsplit h1 h2 h3.
by rewrite -!plusE -!multE => *; lia.
Qed.

End WithSplit.

(** ** The halving lemma *)

Theorem matching_halving :
  exists C : {set {set G}},
    [/\ matching C, C \subset A :|: B,
        #|A| + #|B| <= 2 * #|C| + (16 * m + 28) &
        forall i : 'I_m,
          2 * #|C :&: W i| <= #|A :&: W i| + #|B :&: W i| + (8 * m + 16)].
Proof.
have [a [hsz hcuts hshare]] :=
  splitting_necklace_seq (ltn0Sn 1) (fun k => cs_even k).
have ht : cuts_seq a <= 2 * m.+1 + 1.
  by move: hcuts; rewrite muln1 card_TT addn1.
exists (Chalf a); split.
- exact: (Chalf_matching a).
- exact: (Chalf_sub a).
- apply: (leq_trans (Chalf_size hsz hshare)).
  rewrite leq_add2l.
  move/leP: ht => ht; apply/leP; move: ht.
  by rewrite -!plusE -!multE => *; lia.
- move=> i.
  have hlift : forall e : {set G}, wpred (lift ord0 i) e = (e \in W i).
    by move=> e; rewrite /wpred liftK.
  have hWset : forall X : {set {set G}},
      [set e in X | wpred (lift ord0 i) e] = X :&: W i.
    by move=> X; apply/setP => e; rewrite memsetP hlift in_setI.
  have := Chalf_stat hsz hshare (lift ord0 i).
  rewrite !hWset => hstat.
  apply: (leq_trans hstat); rewrite leq_add2l.
  move/leP: ht => ht; apply/leP; move: ht.
  by rewrite -!plusE -!multE => *; lia.
Qed.

End Halving.

(** * Step 4: interpolating several matchings ******************************)

(** Chains of halvings realise any convex combination of finitely many
    matchings, with an error that does not grow with the precision of the
    weights.  See step 4 of the header. *)

(** Scaled arithmetic, discharged by [lia]. *)

Lemma half_arith_size (d YA YB EA EB cA cB cC K : nat) :
  YA <= d * cA + EA -> YB <= d * cB + EB ->
  d * (cA + cB) <= d * (2 * cC + K) ->
  YA + YB <= 2 * d * cC + (EA + EB + d * K).
Proof.
move=> /leP h1 /leP h2 /leP h3; apply/leP.
by move: h1 h2 h3; rewrite -!plusE -!multE => *; lia.
Qed.

Lemma half_arith_stat (d VA VB EA EB cA cB cC K : nat) :
  d * cA <= VA + EA -> d * cB <= VB + EB ->
  d * (2 * cC) <= d * (cA + cB + K) ->
  2 * d * cC <= VA + VB + (EA + EB + d * K).
Proof.
move=> /leP h1 /leP h2 /leP h3; apply/leP.
by move: h1 h2 h3; rewrite -!plusE -!multE => *; lia.
Qed.

Lemma drift_arith (a b c dd e : nat) : a <= b + c -> b <= dd + e -> a <= dd + (c + e).
Proof.
move=> /leP h1 /leP h2; apply/leP.
by move: h1 h2; rewrite -!plusE => *; lia.
Qed.

Lemma dyad_lo (X k YA YB : nat) : k <= X ->
  X * YB + (k * YA + (X - k) * YB) = k * YA + (2 * X - k) * YB.
Proof.
move=> h; rewrite addnCA -mulnDl; congr (_ + _ * _).
by rewrite addnBA // addnn -mul2n.
Qed.

Lemma dyad_hi {X k k' YA YB : nat} : k' <= X -> k = X + k' ->
  X * YA + (k' * YA + (X - k') * YB) = k * YA + (2 * X - k) * YB.
Proof.
move=> h ->; rewrite addnA -mulnDl; congr (_ * _ + _ * _).
by rewrite mul2n -addnn subnDl.
Qed.

Lemma dyad_err (X E d e : nat) :
  X * E + X * (E + d * e) + X * d * e = 2 * X * (E + d * e).
Proof. by rewrite -!plusE -!multE; lia. Qed.

Lemma sub_id (M1 M2 M3 : nat) : M3 + M2 <= M1 -> M1 - M2 = M3 + (M1 - (M3 + M2)).
Proof. by move=> /leP h; rewrite -!plusE -!minusE in h *; lia. Qed.

Lemma sub_le (M1 M2 M3 : nat) : M1 <= M2 + M3 -> M1 - M2 <= M3.
Proof. by move=> /leP h; apply/leP; rewrite -!plusE -!minusE in h *; lia. Qed.

Lemma hE_arith (Lam L' X P e Nn : nat) : Lam * L' * Nn <= Lam * L' * X ->
  Lam * (X * (L' * P + L' * e)) + Lam * L' * Nn
  <= X * L' * (Lam * (P + (e + 1))).
Proof.
by move=> /leP h; apply/leP; rewrite -!plusE -!multE in h *; nia.
Qed.

Lemma key_id {k j a L' S c u : nat} :
  j * L' = a * k + u ->
  (k + j) * L' * (a * c + S) + L' * u * c
  = (a + L') * (k * S + j * L' * c) + u * S.
Proof. by move=> h; rewrite mulnDl !h -!plusE -!multE; nia. Qed.

Lemma key_arith {k j a L' S c N u : nat} :
  j * L' = a * k + u -> u <= a + L' -> S <= L' * N ->
  (k + j) * L' * (a * c + S)
  <= (a + L') * (k * S + j * L' * c) + (a + L') * L' * N.
Proof.
move=> hu hua hS.
apply: (leq_trans (_ : _ <= (k + j) * L' * (a * c + S) + L' * u * c));
  first exact: leq_addr.
by rewrite (key_id hu) leq_add2l -mulnA; apply: leq_mul.
Qed.

Lemma key_arith2 {k j a L' S c N u : nat} :
  j * L' = a * k + u -> u <= a + L' -> c <= N ->
  (a + L') * (k * S + j * L' * c)
  <= (k + j) * L' * (a * c + S) + (a + L') * L' * N.
Proof.
move=> hu hua hc.
apply: (leq_trans (_ : _ <= (a + L') * (k * S + j * L' * c) + u * S));
  first exact: leq_addr.
rewrite -(key_id hu) leq_add2l.
apply: leq_mul; last exact: hc.
by rewrite mulnC leq_mul2r hua orbT.
Qed.

Section Mixing.
Variables (G : sgraph) (f : G -> bool) (m : nat) (W : 'I_m -> {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.

Definition realisesN (d : nat) (C : {set {set G}})
    (Y : nat) (V : 'I_m -> nat) (E : nat) : Prop :=
  (Y <= d * #|C| + E) /\ (forall i, d * #|C :&: W i| <= V i + E).

(** The error of one halving, scaled by one. *)
Definition eh : nat := 16 * m + 28.

Lemma realisesN_le (d : nat) (C : {set {set G}}) (Y : nat) (V : 'I_m -> nat)
    (E E' : nat) :
  realisesN d C Y V E -> E <= E' -> realisesN d C Y V E'.
Proof.
move=> [h1 h2] hE; split.
  by apply: leq_trans h1 _; rewrite leq_add2l.
by move=> i; apply: leq_trans (h2 i) _; rewrite leq_add2l.
Qed.

Lemma realisesN_scale (c d : nat) (C : {set {set G}}) (Y : nat) (V : 'I_m -> nat)
    (E : nat) :
  realisesN d C Y V E ->
  realisesN (c * d) C (c * Y) (fun i => c * V i) (c * E).
Proof.
move=> [h1 h2]; split.
  rewrite -mulnA -mulnDr leq_mul2l; apply/orP; right; exact: h1.
move=> i; rewrite -mulnA -mulnDr leq_mul2l; apply/orP; right; exact: (h2 i).
Qed.

Lemma realisesN_drift (d : nat) (C : {set {set G}}) (Y Y' : nat)
    (V V' : 'I_m -> nat) (E D : nat) :
  realisesN d C Y V E -> Y' <= Y + D -> (forall i, V i <= V' i + D) ->
  realisesN d C Y' V' (E + D).
Proof.
move=> [h1 h2] hY hV; split.
  by apply: leq_trans hY _; rewrite addnA leq_add2r.
by move=> i; apply: (drift_arith (h2 i) (hV i)).
Qed.

(** ** Halving *)

Lemma mix_half (A B : {set {set G}}) (d YA YB : nat) (VA VB : 'I_m -> nat)
    (EA EB : nat) :
  matching A -> matching B ->
  realisesN d A YA VA EA -> realisesN d B YB VB EB ->
  exists C, matching C /\
    realisesN (2 * d) C (YA + YB) (fun i => VA i + VB i) (EA + EB + d * eh).
Proof.
move=> hmA hmB [hA1 hA2] [hB1 hB2].
have [C [hmC hsubC hsize hstat]] := @matching_halving G f A B m W bipf hmA hmB.
have hsized : d * (#|A| + #|B|) <= d * (2 * #|C| + (16 * m + 28)).
  by rewrite leq_mul2l hsize orbT.
exists C; split=> //; split.
  by rewrite /eh; apply: (half_arith_size hA1 hB1 hsized).
move=> i.
have hstatd : d * (2 * #|C :&: W i|) <= d * (#|A :&: W i| + #|B :&: W i| + (8 * m + 16)).
  by rewrite leq_mul2l (hstat i) orbT.
apply: (leq_trans (half_arith_stat (hA2 i) (hB2 i) hstatd)).
rewrite leq_add2l leq_add2l leq_mul2l /eh; apply/orP; right.
by apply: leq_add; rewrite ?leq_mul2r ?orbT.
Qed.

Lemma realisesN_ext (d d' : nat) (C : {set {set G}}) (Y Y' : nat)
    (V V' : 'I_m -> nat) (E E' : nat) :
  realisesN d C Y V E -> d = d' -> Y' = Y -> V =1 V' -> E = E' ->
  realisesN d' C Y' V' E'.
Proof.
by move=> [h1 h2] <- -> hV <-; split=> // i; rewrite -hV; exact: h2.
Qed.

(** ** Any dyadic ratio, by chaining halvings *)

Lemma mix_dyadic (L : nat) (A B : {set {set G}}) (d YA YB : nat)
    (VA VB : 'I_m -> nat) (E : nat) :
  matching A -> matching B ->
  realisesN d A YA VA E -> realisesN d B YB VB E ->
  forall k : nat, k <= 2^L ->
  exists C, matching C /\
    realisesN (2^L * d) C (k * YA + (2^L - k) * YB)
              (fun i => k * VA i + (2^L - k) * VB i) (2^L * (E + d * eh)).
Proof.
move=> hmA hmB hA hB; elim: L => [|L IH] k hk.
  move: hk; rewrite expn0 !mul1n => hk.
  case: (posnP k) => [->|hk0].
    exists B; split=> //.
    apply: (realisesN_le (E := E)); last by rewrite leq_addr.
    apply: (realisesN_ext hB) => // [|i]; first by rewrite mul0n add0n subn0 mul1n.
    by rewrite mul0n add0n subn0 mul1n.
  have hk1 : k = 1 by apply/eqP; rewrite eqn_leq hk hk0.
  exists A; split=> //.
  apply: (realisesN_le (E := E)); last by rewrite leq_addr.
  apply: (realisesN_ext hA) => // [|i]; first by rewrite hk1 mul1n subnn mul0n addn0.
  by rewrite hk1 mul1n subnn mul0n addn0.
have hexp : 2^(L.+1) = 2 * 2^L by rewrite expnS.
case: (leqP k (2^L)) => hkL.
  have [C' [hmC' hC']] := IH k hkL.
  have [C [hmC hC]] := mix_half hmB hmC' (realisesN_scale (2^L) hB) hC'.
  exists C; split=> //.
  apply: (realisesN_ext hC).
  - by rewrite hexp mulnA.
  - by rewrite hexp dyad_lo.
  - by move=> i; rewrite hexp dyad_lo.
  - by rewrite hexp dyad_err.
have hk' : k - 2^L <= 2^L.
  by rewrite leq_subLR addnn -mul2n -hexp.
have hkeq : k = 2^L + (k - 2^L) by rewrite subnKC // ltnW.
have [C' [hmC' hC']] := IH (k - 2^L) hk'.
have [C [hmC hC]] := mix_half hmA hmC' (realisesN_scale (2^L) hA) hC'.
exists C; split=> //.
apply: (realisesN_ext hC).
- by rewrite hexp mulnA.
- by rewrite hexp (dyad_hi hk' hkeq).
- by move=> i; rewrite hexp (dyad_hi hk' hkeq).
- by rewrite hexp dyad_err.
Qed.

(** ** Any convex combination of a list of matchings *)

Lemma realisesN_conv (d d' : nat) (C : {set {set G}}) (Y Y' : nat)
    (V V' : 'I_m -> nat) (E E' X : nat) :
  0 < d -> realisesN d C Y V E ->
  d * Y' <= d' * Y + X -> (forall i, d' * V i <= d * V' i + X) ->
  d' * E + X <= d * E' ->
  realisesN d' C Y' V' E'.
Proof.
move=> hd [h1 h2] hY hV hE; split.
  rewrite -(leq_pmul2l hd).
  apply: (leq_trans hY).
  apply: (leq_trans (_ : d' * Y + X <= d' * (d * #|C| + E) + X)).
    by rewrite leq_add2r leq_mul2l h1 orbT.
  rewrite !mulnDr -addnA; apply: leq_add; last exact: hE.
  by rewrite mulnCA.
move=> i; rewrite -(leq_pmul2l hd) mulnDr.
apply: (leq_trans (_ : d * (d' * #|C :&: W i|) <= d' * (V i + E))).
  by rewrite mulnCA leq_mul2l (h2 i) orbT.
rewrite mulnDr.
apply: (leq_trans (_ : d' * V i + d' * E <= d * V' i + X + d' * E)).
  by rewrite leq_add2r; exact: hV.
by rewrite -addnA [X + d' * E]addnC leq_add2l; exact: hE.
Qed.

Lemma mix_list (N : nat) (s : seq ({set {set G}} * nat)) :
  (forall p, p \in s -> matching p.1) ->
  (forall p, p \in s -> #|p.1| <= N) ->
  (forall p i, p \in s -> #|p.1 :&: W i| <= N) ->
  0 < \sum_(p <- s) p.2 ->
  exists C, matching C /\
    realisesN (\sum_(p <- s) p.2) C (\sum_(p <- s) p.2 * #|p.1|)
              (fun i => \sum_(p <- s) p.2 * #|p.1 :&: W i|)
              ((\sum_(p <- s) p.2) * ((size s).-1 * (eh + 1))).
Proof.
elim: s => [|p s IH]; first by rewrite big_nil ltnn.
move=> hm hN hNi; rewrite !big_cons /= => hsum.
have hmp : matching p.1 by apply: hm; rewrite inE eqxx.
have hNp : #|p.1| <= N by apply: hN; rewrite inE eqxx.
have hNpi : forall i, #|p.1 :&: W i| <= N by move=> i; apply: hNi; rewrite inE eqxx.
have hbase1 : realisesN 1 p.1 #|p.1| (fun i => #|p.1 :&: W i|) 0.
  by split=> [|i]; rewrite mul1n addn0.
have hbase : realisesN p.2 p.1 (p.2 * #|p.1|)
                      (fun i => p.2 * #|p.1 :&: W i|) 0.
  apply: (realisesN_ext (realisesN_scale p.2 hbase1)); rewrite ?muln1 ?muln0 //.
case: (posnP (\sum_(q <- s) q.2)) => [hL0|hL].
  have hz : \sum_(q <- s) q.2 * #|q.1| = 0.
    apply: big1_seq => q /andP[_ hq]; apply/eqP; rewrite muln_eq0; apply/orP; left.
    by move: hL0 => /eqP; rewrite sum_nat_seq_eq0 => /allP/(_ q hq).
  have hzi : forall i, \sum_(q <- s) q.2 * #|q.1 :&: W i| = 0.
    move=> i; apply: big1_seq => q /andP[_ hq]; apply/eqP.
    rewrite muln_eq0; apply/orP; left.
    by move: hL0 => /eqP; rewrite sum_nat_seq_eq0 => /allP/(_ q hq).
  exists p.1; split=> //.
  apply: (realisesN_le (E := 0)); last by [].
  apply: (realisesN_ext hbase).
  - by rewrite hL0 addn0.
  - by rewrite hz addn0.
  - by move=> i; rewrite big_cons hzi addn0.
  - by [].
have hmS : forall q, q \in s -> matching q.1 by move=> q hq; apply: hm; rewrite inE hq orbT.
have hNS : forall q, q \in s -> #|q.1| <= N by move=> q hq; apply: hN; rewrite inE hq orbT.
have hNSi : forall q i, q \in s -> #|q.1 :&: W i| <= N.
  by move=> q i hq; apply: hNi; rewrite inE hq orbT.
have [C' [hmC' hC']] := IH hmS hNS hNSi hL.
set a := p.2; set L' := \sum_(q <- s) q.2.
set S' := \sum_(q <- s) q.2 * #|q.1|.
set E' := L' * ((size s).-1 * (eh + 1)).
set Lam := a + L'.
have hLam : 0 < Lam by rewrite /Lam addn_gt0 hL orbT.
have h2N : 0 < 2^N by rewrite expn_gt0.
set k := (L' * 2^N) %/ Lam.
set j := 2^N - k.
have hkle : k <= 2^N.
  have h1 : L' * 2^N <= Lam * 2^N.
    by rewrite leq_mul2r /Lam leq_addl orbT.
  by rewrite /k -{2}(mulKn (2^N) hLam); apply: leq_div2r.
have hkj : k + j = 2^N by rewrite /j subnKC.
have hk1 : Lam * k <= L' * 2^N.
  by rewrite mulnC /k leq_divM.
have hk2 : L' * 2^N < Lam * k + Lam.
  by rewrite -mulnSr [Lam * k.+1]mulnC /k ltn_ceil.
have hbaseL : realisesN L' p.1 (L' * #|p.1|) (fun i => L' * #|p.1 :&: W i|) E'.
  apply: (realisesN_le (E := 0)); last by [].
  by apply: (realisesN_ext (realisesN_scale L' hbase1)); rewrite ?muln1 ?muln0.
have [C [hmC hC]] := mix_dyadic hmC' hmp hC' hbaseL hkle.
have hsizes : 0 < size s.
  by rewrite lt0n size_eq0; apply/eqP => h0; move: hL; rewrite h0 big_nil ltnn.
have hNexp : N <= 2^N by apply: ltnW; apply: ltn_expl.
set u := L' * 2^N - Lam * k.
have hu : j * L' = a * k + u.
  rewrite /u /j /Lam mulnBl mulnDl [k * L']mulnC [2 ^ N * L']mulnC.
  by apply: sub_id; move: hk1; rewrite /Lam mulnDl.
have hua : u <= a + L'.
  by rewrite /u -/Lam; apply: sub_le; exact: ltnW.
have hSN : S' <= L' * N.
  rewrite /S' /L' big_distrl /=.
  rewrite big_seq_cond [X in _ <= X]big_seq_cond.
  apply: leq_sum => q /andP[hq _].
  by rewrite leq_mul2l hNS ?orbT.
have hSNi : forall i, #|p.1 :&: W i| <= N by [].
exists C; split=> //.
have hd : 0 < 2^N * L' by rewrite muln_gt0 h2N hL.
apply: (realisesN_conv (X := Lam * L' * N) hd hC).
- rewrite -/j -hkj mulnA -/S'.
  exact: (key_arith hu hua hSN).
- move=> i; rewrite big_cons -/j -hkj mulnA.
  by apply: (key_arith2 hu hua); exact: hNpi.
- have hsz : size s * (eh + 1) = (size s).-1 * (eh + 1) + (eh + 1).
    by rewrite -{1}(prednK hsizes) mulSnr.
  rewrite /E' hsz.
  apply: hE_arith.
  by rewrite leq_mul2l hNexp orbT.
Qed.

End Mixing.

(** ** The colour classes of a line colouring, as a family indexed by ['I_D] *)

Section Assembly.
Variables (G : sgraph) (f : G -> bool) (m : nat) (E : 'I_m -> {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis subE : forall i : 'I_m, E i \subset E(G).
Variable D : nat.
Hypothesis D_gt0 : 0 < D.
Hypothesis D_deg : forall v : G, #|N(v)| <= D.

Variable col : {set G} -> nat.
Hypothesis col_lt : forall e : {set G}, e \in E(G) -> col e < D.
Hypothesis col_match : forall j : nat, matching [set e in E(G) | col e == j].

Definition cls (j : 'I_D) : {set {set G}} := [set e in E(G) | col e == val j].

Lemma cls_matching (j : 'I_D) : matching (cls j).
Proof. exact: col_match. Qed.

Lemma cls_sub (j : 'I_D) : cls j \subset E(G).
Proof. by apply/subsetP => e; rewrite inE => /andP[]. Qed.

(** The colour classes partition [E(G)], hence partition every [X \subset E(G)]. *)
Lemma cls_card (X : {set {set G}}) (j : 'I_D) :
  #|X :&: cls j| = \sum_(e in X) (e \in cls j : nat).
Proof.
rewrite -sum1_card big_mkcond /= [RHS]big_mkcond /=.
by apply: eq_bigr => e _; rewrite inE; case: (e \in X); case: (e \in cls j).
Qed.

Lemma cls_uniq (e : {set G}) : e \in E(G) -> \sum_(j < D) (e \in cls j : nat) = 1.
Proof.
move=> he.
rewrite (bigD1 (Ordinal (col_lt he))) //= big1 ?addn0.
  by rewrite !inE he eqxx.
move=> j hj; apply/eqP; rewrite eqb0 !inE he /=.
by apply: contra hj => /eqP hcol; apply/eqP/val_inj.
Qed.

Lemma cls_partition (X : {set {set G}}) :
  X \subset E(G) -> \sum_(j < D) #|X :&: cls j| = #|X|.
Proof.
move=> hX.
rewrite (eq_bigr _ (fun j _ => cls_card X j)) exchange_big /=.
rewrite -sum1_card big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => e _.
case: (boolP (e \in X)) => heX //=.
by rewrite (cls_uniq (subsetP hX _ heX)).
Qed.

(** ** Reducing to at most [m+2] colour classes *)

Definition zstat (j : 'I_D) (l : 'I_m.+1) : nat :=
  if unlift ord0 l is Some i then #|cls j :&: E i| else #|cls j|.

Definition wone (j : 'I_D) : nat := 1.

Lemma sum_wone : \sum_(j < D) wone j = D.
Proof. by rewrite sum1_card card_ord. Qed.

Lemma sum_zstat (l : 'I_m.+1) :
  \sum_(j < D) wone j * zstat j l
  = if unlift ord0 l is Some i then #|E i| else #|E(G)|.
Proof.
rewrite (eq_bigr (fun j => zstat j l)); last by move=> j _; rewrite mul1n.
rewrite /zstat; case: (unlift ord0 l) => [i|].
  rewrite -(cls_partition (subE i)).
  by apply: eq_bigr => j _; rewrite setIC.
rewrite -(cls_partition (subxx E(G))).
apply: eq_bigr => j _.
have -> : E(G) :&: cls j = cls j by apply/setIidPr; exact: cls_sub.
by [].
Qed.

(** ** The approximate fair matching *)

Definition Bmix : nat := m.+1 * (16 * m + 29).

Theorem approx_fair_core :
  exists C : {set {set G}},
    [/\ matching C,
        #|E(G)| %/ D <= #|C| + Bmix &
        forall i : 'I_m, #|C :&: E i| <= #|E i| %/ D + Bmix].
Proof.
have hw : 0 < \sum_(j < D) wone j by rewrite sum_wone.
have [a [hapos hasupp haeq]] := caratheodory_nat zstat hw.
pose s : seq ({set {set G}} * nat) := [seq (cls j, a j) | j <- enum 'I_D & a j != 0].
have hmatch : forall p, p \in s -> matching p.1.
  by move=> p /mapP[j _ ->]; exact: cls_matching.
have hNb : forall p, p \in s -> #|p.1| <= #|E(G)|.
  by move=> p /mapP[j _ ->]; apply: subset_leq_card; exact: cls_sub.
have hNbi : forall p (i : 'I_m), p \in s -> #|p.1 :&: E i| <= #|E(G)|.
  move=> p i /mapP[j _ ->]; apply: subset_leq_card => /=.
  by apply: (subset_trans (subsetIl _ _)); exact: cls_sub.
have hsum2 : \sum_(p <- s) p.2 = \sum_(j < D) a j.
  rewrite /s big_map big_filter big_enum_cond /= [RHS](bigID (fun j => a j != 0)) /=.
  rewrite [X in _ + X]big1 ?addn0 // => j.
  by rewrite negbK => /eqP.
have hsumY : \sum_(p <- s) p.2 * #|p.1| = \sum_(j < D) a j * #|cls j|.
  rewrite /s big_map big_filter big_enum_cond /= [RHS](bigID (fun j => a j != 0)) /=.
  rewrite [X in _ + X]big1 ?addn0 // => j.
  by rewrite negbK => /eqP ->; rewrite mul0n.
have hsumV : forall i : 'I_m,
    \sum_(p <- s) p.2 * #|p.1 :&: E i| = \sum_(j < D) a j * #|cls j :&: E i|.
  move=> i; rewrite /s big_map big_filter big_enum_cond /= [RHS](bigID (fun j => a j != 0)) /=.
  rewrite [X in _ + X]big1 ?addn0 // => j.
  by rewrite negbK => /eqP ->; rewrite mul0n.
have hsumpos : 0 < \sum_(p <- s) p.2 by rewrite hsum2.
have hcount : forall (T : finType) (P : pred T),
    #|[set t | P t]| = count P (enum T).
  move=> T P; rewrite cardsE cardE /enum_mem -enumT size_filter.
  by rewrite filter_predT.
have hsize : size s <= m.+2.
  apply: (leq_trans _ hasupp).
  by rewrite /s size_map size_filter hcount.
have hB0 : (size s).-1 * (eh m + 1) <= Bmix.
  rewrite /Bmix /eh -addnA; apply: leq_mul; last by [].
  by rewrite -subn1 -[m.+1]/(m.+2 - 1) leq_sub2r.
have hz0 : forall j, zstat j ord0 = #|cls j|.
  by move=> j; rewrite /zstat unlift_none.
have hzi : forall j (i : 'I_m), zstat j (lift ord0 i) = #|cls j :&: E i|.
  by move=> j i; rewrite /zstat liftK.
have hzsum0 : \sum_(j < D) a j * zstat j ord0 = \sum_(j < D) a j * #|cls j|.
  by apply: eq_bigr => j _; rewrite hz0.
have hzsumi : forall i : 'I_m,
    \sum_(j < D) a j * zstat j (lift ord0 i)
    = \sum_(j < D) a j * #|cls j :&: E i|.
  by move=> i; apply: eq_bigr => j _; rewrite hzi.
have h0 : (\sum_(j < D) a j * #|cls j|) * D = #|E(G)| * (\sum_(j < D) a j).
  move: (haeq ord0).
  by rewrite hzsum0 sum_wone (sum_zstat ord0) unlift_none /= => ->.
have hi : forall i : 'I_m,
    (\sum_(j < D) a j * #|cls j :&: E i|) * D = #|E i| * (\sum_(j < D) a j).
  move=> i; move: (haeq (lift ord0 i)).
  by rewrite (hzsumi i) sum_wone (sum_zstat (lift ord0 i)) liftK /= => ->.
have hL : 0 < \sum_(j < D) a j by rewrite -hsum2.
have [C [hmC hC]] := mix_list bipf hmatch hNb hNbi hsumpos.
case: hC => hY hV.
rewrite hsumY hsum2 in hY.
exists C; split => //.
  have hYB : \sum_(j < D) a j * #|cls j|
           <= (\sum_(j < D) a j) * #|C| + (\sum_(j < D) a j) * Bmix.
    apply: leq_trans hY _; rewrite leq_add2l.
    by apply: leq_mul.
  have keyA : #|E(G)| <= (#|C| + Bmix) * D.
    rewrite -(leq_pmul2l hL) [X in X <= _]mulnC -h0 mulnA mulnDr.
    by rewrite leq_pmul2r.
  apply: leq_trans (leq_div2r D keyA) _.
  by rewrite mulnK.
move=> i; move: (hV i); rewrite (hsumV i) hsum2 => hVi.
have hVB : (\sum_(j < D) a j) * #|C :&: E i|
         <= \sum_(j < D) a j * #|cls j :&: E i| + (\sum_(j < D) a j) * Bmix.
  apply: leq_trans hVi _; rewrite leq_add2l.
  by apply: leq_mul.
have keyB : #|C :&: E i| * D <= #|E i| + Bmix * D.
  rewrite -(leq_pmul2l hL) mulnA mulnDr [X in _ + X]mulnA.
  have -> : (\sum_(j < D) a j) * #|E i|
          = (\sum_(j < D) a j * #|cls j :&: E i|) * D.
    by rewrite (hi i) mulnC.
  by rewrite -mulnDl leq_pmul2r.
rewrite addnC -leq_subLR leq_divRL // mulnBl leq_subLR addnC.
exact: keyB.
Qed.

End Assembly.

(** ** The approximate fair matching, in the vocabulary of [X15] *)

Theorem x15_approx_fair_proof (m : nat) : x15_approx_fair m (Bmix m).
Proof.
move=> G E [f fP] dpos famE.
have D_deg (v : G) : #|N(v)| <= Delta G by exact: leq_bigmax.
have [col [col_lt col_match]] := line_colouring_E fP D_deg.
have subE (i : 'I_m) : E i \subset E(G).
  by move: (famE i); rewrite x15_edge_setE.
have [C [mC hsz hcl]] := approx_fair_core fP subE dpos col_lt col_match.
exists C; split; first exact: matching_x15.
split; first by rewrite x15_edge_setE.
move=> i; apply: leq_trans (hcl i) _; rewrite leq_add2r.
by rewrite /ceil_div; apply: leq_div2r; rewrite -addnBA // leq_addr.
Qed.

Lemma Bmix_le (m : nat) : Bmix m <= 32 * (m + 1)^2.
Proof.
have h1 : 0 < m + 1 by rewrite addn1.
rewrite /Bmix -addn1 expnS expn1 mulnCA leq_pmul2l //.
by rewrite -!plusE -!multE; apply/leP; lia.
Qed.

Theorem x15_llm_proof : bipartite_matching_underrepresentation_llm_statement.
Proof.
apply: x15_approx_fair_llm => m G E bipG dpos famE.
have [C [mC [sC fC]]] := @x15_approx_fair_proof m G E bipG dpos famE.
exists C; split => //; split.
  by apply: leq_trans sC _; rewrite leq_add2l Bmix_le.
by move=> i; apply: leq_trans (fC i) _; rewrite leq_add2l Bmix_le.
Qed.

(** The constant this development actually reaches, one factor [m+1] below the
    [32(m+1)^3] claimed by the attack: [Bmix m] on the approximate fair matching
    of [x15_approx_fair_proof], times [m+1] for the trimming. *)
Theorem x15_llm2_proof : bipartite_matching_underrepresentation_llm2_statement.
Proof.
move=> m; exists ((m + 1) * Bmix m); split.
  by rewrite /Bmix expnS expn1 -mulnA !addn1.
move=> G E bipG dpos famE.
exact: x15_trim_instance (@x15_approx_fair_proof m G E bipG dpos famE).
Qed.

(** Conjecture 1.15 itself, without the explicit constant. *)
Corollary bipartite_matching_underrepresentation :
  bipartite_matching_underrepresentation_statement.
Proof. by move=> m; have [c [_ hc]] := x15_llm_proof m; exists c. Qed.

Print Assumptions x15_big_matching.
Print Assumptions trim_exists.
Print Assumptions x15_approx_fair_llm.
Print Assumptions x15_llm_instance0.
Print Assumptions x15_approx_fair_proof.
Print Assumptions x15_llm_proof.
Print Assumptions x15_llm2_proof.
Print Assumptions bipartite_matching_underrepresentation.
