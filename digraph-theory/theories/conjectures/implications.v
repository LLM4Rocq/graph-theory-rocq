(** * Digraph.conjectures.implications — §7 dependency-graph EDGES

    Machine-checked implication edges between the committed conjecture statements.
    Each edge is a *relative* theorem: it is provable WITHOUT resolving (proving or
    refuting) any of the conjectures it relates — it only transports one conjectural
    hypothesis to another. So, unlike the [_statement] Definitions (which are merely
    typed [Prop]s), this layer is genuine [Qed]-closed content.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §7 (deliverable 2).

    Edges proved here:
      - [caccetta_haggkvist_implies_triangle]
            Caccetta–Häggkvist (general) ⟹ the famous triangle case.
            Instantiate CH at r = ⌈n/3⌉ = (n+2)%/3: min out-degree ≥ n/3 gives
            r ≤ δ⁺, and the returned cycle has length ≤ ⌈n/⌈n/3⌉⌉ ≤ 3; in an oriented
            graph every dicycle has length ≥ 3 ([oriented_dicycle_size_ge3]), so it is
            exactly a directed triangle.
      - [conj_4_2_implies_conj_4_4]
            Conjecture 4.2 (hero dichotomy) ⟹ Conjecture 4.4, at H = TT l (a transitive
            tournament — the right disjunct of the dichotomy). The bridge [hero (TT l)]
            is carried as an explicit hypothesis (the inductive [hero] predicate is up to
            the exact carrier type, so "transitive tournaments are heroes" is not provable
            here without an up-to-iso closure; keeping it a hypothesis stays Qed-closed).
            The class inclusion [no_induced_Kl l ⊆ ind_free (TT l)] (forbidding *every*
            orientation of K_l is stronger than forbidding the single transitive one)
            restricts the 4.2-bound down to the 4.4-class.

    Supporting (Qed-closed) bridge lemmas:
      - [noKl_implies_indfree_TT] : no_induced_Kl l D -> ind_free (TT l) D.
      - [transitive_tournament_TT] : transitive_tournament (TT l). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory.
From Digraph Require Import digraph oriented tournament dipath strong.
From Digraph Require Import dichromatic heroes heroes_dichotomy.
From Digraph Require Import classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edge 1: Caccetta–Häggkvist (general) ⟹ the triangle case *)

(** Two arithmetic facts about r = ⌈n/3⌉ = (n+2)%/3, isolated for clarity. *)

(** With n ≤ 3·δ⁺, the threshold ⌈n/3⌉ is at most the out-degree δ⁺. *)
Lemma ceil_div3_le n o : n <= 3 * o -> (n + 2) %/ 3 <= o.
Proof.
move=> h; apply: leq_trans (_ : (o * 3 + 2) %/ 3 <= o).
  by rewrite leq_div2r // -mulnC leq_add2r.
by rewrite divnMDl // divn_small // addn0.
Qed.

(** With n ≤ 3·r and r > 0, the CH bound ⌈n/r⌉ = (n+r−1)%/r is at most 3. *)
Lemma ch_bound_le3 n r : 0 < r -> n <= 3 * r -> (n + r - 1) %/ r <= 3.
Proof.
move=> r0 h; rewrite -ltnS ltn_divLR //.
apply: leq_ltn_trans (_ : 3 * r + r - 1 < 4 * r).
  by rewrite leq_sub2r // leq_add2r.
have e : 3 * r + r = 4 * r by rewrite -mulSnr.
rewrite e; have : 0 < 4 * r by rewrite muln_gt0.
by case: (4 * r) => // m _; rewrite subSS ltnS leq_subr.
Qed.

(** ⌈n/3⌉ is positive whenever n is. *)
Lemma ceil_div3_gt0 n : 0 < n -> 0 < (n + 2) %/ 3.
Proof. by move=> n0; rewrite divn_gt0 // -[3]/(1 + 2) leq_add2r. Qed.

(** n is at most 3·⌈n/3⌉ (so r = ⌈n/3⌉ feeds n ≤ 3·r into [ch_bound_le3]). *)
Lemma n_le_3_ceil_div3 n : n <= 3 * ((n + 2) %/ 3).
Proof.
have e := divn_eq (n + 2) 3; have hm : (n + 2) %% 3 < 3 by rewrite ltn_mod.
rewrite mulnC; move: e hm; set q := (n + 2) %/ 3; set s := (n + 2) %% 3 => e hm.
have : n + 2 <= q * 3 + 2 by rewrite e leq_add2l -ltnS.
by rewrite leq_add2r.
Qed.

(** Caccetta–Häggkvist (general loopless-digraph form) ⟹ the triangle case.
    An oriented graph with δ⁺ ≥ n/3 has a directed cycle of length ≤ ⌈n/⌈n/3⌉⌉ ≤ 3;
    being oriented it has no loop and no digon, so that cycle has length ≥ 3, hence = 3. *)
Theorem caccetta_haggkvist_implies_triangle :
  caccetta_haggkvist_statement -> caccetta_haggkvist_triangle_statement.
Proof.
move=> CH D Dn Hdeg.
set r := (#|D| + 2) %/ 3.
have r0 : (0 < r)%N by exact: ceil_div3_gt0.
(* the oriented graph D, viewed as a loopless digraph, has min out-degree ≥ r *)
have noloop : forall v : D, ~~ (v --> v) by move=> v; rewrite arc_irrefl.
have rdeg : forall v : D, (r <= outdeg v)%N.
  by move=> v; apply: ceil_div3_le; exact: Hdeg.
have [c [dc szle]] := CH D r Dn noloop r0 rdeg.
(* lower bound: an oriented dicycle has length ≥ 3 *)
have szge := oriented_dicycle_size_ge3 dc.
(* upper bound: ⌈n/r⌉ ≤ 3 since n ≤ 3·r (= 3·⌈n/3⌉) *)
have n3r : (#|D| <= 3 * r)%N by rewrite /r; exact: n_le_3_ceil_div3.
have szle3 : (size c <= 3)%N.
  by apply: leq_trans szle _; apply: ch_bound_le3.

by exists c; split=> //; apply/eqP; rewrite eqn_leq szle3 szge.
Qed.

(** ** Edge 2: hero dichotomy (Conj 4.2) ⟹ Conj 4.4 *)

(** Bridge A: a transitive tournament [TT l] satisfies the right disjunct of the
    dichotomy. (Irreflexive + total + asymmetric = tournament; [<] is transitive.) *)
Lemma transitive_tournament_TT (l : nat) : transitive_tournament (TT l).
Proof.
split.
- split.
  + exact: (@TT_irrefl l).
  + by move=> u v; exact: arc_or.
  + by move=> u v; exact: arc_asym.
- by apply/transbP; exact: TT_transb.
Qed.

(** Bridge B (class inclusion): forbidding *every* orientation of K_l is stronger than
    forbidding the single transitive tournament TT_l. An induced copy of [TT l] is l
    pairwise-adjacent vertices (the embedding reflects arcs, and a tournament is
    semicomplete), i.e. a K_l — so no_induced_Kl rules out the TT_l copy as well. *)
Lemma noKl_implies_indfree_TT (l : nat) (D : diGraphType) :
  no_induced_Kl l D -> ind_free (TT l) D.
Proof.
move=> noK [f [finj farc]]; apply: noK.
exists [set f u | u : TT l]; split.
  by rewrite card_imset // card_TT.
move=> u v /imsetP[a _ ->] /imsetP[b _ ->] hne.
have ab : a != b by apply: contra hne => /eqP->.
by rewrite !farc; exact: arc_or.
Qed.

(** Conjecture 4.2 (hero dichotomy) ⟹ Conjecture 4.4.
    Instantiate 4.2 at H = TT l: it is a hero (carried hypothesis) and a transitive
    tournament (Bridge A), so the right disjunct holds and the ⟺ delivers a dichromatic
    bound for the class {oriented, ind_free (TT l), ind_free F}. The 4.4-class
    {oriented, no_induced_Kl l, ind_free F} is contained in it (Bridge B), so the same
    bound dicolours every 4.4-member. *)
Theorem conj_4_2_implies_conj_4_4 :
  (forall l : nat, hero (TT l)) ->     (* "transitive tournaments are heroes" — Berger *)
  conj_4_2 -> conj_4_4.
Proof.
move=> heroTT C42 F l Ffor.
have hH : hero (TT l) by exact: heroTT.
have [B HB] := (C42 (TT l) F hH Ffor).2 (or_intror (transitive_tournament_TT l)).
exists B => D [Dor noK Ffree].
apply: HB; split=> //.
by apply: noKl_implies_indfree_TT.
Qed.

(** ** Edge 3: a faithful specialization within the heroes corpus.

    Conjecture 6.2 (the C₃ / S₂⁺ beachhead) and Theorem 6.1 (the C₃ / →K₂+K₁ landmark)
    share the same conclusion; whenever a digraph satisfies BOTH forbidden-pattern
    hypotheses, either statement applied to it yields 2-dicolourability. This records the
    trivial "either premise suffices on the common subclass" edge (Qed-closed). *)
Theorem conj_6_2_or_thm_6_1_on_common :
  (conj_6_2 \/ thm_6_1) ->
  forall D : diGraphType,
    oriented_dg D -> no_induced_C3 D ->
    no_induced_S2plus D -> no_induced_arrowK2_K1 D -> dicolorableb D 2.
Proof.
by move=> [H|H] D Dor c3 s2 ak; [exact: H | exact: H].
Qed.
