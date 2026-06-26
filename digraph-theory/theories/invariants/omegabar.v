(** * Digraph.omegabar — the clique number of a tournament

    ω̄(T) is the minimum, over all vertex orders [p : {perm T}], of the clique
    number ω of the backedge graph [backedge p] (Aboulker–Aubian–Charbit–Lopes,
    arXiv:2310.04265, §2; docs/DESIGN.md §5). The minimum is taken with
    mathcomp's [arg min] over the (nonempty) finType [{perm T}].

    Main results here:
    - [omegabar_min], [omegabar_witness]: ω̄ is a realized minimum;
    - [omegabar_gt0]: ω̄ ≥ 1 on nonempty tournaments;
    - [omegabar_transb]: ω̄(T) = 1 iff T is transitive (for T nonempty) — in
      particular [omegabar_TT]: ω̄(TTₙ) = 1;
    - [omegabar_sub]: monotonicity under sub-tournaments (hence deletion);
    - [omegabar_C3]: ω̄(C3) = 2.

    Cross-checked against the exact Python oracle (scripts/core.py):
    ω̄(C3) = 2, ω̄(TT₄) = 1. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definition *)

Definition omegab_at (T : tournament) (p : {perm T}) : nat :=
  ω([set: backedge p]).

Definition omegabar (T : tournament) : nat :=
  omegab_at [arg min_(p < (1%g : {perm T})) omegab_at p].

Notation "ω̄( T )" := (omegabar T) (at level 0, format "ω̄( T )").

(** ** ω̄ is a realized minimum *)

Section OmegaBarBasics.
Variable T : tournament.

Lemma omegabar_min (p : {perm T}) : ω̄(T) <= omegab_at p.
Proof. by rewrite /omegabar; case: arg_minnP => // q _; apply. Qed.

Lemma omegabar_witness : {p : {perm T} | ω̄(T) = omegab_at p}.
Proof. by rewrite /omegabar; eexists. Qed.

Lemma omegabar_gt0 : 0 < #|T| -> 0 < ω̄(T).
Proof.
case/card_gt0P=> x _; have [p ->] := omegabar_witness.
by apply: omega_ge1; apply/set0Pn; exists x; rewrite inE.
Qed.

(** ** ω̄ = 1 characterizes transitivity *)

Lemma omegab_at_le1 (p : {perm T}) :
  (forall u v : T, u --> v -> ltp p u v) -> omegab_at p <= 1.
Proof.
move=> fwd; apply: omega_le1 => u v _ _.
exact: backedge_arc_forward.
Qed.

Lemma omegabar_le1 : transb T -> ω̄(T) <= 1.
Proof.
move/transbP=> tr.
have arc_irr : irreflexive (arc : rel T) := @arcxx T.
have arc_tot (u v : T) : u != v -> (u --> v) || (v --> u) := @arc_or T u v.
pose q := realize (arc : rel T).
have fwd (u v : T) : u --> v -> ltp q u v.
  by rewrite (ltp_realizeE arc_irr tr arc_tot).
exact: leq_trans (omegabar_min q) (omegab_at_le1 fwd).
Qed.

Lemma omegabar_transb : 0 < #|T| -> (ω̄(T) == 1) = transb T.
Proof.
move=> T0; apply/idP/idP => [/eqP ob1 | /omegabar_le1 le1]; last first.
  by rewrite eqn_leq le1 omegabar_gt0.
have [p obp] := omegabar_witness.
(* ω(backedge p) = 1: the backedge graph is edgeless *)
have noedge (u v : backedge p) : ~~ (u -- v).
  apply/negP=> uv; have := omega_ge2 (in_setT u) (in_setT v) uv.
  by rewrite -[ω(_)]/(omegab_at p) -obp ob1.

(* hence every arc points forward w.r.t. p *)
have fwd (u v : T) : u --> v -> ltp p u v.
  move=> auv; have uDv := arc_neq auv.
  have /orP[//|vltu] := ltp_total p uDv.
  have /negP[] := noedge v u.
  by rewrite backedgeE vltu auv.
(* arcs forward along a strict order are transitive *)
apply/transbP=> y x z xy yz.
have xDz : x != z.
  apply: contraTneq xy => xz; rewrite -xz in yz.
  exact: arc_asym yz.
have /orP[//|zx] := arc_or xDz.
have := ltp_asym (ltp_trans (fwd _ _ xy) (fwd _ _ yz)).
by rewrite (fwd _ _ zx).
Qed.

End OmegaBarBasics.

(** ** Monotonicity under arc-preserving embeddings

    Any injective map that reflects arcs both ways pushes ω̄ up: the witness
    order on the big tournament pulls back along the embedding
    ([ltp_pullback]) and the backedge graphs correspond edge-for-edge. *)

Lemma omegabar_embed (T1 T2 : tournament) (f : T1 -> T2) :
  injective f -> (forall u v, (f u --> f v) = (u --> v)) ->
  ω̄(T1) <= ω̄(T2).
Proof.
move=> inj_f arcE.
have [p obp] := omegabar_witness T2; rewrite obp.
have [q qE] := @ltp_pullback _ _ f p inj_f.
apply: (leq_trans (omegabar_min q)).
rewrite /omegab_at.
have h_hom : {in [set: backedge q] &,
    forall u v : backedge q, u -- v -> (f u : backedge p) -- (f v)}.
  by move=> u v _ _; rewrite !backedgeE !qE !arcE.
apply: (leq_trans
  (@omega_hom (backedge q) (backedge p) f [set: backedge q] inj_f h_hom)).
exact: sub_omega (subsetT _).
Qed.

(** ω̄ is invariant under digraph isomorphism. *)
Lemma omegabar_dgiso (T1 T2 : tournament) (f : T1 -> T2) :
  bijective f -> (forall u v, (f u --> f v) = (u --> v)) ->
  ω̄(T1) = ω̄(T2).
Proof.
move=> bij_f arcE; have [g fK gK] := bij_f.
apply/anti_leq/andP; split; first exact: omegabar_embed (bij_inj bij_f) arcE.
apply: (@omegabar_embed _ _ g); first exact: bij_inj (bij_can_bij bij_f fK).
by move=> u v; rewrite -{2}[u]gK -{2}[v]gK arcE.
Qed.

(** Sub-tournaments and vertex deletion. *)
Lemma omegabar_sub (T : tournament) (S : {set T}) :
  ω̄(sub_tournament S) <= ω̄(T).
Proof.
by apply: (@omegabar_embed (sub_tournament S) T val val_inj) => u v.
Qed.

Lemma omegabar_del (T : tournament) (v : T) :
  ω̄(del_tournament v) <= ω̄(T).
Proof. exact: omegabar_sub. Qed.

(** ω̄ on degenerate and tiny tournaments. *)
Lemma omegabar_nil (T : tournament) : #|T| = 0 -> ω̄(T) = 0.
Proof.
move=> T0; have [p ->] := omegabar_witness T; rewrite /omegab_at.
have -> : [set: backedge p] = set0.
  by apply/eqP; rewrite -cards_eq0 cardsT T0.
by rewrite omega0.
Qed.

Lemma omegabar_card_le2 (T : tournament) : 0 < #|T| <= 2 -> ω̄(T) = 1.
Proof.
case/andP=> pos le2; apply/eqP; rewrite omegabar_transb //.
exact: card_le2_transb.
Qed.

(** ** The two reference values *)

Lemma omegabar_TT n : 0 < n -> ω̄((TT n : tournament)) = 1.
Proof.
by move=> n0; apply/eqP; rewrite omegabar_transb ?card_TT //; exact: TT_transb.
Qed.

Lemma omegabar_C3 : ω̄((C3 : tournament)) = 2.
Proof.
(* The natural order 0 < 1 < 2, realized as a permutation: its backedge graph
   has the single edge {0, 2}, so ω = 2; and ω̄ ≥ 2 since C3 is intransitive. *)
pose r := [rel u v : C3 | (val u < val v)%N].
have r_irr : irreflexive r by move=> u /=; rewrite ltnn.
have r_trans : transitive r by move=> a b c /=; apply: ltn_trans.
have r_total (u v : C3) : u != v -> r u v || r v u.
  by case: u v => -[|[|[|//]]] ? [[|[|[|//]]] ?].
have c3pos : 0 < #|(C3 : tournament)| by apply/card_gt0P; exists 0%R.
apply/anti_leq/andP; split.
- (* ω̄ ≤ 2: no triangle in the backedge graph of the natural order *)
  apply: (leq_trans (omegabar_min (realize r))).
  rewrite /omegab_at; case: omegaP => K Kmax.
  rewrite leqNgt; apply/negP=> /card_gt2P[u [v [w]]] [[uK vK wK] [uDv vDw wDu]].
  have Kcl := maxclique_clique Kmax.
  have e1 := Kcl _ _ uK vK uDv.
  have e2 := Kcl _ _ vK wK vDw.
  have e3 := Kcl _ _ wK uK wDu.
  rewrite !backedgeE !(ltp_realizeE r_irr r_trans r_total) in e1 e2 e3.
  clear Kmax Kcl uK vK wK K.
  by move: uDv vDw wDu e1 e2 e3; case: u => -[|[|[|//]]] ?;
     case: v => -[|[|[|//]]] ?; case: w => -[|[|[|//]]] ?.
- (* ω̄ ≥ 2: C3 is not transitive *)
  by rewrite ltn_neqAle eq_sym omegabar_transb // (negbTE C3_Ntransb) omegabar_gt0.
Qed.
