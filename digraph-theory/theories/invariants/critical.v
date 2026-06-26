(** * Digraph.critical — k-ω̄-critical tournaments

    A tournament is [k]-ω̄-critical when ω̄(T) = k and deleting *any* vertex
    drops ω̄ to k−1 (Aboulker–Aubian–Charbit–Lopes; docs/DESIGN.md §6).

    Main results:
    - [C3_kcritical2]: the directed triangle is 2-ω̄-critical;
    - [kcritical2_card3]: a 2-ω̄-critical tournament has exactly 3 vertices;
    - [kcritical2_uniq]: it is isomorphic to [C3] — i.e. C3 is the *unique*
      2-ω̄-critical tournament (M1 exit theorem). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition kcritical (k : nat) (T : tournament) : bool :=
  (ω̄(T) == k) && [forall v : T, ω̄(del_tournament v) == k.-1].

Lemma kcriticalP (k : nat) (T : tournament) :
  reflect (ω̄(T) = k /\ forall v : T, ω̄(del_tournament v) = k.-1)
          (kcritical k T).
Proof.
apply: (iffP andP) => -[/eqP obk dels]; split=> //.
- by move=> v; apply/eqP; exact: (forallP dels).
- by apply/forallP=> v; apply/eqP.
Qed.

(** Deleting a vertex removes exactly one vertex. *)
Lemma card_del (T : tournament) (v : T) : #|del_tournament v| = #|T|.-1.
Proof.
by rewrite card_sig (@eq_card _ _ (mem [set~ v])) ?cardsC1 // => x; rewrite !inE.
Qed.

(** ** Proper subtournaments of critical tournaments

    In a k-ω̄-critical tournament every *proper* subtournament has
    ω̄ ≤ k − 1: it omits some vertex, hence embeds into that vertex's
    deletion (the Question-5.9-failure mechanism, stated once; G1 of
    docs/k34_dossier.md). *)

Lemma kcritical_proper_sub (k : nat) (T : tournament) (S : {set T}) :
  kcritical k T -> S != [set: T] -> (ω̄(sub_tournament S) <= k.-1)%N.
Proof.
case/kcriticalP=> _ dels Sproper.
have /subsetPn[v _ vNS] : ~~ ([set: T] \subset S).
  by move: Sproper; apply: contraNN => sub; rewrite eqEsubset sub subsetT.
have memf (x : sub_tournament S) : val x \in [set~ v].
  by rewrite !inE; apply: contraNneq vNS => <-; exact: (valP x).
pose f (x : sub_tournament S) : del_tournament v := Sub (val x) (memf x).
have f_inj : injective f.
  by move=> x y /(congr1 val); rewrite !SubK => /val_inj.
have f_arc (x y : sub_tournament S) : (f x --> f y) = (x --> y).
  by rewrite !sub_arcE !SubK.
by rewrite -(dels v); exact: (omegabar_embed f_inj f_arc).
Qed.

(** ** C3 is 2-ω̄-critical *)

Lemma C3_kcritical2 : kcritical 2 (C3 : tournament).
Proof.
apply/kcriticalP; split; first exact: omegabar_C3.
move=> v; apply: omegabar_card_le2.
by rewrite card_del card_C3.
Qed.

(** ** Uniqueness: a 2-ω̄-critical tournament is C3 *)

Section Uniqueness.
Variable T : tournament.
Hypothesis crit : kcritical 2 T.

Let ob2 : ω̄(T) = 2. Proof. by case/kcriticalP: crit. Qed.
Let del1 (v : T) : ω̄(del_tournament v) = 1.
Proof. by case/kcriticalP: crit => _ /(_ v). Qed.

Let Tpos : 0 < #|T|.
Proof.
by case: (posnP #|T|) => // /omegabar_nil T0; move: ob2; rewrite T0.
Qed.

Let Ntr : ~~ transb T.
Proof. by rewrite -[transb T](omegabar_transb Tpos) ob2. Qed.

(** The directed triangle inside T. *)
Let cyc : exists u v w : T, [/\ u --> v, v --> w & w --> u].
Proof. exact/ntransbP. Qed.

(** A 2-critical tournament has no 4th vertex: deleting it would leave the
    triangle, contradicting ω̄(T − x) = 1. *)
Lemma kcritical2_card3 : #|T| = 3.
Proof.
have [u [v [w [uv vw wu]]]] := cyc.
have uDv := arc_neq uv; have vDw := arc_neq vw; have wDu := arc_neq wu.
have card_uvw : #|[set u; v; w]| = 3.
  by rewrite -setUA cardsU1 !inE negb_or uDv eq_sym wDu cards2 vDw.
apply/anti_leq/andP; split; last first.
  by rewrite -card_uvw; apply: max_card.
rewrite leqNgt; apply/negP=> Tgt3.
(* pick a vertex x outside the triangle *)
have /set0Pn[x xout] : [set: T] :\: [set u; v; w] != set0.
  by rewrite -card_gt0 cardsD setTI cardsT card_uvw subn_gt0.
move: xout; rewrite !inE andbT !negb_or => /andP[/andP[xDu xDv] xDw].
(* lift the triangle into T − x *)
have uIn : u \in [set~ x] by rewrite !inE eq_sym.
have vIn : v \in [set~ x] by rewrite !inE eq_sym.
have wIn : w \in [set~ x] by rewrite !inE eq_sym.
pose u' : del_tournament x := Sub u uIn.
pose v' : del_tournament x := Sub v vIn.
pose w' : del_tournament x := Sub w wIn.
have Ntr' : ~~ transb (del_tournament x).
  apply/ntransbP; exists u', v', w'.
  by split; rewrite sub_arcE !SubK.
have pos' : 0 < #|del_tournament x|.
  by apply/card_gt0P; exists u'.
by have := del1 x; move/eqP; rewrite (omegabar_transb pos') (negbTE Ntr').
Qed.

(** The explicit isomorphism C3 ≅ T sending 0,1,2 to the triangle. *)
Theorem kcritical2_uniq : dgiso (C3 : diGraphType) T.
Proof.
have [u [v [w [uv vw wu]]]] := cyc.
have uDv := arc_neq uv; have vDw := arc_neq vw; have wDu := arc_neq wu.
pose f : C3 -> T := fun i =>
  if val i == 0%N then u else if val i == 1%N then v else w.
have inj_f : injective f.
  move=> i j; rewrite /f; case: i => -[|[|[|//]]] ?; case: j => -[|[|[|//]]] ? //= e.
  - by apply: val_inj.
  - by rewrite e eqxx in uDv.
  - by rewrite e eqxx in wDu.
  - by rewrite e eqxx in uDv.
  - by apply: val_inj.
  - by rewrite e eqxx in vDw.
  - by rewrite e eqxx in wDu.
  - by rewrite e eqxx in vDw.
  - by apply: val_inj.
have bij_f : bijective f.
  apply: inj_card_bij inj_f _.
  by rewrite kcritical2_card3 card_C3.
exists f; split; first exact: bij_f.
move=> i j.
(* the three forward arcs close by assumption (is_true unfolds to = true);
   six cases remain: diagonals and reversed arcs *)
rewrite /f; case: i => -[|[|[|//]]] ?; case: j => -[|[|[|//]]] ? //=.
- by rewrite arcxx.
- by rewrite (negbTE (arc_asym wu)).
- by rewrite (negbTE (arc_asym uv)).
- by rewrite arcxx.
- by rewrite (negbTE (arc_asym vw)).
- by rewrite arcxx.
Qed.

End Uniqueness.
