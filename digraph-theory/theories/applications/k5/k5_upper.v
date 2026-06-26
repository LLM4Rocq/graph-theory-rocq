(** * Digraph.k5_upper — ω̄(ACₙ[ACₙ]) ≤ 5 and ω̄(ACₙ[ACₙ] − (0,0)) ≤ 4

    The upper bounds of the k = 5 theorem (paper §5.4). The witness order is
    the key order [qk] of cells.v. For any clique K of its backedge graph,
    cells.v gives one vertex per cell ([card_clique_cidx]), obstructions.v
    rules every obstruction set out of the occupancy pattern
    ([no_obstruction]), and coverage.v caps the surviving patterns at 4
    occupied proper cells ([coverage5]); cell 8 — the single vertex (0,0) —
    contributes at most 1, whence #|K| ≤ 5.

    For the deleted tournament T − (0,0) the same order is pulled back along
    [val]; cliques then avoid cell 8 entirely and #|K| ≤ 4. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base in_neighbourhood cells.
From Digraph Require Import obstructions coverage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section K5Upper.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation T5 := (lexprod_tournament ACm ACm).

(** Unfold the 9-term occupancy sum into the shape consumed by [coverage5]. *)
Let sum9 (K : {set backedge (qk m')}) :
  (\sum_(i < 9) occ K i =
   occ K 0 + occ K 1 + occ K 2 + occ K 3 + occ K 4 + occ K 5
   + occ K 6 + occ K 7 + occ K 8)%N.
Proof. by rewrite !big_ord_recr big_ord0. Qed.

(** ** ω̄(T) ≤ 5 *)

Lemma omegab_at_qk_le5 : (omegab_at (qk m') <= 5)%N.
Proof.
rewrite /omegab_at; case: omegaP => K Kmax.
have Kcl : forall u v : backedge (qk m'),
    u \in K -> v \in K -> u != v -> u -- v.
  by have cl := maxclique_clique Kmax; move=> u v uK vK; exact: cl.
rewrite (card_clique_cidx Kcl) sum9 -[5%N]/(4 + 1)%N.
apply: leq_add; last exact: leq_b1.
exact: coverage5 (negbT (no_obstruction Kcl)).
Qed.

Theorem omegabar_T_le5 : (ω̄(T5) <= 5)%N.
Proof. exact: leq_trans (omegabar_min (qk m')) omegab_at_qk_le5. Qed.

(** ** ω̄(T − (0,0)) ≤ 4 *)

Let z0 : ACm := (0 : 'Z_n).
Let o00 : T5 := (z0, z0).
Local Notation T5del := (del_tournament o00).

(** The key order pulled back to the deleted tournament. *)
Let rd := [rel u v : T5del | (key (val u : T5) < key (val v : T5))%N].

Fact rd_irr : irreflexive rd.
Proof. by move=> u /=; rewrite ltnn. Qed.

Fact rd_trans : transitive rd.
Proof. by move=> a b c /=; apply: ltn_trans. Qed.

Fact rd_total (u v : T5del) : u != v -> rd u v || rd v u.
Proof.
move=> uDv; rewrite /= -neq_ltn.
by apply: contraNneq uDv => /key_inj/val_inj->.
Qed.

Let qd : {perm T5del} := realize rd.
Let qdE := ltp_realizeE rd_irr rd_trans rd_total.

Lemma omegab_at_qd_le4 : (omegab_at qd <= 4)%N.
Proof.
rewrite /omegab_at; case: omegaP => K Kmax.
have Kcl := maxclique_clique Kmax.
pose K' : {set backedge (qk m')} := [set (val u : T5) | u in K].
have K'cl : forall x y : backedge (qk m'),
    x \in K' -> y \in K' -> x != y -> x -- y.
  move=> x y /imsetP[u uK ->] /imsetP[v vK ->] neq.
  have uDv : u != v by apply: contraNneq neq => ->.
  have := Kcl _ _ uK vK uDv.
  by rewrite !backedgeE !qdE !qkE /= !sub_arcE.
have cardE : #|K'| = #|K| by apply: card_imset; exact: val_inj.
have occ8F : occ K' 8 = false.
  apply/negbTE/negP=> /occP[x /imsetP[u uK xE] e8].
  have [bH bL] := cidx_decode (x : T5).
  rewrite e8 in bH bL.
  have /eqP v2 : (val ((x : T5).2) == 0)%N by rewrite -(band3P _) bH.
  have /eqP v1 : (val ((x : T5).1) == 0)%N by rewrite -(band3P _) bL.
  have e1 : (x : T5).1 = z0 by apply: val_inj; rewrite v1.
  have e2 : (x : T5).2 = z0 by apply: val_inj; rewrite v2.
  have xeq : x = o00 :> T5 by rewrite [LHS]surjective_pairing e1 e2.
  by have := valP u; rewrite !inE -xE xeq eqxx.
rewrite -cardE (card_clique_cidx K'cl) sum9 occ8F addn0.
exact: coverage5 (negbT (no_obstruction K'cl)).
Qed.

Theorem omegabar_Tdel_le4 : (ω̄(T5del) <= 4)%N.
Proof. exact: leq_trans (omegabar_min qd) omegab_at_qd_le4. Qed.

End K5Upper.
