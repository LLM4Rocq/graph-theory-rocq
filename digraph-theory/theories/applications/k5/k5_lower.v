(** * Digraph.k5_lower — the lower bounds for T = ACₙ[ACₙ]

    M5 (docs/DESIGN.md §7, items 3): for n = 2m+1, m ≥ 3 and
    T = ACₙ[ACₙ] (the lexicographic substitution):

    - [omegabar_T_ge5]    : ω̄(T) ≥ 5,
      by the substitution lower bound (M3) with ω̄(ACₙ) = 3 (M4):
      ω̄(T) ≥ 3 + 3 − 1.
    - [omegabar_Tdel_ge4] : ω̄(T − (0,0)) ≥ 4,
      because (ACₙ−0)[ACₙ] embeds arc-preservingly into T − (0,0)
      (every vertex of the deleted block {0}×ACₙ other than (0,0) is
      simply *absent* from the sub-product), and
      ω̄((ACₙ−0)[ACₙ]) ≥ ω̄(ACₙ−0) + ω̄(ACₙ) − 1 = 2 + 3 − 1 = 4. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive.
From Digraph Require Import substitution acn_arc_facts acn_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section K5Lower.
Variable m' : nat.
Hypothesis m3 : (3 <= m'.+1)%N.

Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation T5 := (lexprod_tournament ACm ACm).

Let z0 : ACm := (0 : 'Z_n).

Fact ACm_pos : (0 < #|ACm|)%N.
Proof. by rewrite card_AC. Qed.

Fact ACdel_pos : (0 < #|del_tournament z0|)%N.
Proof. by rewrite card_del card_AC. Qed.

(** ** ω̄(T) ≥ 5 *)

Theorem omegabar_T_ge5 : (5 <= ω̄(T5))%N.
Proof.
have := omegabar_lexprod_ge ACm_pos ACm_pos.
by rewrite !(omegabar_AC m3) addn1 ltnS.
Qed.

(** ** ω̄(T − (0,0)) ≥ 4 *)

(** The sub-product (ACₙ−0)[ACₙ] embeds into T − (0,0). *)
Let SD := lexprod_tournament (del_tournament z0) ACm.
Let T5del := del_tournament ((z0, z0) : T5).

Let emb (u : SD) : T5 := (val u.1, u.2).

Fact emb_mem (u : SD) : emb u \in [set~ ((z0, z0) : T5)].
Proof.
rewrite !inE /emb xpair_eqE negb_and.
have := valP u.1; rewrite !inE => h.
by rewrite h.
Qed.

Let f (u : SD) : T5del := Sub (emb u) (emb_mem u).

Fact f_inj : injective f.
Proof.
move=> [u1 u2] [v1 v2] /(congr1 val); rewrite !SubK /emb /=.
by case=> /val_inj-> ->.
Qed.

Fact f_arc (u v : SD) : (f u --> f v) = (u --> v).
Proof.
rewrite sub_arcE !SubK /emb !lexprod_arcE /=.
by rewrite !sub_arcE -val_eqE.
Qed.

Theorem omegabar_Tdel_ge4 : (4 <= ω̄(T5del))%N.
Proof.
have h1 : (4 <= ω̄(SD))%N.
  have := omegabar_lexprod_ge ACdel_pos ACm_pos.
  by rewrite (omegabar_AC m3) (omegabar_AC_del z0 m3) addn1 ltnS.
exact: leq_trans h1 (omegabar_embed f_inj f_arc).
Qed.

End K5Lower.
