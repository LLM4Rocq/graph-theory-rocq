(** * Digraph.k4_lower — the lower bounds for T4 = ACₙ[C₃]

    M14 (docs/PLAN_K34.md, docs/k34_dossier.md §4): for n = 2m+1, m ≥ 3
    and T4 = ACₙ[C₃] (the lexicographic substitution):

    - [omegabar_T4_ge4]    : ω̄(T4) ≥ 4,
      by the substitution lower bound with ω̄(ACₙ) = 3 and ω̄(C₃) = 2:
      ω̄(T4) ≥ 3 + 2 − 1 (item L1).
    - [omegabar_T4del_ge3] : ω̄(T4 − (0,0)) ≥ 3,
      because the constant-h copy t ↦ (t, 1) of ACₙ avoids the whole
      h = 0 layer, hence the deleted vertex, and is arc-preserving
      (blocks always differ or the inner arc is the irreflexive 1 → 1):
      ω̄(T4 − (0,0)) ≥ ω̄(ACₙ) = 3 (item L2). *)

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

Section K4Lower.
Variable m' : nat.
Hypothesis m3 : (3 <= m'.+1)%N.

Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation C3t := (C3 : tournament).
Local Notation T4 := (lexprod_tournament ACm C3t).

Let z0 : ACm := (0 : 'Z_n).
Let h0 : C3t := (0 : 'Z_3).
Let h1 : C3t := (1 : 'Z_3).
Let o00 : T4 := (z0, h0).

Fact ACm_pos : (0 < #|ACm|)%N.
Proof. by rewrite card_AC. Qed.

Fact C3_pos : (0 < #|C3t|)%N.
Proof. by rewrite card_C3. Qed.

(** ** ω̄(T4) ≥ 4 (L1) *)

Theorem omegabar_T4_ge4 : (4 <= ω̄(T4))%N.
Proof.
have := omegabar_lexprod_ge ACm_pos C3_pos.
by rewrite (omegabar_AC m3) omegabar_C3 addn1 ltnS.
Qed.

(** ** ω̄(T4 − (0,0)) ≥ 3 (L2) *)

Let T4del := del_tournament o00.

Let emb (t : ACm) : T4 := (t, h1).

Fact emb_mem (t : ACm) : emb t \in [set~ o00].
Proof. by rewrite !inE /emb xpair_eqE negb_and orbC. Qed.

Let f (t : ACm) : T4del := Sub (emb t) (emb_mem t).

Fact f_inj : injective f.
Proof. by move=> t t' /(congr1 val); rewrite !SubK /emb; case=> ->. Qed.

Fact f_arc (t t' : ACm) : (f t --> f t') = (t --> t').
Proof.
by rewrite sub_arcE !SubK /emb lexprod_arcE /= arcxx andbF orbF.
Qed.

Theorem omegabar_T4del_ge3 : (3 <= ω̄(T4del))%N.
Proof.
have h3 : (3 <= ω̄(ACm))%N by rewrite (omegabar_AC m3).
exact: leq_trans h3 (omegabar_embed f_inj f_arc).
Qed.

End K4Lower.
