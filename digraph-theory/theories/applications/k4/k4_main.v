(** * Digraph.k4_main — T4 = ACₙ[C₃] is 4-ω̄-critical; Conjecture 5.10 at k = 4

    M17 (docs/k34_dossier.md §4, P1–P3). For every n = 2m+1, m ≥ 3, the
    tournament T4 = ACₙ[C₃] on 3n vertices satisfies ω̄(T4) = 4 (M15) and
    ω̄(T4 − v) = 3 for every v (M16 at (0,0) + vertex-transitivity), so it
    is 4-ω̄-critical ([T4_kcritical4]). The family is infinite, proving
    Conjecture 5.10 of Aboulker–Aubian–Charbit–Lopes at k = 4
    ([conjecture_5_10_at_k4]); by [kcritical_proper_sub] the only
    subtournament with ω̄ ≥ 4 is T4 itself, so no bound ℓ(4) exists and
    Question 5.9 fails at k = 4 ([question_5_9_fails_at_k4]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base acn_bands.
From Digraph Require Import k4_lower k4_value k4_del.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Main.
Variable m' : nat.
Hypothesis m3 : (3 <= m'.+1)%N.

Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation C3t := (C3 : tournament).
Local Notation T4 := (lexprod_tournament ACm C3t).

Let z0 : ACm := (0 : 'Z_n).
Let hz : C3t := (0 : 'Z_3).
Let o00 : T4 := (z0, hz).

(** The product of the vertex-transitive ACₙ with the vertex-transitive
    C₃ is vertex-transitive. *)
Lemma T4_vertex_transitive : vertex_transitiveb (T4 : diGraphType).
Proof.
exact: (lexprod_vertex_transitive
          (AC_vertex_transitive m') C3_vertex_transitive).
Qed.

(** ** ω̄(T4 − v) = 3 for every vertex v *)

Theorem omegabar_T4_del (v : T4) : ω̄(del_tournament v) = 3.
Proof.
rewrite (omegabar_del_vt T4_vertex_transitive v o00).
exact: (omegabar_T4del0 m3).
Qed.

(** ** T4 is 4-ω̄-critical *)

Theorem T4_kcritical4 : kcritical 4 T4.
Proof.
rewrite (vt_kcritical 4 o00 T4_vertex_transitive).
by rewrite (omegabar_T4 m3) omegabar_T4_del !eqxx.
Qed.

(** ** T4 has order 3n *)

Lemma card_T4 : #|T4| = (n * 3)%N.
Proof. by rewrite card_lexprod card_AC card_C3. Qed.

End Main.

(** ** Conjecture 5.10 at k = 4: an infinite family *)

Theorem conjecture_5_10_at_k4 (N : nat) :
  exists T : tournament, kcritical 4 T /\ (N < #|T|)%N.
Proof.
pose k := maxn 2 N.
have m3 : (3 <= k.+1)%N by rewrite ltnS leq_max leqnn.
exists (lexprod_tournament (AC k) (C3 : tournament)); split.
  exact: (T4_kcritical4 m3).
rewrite card_T4.
have kn : (k < (k.+1).*2.+1)%N.
  by rewrite doubleS !ltnS -addnn (leq_trans (leq_addr k.+1 k)) // addnS.
exact: leq_ltn_trans (leq_maxr 2 N) (leq_trans kn (leq_pmulr _ _)).
Qed.

(** ** Question 5.9 fails at k = 4 *)

Theorem question_5_9_fails_at_k4 (L : nat) :
  exists T : tournament,
    [/\ kcritical 4 T, (L < #|T|)%N
      & forall S : {set T}, (4 <= ω̄(sub_tournament S))%N -> S = [set: T]].
Proof.
pose k := maxn 2 L.
have m3 : (3 <= k.+1)%N by rewrite ltnS leq_max leqnn.
have crit := T4_kcritical4 m3.
exists (lexprod_tournament (AC k) (C3 : tournament)); split=> //.
- rewrite card_T4.
  have kn : (k < (k.+1).*2.+1)%N.
    by rewrite doubleS !ltnS -addnn (leq_trans (leq_addr k.+1 k)) // addnS.
  exact: leq_ltn_trans (leq_maxr 2 L) (leq_trans kn (leq_pmulr _ _)).
- move=> S h4; case: (eqVneq S [set: _]) => // neq.
  by have := leq_trans h4 (kcritical_proper_sub crit neq).
Qed.
