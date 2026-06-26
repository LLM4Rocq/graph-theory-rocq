(** * Digraph.unified — Conjecture 5.10 holds at every k ∈ {3, 4, 5}

    The unified headline (conjecture_5_10_k345_unified.md): for each
    k ∈ {3,4,5} there are infinitely many k-ω̄-critical tournaments —
    witnessed by the three families over the same circulant platform:

    - k = 3 : ACₙ itself (n = 2m+1 vertices, M4's [AC_kcritical3]);
    - k = 4 : ACₙ[C₃] (3n vertices, applications/k4/);
    - k = 5 : ACₙ[ACₙ] (n² vertices, applications/k5/).

    This file adds the k = 3 packaging ([conjecture_5_10_at_k3],
    [question_5_9_fails_at_k3] via the general [kcritical_proper_sub])
    and the quantified headline [conjecture_5_10_at_345]. Question 5.9
    fails at each k: see [question_5_9_fails_at_k3/k4/k5]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base acn_bands.
From Digraph Require Import main k4_main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** ** Conjecture 5.10 at k = 3: an infinite family *)

Theorem conjecture_5_10_at_k3 (N : nat) :
  exists T : tournament, kcritical 3 T /\ (N < #|T|)%N.
Proof.
pose k := maxn 2 N.
have m3 : (3 <= k.+1)%N by rewrite ltnS leq_max leqnn.
exists (AC k : tournament); split; first exact: (AC_kcritical3 m3).
rewrite card_AC.
have kn : (k < (k.+1).*2.+1)%N.
  by rewrite doubleS !ltnS -addnn (leq_trans (leq_addr k.+1 k)) // addnS.
exact: leq_ltn_trans (leq_maxr 2 N) kn.
Qed.

(** ** Question 5.9 fails at k = 3 *)

Theorem question_5_9_fails_at_k3 (L : nat) :
  exists T : tournament,
    [/\ kcritical 3 T, (L < #|T|)%N
      & forall S : {set T}, (3 <= ω̄(sub_tournament S))%N -> S = [set: T]].
Proof.
pose k := maxn 2 L.
have m3 : (3 <= k.+1)%N by rewrite ltnS leq_max leqnn.
have crit := AC_kcritical3 m3.
exists (AC k : tournament); split=> //.
- rewrite card_AC.
  have kn : (k < (k.+1).*2.+1)%N.
    by rewrite doubleS !ltnS -addnn (leq_trans (leq_addr k.+1 k)) // addnS.
  exact: leq_ltn_trans (leq_maxr 2 L) kn.
- move=> S h3; case: (eqVneq S [set: _]) => // neq.
  by have := leq_trans h3 (kcritical_proper_sub crit neq).
Qed.

(** ** The unified headline: every k ∈ {3, 4, 5} *)

Theorem conjecture_5_10_at_345 (k : nat) : (3 <= k <= 5)%N ->
  forall N : nat, exists T : tournament, kcritical k T /\ (N < #|T|)%N.
Proof.
case: k => [|[|[|[|[|[|k]]]]]] // _ N.
- exact: conjecture_5_10_at_k3.
- exact: conjecture_5_10_at_k4.
- exact: conjecture_5_10_at_k5.
Qed.
