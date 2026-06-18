(** * Digraph.conjectures.clique_cluster — AACL "clique number of tournaments" cluster

    Statement-only formalization (no axioms) of the ω̄-cluster conjectures of
    Aboulker–Aubian–Charbit–Lopes, "The clique number of tournaments" (arXiv:2310.04265),
    together with the literature-stated implication edges between them.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §1, §5 (P1), §7.

    Here ω̄(T) = [omegabar T] is the tournament clique number (min over vertex orders of
    the clique number of the back-edge graph), [kcritical k T] is k-ω̄-criticality, and
    [domnum T] is the directed domination number; all are reused from the invariants layer.

    Nodes (Definitions of type Prop):
      - [conjecture_5_10_statement]   : for every k ≥ 3, infinitely many k-ω̄-critical
                                        tournaments (the OPEN ∀k generalization; the
                                        k ∈ {3,4,5} instances are PROVED in
                                        applications/unified.v, [conjecture_5_10_at_345]).
      - [question_5_9_statement]      : the f = id "ω̄-cluster" question, positive form —
                                        ω̄(T) ≥ k is witnessed by a subtournament of size
                                        ≤ ℓ(k).
      - [conjecture_5_8_statement]    : the f ≠ id weakening of Q5.9.
      - [dom_omega_cluster_statement] : "large domination number ⇒ ω̄-cluster".

    Edges (Qed-closed relative theorems — provable without resolving any conjecture):
      - [conj_5_10_implies_neg_Q5_9]   : Conjecture 5.10  ⟹  ¬ Question 5.9.
      - [Q5_9_implies_conj_5_8]        : Question 5.9     ⟹  Conjecture 5.8.
      - [conj_5_8_implies_dom_cluster] : Conjecture 5.8   ⟹  dom⇒ω̄-cluster (via dom ≤ ω̄). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph tournament.
From Digraph Require Import omegabar critical domination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Nodes *)

(** Conjecture 5.10: for every k ≥ 3 there are arbitrarily large k-ω̄-critical
    tournaments (≡ infinitely many up to isomorphism). *)
Definition conjecture_5_10_statement : Prop :=
  forall k : nat, (3 <= k)%N ->
    forall N : nat, exists T : tournament, kcritical k T /\ (N < #|T|)%N.

(** Question 5.9 (positive / f = id form): there is a bound ℓ such that whenever
    ω̄(T) ≥ k, some subtournament A with |A| ≤ ℓ(k) already has ω̄(A) ≥ k. *)
Definition question_5_9_statement : Prop :=
  exists ell : nat -> nat,
    forall (T : tournament) (k : nat), (k <= ω̄(T))%N ->
      exists S : {set T}, (#|S| <= ell k)%N /\ (k <= ω̄(sub_tournament S))%N.

(** Conjecture 5.8: the f ≠ id weakening — two functions f, ℓ with ω̄(T) ≥ f(k) forcing a
    size-≤ ℓ(k) subtournament of ω̄ ≥ k. *)
Definition conjecture_5_8_statement : Prop :=
  exists f ell : nat -> nat,
    forall (T : tournament) (k : nat), (f k <= ω̄(T))%N ->
      exists S : {set T}, (#|S| <= ell k)%N /\ (k <= ω̄(sub_tournament S))%N.

(** "Large domination ⇒ ω̄-cluster": the same conclusion under a domination-number
    hypothesis dom(T) ≥ f(k). *)
Definition dom_omega_cluster_statement : Prop :=
  exists f ell : nat -> nat,
    forall (T : tournament) (k : nat), (f k <= domnum T)%N ->
      exists S : {set T}, (#|S| <= ell k)%N /\ (k <= ω̄(sub_tournament S))%N.

(** ** Edges *)

(** Conjecture 5.10 ⟹ ¬ Question 5.9.  If both held, take (at k = 3) a 3-ω̄-critical T
    larger than ℓ(3); Q5.9 yields a subtournament S with |S| ≤ ℓ(3) < |T|, hence S proper,
    so ω̄(S) ≤ 3−1 = 2 by criticality, contradicting ω̄(S) ≥ 3. *)
Theorem conj_5_10_implies_neg_Q5_9 :
  conjecture_5_10_statement -> ~ question_5_9_statement.
Proof.
move=> C10 [ell HQ].
have [T [crit cardT]] := C10 3 (leqnn 3) (ell 3).
have oT : ω̄(T) = 3 by have /kcriticalP[E _] := crit; exact: E.
have h3 : (3 <= ω̄(T))%N by rewrite oT.
have [S [cardS oS]] := HQ T 3 h3.
have Sproper : S != [set: T].
  apply/eqP => ST.
  move: cardS; rewrite ST cardsT => hTle.
  have habs := leq_ltn_trans hTle cardT.
  by rewrite ltnn in habs.
have hle := kcritical_proper_sub crit Sproper.
have habs2 : (ω̄(sub_tournament S) < ω̄(sub_tournament S))%N.
  by apply: (leq_ltn_trans hle); exact: oS.
by rewrite ltnn in habs2.
Qed.

(** Question 5.9 ⟹ Conjecture 5.8 (it is the special case f = id). *)
Theorem Q5_9_implies_conj_5_8 :
  question_5_9_statement -> conjecture_5_8_statement.
Proof. by case=> ell HQ; exists (fun k => k), ell => T k; exact: (HQ T k). Qed.

(** Conjecture 5.8 ⟹ "large dom ⇒ ω̄-cluster" (via dom(T) ≤ ω̄(T)). *)
Theorem conj_5_8_implies_dom_cluster :
  conjecture_5_8_statement -> dom_omega_cluster_statement.
Proof.
case=> f [ell H58]; exists f, ell => T k hf.
apply: (H58 T k).
exact: leq_trans hf (domnum_le_omegabar T).
Qed.
