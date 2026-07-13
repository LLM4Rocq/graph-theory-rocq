(** * Digraph.conjectures.X53 -- v2 asymmetric bipartite girth row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X53 vocabulary ************************************************)

Definition x53_bipartition (D : diGraphType) (A B : {set D}) : Prop :=
  [disjoint A & B] /\
  A :|: B = [set: D] /\
  forall u v : D,
    u --> v ->
    ((u \in A) && (v \in B)) || ((u \in B) && (v \in A)).

Definition x53_out_to (D : diGraphType) (S : {set D}) (v : D) : nat :=
  #|[set w in S | v --> w]|.

Definition x53_positive_rational (num den : nat) : Prop :=
  0 < num /\ 0 < den.

Definition x53_k_alpha_plus_beta_gt_one
    (k alpha_num alpha_den beta_num beta_den : nat) : Prop :=
  (alpha_den * beta_den
    < k * alpha_num * beta_den + beta_num * alpha_den)%N.

(** ** X53 statements ******************************************************)

(** arXiv:1809.08324, Conjecture 1.5: asymmetric bipartite outdegree
    hypotheses force directed girth at most 2k. *)
Definition bipartite_digraph_asymmetric_outdegree_girth_statement : Prop :=
  forall (k alpha_num alpha_den beta_num beta_den : nat),
    1 <= k ->
    x53_positive_rational alpha_num alpha_den ->
    x53_positive_rational beta_num beta_den ->
    x53_k_alpha_plus_beta_gt_one k alpha_num alpha_den beta_num beta_den ->
    forall (D : diGraphType) (A B : {set D}),
      0 < #|D| ->
      x53_bipartition A B ->
      (forall v : D, v \in A ->
        beta_num * #|B| <= beta_den * x53_out_to B v) ->
      (forall v : D, v \in B ->
        alpha_num * #|A| <= alpha_den * x53_out_to A v) ->
      exists c : seq D,
        dicycle c /\
        size c <= 2 * k.
