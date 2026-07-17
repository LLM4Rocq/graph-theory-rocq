(** * Minor.conjectures.X201 -- v2 treewidth Erdos-Posa row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X201 vocabulary ***********************************************)

Definition x201_treewidth_at_least (G : sgraph) (r : nat) : Prop :=
  forall k : nat, x27_treewidth_at_most G k -> r <= k.

Definition x201_k_disjoint_large_treewidth_subgraphs
    (G : sgraph) (r k : nat) : Prop :=
  exists S : 'I_k -> {set G},
    (forall i : 'I_k, S i != set0) /\
    (forall i j : 'I_k, i != j -> S i :&: S j = set0) /\
    forall i : 'I_k, x201_treewidth_at_least (induced (S i)) r.

(** ** X201 statements *****************************************************)

(** Conjecture 1.4: sufficiently large treewidth, at scale
    [f(r) * k log(k+1)], forces [k] vertex-disjoint subgraphs each of treewidth
    at least [r]. *)
Definition treewidth_vertex_disjoint_subgraphs_log_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (r k : nat) (G : sgraph),
      1 <= r ->
      1 <= k ->
      x201_treewidth_at_least G (f r * k * (trunc_log 2 k.+1).+1) ->
      x201_k_disjoint_large_treewidth_subgraphs G r k.
