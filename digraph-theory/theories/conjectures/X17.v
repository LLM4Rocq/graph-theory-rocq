(** * Digraph.conjectures.X17 -- v2 oriented-path and unavoidability rows *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.conjectures Require Import X2 unvd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X17 vocabulary ************************************************)

Definition x17_min_semidegree_strict_half (D : diGraphType) (k : nat) : Prop :=
  forall v : D, (k < 2 * outdeg v)%N /\ (k < 2 * classic_core.indeg v)%N.

(** ** X17 statements ******************************************************)

(** Studies slice: Stein's conjecture on oriented paths. *)
Definition stein_oriented_paths_strict_semidegree_statement : Prop :=
  forall (k : nat) (G : orientedDigraph),
    0 < k ->
    (0 < #|G|)%N ->
    x17_min_semidegree_strict_half G k ->
    forall P : orientedDigraph,
      oriented_path P k -> subdigraph_embed P G.

(** Studies slice: Sumner's tournament-unavoidability conjecture. *)
Definition sumner_oriented_tree_unavoidable_statement : Prop :=
  forall (n : nat) (T : orientedDigraph),
    1 < n ->
    oriented_tree T ->
    #|T| = n ->
    unavoidable T (2 * n - 2).
