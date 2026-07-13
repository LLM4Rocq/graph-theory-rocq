(** * Packing.conjectures.X48 -- v2 leaf-parameter tree decomposition row *)

From GTBase Require Export base.
From Packing.conjectures Require Import X47.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X48 vocabulary ************************************************)

Definition x48_leaf_count (T : sgraph) : nat :=
  #|[set v : T | #|N(v)| == 1]|.

(** ** X48 statements ******************************************************)

(** arXiv:1907.11600, tree decomposition with connectivity controlled by the
    number of leaves. *)
Definition tree_decomposition_leaf_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (x48_leaf_count T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.
