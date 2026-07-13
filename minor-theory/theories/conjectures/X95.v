(** * Minor.conjectures.X95 -- v2 subgraph-indexed tree-decomposition row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X95 vocabulary ************************************************)

Definition x95_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x95_pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    x95_path_index_graph T /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

Definition x95_index_tree_subgraph (T G : sgraph) : Prop :=
  exists f : T -> G,
    injective f /\ forall u v : T, u -- v -> f u -- f v.

Definition x95_subgraph_indexed_tree_decomposition_width_at_most
    (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x95_index_tree_subgraph T G /\
    x27_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

(** ** X95 statements ******************************************************)

(** Studies slice: Blanco-Cook-Hatzel-Hilaire-Illingworth-McCarty question:
    connected graphs should admit a tree-decomposition whose indexing tree is
    a subgraph of the graph, with width bounded by a function of pathwidth. *)
Definition subgraph_indexed_tree_decomposition_pathwidth_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      connected [set: G] ->
      x95_pathwidth_at_most G p ->
      x95_subgraph_indexed_tree_decomposition_width_at_most G (f p).
