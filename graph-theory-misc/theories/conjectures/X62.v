(** * GTMisc.conjectures.X62 -- v2 rainbow path cover row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X14.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X62 vocabulary ************************************************)

Definition x62_edges_covered_by_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall e : {set G},
    e \in x14_edge_set G ->
    exists p : seq G, p \in paths /\ e \in x14_path_edges p.

(** ** X62 statements ******************************************************)

(** arXiv:2301.08707, Problem 4: properly edge-coloured graphs should have a
    linear-size cover of their edge set by rainbow paths. *)
Definition rainbow_paths_linear_edge_cover_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (C : finType) (col : {set G} -> C),
      x14_proper_edge_colouring col ->
      exists paths : seq (seq G),
        size paths <= c * #|G| /\
        (forall p : seq G, p \in paths -> x14_rainbow_path col p) /\
        x62_edges_covered_by_paths paths.
