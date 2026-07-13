(** * Chromatic.conjectures.X32 -- v2 planar induced degeneracy row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X32 statements ******************************************************)

(** arXiv:1709.04036, induced 2-degenerate subgraph in triangle-free planar
    graphs. *)
Definition triangle_free_planar_large_induced_two_degenerate_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    triangle_free G ->
    exists S : {set G},
      (8 * #|S| >= 7 * #|G|)%N /\
      k_degenerate (induced S) 2.
