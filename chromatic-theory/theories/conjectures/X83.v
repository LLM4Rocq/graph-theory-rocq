(** * Chromatic.conjectures.X83 -- v2 rainbow induced path row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X83 vocabulary ************************************************)

Definition x83_rainbow_induced_path
    (G : sgraph) (C : finType) (col : G -> C) (p : seq G) : Prop :=
  x3_induced_path p /\ uniq (map col p).

(** ** X83 statements ******************************************************)

(** Studies slice: Aravind's conjecture that every colouring of a triangle-free
    graph contains a rainbow induced path on chi(G) vertices. *)
Definition aravind_rainbow_induced_chromatic_path_statement : Prop :=
  forall (G : sgraph) (C : finType) (col : G -> C),
    0 < #|G| ->
    triangle_free G ->
    x3_proper_colouring col ->
    exists p : seq G,
      size p = χ([set: G]) /\
      x83_rainbow_induced_path col p.
