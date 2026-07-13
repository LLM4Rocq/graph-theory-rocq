(** * GTMisc.conjectures.X101 -- v2 planar proper-orientation row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X82.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X101 statements *****************************************************)

(** Studies slice: bounded proper orientation number for planar graphs. *)
Definition planar_bounded_proper_orientation_number_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      wagner_planar G ->
      x82_proper_orientation_bound G C.
