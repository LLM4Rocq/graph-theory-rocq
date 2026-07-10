(** * Minor.conjectures.X8 -- v2 clean list-colouring/minor rows *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X8 statements *******************************************************)

(** arXiv:2201.09115, Question 1. *)
Definition kt_minor_free_seven_choosable_statement : Prop :=
  (forall (G : sgraph) (ch : nat),
      ~ minor G (KB 4 4) ->
      is_choice_number G ch ->
      ch <= 7) /\
  forall (G : sgraph) (ch : nat),
      ~ minor G (KB 3 5) ->
      is_choice_number G ch ->
      ch <= 7.

(** arXiv:2201.09115, Question 2. *)
Definition kt_minor_free_two_s_plus_t_choosable_statement : Prop :=
  forall (s t ch : nat) (G : sgraph),
    1 <= s -> s <= t ->
    ~ minor G (KB s t) ->
    is_choice_number G ch ->
    ch <= 2 * s + t.
