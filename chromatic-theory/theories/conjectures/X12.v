(** * Chromatic.conjectures.X12 -- v2 Woodall list-colouring row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X12 statements ******************************************************)

(** Studies slice: Woodall's list-colouring conjecture for K_{s,t}-minor-free
    graphs. *)
Definition woodall_ks_t_minor_free_list_colouring_statement : Prop :=
  forall (s t ch : nat) (G : sgraph),
    1 <= s -> 1 <= t ->
    ~ minor G (KB s t) ->
    is_choice_number G ch ->
    ch <= s + t - 1.
