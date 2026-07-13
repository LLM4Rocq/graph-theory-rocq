(** * Digraph.conjectures.X93 -- v2 local-to-global tournament colouring row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph tournament dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X93 vocabulary ************************************************)

Definition x93_t_local_tournament (T : tournament) (t : nat) : Prop :=
  forall v : T, dicolorableb (induced_digraph (N_out v)) t.

(** ** X93 statements ******************************************************)

(** Studies slice: Berger et al. local-to-global conjecture for tournaments:
    bounded dichromatic number on every out-neighbourhood forces bounded global
    dichromatic number. *)
Definition local_tournament_dichromatic_bound_statement : Prop :=
  exists f : nat -> nat,
    forall (t : nat) (T : tournament),
      x93_t_local_tournament T t ->
      dicolorableb T (f t).
