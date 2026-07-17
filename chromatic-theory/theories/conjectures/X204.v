(** * Chromatic.conjectures.X204 -- v2 planar no 4/5-cycle fractional row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X204 vocabulary ***********************************************)

Definition x204_no_cycle_length (G : sgraph) (n : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> size c != n.

(** ** X204 statements *****************************************************)

(** Dvorak-Hu informal conjecture: the constant [11/3] for planar graphs with
    no 4- or 5-cycles is not optimal; equivalently, some uniform rational bound
    strictly below [11/3] should suffice.

    This uses X130's fractional-colouring witness and the available Wagner
    planarity predicate. *)
Definition planar_no_4_5_cycles_fractional_below_eleven_thirds_statement : Prop :=
  exists p q : nat,
    [/\ 0 < q, 3 * p < 11 * q &
      forall G : sgraph,
        wagner_planar G ->
        x204_no_cycle_length G 4 ->
        x204_no_cycle_length G 5 ->
        x130_frac_chi_le G p q].

