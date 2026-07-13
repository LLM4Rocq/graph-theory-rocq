(** * Chromatic.conjectures.X28 -- v2 planar choosability row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X28 vocabulary ************************************************)

Definition x28_no_cycle_length_between (G : sgraph) (a b : nat) : Prop :=
  forall c : seq G,
    ucycle (--) c ->
    a <= size c ->
    size c <= b ->
    False.

(** ** X28 statements ******************************************************)

(** arXiv:1508.03437, planar graphs with no cycles of lengths 4--6. *)
Definition planar_no_4_to_6_cycles_three_choosable_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    x28_no_cycle_length_between G 4 6 ->
    choosable G 3.
