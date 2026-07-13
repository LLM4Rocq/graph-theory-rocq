(** * Chromatic.conjectures.X75 -- v2 Albertson list-precolouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X75 vocabulary ************************************************)

Definition x75_lists_size_one_or_five
    (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  forall v : G, (#|L v| == 1) || (#|L v| == 5).

Definition x75_singleton_lists_far
    (G : sgraph) (C : finType) (L : G -> {set C}) (d : nat) : Prop :=
  forall x y : G,
    x != y -> #|L x| = 1 -> #|L y| = 1 -> y \notin ball d.-1 x.

(** ** X75 statements ******************************************************)

(** Studies slice: Albertson's planar list/precolouring extension problem with
    singleton lists pairwise far apart. *)
Definition albertson_distance_constrained_list_colouring_statement : Prop :=
  exists d : nat,
    forall (G : sgraph) (C : finType) (L : G -> {set C}),
      wagner_planar G ->
      x75_lists_size_one_or_five L ->
      x75_singleton_lists_far L d ->
      list_colourable L.
