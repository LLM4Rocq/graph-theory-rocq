(** * Chromatic.conjectures.X68 -- v2 distant precolouring extension row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X68 vocabulary ************************************************)

Definition x68_proper_three_colouring (G : sgraph) (col : G -> 'I_3) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x68_pairwise_distance_at_least
    (G : sgraph) (d : nat) (S : {set G}) : Prop :=
  forall x y : G,
    x \in S -> y \in S -> x != y -> y \notin ball d.-1 x.

(** ** X68 statements ******************************************************)

(** arXiv:0911.0885, Conjecture 1.4: distant precoloured vertices in a plane
    triangle-free graph extend to a 3-colouring. *)
Definition triangle_free_planar_distant_precolouring_extension_statement : Prop :=
  exists d : nat,
    2 <= d /\
    forall (G : sgraph) (S : {set G}) (psi : G -> 'I_3),
      wagner_planar G ->
      triangle_free G ->
      x68_pairwise_distance_at_least d S ->
      exists col : G -> 'I_3,
        x68_proper_three_colouring col /\
        forall v : G, v \in S -> col v = psi v.
