(** * Topological.conjectures.X138 -- v2 clustered-colouring on surfaces row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X138 vocabulary ***********************************************)

Definition x138_embeddable_on_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x138_clustered_two_colourable (G : sgraph) : Prop :=
  clustered_chromatic_at_most G 2.

(** ** X138 statements *****************************************************)

(** Esperet-Joret: for every surface Sigma and maximum-degree bound Delta,
    triangle-free graphs of maximum degree Delta embeddable in Sigma have
    clustered chromatic number at most two. *)
Definition esperet_joret_surface_triangle_free_clustered_two_colouring_statement : Prop :=
  forall (surface Delta0 : nat) (G : sgraph),
    girth_geq G 4 ->
    Delta G <= Delta0 ->
    x138_embeddable_on_surface surface G ->
    x138_clustered_two_colourable G.
