(** * Chromatic.conjectures.X150 -- v2 surface 3-colourability algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X150 vocabulary ***********************************************)

Definition x150_embeddable_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x150_polytime_decides_3_colourability_on_surface (surface : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x150_embeddable_in_fixed_surface surface G /\ girth_geq G 4)
    (fun G : sgraph => χ([set: G]) <= 3).

(** ** X150 statements *****************************************************)

(** Gimbel-Thomassen Problem 3: for every fixed surface, test 3-colourability of
    triangle-free graphs embeddable in that surface in polynomial time. *)
Definition gimbel_thomassen_triangle_free_surface_three_colourability_polytime_statement : Prop :=
  forall surface : nat, x150_polytime_decides_3_colourability_on_surface surface.
