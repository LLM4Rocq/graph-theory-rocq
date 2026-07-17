(** * Chromatic.conjectures.X152 -- v2 fixed-surface 4-colourability algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X152 vocabulary ***********************************************)

Definition x152_embeddable_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x152_polytime_decides_four_colourability (surface : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x152_embeddable_in_fixed_surface surface G)
    (fun G : sgraph => χ([set: G]) <= 4).

(** ** X152 statements *****************************************************)

(** Open problem: for each fixed non-spherical surface, test 4-colourability of
    graphs drawn in that surface in polynomial time. *)
Definition fixed_surface_four_colourability_polytime_statement : Prop :=
  forall surface : nat,
    0 < surface -> x152_polytime_decides_four_colourability surface.
