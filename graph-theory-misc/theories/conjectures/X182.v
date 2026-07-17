(** * GTMisc.conjectures.X182 -- v2 planar-cover poset dimension row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X182 statements *****************************************************)

(** Open problem: whether the dimension of posets with planar cover graphs is
    bounded by a polynomial, or even a linear function, of their height.  The
    statement records the polynomial version: if [h] is an upper bound on the
    poset height, then the dimension is bounded by a polynomial in [h]. *)
Definition planar_cover_poset_dimension_polynomial_bound_statement : Prop :=
  exists C d : nat,
    forall (P : finite_poset) (h : nat),
      wagner_planar (poset_cover_graph P) ->
      poset_height_at_most P h ->
      poset_dimension_at_most P (C * h.+1 ^ d).
