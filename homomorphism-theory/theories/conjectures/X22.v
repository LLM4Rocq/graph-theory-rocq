(** * Hom.conjectures.X22 -- v2 planar high-girth homomorphism row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X22 statements ******************************************************)

(** Studies slice: Jaeger's high-girth planar graph homomorphism conjecture. *)
Definition jaeger_high_girth_planar_odd_cycle_hom_statement : Prop :=
  forall (k : nat) (G : sgraph),
    1 <= k ->
    wagner_planar G ->
    girth_geq G (4 * k) ->
    homs_to G (cycle_graph (2 * k + 1)).
