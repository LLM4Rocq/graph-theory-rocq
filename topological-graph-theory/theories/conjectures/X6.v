(** * Topological.conjectures.X6 -- v2 milestone X6, clean planar induced-forest rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X6 statements *******************************************************)

(** Studies slice: Akiyama-Watanabe induced forest conjecture. *)
Definition bipartite_planar_induced_forest_five_eighths_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> bipartite G ->
    exists S : {set G}, is_forest S /\ 5 * #|G| <= 8 * #|S|.

(** Studies slice: Kowalik-Luzar-Krekovski induced forest conjecture. *)
Definition girth_five_planar_induced_forest_seven_tenths_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> girth_geq G 5 ->
    exists S : {set G}, is_forest S /\ 7 * #|G| <= 10 * #|S|.
