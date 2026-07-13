(** * Chromatic.conjectures.X69 -- v2 Havel problem row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X69 vocabulary ************************************************)

Definition x69_triangle (G : sgraph) (T : {set G}) : Prop :=
  #|T| = 3 /\ clique T.

Definition x69_triangles_distance_at_least (G : sgraph) (d : nat) : Prop :=
  forall A B : {set G},
    x69_triangle A ->
    x69_triangle B ->
    A != B ->
    forall a b : G, a \in A -> b \in B -> b \notin ball d.-1 a.

(** ** X69 statements ******************************************************)

(** Studies slice: Havel's problem on planar graphs with distant triangles. *)
Definition havel_distant_triangles_three_colourable_statement : Prop :=
  exists d : nat,
    0 < d /\
    forall G : sgraph,
      wagner_planar G ->
      x69_triangles_distance_at_least G d ->
      χ([set: G]) <= 3.
