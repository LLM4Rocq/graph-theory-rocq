(** * Chromatic.conjectures.X161 -- v2 controlled triangle-free four-hole row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X161 vocabulary ***********************************************)

Definition x161_local_chromatic_radius_two (G : sgraph) : nat :=
  \max_(v : G) χ([set: induced (rel_ball (--) 2 v)]).

Definition x161_two_phi_controlled (G : sgraph) (phi : nat -> nat) : Prop :=
  forall S : {set G},
    χ([set: induced S]) <= phi (x161_local_chromatic_radius_two (induced S)).

Definition x161_has_four_hole (G : sgraph) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = 4.

(** ** X161 statements *****************************************************)

(** Informal question: Statement 2.1 may hold for ell=4.  The control hypothesis
    is rendered as the usual radius-2 local-chromatic control inequality for every
    induced subgraph. *)
Definition controlled_triangle_free_four_hole_statement : Prop :=
  forall phi : nat -> nat,
    {mono phi : x y / x <= y >-> x <= y} ->
    exists n : nat,
      forall G : sgraph,
        triangle_free G ->
        x161_two_phi_controlled G phi ->
        n < χ([set: G]) ->
        x161_has_four_hole G.
