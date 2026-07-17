(** * Chromatic.conjectures.X192 -- v2 triangle-free additive approximation row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X192 vocabulary ***********************************************)

Definition x192_proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  exists H : sgraph, forall G : sgraph, C G -> ~ minor G H.

Definition x192_triangle_free (G : sgraph) : Prop := girth_geq G 4.

Definition x192_additive_chromatic_output
    (alpha : nat) (G : sgraph) (out : data) : Prop :=
  χ([set: G]) <= data_nat_value out /\
  data_nat_value out <= χ([set: G]) + alpha.

Definition x192_polytime_additive_chromatic_approx
    (C : sgraph -> Prop) (alpha : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => C G /\ x192_triangle_free G)
    (x192_additive_chromatic_output alpha).

(** ** X192 statements *****************************************************)

(** Dvorak-Kawarabayashi open question: whether a universal additive constant
    suffices for polynomial-time approximation of chromatic number on
    triangle-free graphs in every proper minor-closed class. *)
Definition triangle_free_minor_closed_chromatic_additive_approx_statement : Prop :=
  exists alpha : nat,
    forall C : sgraph -> Prop,
      x192_proper_minor_closed_class C ->
      x192_polytime_additive_chromatic_approx C alpha.
