(** * Extremal.conjectures.X207 -- v2 polynomial Rodl dependence row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X207 vocabulary ***********************************************)

Definition x207_H_free (H G : sgraph) : Prop := ~ minor G H.

Definition x207_density_at_least (G : sgraph) (a b : nat) : Prop :=
  a * #|G| * #|G| <= b * (2 * fg_edge_count G).

Definition x207_rodl_delta_works (H : sgraph) (d delta_num delta_den : nat) : Prop :=
  0 < delta_num /\ delta_num <= delta_den /\
  forall G : sgraph,
    x207_H_free H G ->
    exists S : {set G},
      #|S| * delta_den >= delta_num * #|G| /\
      (x207_density_at_least (induced S) d 1 \/
       x207_density_at_least (induced S) (1 - d) 1).

Definition x207_polynomial_rodl_delta (H : sgraph) : Prop :=
  exists C e : nat,
    forall d : nat,
      0 < d ->
      exists delta_num delta_den : nat,
        x207_rodl_delta_works H d delta_num delta_den /\
        delta_den <= C * d ^ e + C.

(** ** X207 statements *****************************************************)

(** Chudnovsky-Fox-Scott-Seymour-Spirkl discussion: a polynomial dependence of
    the Rodl-theorem parameter would imply Erdos-Hajnal. *)
Definition polynomial_rodl_dependence_statement : Prop :=
  forall H : sgraph, x207_polynomial_rodl_delta H.
