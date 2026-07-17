(** * Chromatic.conjectures.X203 -- v2 separation choosability min-degree row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X203 vocabulary ***********************************************)

Definition x203_separated_k_list_assignment
    (G : sgraph) (C : finType) (L : G -> {set C}) (k : nat) : Prop :=
  (forall v : G, #|L v| = k) /\
  forall u v : G, u -- v -> #|L u :&: L v| <= 1.

Definition x203_separation_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    x203_separated_k_list_assignment L k -> @list_colourable G C L.

Definition x203_separation_choosability_at_least (G : sgraph) (k : nat) : Prop :=
  forall j : nat, j < k -> ~ x203_separation_choosable G j.

Definition x203_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

(** ** X203 statements *****************************************************)

(** Esperet-Kang-Thomasse Conjecture 1.3: separation choosability tends to
    infinity with minimum degree. *)
Definition separation_choosability_min_degree_unbounded_statement : Prop :=
  exists x : nat -> nat,
    (forall B : nat, exists d : nat, B <= x d) /\
    forall (d : nat) (G : sgraph),
      x203_min_degree_at_least G d ->
      x203_separation_choosability_at_least G (x d).
