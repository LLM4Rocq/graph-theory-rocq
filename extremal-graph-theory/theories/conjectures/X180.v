(** * Extremal.conjectures.X180 -- v2 logarithmic-degree multitasker row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X180 vocabulary ***********************************************)

Definition x180_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset fg_edges G /\
  forall e f : {set G}, e \in M -> f \in M -> e != f -> e :&: f = set0.

Definition x180_induced_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  x180_matching M /\
  forall e f : {set G}, e \in M -> f \in M -> e != f ->
    forall x y : G, x \in e -> y \in f -> ~~ (x -- y).

Definition x180_multitasker_capacity_at_least (G : sgraph) (a b : nat) : Prop :=
  0 < b /\
  forall M : {set {set G}},
    x180_matching M ->
    exists I : {set {set G}},
      I \subset M /\ x180_induced_matching I /\ b * #|I| >= a * #|M|.

Definition x180_multitasker_capacity_positive (G : sgraph) : Prop :=
  exists a b : nat, 0 < a /\ x180_multitasker_capacity_at_least G a b.

Definition x180_average_degree_logarithmic (G : sgraph) : Prop :=
  exists c C : nat,
    0 < c /\ 0 < C /\
    c * #|G| * (trunc_log 2 #|G|).+1 <= 2 * fg_edge_count G /\
    2 * fg_edge_count G <= C * #|G| * (trunc_log 2 #|G|).+1.

(** ** X180 statements *****************************************************)

(** Alon-Cohen-Dey-Griffiths-Musslick-Ozcimder-Reichman-Shinkar-Wagner open
    problem: whether multitaskers with capacity bounded away from zero exist at
    average degree [Theta(log n)]. *)
Definition log_degree_multitasker_exists_statement : Prop :=
  forall n0 : nat,
    exists G : sgraph,
      n0 <= #|G| /\
      x180_average_degree_logarithmic G /\
      x180_multitasker_capacity_positive G.
