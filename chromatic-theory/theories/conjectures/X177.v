(** * Chromatic.conjectures.X177 -- v2 forests of lanterns pervasive row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X177 vocabulary ***********************************************)

Definition x177_induced_path_between
    (G : sgraph) (x y : G) (p : seq G) : Prop :=
  path (--) x p /\
  last x p = y /\
  uniq (x :: p) /\
  forall u v : G,
    u \in x :: p -> v \in x :: p -> u -- v ->
    exists z : G, (u == z /\ v \in p /\ last u [:: v] = v) \/
      (v == z /\ u \in p /\ last v [:: u] = u).

Definition x177_lantern (H : sgraph) : Prop :=
  exists a b : H,
    a != b /\
    forall i : 'I_3,
      exists p : seq H,
        x177_induced_path_between a b p /\ 2 <= size p.

Definition x177_forest_of_lanterns (H : sgraph) : Prop :=
  exists (T : sgraph) (piece : T -> {set H}),
    is_tree [set: T] /\
    (forall v : H, exists t : T, v \in piece t) /\
    (forall t : T, is_forest (piece t) \/ x177_lantern (induced (piece t))) /\
    (forall t u : T, t != u -> #|piece t :&: piece u| <= 1).

Definition x177_contains_induced_long_subdivision
    (G H : sgraph) (ell : nat) : Prop :=
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            ell <= size p,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].

(** ** X177 statements *****************************************************)

(** Scott-Seymour informal conjecture: every forest of lanterns is pervasive,
    using a finite tree of forest/lantern pieces and long induced-subdivision
    branch-path witnesses. *)
Definition forest_of_lanterns_pervasive_statement : Prop :=
  forall (H : sgraph) (nu ell : nat),
    x177_forest_of_lanterns H ->
    exists c : nat,
      forall G : sgraph,
        ω([set: G]) <= nu ->
        c < χ([set: G]) ->
        x177_contains_induced_long_subdivision G H ell.
