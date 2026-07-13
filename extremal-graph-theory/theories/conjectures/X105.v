(** * Extremal.conjectures.X105 -- v2 tree inducibility row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X105 vocabulary ***********************************************)

Definition x105_induced_copy_family
    (H G : sgraph) (C : {set {set G}}) : Prop :=
  forall S : {set G},
    S \in C <-> #|S| = #|H| /\ inhabited (induced S ≃ H).

Definition x105_path_tree (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x105_star_tree (T : sgraph) : Prop :=
  is_tree [set: T] /\
  exists c : T, forall v : T, v != c -> v -- c /\ #|N(v)| = 1.

Definition x105_density_at_most
    (H G : sgraph) (C : {set {set G}}) (num den : nat) : Prop :=
  den * #|C| <= num * 'C(#|G|, #|H|).

(** ** X105 statements *****************************************************)

(** Studies slice: Bubeck-Linial problem asking for a universal epsilon so
    every tree that is neither a star nor a path has inducibility at most
    1-epsilon. *)
Definition non_star_non_path_tree_inducibility_bounded_away_statement : Prop :=
  exists eps_num eps_den : nat,
    [/\ 0 < eps_num, eps_num < eps_den
      & forall T : sgraph,
          is_tree [set: T] ->
          ~ x105_star_tree T ->
          ~ x105_path_tree T ->
          exists N : nat,
            forall (G : sgraph) (C : {set {set G}}),
              N <= #|G| ->
              @x105_induced_copy_family T G C ->
              @x105_density_at_most T G C (eps_den - eps_num) eps_den].
