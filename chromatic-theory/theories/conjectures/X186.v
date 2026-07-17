(** * Chromatic.conjectures.X186 -- v2 subdivision or chi2 row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X186 vocabulary ***********************************************)

Definition x186_chi2 (G : sgraph) : nat :=
  \max_(v : G) χ([set: induced (rel_ball (--) 2 v)]).

Definition x186_contains_induced_subdivision (G J : sgraph) : Prop :=
  exists branch : J -> G,
    injective branch /\
    forall x y : J,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : J, z != branch u].

(** ** X186 statements *****************************************************)

(** Scott-Seymour Conjecture 1.10: large chromatic number forces either an
    induced subdivision of [J] or large [chi_2]. *)
Definition subdivision_or_local_chi_two_statement : Prop :=
  forall (J : sgraph) (tau : nat),
    exists c : nat,
      forall G : sgraph,
        c < χ([set: G]) ->
        x186_contains_induced_subdivision G J \/ tau < x186_chi2 G.
