(** * Chromatic.conjectures.X206 -- v2 list-chromatic Delta/c row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X206 vocabulary ***********************************************)

(** [omega(G) <= Delta(G)^(1/q)] without real exponents, equivalently
    [omega(G)^q <= Delta(G)] for positive integer [q]. *)
Definition x206_subpower_clique_bound (G : sgraph) (q : nat) : Prop :=
  (ω([set: G])) ^ q <= Delta G.

(** ** X206 statements *****************************************************)

(** Bonamy-Kelly-Nelson-Postle Question 1.5: under a subpower clique bound,
    list chromatic number should be at most [Delta/c].

    The real parameter [c > 1] is represented by a positive rational [a/b > 1].
    The real inequality [chi_l(G) <= Delta/c] becomes
    [a * chi_l(G) <= b * Delta(G)].  The function [f] is represented on
    rational inputs by a positive integer exponent denominator [f a b]; this is
    faithful to the source question because increasing [f(c)] only strengthens
    the clique-size hypothesis. *)
Definition list_chromatic_delta_over_c_subpower_clique_statement : Prop :=
  exists f : nat -> nat -> nat,
    forall a b : nat,
      0 < b ->
      b < a ->
      0 < f a b /\
      forall (G : sgraph) (m : nat),
        is_choice_number G m ->
        x206_subpower_clique_bound G (f a b) ->
        a * m <= b * Delta G.
