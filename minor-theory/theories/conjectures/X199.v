(** * Minor.conjectures.X199 -- v2 constant-size separator residue row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X199 vocabulary ***********************************************)

Definition x199_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x199_weighted_balanced_separator
    (G : sgraph) (rho : G -> nat) (S M : {set G}) : Prop :=
  forall A : {set G},
    A \subset ~: (S :|: M) ->
    connected A ->
    2 * x199_weight rho A <= x199_weight rho [set: G].

Definition x199_weighted_balanced_separator_with_constant_M
    (C : sgraph -> Prop) (ell bound : nat) : Prop :=
  forall (G : sgraph) (rho : G -> nat),
    C G ->
    exists S M : {set G},
      [/\ #|M| <= bound,
          #|S| <= ell * sqrt_ceil #|G|.+1 + ell &
          x199_weighted_balanced_separator rho S M].

(** ** X199 statements *****************************************************)

(** Dvorak conjecture: in the separator theorem for classes with polynomial
    omega-expansion, the auxiliary set [M] can have constant size independent of
    [|V(G)|]. *)
Definition strongly_sublinear_separator_constant_M_statement : Prop :=
  forall C : sgraph -> Prop,
    exists bound : nat,
      forall ell : nat,
        1 <= ell ->
        x199_weighted_balanced_separator_with_constant_M C ell bound.
