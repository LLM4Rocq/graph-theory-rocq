(** * GTMisc.conjectures.X128 -- v2 cheap balanced separators row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X128 vocabulary ***********************************************)

Fixpoint x128_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x128_poly_eval q x else 0.

(** Radius-bounded branch sets for shallow minors. *)
Definition x128_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition x128_shallow_minor_model (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, x128_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x128_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    x128_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, x128_grad_at_most G r (x128_poly_eval p r).

Definition x128_weight (G : sgraph) (rho : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) rho v.

Definition x128_cheap_bal_sep (G : sgraph) (rho : G -> nat) (t k : nat) : Prop :=
  exists S Z : {set G},
    [/\ #|Z| <= k,
        t * x128_weight rho S <= x128_weight rho [set: G] &
        forall A : {set G},
          A \subset ~: (S :|: Z) ->
          connected A ->
          2 * x128_weight rho A <= x128_weight rho [set: G]].

(** ** X128 statements *****************************************************)

(** Studies slice: Dvorak conjecture -- for every polynomial p there is a function
    q such that every graph of expansion bounded by p, with any cost assignment
    rho and any t >= 1, has a balanced separator that is (rho/t)-cheap with q(t)
    outliers.  Bounded expansion is stated through exact finite shallow-minor
    branch-set models; cheapness and balance are cross-multiplied over natural
    vertex weights. *)
Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).
