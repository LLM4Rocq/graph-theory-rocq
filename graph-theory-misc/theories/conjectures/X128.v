(** * GTMisc.conjectures.X128 -- v2 cheap balanced separators row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X128 vocabulary ***********************************************)

Fixpoint x128_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x128_poly_eval q x else 0.

(** PLACEHOLDER for "[G] has expansion bounded by the polynomial [p]".  Bounded
    expansion is a sparsity notion (grad_r / shallow-minor densities) with no
    foundation in this corpus; proxied here by the (over-restrictive) condition
    that the order of [G] is bounded by [p(0)].  NOT faithful. *)
Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  #|G| <= x128_poly_eval p 0.

(** PLACEHOLDER for "[G] has a balanced separator that is (rho/t)-cheap with at
    most [k] outliers".  Balanced separators, real-valued cost assignments
    [rho : V(G) -> R+_0] (proxied by [G -> nat]), the cheapness ratio, and the
    outlier count are not formalized; proxied here by the (over-restrictive)
    condition that [k] bounds the order of [G], which ignores [rho] and [t].
    NOT faithful. *)
Definition x128_cheap_bal_sep (G : sgraph) (rho : G -> nat) (t k : nat) : Prop :=
  #|G| <= k.

(** ** X128 statements *****************************************************)

(** Studies slice: Dvorak conjecture -- for every polynomial p there is a function
    q such that every graph of expansion bounded by p, with any cost assignment
    rho and any t >= 1, has a balanced separator that is (rho/t)-cheap with q(t)
    outliers.

    /!\ FAITHFULNESS DEFECT (tracked BLOCKED -- meta/X111-X130_faithfulness_audit.md, X128):
    The two missing notions are replaced by CONCRETE LOCAL PLACEHOLDERS above
    ([x128_expansion_bounded], [x128_cheap_bal_sep]), which is why the statement
    below is NOT a faithful encoding:
      (1) [x128_expansion_bounded G p] -- "G has expansion bounded by p": bounded
          expansion (grad_r / shallow-minor densities) has no foundation here;
      (2) [x128_cheap_bal_sep G rho t k] -- "G has a (rho/t)-cheap balanced
          separator with at most k outliers": balanced separators, real-valued cost
          assignments, the cheapness ratio, and the outlier count are not formalized.
    The placeholders are deliberately over-restrictive, so the statement leans
    vacuously true (like X90) rather than being definitionally refutable: note it
    is a CONCRETE Prop with no top-level [forall] over an unconstrained predicate,
    so it cannot be collapsed to False by instantiation.  A faithful fix needs a
    bounded-expansion / sparsity foundation and a real-cost separator layer,
    deliberately out of scope.  Statement leg is `blocked` in
    v2_statement_waves.json (this .v still compiles). *)
Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).
