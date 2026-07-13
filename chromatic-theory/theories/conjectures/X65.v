(** * Chromatic.conjectures.X65 -- v2 polynomial Gyarfas-Sumner row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import U8 X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X65 statements ******************************************************)

(** arXiv:2202.05557, Conjecture 1.3: every forest-free class is
    polynomially chi-bounded. *)
Definition forest_free_polynomial_chi_bound_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    x3_polynomially_chi_bounded (fun G : sgraph => ~ has_induced H G).
