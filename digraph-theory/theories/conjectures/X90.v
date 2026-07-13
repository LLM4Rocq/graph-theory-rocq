(** * Digraph.conjectures.X90 -- v2 F-subdivision complexity row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X90 vocabulary ************************************************)

Fixpoint x90_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x90_poly_eval q x else 0.

Definition x90_problem := diGraphType -> Prop.

Definition x90_polynomial_time_decidable (P : x90_problem) : Prop :=
  exists (dec : diGraphType -> bool) (cost : diGraphType -> nat) (p : seq nat),
    (forall D : diGraphType, dec D <-> P D) /\
    forall D : diGraphType, cost D <= x90_poly_eval p #|D|.

Definition x90_many_one_poly_reduces (P Q : x90_problem) : Prop :=
  exists (red : diGraphType -> diGraphType) (cost : diGraphType -> nat) (p : seq nat),
    (forall D : diGraphType, P D <-> Q (red D)) /\
    forall D : diGraphType, cost D <= x90_poly_eval p #|D|.

Definition x90_in_np (P : x90_problem) : Prop :=
  exists (cert_size : diGraphType -> nat) (p : seq nat),
    forall D : diGraphType, cert_size D <= x90_poly_eval p #|D|.

Definition x90_np_complete (P : x90_problem) : Prop :=
  x90_in_np P /\
  forall Q : x90_problem, x90_in_np Q -> x90_many_one_poly_reduces Q P.

Definition x90_f_subdivision_problem (F : diGraphType) : x90_problem :=
  fun D : diGraphType => contains_subdivision F D.

(** ** X90 statements ******************************************************)

(** Studies slice: Bang-Jensen et al. dichotomy conjecture for the
    F-Subdivision problem.  The computation model is a local polynomial
    cost/reduction interface over finite digraph instances.

    /!\ FAITHFULNESS DEFECT (tracked BLOCKED — meta/X10-X110_faithfulness_audit.md, X90):
    [cost]/[cert_size] above are decoupled from any computation (only bounded by a
    polynomial), so [x90_in_np] holds for EVERY problem (cert_size := 0) and
    [x90_polynomial_time_decidable] collapses to bare decidability — the dichotomy
    is vacuously true.  A faithful fix needs a genuine poly-TIME model (Turing/RAM/
    unit-cost lambda), deliberately out of scope; see meta/X90_polytime_fix_sketch.md.
    Statement leg is `blocked` in v2_statement_waves.json (this .v still compiles). *)
Definition f_subdivision_complexity_dichotomy_statement : Prop :=
  forall F : diGraphType,
    x90_polynomial_time_decidable (x90_f_subdivision_problem F) \/
    x90_np_complete (x90_f_subdivision_problem F).
