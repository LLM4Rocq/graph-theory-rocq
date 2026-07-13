(** * Digraph.conjectures.X16 -- v2 quasi-kernel rows *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented.
From Digraph.conjectures Require Import X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X16 vocabulary ************************************************)

Definition x16_loopless (D : diGraphType) : Prop :=
  forall v : D, ~~ (v --> v).

(** Rocq's [diGraphType] permits loops; the source convention for "no source" is
    loopless digraphs, so an in-neighbour is required to be distinct. *)
Definition x16_no_sources (D : diGraphType) : Prop :=
  forall v : D, [exists u : D, (u != v) && (u --> v)].

Definition x16_one_covered_set (D : diGraphType) (K : {set D}) : {set D} :=
  [set v : D | @x2_covers1 D K v].

(** ** X16 statements ******************************************************)

(** Studies slice: Erdős-Székely small quasi-kernel conjecture. *)
Definition small_quasi_kernel_statement : Prop :=
  forall D : diGraphType,
    x16_loopless D ->
    x16_no_sources D ->
    exists K : {set D},
      @two_kernel D K /\ (2 * #|K| <= #|D|)%N.

(** Studies slice: Spiro's quasi-kernel half-covered conjecture. *)
Definition spiro_quasi_kernel_half_covered_statement : Prop :=
  forall D : diGraphType,
    x16_loopless D ->
    exists K : {set D},
      @two_kernel D K /\ (#|D| <= 2 * #|x16_one_covered_set K|)%N.
