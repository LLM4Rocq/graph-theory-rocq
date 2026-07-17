(** * Chromatic.conjectures.X149 -- v2 4-chromatic planar fractional row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Gimbel-Kundgen-Li-Thomassen: every 4-chromatic planar graph has fractional
    chromatic number strictly greater than 3.  The strict inequality is encoded
    as the negation of X130's audited [chi_f(G) <= 3] rational witness. *)
Definition gimbel_kundgen_li_thomassen_four_chromatic_planar_fractional_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    χ([set: G]) = 4 ->
    ~ x130_frac_chi_le G 3 1.

