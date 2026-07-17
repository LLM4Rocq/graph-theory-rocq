(** * Chromatic.conjectures.X131 -- v2 duplicate Dvorak-Mnich fractional row *)

From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This studies-slice row is a duplicate of X130: the same Dvorak-Mnich
    conjecture that planar graphs of girth at least five have fractional
    chromatic number uniformly bounded below 3.  Reuse the audited X130
    encoding byte-for-byte through a synonym, so the duplicate row cannot drift. *)
Definition dvorak_mnich_planar_girth5_fractional_chromatic_duplicate_statement : Prop :=
  dvorak_mnich_planar_girth5_fractional_chromatic_statement.

