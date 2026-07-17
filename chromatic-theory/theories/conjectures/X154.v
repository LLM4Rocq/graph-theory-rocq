(** * Chromatic.conjectures.X154 -- v2 duplicate fixed-surface 4-colourability row *)

From Chromatic.conjectures Require Import X152.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Same fixed-surface 4-colourability algorithm question as X152, extracted
    from a later paper as an open step in Thomassen's program.  Reuse the X152
    statement so the duplicate cannot drift. *)
Definition fixed_surface_four_colourability_polytime_duplicate_statement : Prop :=
  fixed_surface_four_colourability_polytime_statement.
