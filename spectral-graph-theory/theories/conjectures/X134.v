(** * Spectral.conjectures.X134 -- v2 squared-energy duplicate row *)

From Spectral.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The squared-energy statement min{E2+(G),E2-(G)} >= n-1 is exactly the
    conjunction encoded in the audited X6 s+/s- row.  Reuse it as a synonym. *)
Definition elphick_farber_goldberg_wocjan_squared_energy_statement : Prop :=
  elphick_farber_goldberg_wocjan_splus_sminus_statement.

