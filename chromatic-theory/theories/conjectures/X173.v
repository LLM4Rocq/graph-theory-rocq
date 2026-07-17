(** * Chromatic.conjectures.X173 -- v2 planar triangle-free fractional row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X130.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Dvorak-Masarik-Musilek-Pangrac: every n-vertex planar triangle-free graph
    has fractional chromatic number at most [3 - 3/(n+1)].

    The rational bound is encoded as [3n/(n+1)] using X130's audited finite-graph
    fractional-chromatic predicate.  Triangle-free is [girth_geq G 4]. *)
Definition planar_triangle_free_fractional_chromatic_bound_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    girth_geq G 4 ->
    x130_frac_chi_le G (3 * #|G|) (#|G|).+1.

