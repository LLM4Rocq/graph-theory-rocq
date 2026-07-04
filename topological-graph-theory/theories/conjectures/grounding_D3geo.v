(** * Grounding for the D3 metric-geometry row (non-vacuity of the encoding). *)

From GTBase Require Export base.
From mathcomp Require Import all_algebra.
From Topological.foundations Require Import geometry.
From Topological.conjectures Require Import D3geo.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope ring_scope.

(** The geometric primitive has content: a non-degenerate right triangle has
    nonzero orientation ([orient_unit] in geometry.v proves it equals [1]), so
    [orient] is not the constant-zero relation — hence [between], [seg_cross] and
    [seg_meet] are all non-trivial (not silently satisfiable / silently false). *)

(** A single vertex embeds straight-line onto any point (no edges to constrain),
    so [straightline_planar] is satisfiable — the drawing predicate underlying
    [n_universal] is not vacuously false. *)
Lemma straightline_drawing_inhabited (R : realFieldType) (a : pt R) :
  straightline_planar (G := 'K_1) (fun=> a).
Proof. exact: straightline_planar_K1. Qed.
