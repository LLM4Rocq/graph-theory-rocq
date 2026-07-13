(** * Topological.conjectures.X103 -- v2 simultaneous embeddability row *)

From Stdlib Require Import ZArith.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope Z_scope.

(** ** Local X103 vocabulary ***********************************************)

Definition x103_point := (Z * Z)%type.

Definition x103_px (p : x103_point) : Z :=
  match p with (x, _) => x end.

Definition x103_py (p : x103_point) : Z :=
  match p with (_, y) => y end.

Definition x103_cross (a b c : x103_point) : Z :=
  (x103_px b - x103_px a) * (x103_py c - x103_py a) -
  (x103_py b - x103_py a) * (x103_px c - x103_px a).

Definition x103_between_coord (a b c : Z) : Prop :=
  (a <= c <= b) \/ (b <= c <= a).

Definition x103_on_segment (a b c : x103_point) : Prop :=
  x103_cross a b c = 0 /\
  x103_between_coord (x103_px a) (x103_px b) (x103_px c) /\
  x103_between_coord (x103_py a) (x103_py b) (x103_py c).

Definition x103_opposite_or_zero (a b : Z) : Prop :=
  (a <= 0 <= b) \/ (b <= 0 <= a).

Definition x103_segments_intersect
    (a b c d : x103_point) : Prop :=
  (x103_opposite_or_zero (x103_cross a b c) (x103_cross a b d) /\
   x103_opposite_or_zero (x103_cross c d a) (x103_cross c d b)) \/
  x103_on_segment a b c \/ x103_on_segment a b d \/
  x103_on_segment c d a \/ x103_on_segment c d b.

Definition x103_crossing_free_drawing
    (G : sgraph) (place : G -> x103_point) : Prop :=
  injective place /\
  forall x y u v : G,
    x -- y ->
    u -- v ->
    [&& x != u, x != v, y != u & y != v] ->
    ~ x103_segments_intersect (place x) (place y) (place u) (place v).

Definition x103_same_point_set
    (G H : sgraph) (placeG : G -> x103_point) (placeH : H -> x103_point)
    : Prop :=
  (forall x : G, exists y : H, placeG x = placeH y) /\
  forall y : H, exists x : G, placeH y = placeG x.

Definition x103_common_point_set_embedding (G H : sgraph) : Prop :=
  exists (placeG : G -> x103_point) (placeH : H -> x103_point),
    x103_crossing_free_drawing placeG /\
    x103_crossing_free_drawing placeH /\
    x103_same_point_set placeG placeH.

Definition x103_simultaneously_embeddable (G H : sgraph) : Prop :=
  x103_common_point_set_embedding G H.

(** ** X103 statements *****************************************************)

(** Studies slice: Brass et al. problem asking for two same-order planar
    graphs that are not simultaneously embeddable on a common point set.  The
    point-set drawing/crossing-free condition is kept as the local graph-drawing
    primitive for this row. *)
Definition two_planar_graphs_not_simultaneously_embeddable_statement : Prop :=
  exists G H : sgraph,
    [/\ wagner_planar G,
        wagner_planar H,
        Nat.eq #|G| #|H|
      & ~ x103_simultaneously_embeddable G H].
