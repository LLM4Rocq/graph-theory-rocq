(** A repair of the viability step in attacks/2312.13061__01.

    Source: arXiv:2312.13061v1, Section 2.  The target grid has vertex
    set Z^2, steps +/-(1,0), +/-(0,1), +/-(1,1), hue (x+y) mod 3,
    and color (x mod 2,y mod 2).  Viability means an edge-, hue-, and
    color-preserving map to this infinite grid.

    This proves the exact six-cycle viability repair, not the complete
    arbitrary-d planar counterexample or a resolution of Conjecture 4. *)
From Stdlib Require Import ZArith Lia.
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition grid_point := (Z * Z)%type.
Definition grid_adj (p q : grid_point) : Prop :=
  let d := (Z.sub q.1 p.1, Z.sub q.2 p.2) in
  d = (1%Z,0%Z) \/ d = ((-1)%Z,0%Z) \/
  d = (0%Z,1%Z) \/ d = (0%Z,(-1)%Z) \/
  d = (1%Z,1%Z) \/ d = ((-1)%Z,(-1)%Z).
Definition grid_hue (p : grid_point) : Z := Z.modulo (Z.add p.1 p.2) 3.
Definition grid_color (p : grid_point) : grid_point :=
  (Z.modulo p.1 2, Z.modulo p.2 2).

Definition dappled_homomorphism (V : Type) (E : V -> V -> Prop)
    (hue : V -> Z) (color : V -> grid_point) (f : V -> grid_point) : Prop :=
  (forall u v, E u v -> grid_adj (f u) (f v)) /\
  (forall v, grid_hue (f v) = hue v) /\
  (forall v, grid_color (f v) = color v).

Definition viable (V : Type) (E : V -> V -> Prop)
    (hue : V -> Z) (color : V -> grid_point) : Prop :=
  exists f : V -> grid_point, dappled_homomorphism E hue color f.

Definition boundary_rel (i j : 'I_6) : bool :=
  (val j == (val i).+1 %% 6) || (val i == (val j).+1 %% 6).
Lemma boundary_sym : symmetric boundary_rel.
Proof. by move=> i j; rewrite /boundary_rel orbC. Qed.
Lemma boundary_irrefl : irreflexive boundary_rel.
Proof.
case=> -[|[|[|[|[|[|//]]]]]] hi; by vm_compute.
Qed.
Definition boundary : sgraph := SGraph boundary_sym boundary_irrefl.

Definition boundary_hue (v : boundary) : Z :=
  if odd (val v) then 1%Z else 0%Z.
Definition boundary_color (v : boundary) : grid_point :=
  match val v with
  | 0 => (0%Z,0%Z) | 1 => (0%Z,1%Z) | 2 => (1%Z,0%Z)
  | 3 => (1%Z,1%Z) | 4 => (1%Z,0%Z) | _ => (0%Z,1%Z)
  end.
Definition boundary_lift (v : boundary) : grid_point :=
  match val v with
  | 0 => (0%Z,0%Z) | 1 => (0%Z,1%Z) | 2 => (1%Z,2%Z)
  | 3 => (1%Z,3%Z) | 4 => (1%Z,2%Z) | _ => (0%Z,1%Z)
  end.

Lemma boundary_hue_proper : forall u v : boundary,
  u -- v -> boundary_hue u <> boundary_hue v.
Proof.
case=> -[|[|[|[|[|[|//]]]]]] hu;
case=> -[|[|[|[|[|[|//]]]]]] hv;
  by vm_compute.
Qed.
Lemma boundary_color_proper : forall u v : boundary,
  u -- v -> boundary_color u <> boundary_color v.
Proof.
case=> -[|[|[|[|[|[|//]]]]]] hu;
case=> -[|[|[|[|[|[|//]]]]]] hv;
  by vm_compute.
Qed.
Lemma boundary_lift_edges : forall u v : boundary,
  u -- v -> grid_adj (boundary_lift u) (boundary_lift v).
Proof.
case=> -[|[|[|[|[|[|//]]]]]] hu;
case=> -[|[|[|[|[|[|//]]]]]] hv;
  vm_compute; intuition congruence.
Qed.
Lemma boundary_lift_hues : forall v : boundary,
  grid_hue (boundary_lift v) = boundary_hue v.
Proof. case=> -[|[|[|[|[|[|//]]]]]] hv; by vm_compute. Qed.
Lemma boundary_lift_colors : forall v : boundary,
  grid_color (boundary_lift v) = boundary_color v.
Proof. case=> -[|[|[|[|[|[|//]]]]]] hv; by vm_compute. Qed.

Theorem six_cycle_precoloring_viable :
  viable (fun u v : boundary => is_true (u -- v)) boundary_hue boundary_color.
Proof.
exists boundary_lift; split; first exact: boundary_lift_edges.
split; [exact: boundary_lift_hues | exact: boundary_lift_colors].
Qed.

(* The opposite choice of bipartition labels is covered as well. The grid
   transformation (x,y) |-> (2-x,2-y) preserves parity and exchanges hues
   zero and one on this boundary. *)
Definition boundary_hue_swapped (v : boundary) : Z :=
  if odd (val v) then 0%Z else 1%Z.
Definition boundary_lift_swapped (v : boundary) : grid_point :=
  (Z.sub 2 (boundary_lift v).1, Z.sub 2 (boundary_lift v).2).

Lemma boundary_lift_swapped_edges : forall u v : boundary,
  u -- v -> grid_adj (boundary_lift_swapped u) (boundary_lift_swapped v).
Proof.
case=> -[|[|[|[|[|[|//]]]]]] hu;
case=> -[|[|[|[|[|[|//]]]]]] hv;
  vm_compute; intuition congruence.
Qed.
Lemma boundary_lift_swapped_hues : forall v : boundary,
  grid_hue (boundary_lift_swapped v) = boundary_hue_swapped v.
Proof. case=> -[|[|[|[|[|[|//]]]]]] hv; by vm_compute. Qed.
Lemma boundary_lift_swapped_colors : forall v : boundary,
  grid_color (boundary_lift_swapped v) = boundary_color v.
Proof. case=> -[|[|[|[|[|[|//]]]]]] hv; by vm_compute. Qed.

Theorem six_cycle_precoloring_viable_swapped :
  viable (fun u v : boundary => is_true (u -- v))
    boundary_hue_swapped boundary_color.
Proof.
exists boundary_lift_swapped; split; first exact: boundary_lift_swapped_edges.
split; [exact: boundary_lift_swapped_hues | exact: boundary_lift_swapped_colors].
Qed.

Print Assumptions six_cycle_precoloring_viable.
Print Assumptions six_cycle_precoloring_viable_swapped.
