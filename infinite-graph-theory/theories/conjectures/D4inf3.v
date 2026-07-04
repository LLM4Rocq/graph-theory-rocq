(** * Infinite.conjectures.D4inf3 — the two ENDS rows.

    Both are built on the combinatorial end-equivalence [end_equiv]
    (foundations.igraph), itself on [finite_sub]/[reachP] — no point-set topology,
    no Freudenthal compactification, no choice.

    - end_devouring_rays (done): a purely combinatorial reconfiguration claim.
    - infinite_uniquely_hamiltonian (PARTIAL): "uniquely hamiltonian" is rendered
      by a spanning DOUBLE RAY (an [int]-indexed two-way path).  In the co-assumed
      one-ended locally-finite class a Hamilton CIRCLE of [|G|] collapses to a
      spanning double ray, so this is a faithful proxy there — but it is NOT the
      general topological Hamilton circle, hence PARTIAL. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** end_devouring_rays  (Problem, OPEN)

    Source: "Let [G] be a graph, [ω] a countable end, [K] an infinite set of
    pairwise-disjoint [ω]-rays.  Prove there is a set [K'] of pairwise-disjoint
    [ω]-rays that DEVOURS [ω] whose set of starting vertices equals that of [K]."

    The end [ω] is given by a representative ray [r0]; an [ω]-ray is a ray
    end-equivalent to [r0] ([wray]).  [K],[K'] are [nat]-indexed families of rays
    (infinite + pairwise disjoint).  [K'] DEVOURS [ω] when every [ω]-ray meets
    some ray of [K']; [same_start] equates the two families' initial vertices.
    "Countable end" is guarded by [countable_graph]. *)
Definition wray (G : iGraph) (r0 r : nat -> iV G) : Prop :=
  ray r /\ end_equiv r r0.
Definition disjoint_rays (G : iGraph) (K : nat -> nat -> iV G) : Prop :=
  forall i j n m, i <> j -> K i n <> K j m.
Definition devours (G : iGraph) (r0 : nat -> iV G) (K' : nat -> nat -> iV G) : Prop :=
  forall r : nat -> iV G, wray r0 r -> exists i n m, r n = K' i m.
Definition same_start (G : iGraph) (K K' : nat -> nat -> iV G) : Prop :=
  (forall i, exists j, K' j 0 = K i 0) /\ (forall j, exists i, K i 0 = K' j 0).

Definition end_devouring_rays_statement : Prop :=
  forall (G : iGraph) (r0 : nat -> iV G) (K : nat -> nat -> iV G),
    countable_graph G -> ray r0 ->
    (forall i, wray r0 (K i)) -> disjoint_rays K ->
    exists K' : nat -> nat -> iV G,
      [/\ (forall i, wray r0 (K' i)), disjoint_rays K',
          devours r0 K' & same_start K K' ].

(** ** infinite_uniquely_hamiltonian_graphs  (Problem, OPEN — PARTIAL proxy)

    Source: "Are there uniquely hamiltonian locally finite 1-ended graphs which
    are regular of degree r > 2?"

    [locally_finite]/[regular r]/[one_ended] are combinatorial (finite_sub,
    end_equiv).  A DOUBLE RAY is an injective [int]-indexed path; a SPANNING one
    is a Hamilton-circle proxy; [uniquely_hamiltonian] asks for one that is unique
    up to its edge set ([same_circle]). *)
Definition locally_finite (G : iGraph) : Prop :=
  forall x : iV G, finite_sub (fun w => iadj x w).
Definition regular (r : nat) (G : iGraph) : Prop :=
  forall x : iV G, exists e : 'I_r -> iV G,
    injective e /\ (forall w, iadj x w <-> exists i, e i = w).
Definition one_ended (G : iGraph) : Prop :=
  (exists r : nat -> iV G, ray r) /\
  (forall r r' : nat -> iV G, ray r -> ray r' -> end_equiv r r').

Definition dray (G : iGraph) (d : int -> iV G) : Prop :=
  injective d /\ forall n : int, iadj (d n) (d (n + 1)%R).
Definition spanning_dray (G : iGraph) (d : int -> iV G) : Prop :=
  dray d /\ forall x : iV G, exists n : int, d n = x.
Definition dray_edge (G : iGraph) (d : int -> iV G) (x y : iV G) : Prop :=
  exists n : int, (d n = x /\ d (n + 1)%R = y) \/ (d n = y /\ d (n + 1)%R = x).
Definition same_circle (G : iGraph) (d d' : int -> iV G) : Prop :=
  forall x y, dray_edge d x y <-> dray_edge d' x y.
Definition uniquely_hamiltonian (G : iGraph) : Prop :=
  exists d : int -> iV G,
    spanning_dray d /\ forall d', spanning_dray d' -> same_circle d d'.

Definition infinite_uniquely_hamiltonian_graphs_statement : Prop :=
  exists (G : iGraph) (r : nat),
    [/\ 2 < r, locally_finite G, regular r G, one_ended G & uniquely_hamiltonian G].
