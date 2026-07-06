(** * Grounding for the ends rows (the ends/ray vocabulary has content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf3.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [reachP] is reflexive on its predicate, so [end_equiv]'s in-component walks
    are non-trivial (a vertex reaches itself). *)
Lemma reachP_refl (G : iGraph) (P : iV G -> Prop) (x : iV G) :
  P x -> reachP P x x.
Proof. exact: reachP0. Qed.

(** A concrete RAY exists (so [ray]/[wray] are non-vacuous): on [Komega] the
    identity sequence [0,1,2,…] is a ray (injective; consecutive vertices
    distinct, hence adjacent). *)
Lemma ray_Komega : ray (G := Komega) id.
Proof.
split; first exact: inj_id.
by move=> n /= H; move: (ltn_eqF (ltnSn n)); rewrite -H eqxx.
Qed.

(** [same_start] and [disjoint_rays] are a genuine equivalence-flavoured / apartness
    relation on families: [same_start] is reflexive, and disjointness is about
    distinct indices only. *)
Lemma same_start_refl (G : iGraph) (K : nat -> nat -> iV G) : same_start K K.
Proof. by split=> i; exists i. Qed.

(** [devours] is inhabited as a shape: the family that repeats [r0] devours the
    end whenever every ω-ray meets [r0] — witnessing the predicate is not
    vacuously false-typed. *)
Lemma devours_selfrepeat (G : iGraph) (r0 : nat -> iV G) :
  (forall r, wray r0 r -> exists n m, r n = r0 m) ->
  devours r0 (fun _ => r0).
Proof. by move=> H r /H [n [m E]]; exists 0, n, m. Qed.

(** The double-ray vocabulary of [uniquely_hamiltonian] has a real carrier: the
    integer line [zline] (vertices [int]; [m ~ n] iff they differ by 1) is a
    genuine [iGraph], and the identity sequence [0,±1,±2,…] is a SPANNING DOUBLE
    RAY on it — grounding both [dray] (injective, consecutive-adjacent) and
    [spanning_dray] (every vertex is hit).  So [spanning_dray] is not vacuous. *)
Definition zadj (m n : int) : Prop := (n = m + 1)%R \/ (m = n + 1)%R.

Lemma zadj_sym : irel_sym zadj.
Proof. by move=> x y [E|E]; [right|left]. Qed.

Lemma zadj_irr : irel_irr zadj.
Proof.
move=> x [] /eqP; rewrite -subr_eq0 opprD addrA subrr add0r oppr_eq0 oner_eq0 //.
Qed.

Definition zline : iGraph := Build_iGraph zadj_sym zadj_irr.

Lemma dray_spanning_zline : spanning_dray (G := zline) id.
Proof.
split; last by move=> x; exists x.
split; first exact: inj_id.
by move=> n; left.
Qed.

(** [same_circle] (the "unique up to edge set" relation at the heart of
    [uniquely_hamiltonian]) is reflexive: every double ray has the same edge set
    as itself. *)
Lemma same_circle_refl (G : iGraph) (d : int -> iV G) : same_circle d d.
Proof. by move=> x y; split. Qed.

(** ================================================================= *)
(** ** Graph POWERS and Hamilton circles

    Row [hamiltonian_cycles_in_powers_of_infinite_graphs] (OPG): "countable
    connected [G] => [G^3] has a Hamilton circle; 2-connected countable [G] =>
    [G^2] has a Hamilton circle".  The row's statement leg is UNFORMALIZED in
    the corpus and its [graph-power] primitive is DEFERRED, so we build the
    power operation faithfully here and record only RIGHT-POLARITY,
    always-true-direction fragments.  The deep content (Fleischner 1974 / the
    Georgakopoulos 2009 infinite refinement) is NOT touched: every lemma below
    only says powers ADD edges and hence never DESTROY a spanning double ray
    (the corpus Hamilton-circle proxy of [D4inf3]).

    [ipow k G] keeps [G]'s vertices and joins two DISTINCT vertices exactly
    when a [G]-walk of length [<= k] connects them; since a shortest walk is a
    path, this is the standard "distance [<= k]" [k]-th power.  Walks are the
    bounded inductive family [bwalk] (edges appended at the tail). *)

(** A walk of length [k] in [G] (repeated vertices allowed). *)
Inductive bwalk (G : iGraph) : nat -> iV G -> iV G -> Prop :=
  | bw0 x : bwalk 0 x x
  | bwS k x y z : bwalk k x y -> iadj y z -> bwalk k.+1 x z.

(** Edge symmetry / irreflexivity as directly-usable facts on [iadj]. *)
Lemma iadj_sym (G : iGraph) (x y : iV G) : iadj x y -> iadj y x.
Proof. exact: iedge_sym. Qed.

Lemma iadj_irr (G : iGraph) (x : iV G) : ~ iadj x x.
Proof. exact: iedge_irr. Qed.

(** Prepend an edge to the front of a walk (the tool to reverse walks). *)
Lemma bwalk_prepend (G : iGraph) k (y z : iV G) :
  bwalk k y z -> forall x : iV G, iadj x y -> bwalk k.+1 x z.
Proof.
elim=> {k y z} [a x e | k a b c _ IH e x f].
- exact: (bwS (bw0 x) e).
- exact: (bwS (IH x f) e).
Qed.

(** Walks reverse (uses edge symmetry): this is what makes [ipow] a valid
    (symmetric) [iGraph]. *)
Lemma bwalk_rev (G : iGraph) k (x y : iV G) : bwalk k x y -> bwalk k y x.
Proof.
elim=> {k x y} [a | k a b c _ IH e].
- exact: bw0.
- exact: (bwalk_prepend IH (iadj_sym e)).
Qed.

(** Adjacency in the [k]-th power: distinct vertices joined by a walk of length
    at most [k]. *)
Definition powadj (k : nat) (G : iGraph) (x y : iV G) : Prop :=
  x <> y /\ exists j, (j <= k)%N /\ bwalk j x y.

Lemma powadj_sym (k : nat) (G : iGraph) : irel_sym (@powadj k G).
Proof.
move=> x y [ne [j [Hj Hw]]]; split.
  by move=> E; apply: ne; rewrite E.
by exists j; split=> //; apply: bwalk_rev.
Qed.

Lemma powadj_irr (k : nat) (G : iGraph) : irel_irr (@powadj k G).
Proof. by move=> x [ne _]; apply: ne. Qed.

(** The [k]-th power of [G] (same vertices, distance-[<= k] edges). *)
Definition ipow (k : nat) (G : iGraph) : iGraph :=
  Build_iGraph (@powadj_sym k G) (@powadj_irr k G).

(** RIGHT-POLARITY (teeth / always-true structural core): powers only ADD
    edges.  Every edge of [G] is an edge of every power [G^{k+1}].  This is the
    load-bearing monotonicity [G = G^1 ⊆ G^{k+1}] that makes powers "richer";
    it can only ever HELP a graph become Hamiltonian, never hurt. *)
Lemma iadj_pow (k : nat) (G : iGraph) (x y : iV G) :
  iadj x y -> iadj (G := ipow k.+1 G) x y.
Proof.
move=> H; split.
  by move=> E; move: H; rewrite E; apply: iadj_irr.
by exists 1; split=> //; apply: (bwS (bw0 x) H).
Qed.

(** RIGHT-POLARITY (always-true direction): edge-monotonicity means a Hamilton
    circle (spanning double ray, the [D4inf3] proxy) is never DESTROYED by
    taking powers.  If [G] already has one, so does every power [G^{k+1}].
    This is the settled/decided upward-closure direction of the conjecture. *)
Lemma pow_preserves_spanning_dray (k : nat) (G : iGraph) (d : int -> iV G) :
  spanning_dray (G := G) d -> spanning_dray (G := ipow k.+1 G) d.
Proof.
move=> [[dinj dadj] dspan]; split; last exact: dspan.
by split; [exact: dinj | move=> n; apply: iadj_pow; apply: dadj].
Qed.

(** RIGHT-POLARITY (small instance of the cube clause): the integer line
    [zline] is a countable connected graph whose CUBE [zline^3] carries a
    spanning double ray — a concrete witness pinning the [k = 3] clause TRUE.
    (Reuses [dray_spanning_zline]; [zline] is already Hamiltonian at [G^1], so
    this is the decided, non-Fleischner corner.) *)
Lemma zline_cube_hamiltonian : spanning_dray (G := ipow 3 zline) id.
Proof.
apply: (pow_preserves_spanning_dray 2).
exact: dray_spanning_zline.
Qed.

(** The antecedent's countability guard is inhabited by [zline] (its vertex
    type [int] injects into [nat]), so the cube witness above genuinely lands
    inside the conjecture's hypothesis class rather than quantifying over
    nothing. *)
Lemma zline_countable : countable_graph zline.
Proof. by exists pickle; apply: (pcan_inj pickleK). Qed.
