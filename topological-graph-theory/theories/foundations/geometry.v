(** * Finite plane geometry over an abstract ordered field — Track-A metric layer.

    Just enough to state straight-line-drawing questions faithfully, per the
    strict "build only what one row justifies" preflight — the single geometric
    primitive is [orient] (the sign of a 2×2 determinant); everything else
    (betweenness, segment meeting, planar straight-line drawing, universal point
    set) is built from it over an arbitrary [realFieldType R].  No metric /
    continuous topology, no Stdlib [Reals] (axiom-laden) — hence axiom-free.

    FAITHFULNESS (adversarial-audit informed).  A planar straight-line drawing
    is captured EXACTLY, with NO general-position side condition (the OPG source
    imposes none — classic universal sets such as grids are non-general-position):
    [straightline_planar] requires injective placement, NO vertex on a
    non-incident edge, and INDEPENDENT edges disjoint (the full [seg_meet], not
    merely a proper crossing).  Adjacent edges may meet only at their shared
    vertex — enforced by the no-vertex-on-edge clause (any overlap would put one
    endpoint on the other edge).  [seg_cross] alone is the proper-crossing test
    (machine-verified equal to the double-strict-straddle predicate).

    FIELD-GENERICITY.  This foundation is stated over an abstract
    [realFieldType] (all it needs is ordered-field arithmetic + [orient] signs).
    The consuming universality STATEMENT (D3geo.v) instead quantifies [forall R :
    rcfType] — real-closed fields — so that, per fixed drawing instance (a
    first-order ordered-field formula), Tarski–Seidenberg model-completeness
    makes its truth identical across all real-closed fields including ℝ; the
    abstract-field reading is then EQUIVALENT to the ℝ² source (both a proof and
    a disproof transfer). *)

From mathcomp Require Import all_boot.
From GTBase Require Import base.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope ring_scope.

Section Geometry.
Variable R : realFieldType.
Definition pt := (R * R)%type.

(** Signed area of (a,b,c): sign of [| b−a  c−a |].  The ONLY geometric primitive. *)
Definition orient (a b c : pt) : R :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1).
Definition collinear (a b c : pt) : Prop := orient a b c = 0.

(** [c] lies on the CLOSED segment [a,b]: collinear and both coordinates between. *)
Definition between (a b c : pt) : Prop :=
  collinear a b c /\ (c.1 - a.1) * (c.1 - b.1) <= 0 /\ (c.2 - a.2) * (c.2 - b.2) <= 0.

(** [a,b] and [c,d] cross PROPERLY (relative interiors meet): double strict straddle. *)
Definition seg_cross (a b c d : pt) : Prop :=
  ~ (0 < orient a b c * orient a b d) /\ ~ (0 < orient c d a * orient c d b) /\
  orient a b c != 0 /\ orient a b d != 0 /\ orient c d a != 0 /\ orient c d b != 0.

(** The closed segments [a,b] and [c,d] share at least one point (proper cross,
    or an endpoint of one lies on the other — covering touch / collinear overlap
    / shared endpoint). *)
Definition seg_meet (a b c d : pt) : Prop :=
  seg_cross a b c d \/ between a b c \/ between a b d \/ between c d a \/ between c d b.

(** Two edges are INDEPENDENT (vertex-disjoint). *)
Definition indep (G : sgraph) (x y u v : G) : bool := [&& x != u, x != v, y != u & y != v].

(** A planar straight-line drawing of a simple graph [G]. *)
Definition straightline_planar (G : sgraph) (pos : G -> pt) : Prop :=
  [/\ injective pos,
      (forall w x y : G, x -- y -> w != x -> w != y -> ~ between (pos x) (pos y) (pos w)) &
      (forall x y u v : G, x -- y -> u -- v -> indep x y u v ->
         ~ seg_meet (pos x) (pos y) (pos u) (pos v)) ].

(** [P] is [n]-universal: every [n]-vertex planar graph ([wagner_planar]) has a
    planar straight-line drawing onto distinct points of [P]. *)
Definition n_universal (P : seq pt) (n : nat) : Prop :=
  forall G : sgraph, wagner_planar G -> #|G| = n ->
    exists pos : G -> pt, straightline_planar pos /\ (forall x : G, pos x \in P).

End Geometry.
Arguments orient {R} a b c.
Arguments between {R} a b c.
Arguments seg_meet {R} a b c d.
Arguments n_universal {R} P n.

(** ** Grounding: [orient] has content; the drawing predicate is inhabited. *)

Lemma orient_id1 (R : realFieldType) (a b : R * R) : orient a a b = 0.
Proof. by rewrite /orient !subrr !mul0r subrr. Qed.
Lemma orient_id2 (R : realFieldType) (a b : R * R) : orient a b b = 0.
Proof. by rewrite /orient mulrC subrr. Qed.
Lemma orient_unit (R : realFieldType) : orient (0, 0) (1, 0) (0, 1) = 1 :> R.
Proof. by rewrite /orient /= !subr0 mul1r mulr0 subr0. Qed.

(** A single-vertex graph has a (trivial) planar straight-line drawing — no
    edges to constrain — so [straightline_planar] is satisfiable, not vacuously
    false. *)
Lemma straightline_planar_K1 (R : realFieldType) (a : pt R) :
  straightline_planar (G := 'K_1) (fun=> a).
Proof.
split=> [x y|w x y|x y u v].
- by rewrite (ord1 x) (ord1 y).
- by rewrite /edge_rel /= /complete_rel (ord1 x) (ord1 y) eqxx.
- by rewrite /edge_rel /= /complete_rel (ord1 x) (ord1 y) eqxx.
Qed.
