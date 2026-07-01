(** * Combinatorial (orientable) graph embeddings — the Track-A topological foundation.

    A faithful, AXIOM-FREE combinatorial-topology layer built from rotation systems
    (a.k.a. combinatorial maps / ribbon graphs), with NO metric geometry.  For a simple
    graph [G]:

    - a [dart] is an oriented edge (an ordered adjacent pair);
    - [edge_perm] is the fixed-point-free involution pairing the two darts of an edge;
    - an [embedding] is a rotation [erot : {perm dart}] whose orbits ARE the vertices
      (source-preserving, and one cycle per vertex) — i.e. a cyclic ordering of the
      darts around each vertex, which is exactly an orientable combinatorial embedding;
    - FACES are the orbits of [face_perm = erot * edge_perm]; the orientable Euler genus
      is [(2 + E - V - F) / 2] on the map's own [V]/[E]/[F] (orbit counts of the three
      permutations), for a connected embedding.

    From these: [planar_embedding] (genus 0), [embeds_in_genus], [min_genus], [toroidal]
    (genus ≤ 1), [triangulation] (every face a triangle), and the combinatorial (corner)
    [combinatorial_curvature].  Everything is finite/decidable at the term level, hence
    axiom-free.

    Scope note: [euler_genus] uses the connected-map Euler relation; rows that quantify
    over embeddings carry the graph's connectivity hypothesis.  Non-vacuity: [edge_perm]
    is a fixed-point-free involution (below).  The generic embedding-existence witness
    ([forall G, inhabited (embedding G)] via the canonical cyclic-successor rotation) is
    the remaining obligation gating "for all/exists embedding" rows — see the Track-A
    roadmap; until it lands, embedding-quantified rows are recorded partial. *)

From mathcomp Require Import all_boot.
From mathcomp Require Import fingroup perm.
From GTBase Require Import base.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.

Section Embedding.
Variable G : sgraph.

(** ** Darts and the edge involution *)

Definition dart : Type := {p : G * G | p.1 -- p.2}.

Lemma rev_dart_proof (d : dart) : (sval d).2 -- (sval d).1.
Proof. by rewrite sg_sym; exact: (svalP d). Qed.
Definition rev_dart (d : dart) : dart := exist _ ((sval d).2, (sval d).1) (rev_dart_proof d).
Lemma rev_dartK : involutive rev_dart.
Proof. by move=> d; apply/val_inj; case: d => [[x y] p]. Qed.

Definition edge_perm : {perm dart} := perm (inv_inj rev_dartK).

Lemma edge_permE (d : dart) : edge_perm d = rev_dart d.
Proof. exact: permE. Qed.
Lemma edge_permK : involutive (@edge_perm).
Proof. by move=> d; rewrite !edge_permE rev_dartK. Qed.
(** Non-vacuity: [edge_perm] is fixed-point-free (each edge has two distinct darts). *)
Lemma edge_perm_fpf (d : dart) : edge_perm d != d.
Proof.
case: d => [[x y] p]; rewrite edge_permE; apply/eqP => /(congr1 val) /= [] eyx _.
by move: p; rewrite eyx sg_irrefl.
Qed.

(** ** Combinatorial embeddings (rotation systems), faces, genus *)

Record embedding := Emb {
  erot : {perm dart};
  erot_src : forall d : dart, (sval (erot d)).1 = (sval d).1;
  erot_vertex : forall d : dart, porbit erot d = [set d' | (sval d').1 == (sval d).1] }.

Definition face_perm (E : embedding) : {perm dart} := (erot E * edge_perm)%g.
Definition face_of (E : embedding) (d : dart) : {set dart} := porbit (face_perm E) d.
Definition darts_at (v : G) : {set dart} := [set d : dart | (sval d).1 == v].

Definition emV (E : embedding) : nat := #|porbits (erot E)|.
Definition emE : nat := #|{: dart}| %/ 2.
Definition emF (E : embedding) : nat := #|porbits (face_perm E)|.

Definition euler_genus (E : embedding) : nat := (2 + emE - emV E - emF E) %/ 2.
Definition planar_embedding (E : embedding) : Prop := euler_genus E = 0.
Definition embeds_in_genus (g : nat) : Prop := exists E : embedding, euler_genus E <= g.
Definition min_genus (g : nat) : Prop :=
  (exists E : embedding, euler_genus E = g) /\ (forall E : embedding, g <= euler_genus E).

Definition face_size (E : embedding) (d : dart) : nat := #|face_of E d|.
Definition triangulation (E : embedding) : Prop := forall d : dart, face_size E d = 3.

(** Combinatorial (corner) curvature at [v]: [1 - deg(v)/2 + Σ_corners 1/face_size]. *)
Definition combinatorial_curvature (E : embedding) (v : G) : rat :=
  (1 - (#|darts_at v|)%:R / 2%:R + \sum_(d in darts_at v) 1 / (face_size E d)%:R)%R.
Definition positive_curvature (E : embedding) : Prop :=
  forall v : G, (0 < combinatorial_curvature E v)%R.

End Embedding.

(** A graph is toroidal iff it embeds in the orientable genus-1 surface. *)
Definition toroidal (G : sgraph) : Prop := embeds_in_genus G 1.
