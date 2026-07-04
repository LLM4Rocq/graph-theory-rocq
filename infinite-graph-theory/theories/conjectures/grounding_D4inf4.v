(** * Grounding for the two carrier rows (hypergraph & digraph vocab has content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf4.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Hypergraph side. *)

(** The empty edge set is a matching, and [card_le] is reflexive, so
    "strongly maximal / minimal" are genuine comparisons (not trivially false). *)
Lemma empty_hmatching (H : iHypergraph) : hmatching (fun _ : hE H => False).
Proof. by move=> e1 e2 []. Qed.

Lemma card_le_reflH (A : Type) (P : A -> Prop) : card_le P P.
Proof. by exists id. Qed.

(** ** Digraph side. *)

(** The identity is an automorphism — so [dautomorphism] is inhabited and
    [highly_arc_transitive] is not vacuously false-typed. *)
Lemma dauto_id (G : iDigraph) : dautomorphism (@id (dV G)).
Proof. by split; [exists id | ]. Qed.

(** A 2-vertex directed path is exactly a single arc. *)
Lemma darc_path2 (G : iDigraph) (a b : dV G) : darc a b -> darc_path [:: a; b].
Proof. by move=> H; split. Qed.

(** A single-arc alternating walk uses that arc — [alt_walk_from]/[walk_uses]
    are inhabited and agree. *)
Lemma alt_walk_single (G : iDigraph) (a c : dV G) :
  darc a c -> alt_walk_from true a [:: c] /\ walk_uses true a [:: c] a c.
Proof. by move=> H; split; [split | left; left]. Qed.

(** The non-vacuity guards genuinely exclude degenerate digraphs: an arc forces
    [~ d_has_arc] false on the edgeless digraph, etc. (sanity: guards are not
    tautologies). *)
Lemma d_no_sink_source_has_arc (G : iDigraph) :
  d_no_sink_source G -> (exists x : dV G, True) -> d_has_arc G.
Proof. by move=> ns [x _]; have [[y hy] _] := ns x; exists x, y. Qed.
