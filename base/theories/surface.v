(** * GTBase.surface -- shared finite surface and clustered-colouring vocabulary *)

From mathcomp Require Import all_boot.
From mathcomp Require Import fingroup perm.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SurfaceEmbedding.
Variable G : sgraph.

Definition surface_dart : Type := {p : G * G | p.1 -- p.2}.

Lemma surface_rev_dart_proof (d : surface_dart) :
  (sval d).2 -- (sval d).1.
Proof. by rewrite sg_sym; exact: (svalP d). Qed.

Definition surface_rev_dart (d : surface_dart) : surface_dart :=
  exist _ ((sval d).2, (sval d).1) (surface_rev_dart_proof d).

Lemma surface_rev_dartK : involutive surface_rev_dart.
Proof. by move=> d; apply/val_inj; case: d => [[x y] p]. Qed.

Definition surface_edge_perm : {perm surface_dart} :=
  perm (inv_inj surface_rev_dartK).

Record surface_embedding := SurfaceEmbedding {
  surface_erot : {perm surface_dart};
  surface_erot_src :
    forall d : surface_dart, (sval (surface_erot d)).1 = (sval d).1;
  surface_erot_vertex :
    forall d : surface_dart,
      porbit surface_erot d = [set d' | (sval d').1 == (sval d).1]
}.

Definition surface_face_perm (E : surface_embedding) : {perm surface_dart} :=
  (surface_erot E * surface_edge_perm)%g.

Definition surface_embedding_vertices (E : surface_embedding) : nat :=
  #|porbits (surface_erot E)|.

Definition surface_embedding_edges : nat := #|{: surface_dart}| %/ 2.

Definition surface_embedding_faces (E : surface_embedding) : nat :=
  #|porbits (surface_face_perm E)|.

(** Orientable Euler genus from a finite rotation system.  Consumers should keep
    the usual connected-graph guard when they need the classical connected
    surface reading. *)
Definition surface_euler_genus (E : surface_embedding) : nat :=
  (2 + surface_embedding_edges - surface_embedding_vertices E -
     surface_embedding_faces E) %/ 2.

Definition surface_embeds_in_euler_genus (g : nat) : Prop :=
  exists E : surface_embedding, surface_euler_genus E <= g.

Definition surface_embeds_in_fixed_surface (surface : nat) : Prop :=
  surface_embeds_in_euler_genus surface.

End SurfaceEmbedding.

Definition surface_embeddable (surface : nat) (G : sgraph) : Prop :=
  surface_embeds_in_fixed_surface G surface.

Definition surface_embeddable_with_boundary
    (surface boundary : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G /\
  exists B : {set G}, #|B| <= boundary.

Definition same_colour_on (G : sgraph) (k : nat)
    (col : G -> 'I_k) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> col x = col y.

(** [clustered_colouring G k c] says every connected monochromatic vertex set
    has size at most [c], equivalently every monochromatic component has size at
    most [c]. *)
Definition clustered_colouring (G : sgraph) (k c : nat) : Prop :=
  exists col : G -> 'I_k,
    forall S : {set G},
      connected S -> same_colour_on col S -> #|S| <= c.

Definition clustered_chromatic_at_most (G : sgraph) (k : nat) : Prop :=
  exists c : nat, clustered_colouring G k c.
