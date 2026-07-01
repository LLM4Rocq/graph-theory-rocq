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
    is a fixed-point-free involution (below).

    EMBEDDING-EXISTENCE (gating "for all/exists embedding" rows → done vs partial): the
    plan is the canonical cyclic-successor rotation [rot_fun d := next (Lv d) d] where
    [Lv d] enumerates the darts at [d]'s source.  Its combinatorial CRUX is now PROVEN —
    [np_orbit] below shows [next] generates a single cycle covering its list, so the
    rotation's orbit at a vertex is exactly that vertex's dart-set ([erot_vertex]).  The
    final assembly ([rot_perm]/[erot_vertex] → [inhabited (embedding G)]) connects
    [np_orbit] to the graph; it is mechanical (the math is done) and is the last Phase-A1
    step.  Until it lands, embedding-quantified rows stay recorded partial. *)

From mathcomp Require Import all_boot.
From mathcomp Require Import fingroup perm.
From GTBase Require Import base.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Reusable: [next] generates a single cycle covering its (uniq) list.

    This is the combinatorial linchpin for embedding-EXISTENCE (the canonical
    cyclic-successor rotation whose orbit at a vertex is exactly that vertex's
    dart-set).  [np Us] is [next s] as a permutation; [np_orbit] shows its orbit
    of any list element is the whole list. *)

Lemma next_nth_cyc (T : eqType) (d : T) s m : uniq s -> m < size s ->
  next s (nth d s m) = nth d s (m.+1 %% size s).
Proof.
case: s => [|y0 p'] // Us Hm.
have zin : nth d (y0 :: p') m \in (y0 :: p') by rewrite mem_nth.
rewrite next_nth zin index_uniq //.
move: Hm; rewrite ltnS leq_eqVlt => /orP[/eqP Em|Hlt].
  by rewrite Em modnn /= nth_default.
by rewrite modn_small ?ltnS //= (set_nth_default d).
Qed.

Section NextCycle.
Variable T : finType.
Variable s : seq T.
Hypothesis Us : uniq s.
Definition np : {perm T} := perm (can_inj (prev_next Us)).
Lemma npE x : np x = next s x. Proof. exact: permE. Qed.
Lemma np_iter x i : x \in s -> (np ^+ i)%g x = nth x s ((index x s + i) %% size s).
Proof.
move=> xs; have Hs : 0 < size s by rewrite lt0n size_eq0; case: (s) xs.
elim: i => [|i IH]; first by rewrite expg0 perm1 addn0 modn_small ?index_mem // nth_index.
rewrite expgSr permM IH npE next_nth_cyc ?ltn_mod //.
have KEY : (index x s + i.+1) %% size s = ((index x s + i) %% size s).+1 %% size s.
  by rewrite addnS -addn1 -modnDml addn1.
by rewrite KEY.
Qed.
Lemma np_orbit x : x \in s -> porbit np x = [set y in s].
Proof.
move=> xs; have Hs : 0 < size s by rewrite lt0n size_eq0; case: (s) xs.
apply/setP => y; rewrite inE; apply/idP/idP.
  by move=> /porbitP[i ->]; rewrite np_iter //; apply: mem_nth; rewrite ltn_mod.
move=> ys; apply/porbitP; exists (index y s + size s - index x s); rewrite np_iter //.
have Hy : index y s < size s by rewrite index_mem.
have Hle : index x s <= index y s + size s.
  by apply: (@leq_trans (size s)); [rewrite ltnW // index_mem | exact: leq_addl].
by rewrite subnKC // modnDr modn_small // nth_index.
Qed.
End NextCycle.

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
