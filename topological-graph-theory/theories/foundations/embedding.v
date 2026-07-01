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

    EMBEDDING-EXISTENCE is PROVEN (foundation complete): [embedding_exists :
    inhabited (embedding G)] for EVERY [G], via the canonical cyclic-successor rotation
    [rot_perm] ([rot_fun d := next (Lv d) d], [Lv d] enumerating the darts at [d]'s
    source).  The combinatorial crux [np_orbit] ([next] generates a single cycle covering
    its list) gives [rot_perm_vertex]: the rotation's orbit at a vertex is exactly that
    vertex's dart-set, so [rot_perm] is a genuine rotation system.  Hence the
    embedding-quantified predicates above are NON-VACUOUS — the Phase-A1 foundation is
    fully green, and Wave-1 rows (grünbaum / circular-embedding / positive-curvature /
    toroidal-Hamilton / plane-triangulation) can land blocked→done. *)

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

(** Abstract iterate-agreement: if [g] agrees with [f] along [f]'s orbit of [x],
    then [g^n x = f^n x] (used to transfer [np]'s single-cycle orbit to the graph
    rotation without unfolding the per-vertex dart-list). *)
Lemma iter_agree (T : finType) (f g : {perm T}) x n :
  (forall k, k < n -> g ((f ^+ k)%g x) = f ((f ^+ k)%g x)) ->
  (g ^+ n)%g x = (f ^+ n)%g x.
Proof.
elim: n => [|n IH] H; first by rewrite !expg0 !perm1.
have Hsub : forall k, k < n -> g ((f ^+ k)%g x) = f ((f ^+ k)%g x).
  by move=> k Hk; apply: H; rewrite ltnS; exact: ltnW.
by rewrite !expgSr !permM (IH Hsub) (H n (ltnSn n)).
Qed.

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

(** SCOPE CAVEAT (Track-A review, confirmed): [euler_genus] hard-codes the
    CONNECTED-map Euler relation [2-2g = V-E+F] over truncating nat arithmetic.
    For a c-component map the true relation is [V-E+F = 2c - 2·Σgᵢ] and graph
    genus is ADDITIVE over components (Battle–Harary–Kodama–Youngs), so on
    disconnected graphs this formula computes [max(0, Σgᵢ + 1 - c)] — it
    UNDERSTATES genus by [c-1] (e.g. K7 ⊎ K7 with torus triangulations gets
    genus 1, though the true genus is 2) and can truncate to 0 (disjoint
    triangles).  Also, [emV] counts erot-orbits, so ISOLATED vertices are
    invisible, and an EDGELESS graph gets [euler_genus = 1] (empty-map anomaly).
    Every consumer of [planar_embedding]/[embeds_in_genus]/[min_genus]/[toroidal]
    must therefore carry a connectivity hypothesis (all current rows do:
    U2 via [k_connected G 4], U13 + the D6emb curvature row via
    [connected [set: G]]); an unguarded use on possibly-disconnected graphs is
    UNFAITHFUL. *)
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

(** ** Embedding EXISTENCE — every graph has a combinatorial embedding.

    The canonical rotation [rot_perm] sends each dart to the cyclic successor in
    its source-vertex dart-list [Lv].  Via [np_orbit] (the [next] single-cycle
    lemma), its orbit at [d] is exactly [darts_at (sval d).1], so [rot_perm] is a
    genuine rotation system.  Hence [inhabited (embedding G)] for EVERY [G] — the
    embedding-quantified predicates above are non-vacuous. *)

Definition Lv (d : dart) := enum (darts_at (sval d).1).
Lemma memLv (d : dart) : d \in Lv d. Proof. by rewrite mem_enum inE. Qed.
Lemma LvE (z d : dart) : (sval z).1 = (sval d).1 -> Lv z = Lv d.
Proof. by rewrite /Lv => ->. Qed.

Definition rot_fun (d : dart) : dart := next (Lv d) d.
Lemma rot_fun_src d : (sval (rot_fun d)).1 = (sval d).1.
Proof.
suff H : rot_fun d \in darts_at (sval d).1 by move: H; rewrite inE => /eqP.
by rewrite -mem_enum -/(Lv d) /rot_fun mem_next memLv.
Qed.
Lemma rot_fun_inj : injective rot_fun.
Proof.
move=> d1 d2 E.
have S : (sval d1).1 = (sval d2).1 by rewrite -(rot_fun_src d1) E rot_fun_src.
move: E; rewrite /rot_fun (LvE S).
exact: (can_inj (prev_next (enum_uniq (darts_at (sval d2).1)))).
Qed.
Definition rot_perm : {perm dart} := perm rot_fun_inj.
Lemma rot_permE d : rot_perm d = next (Lv d) d. Proof. exact: permE. Qed.
Lemma rot_perm_src d : (sval (rot_perm d)).1 = (sval d).1.
Proof. by rewrite rot_permE (rot_fun_src d). Qed.

Lemma np_iter_src d k :
  (sval ((np (enum_uniq (darts_at (sval d).1)) ^+ k)%g d)).1 = (sval d).1.
Proof.
suff H : (np (enum_uniq (darts_at (sval d).1)) ^+ k)%g d \in Lv d
  by move: H; rewrite mem_enum inE => /eqP.
have Ho : (np (enum_uniq (darts_at (sval d).1)) ^+ k)%g d
          \in porbit (np (enum_uniq (darts_at (sval d).1))) d by apply/porbitP; exists k.
by move: Ho; rewrite np_orbit ?memLv // inE.
Qed.
Lemma rot_np_agree (d z : dart) : (sval z).1 = (sval d).1 ->
  rot_perm z = np (enum_uniq (darts_at (sval d).1)) z.
Proof. by move=> Hz; rewrite rot_permE (LvE Hz) npE. Qed.
Lemma rot_iter_np d k :
  (rot_perm ^+ k)%g d = (np (enum_uniq (darts_at (sval d).1)) ^+ k)%g d.
Proof. apply: iter_agree => j _; apply: rot_np_agree; exact: np_iter_src. Qed.

Lemma rot_perm_vertex d : porbit rot_perm d = [set d' | (sval d').1 == (sval d).1].
Proof.
have E : porbit rot_perm d = porbit (np (enum_uniq (darts_at (sval d).1))) d.
  by apply/setP => z; apply/idP/idP => /porbitP[i ->]; apply/porbitP; exists i;
     rewrite rot_iter_np.
by rewrite E np_orbit ?memLv //; apply/setP => z; rewrite !inE mem_enum inE.
Qed.

Definition embedding_of : embedding := Emb rot_perm_src rot_perm_vertex.
Lemma embedding_exists : inhabited embedding. Proof. exact: (inhabits embedding_of). Qed.

End Embedding.

(** A graph is toroidal iff it embeds in the orientable genus-1 surface. *)
Definition toroidal (G : sgraph) : Prop := embeds_in_genus G 1.
