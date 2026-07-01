(** * Topological.conjectures.D6emb — milestone D6emb (namespace Topological, plan v4)

    Statement-only formalizations (AXIOM-FREE: no Conjecture/Axiom/Parameter/
    Admitted) of three EMBEDDING / surface conjectures.  All three are stated
    against the COMPLETE, axiom-free Track-A combinatorial-topology foundation
    [Topological.foundations.embedding] (orientable rotation systems / ribbon
    graphs): [dart], [edge_perm], [embedding] (a rotation system, PROVEN
    inhabited for every [G] by [embedding_exists] — so the embedding TYPE is
    non-empty and every [forall E] / [exists E] quantifier below ranges over an
    inhabited domain; the added [triangulation] / 2-connectivity / positive-
    curvature filters are conjecture HYPOTHESES, not proven realizable),
    [face_perm]/[face_of]/[face_size] (faces =
    orbits of [face_perm = erot * edge_perm]), [triangulation], [planar_embedding]
    (genus 0), and [combinatorial_curvature]/[positive_curvature].  No metric
    geometry; no planarity stack (planar_embedding is the combinatorial genus-0
    predicate of the foundation, not the G2 four-colour planarity oracle).

    CARRIERS (per row.rocq_idiom): each row quantifies over a simple graph
    [G : sgraph] (coq-graph-theory simple graphs = simple + loopless, and the
    rotation system built on it is orientable by construction) together with an
    [embedding G] where the statement is about a chosen/every surface embedding.

    NEW AREA-SPECIFIC PRIMITIVES (all local to this file, none cross-area):
      - [antiprism n : sgraph] — the n-antiprism on ['I_n * bool] (two n-cycles
        plus the connecting triangles: top i ~ bottom i and top i ~ bottom (i+1));
      - [is_prism] / [is_antiprism] — "[G] is (isomorphic to) a prism / antiprism".
    A prism is [cycle_graph n □ 'K_2] (base's [cartesian_product]); the antiprism
    is the concrete graph above.  These are intrinsically about the
    positive-curvature classification and are NOT plausibly cross-area, so they
    stay local (not tagged [@MOVE-to-base]).  Everything else is REUSED verbatim
    from base ([cartesian_product], [cycle_graph], ['K_2], [k_connected], [N(_)],
    [connected], [≃]) or from the embedding foundation. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.foundations Require Import embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The n-antiprism (area-specific primitive)

    Vertices [('I_n * bool)]: the boolean flags the two n-gons ([true] = "top",
    [false] = "bottom").  Directed adjacency [anti_dir], symmetrised to
    [anti_rel]:
      - same n-gon: [i], [j] adjacent on the cycle (base's [cyc_rel]);
      - vertical rung: top [i] ~ bottom [i];
      - slanted rung:  top [i] ~ bottom [i+1] (mod n).
    Together the rungs make the connecting triangles.  Symmetrising by [anti_dir
    u v || anti_dir v u] gives symmetry for free; irreflexivity holds because the
    same-n-gon term is [cyc_rel]-irreflexive and each rung forces [true] on one
    endpoint and [false] on the other. *)

Section Antiprism.
Variable n : nat.

Definition anti_dir (u v : 'I_n * bool) : bool :=
  let: (i, a) := u in let: (j, b) := v in
  ((a == b) && cyc_rel i j)
  || (a && ~~ b && ((i == j) || (((val i).+1 %% n) == val j))).

Definition anti_rel (u v : 'I_n * bool) : bool := anti_dir u v || anti_dir v u.

Lemma anti_sym : symmetric anti_rel.
Proof. by move=> u v; rewrite /anti_rel orbC. Qed.

Lemma anti_irrefl : irreflexive anti_rel.
Proof.
by move=> [i a]; rewrite /anti_rel orbb /anti_dir eqxx cyc_irrefl /= andbN.
Qed.

Definition antiprism : sgraph := SGraph anti_sym anti_irrefl.

End Antiprism.

(** [G] is a prism = [G ≃ C_n □ K_2] for some [n > 2] (guard [2 < n] excludes the
    degenerate small cases and the K_2 / theta base). *)
Definition is_prism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ cartesian_product (cycle_graph n) 'K_2).

(** [G] is an antiprism = [G ≃ antiprism n] for some [n > 2]. *)
Definition is_antiprism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ antiprism n).

(** ** Row 1 — Grünbaum's conjecture (3-edge-colourability of the dual of a
    triangulation of an orientable surface).  OPEN.

    Source (Conjecture): "If [G] is a simple loopless triangulation of an
    orientable surface, then the dual of [G] is 3-edge-colorable."

    Encoding.  [G : sgraph] is simple + loopless; the rotation system [E] is
    orientable by construction, and [triangulation E] says every face is a
    triangle.  The dual of a triangulation is 3-regular, and a proper
    3-edge-colouring of the dual assigns to each PRIMAL EDGE (a pair of darts
    [d], [edge_perm G d]) a colour in ['I_3] such that the three edges bounding
    each triangular face receive pairwise-distinct colours.  The three darts of a
    face are [d], [face_perm E d], [face_perm E (face_perm E d)] (a triangular
    face has period 3 under [face_perm]); each carries the colour of its
    underlying edge (first conjunct: [c] is [edge_perm]-invariant). *)
Definition grunbaums_statement : Prop :=
  forall (G : sgraph) (E : embedding G),
    triangulation E ->
    exists c : dart G -> 'I_3,
      (forall d : dart G, c d = c (edge_perm G d)) /\
      (forall d : dart G,
         c d <> c (face_perm E d) /\
         c (face_perm E d) <> c (face_perm E (face_perm E d)) /\
         c d <> c (face_perm E (face_perm E d))).

(** ** Row 2 — The circular-embedding conjecture.  OPEN.

    Source (Conjecture): "Every 2-connected graph may be embedded in a surface so
    that the boundary of each face is a cycle."

    Encoding.  For every 2-connected [G] there is an embedding [E] all of whose
    face boundaries are cycles = no vertex is repeated on any face: on each face
    [face_of E d] the source map [d' ↦ (sval d').1] is injective, so the darts of
    the face visit pairwise-distinct vertices, i.e. the boundary walk is a simple
    cycle. *)
Definition the_circular_embedding_statement : Prop :=
  forall (G : sgraph),
    k_connected G 2 ->
    exists E : embedding G,
      forall d : dart G,
        {in face_of E d &, injective (fun d' : dart G => (sval d').1)}.

(** ** Row 3 — Largest planar graph of everywhere-positive combinatorial
    curvature that is neither a prism nor an antiprism.  (Open problem: what IS
    it?  The statement below asserts the finiteness that makes "largest"
    meaningful — a uniform vertex bound over the whole class.)

    Source (Problem): "What is the largest connected planar graph of minimum
    degree 3 which has everywhere positive combinatorial curvature, but is not a
    prism or antiprism?"

    Encoding.  There is a uniform bound [Nmax] on the order of any [G] that is
    connected, carries a planar embedding [E] of everywhere-positive
    combinatorial curvature, has minimum degree ≥ 3 ([2 < #|N(v)|] for every [v]),
    and is neither a prism nor an antiprism.  ([Nmax] being an explicit finite
    bound is exactly the content of "there is a largest such graph".) *)
Definition what_is_the_largest_graph_of_positive_curvature_statement : Prop :=
  exists Nmax : nat,
    forall (G : sgraph) (E : embedding G),
      connected [set: G] ->
      planar_embedding E ->
      (forall v : G, 2 < #|N(v)|) ->
      positive_curvature E ->
      ~ is_prism G ->
      ~ is_antiprism G ->
      #|G| <= Nmax.
