(** * Digraph.conjectures.packing — P10 "packing & duality"

    Statement-only formalization (no axioms) of the cluster-P10 open conjectures on
    packing and min–max duality in digraphs, together with the literature-stated edges.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P10), §5 (table), §7 (edges).

    The shared primitives (built once, reused by every statement):

      - VERTEX-DISJOINT CYCLE PACKING — a [seq (seq D)] of directed cycles that are
        pairwise vertex-disjoint ([vtx_disjoint_pack]); the vertices of a dicycle [c]
        are its elements (a dicycle is a uniq seq, so the [pred_of_seq] is its vertex set).

      - MIN OUT-DEGREE — phrased pointwise as [forall v, k <= outdeg v] (per the brief),
        never as a separate min; degenerate empties are guarded with [(0 < #|D|)%N ->]
        only where vacuity would otherwise bite.

      - ARC SELECTORS — a sub(di)graph that keeps ALL vertices and only some arcs is
        represented by an arc selector [f : D -> {set D}] ([w ∈ f u] ↦ keep arc (u,w)).
        It lifts to a genuine [diGraphType] via [outsel f] (oriented.v), so acyclicity
        ([acyclicb]), reachability and cycles can be reused on it verbatim. [real_sel f]
        asks every selected pair to be a real arc; [arc_disjoint_sel f g] asks the two
        selectors to never keep the same ordered pair.

      - OUT-/IN-BRANCHING — a spanning out-arborescence rooted at [r] is the arc selector
        [f] with: all selected pairs real, root [r] with [f]-in-degree 0, every other
        vertex with [f]-in-degree exactly 1, and [outsel f] acyclic (this is the standard
        characterization of a spanning out-branching). An in-branching is an out-branching
        of the converse.

      - DIJOIN / DICUT — a dicut is the arc set of a one-way vertex cut: a nonempty proper
        [B ⊂ V] with NO arc leaving its complement back into it crossing forward — the arcs
        [{(u,v) : u ∈ B, v ∉ B}] with [B] closed under no in-arc from outside (precisely:
        [forall u v, u ∉ B -> v ∈ B -> ~ u --> v], a "one-way / source-side" set). The
        dicut is then the forward crossing arcs. A dijoin is an arc set meeting every dicut.

      - PATH-PARTITION & k-NORM — a partition of [V] into vertex-disjoint dipaths; its
        k-norm is [\sum_paths min(k, length+1)] (lengths counted in VERTICES).

    Nodes (Definitions of type Prop):
      - [bermond_thomassen_statement]   : δ⁺ ≥ 2k−1 ⟹ k vertex-disjoint dicycles.
      - [hoang_reed_statement]          : δ⁺ ≥ k ⟹ k dicycles with the laminar
                                          (intersection-forest) property.
      - [woodall_statement]             : min dicut size = k ⟹ k arc-disjoint dijoins.
      - [linial_berge_statement]        : path-partition / colour duality.
      - [erdos_posa_long_dicycles_statement] : Erdős–Pósa for long directed cycles.

    Edges (Qed-closed relative theorems):
      - [bermond_thomassen_implies_hoang_reed_weak] : Bermond–Thomassen gives, at δ⁺ ≥ 2k−1,
        the k disjoint cycles whose (empty) pairwise intersections are trivially laminar —
        a "weak Hoàng–Reed at the stronger degree threshold" sanity edge.
      - [hoang_reed_implies_one_cycle] : Hoàng–Reed (at k = 1) gives a directed cycle in any
        digraph of min out-degree ≥ 1 (the classic δ⁺ ≥ 1 ⟹ cycle, here relative). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong.
From Digraph Require Import classic_core dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared primitives *)

Section Packing.
Variable D : diGraphType.
Implicit Types (v w : D) (c : seq D).

(** *** Vertex-disjoint cycle packing *)

(** A [cycle pack] is a [seq (seq D)] each of whose members is a directed cycle. *)
Definition cycle_pack (P : seq (seq D)) : bool := all (@dicycle D) P.

(** Two seqs are vertex-disjoint iff they share no element. *)
Definition vtx_disjoint c c' : bool := ~~ has (mem c') c.

(** A packing is vertex-disjoint iff every two distinct members are vertex-disjoint.
    (Indexing by position so reflexive pairs [i = i] are excluded.) *)
Definition vtx_disjoint_pack (P : seq (seq D)) : bool :=
  [forall i : 'I_(size P), forall j : 'I_(size P),
     (i != j) ==> vtx_disjoint (nth [::] P i) (nth [::] P j)].

(** *** Arc selectors (all-vertex sub-digraphs) *)

(** [f u] is the set of out-neighbours kept at [u]. *)
Implicit Types (f g : D -> {set D}).

(** [f] keeps only real arcs of [D]. *)
Definition real_sel f : bool := [forall u, [forall w, (w \in f u) ==> (u --> w)]].

(** Two selectors keep no common ordered pair. *)
Definition arc_disjoint_sel f g : bool :=
  [forall u, [forall w, ~~ ((w \in f u) && (w \in g u))]].

(** [f]-in-degree of [v]: the number of kept arcs into [v]. *)
Definition selindeg f v : nat := #|[set u | v \in f u]|.

(** *** Out-/in-branchings (spanning arborescences) *)

(** A spanning OUT-branching rooted at [r]: real arcs only, [r] has no kept in-arc,
    every other vertex has exactly one kept in-arc, and the kept sub-digraph is acyclic.
    Together these force a spanning arborescence out of [r]. *)
Definition out_branching f (r : D) : bool :=
  [&& real_sel f,
      selindeg f r == 0,
      [forall v, (v != r) ==> (selindeg f v == 1)] &
      acyclicb (outsel f)].

(** An IN-branching rooted at [r] is an out-branching in the converse digraph. We model
    it directly: real arcs only, [r] has no kept OUT-arc, every other vertex has exactly
    one kept out-arc, acyclic. ([f u] is read as the kept out-neighbours, so "out-degree
    of [u] in [f]" is [#|f u|] intersected with real arcs; for a [real_sel] it is [#|f u|].) *)
Definition in_branching f (r : D) : bool :=
  [&& real_sel f,
      #|f r| == 0,
      [forall v, (v != r) ==> (#|f v| == 1)] &
      acyclicb (outsel f)].

(** *** Dijoins and dicuts *)

(** [B] is a one-way (source-side) set: nonempty, proper, and no arc enters [B] from
    outside it. Its DICUT is the set of forward-crossing arcs [{(u,v) : u ∈ B, v ∉ B}]. *)
Definition oneway (B : {set D}) : bool :=
  [&& B != set0, B != [set: D] & [forall u, forall v, (u \notin B) ==> (v \in B) ==> ~~ (u --> v)]].

(** Arc [(u,v)] is in the dicut of [B]. *)
Definition in_dicut (B : {set D}) (u v : D) : bool := (u \in B) && (v \notin B) && (u --> v).

(** Size of the dicut of [B] = number of forward-crossing arcs. *)
Definition dicut_size (B : {set D}) : nat :=
  #|[set p : D * D | in_dicut B p.1 p.2]|.

(** A dijoin is a real arc selector that meets every dicut: for every one-way set [B],
    [f] keeps at least one arc of [B]'s dicut. *)
Definition dijoin f : bool :=
  real_sel f &&
  [forall B : {set D}, oneway B ==>
     [exists u, exists w, (w \in f u) && in_dicut B u w]].

(** *** Path-partition and k-norm *)

(** A path-partition: a list of dipaths (each a [(start, rest)] pair) whose vertex sets
    partition [V] (cover everything, pairwise disjoint). We carry the start vertex and the
    rest-seq together as [seq (D * seq D)]; the vertex set of one path is [x :: s]. *)
Definition pp_paths (Q : seq (D * seq D)) : bool := all (fun p => dipath p.1 p.2) Q.

Definition pp_vtx (p : D * seq D) : seq D := p.1 :: p.2.

Definition pp_partition (Q : seq (D * seq D)) : bool :=
  [&& pp_paths Q,
      (* covers every vertex *)
      [forall v : D, has (fun p => v \in pp_vtx p) Q] &
      (* every vertex lies on at most one path (so the paths partition V) *)
      [forall v : D, count (fun p => v \in pp_vtx p) Q <= 1]].

(** k-norm of a path-partition: each path contributes [min(k, #vertices)]. *)
Definition pp_knorm (k : nat) (Q : seq (D * seq D)) : nat :=
  \sum_(p <- Q) minn k (size (pp_vtx p)).

End Packing.

Arguments cycle_pack {D}.
Arguments vtx_disjoint {D}.
Arguments vtx_disjoint_pack {D}.
Arguments real_sel {D}.
Arguments arc_disjoint_sel {D}.
Arguments selindeg {D}.
Arguments out_branching {D}.
Arguments in_branching {D}.
Arguments oneway {D}.
Arguments in_dicut {D}.
Arguments dicut_size {D}.
Arguments dijoin {D}.
Arguments pp_partition {D}.
Arguments pp_knorm {D}.

(** ** Bermond–Thomassen Conjecture

    Every digraph of minimum out-degree ≥ 2k−1 contains k vertex-disjoint directed cycles.
    (Verbatim sketch: [min_outdeg D >= 2*k-1 -> exists cs, vertex_disjoint cs /\ size cs = k
    /\ all (dicycle D) cs].) Min out-degree is pointwise [forall v, 2*k-1 <= outdeg v]. *)
Definition bermond_thomassen_statement : Prop :=
  forall (D : diGraphType) (k : nat),
    (0 < #|D|)%N ->
    (forall v : D, (2 * k - 1 <= outdeg v)%N) ->
    exists P : seq (seq D),
      [/\ cycle_pack P, vtx_disjoint_pack P & size P = k].

(** ** Hoàng–Reed Conjecture

    Every digraph of minimum out-degree ≥ k contains k directed cycles
    [C_1, …, C_k] with the laminar / intersection-forest property: for every
    [2 ≤ j ≤ k], [C_j] meets [C_1 ∪ ⋯ ∪ C_{j−1}] in at most one vertex.
    (Verbatim sketch: [(forall v, outdeg v >= k) -> exists Cs : k.-tuple (dicycle),
    forall j, 2<=j<=k -> #|verts (Cs j) :&: ⋃_{i<j} verts (Cs i)| <= 1].) *)
Definition hoang_reed_statement : Prop :=
  forall (D : diGraphType) (k : nat),
    (0 < #|D|)%N ->
    (forall v : D, (k <= outdeg v)%N) ->
    exists P : seq (seq D),
      [/\ cycle_pack P,
          size P = k &
          (* intersection-forest: cycle #j meets the union of the earlier ones
             in at most one vertex, for every 1 <= j < size P *)
          forall j : 'I_(size P), (0 < j)%N ->
            (#|[set v : D | (v \in nth [::] P j) &&
                 [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]]| <= 1)%N].

(** ** Woodall's Conjecture (directed Lucchesi–Younger)

    In every digraph the minimum size of a dicut equals the maximum number of
    arc-disjoint dijoins: if the minimum dicut size is [k] then there exist [k]
    pairwise arc-disjoint dijoins.
    (Verbatim sketch: [min_dicut_size G = k -> exists Js, size Js = k /\
    arc_disjoint Js /\ all (dijoin G) Js].) We phrase "minimum dicut size = k" as: some
    one-way set has dicut [k], and no one-way set has a smaller dicut. *)
Definition woodall_statement : Prop :=
  forall (D : diGraphType) (k : nat),
    (exists B : {set D}, oneway B /\ dicut_size B = k) ->
    (forall B : {set D}, oneway B -> (k <= dicut_size B)%N) ->
    exists Js : seq (D -> {set D}),
      [/\ all dijoin Js,
          size Js = k &
          (* pairwise arc-disjoint *)
          [forall i : 'I_(size Js), forall j : 'I_(size Js),
             (i != j) ==>
             arc_disjoint_sel (nth (fun _ => set0) Js i) (nth (fun _ => set0) Js j)]].

(** ** Linial–Berge path-partition duality

    For every digraph and every [k], the minimum k-norm over all path-partitions equals
    the maximum, over induced subdigraphs that are k-colourable (in the directed/acyclic
    sense χ⃗ ≤ k), of the number of vertices. We state the LE direction that is the
    content of the conjecture (the dual GE is the easy direction):
       min over path-partitions of (k-norm)  ≥  |S|  for every χ⃗(D[S]) ≤ k induced S,
    and a path-partition realizing the value [|S|] exists.
    (Verbatim sketch: [min_over_path_partitions (k_norm k) D <=
    max_over_induced (fun S => k_colorableb S && #|S|) D].) *)
Definition linial_berge_statement : Prop :=
  forall (D : diGraphType) (k : nat),
    exists (Q : seq (D * seq D)) (S : {set D}),
      [/\ (* Q is a path-partition realizing the minimum k-norm *)
          pp_partition Q,
          (* S induces a χ⃗ ≤ k subdigraph (a union of k acyclic sets) *)
          dicolorableb (induced_digraph S) k,
          (* duality: the realized k-norm equals |S| *)
          pp_knorm k Q = #|S| &
          (* and this is optimal: no path-partition has smaller k-norm than |S|,
             i.e. |S| is a certificate matching the path-partition optimum *)
          forall Q' : seq (D * seq D), pp_partition Q' -> (#|S| <= pp_knorm k Q')%N].

(** ** Erdős–Pósa for long directed cycles

    For every [ℓ ≥ 2] there is a function [t(·)] such that every digraph either contains
    [n] vertex-disjoint directed cycles each of length ≥ [ℓ], or has a set of ≤ [t(n)]
    vertices meeting every directed cycle of length ≥ [ℓ].
    (Verbatim sketch: [forall ell>=2, forall n, exists t, forall D, (exists pk : n.-tuple,
    vtx_disjoint pk /\ all (length >= ell) pk) \/ (exists T, #|T|<=t /\
    no_long_dicycle (del_vtxs D T) ell)].)

    We say a vertex set [T] is a "long-cycle transversal" ([meets_long_dicycles]) if
    every directed cycle of length ≥ [ℓ] in [D] meets [T]. *)
Definition meets_long_dicycles (D : diGraphType) (ell : nat) (T : {set D}) : Prop :=
  forall c : seq D, dicycle c -> (ell <= size c)%N -> exists2 v, v \in T & v \in c.

Definition erdos_posa_long_dicycles_statement : Prop :=
  forall ell : nat, (2 <= ell)%N ->
  forall n : nat, exists t : nat,
    forall D : diGraphType,
      (exists P : seq (seq D),
         [/\ cycle_pack P, vtx_disjoint_pack P, size P = n &
             all (fun c => ell <= size c)%N P])
      \/
      (exists T : {set D}, (#|T| <= t)%N /\ meets_long_dicycles ell T).

(** ** Edges *)

(** Bermond–Thomassen ⟹ "weak Hoàng–Reed at the stronger threshold": at the higher
    degree bound δ⁺ ≥ 2k−1 the disjoint cycles are pairwise DISJOINT, so each later
    cycle meets the union of the earlier ones in 0 ≤ 1 vertices — the laminar property
    holds trivially. (Hoàng–Reed proper asks for it already at δ⁺ ≥ k.) *)
Theorem bermond_thomassen_implies_hoang_reed_weak :
  bermond_thomassen_statement ->
  forall (D : diGraphType) (k : nat),
    (0 < #|D|)%N ->
    (forall v : D, (2 * k - 1 <= outdeg v)%N) ->
    exists P : seq (seq D),
      [/\ cycle_pack P,
          size P = k &
          forall j : 'I_(size P), (0 < j)%N ->
            (#|[set v : D | (v \in nth [::] P j) &&
                 [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]]| <= 1)%N].
Proof.
move=> BT D k Dpos hdeg.
have [P [cp vdp szP]] := BT D k Dpos hdeg.
exists P; split=> // j jpos.
have -> : [set v : D | (v \in nth [::] P j) &&
            [exists i : 'I_(size P), (i < j)%N && (v \in nth [::] P i)]] = set0.
  apply/setP=> v; rewrite !inE.
  apply/andP=> -[vj /existsP[i /andP[ij vi]]].
(* i < j so i != j; disjointness of P forces no common vertex of cycles i, j *)
have iNj : i != j by rewrite -(inj_eq val_inj); apply/eqP=> e; rewrite e ltnn in ij.
  move/forallP/(_ i)/forallP/(_ j): vdp; rewrite iNj /=.
  rewrite /vtx_disjoint => /hasPn/(_ v vi) /negP; exact.
by rewrite cards0.
Qed.

(** Hoàng–Reed at [k = 1] (over a digraph of min out-degree ≥ 1) yields a directed cycle:
    the packing has size 1, its single member is a dicycle. *)
Theorem hoang_reed_implies_one_cycle :
  hoang_reed_statement ->
  forall D : diGraphType, (0 < #|D|)%N -> (forall v : D, (1 <= outdeg v)%N) ->
    exists c : seq D, dicycle c.
Proof.
move=> HR D Dpos hdeg.
have [P [cp szP _]] := HR D 1 Dpos hdeg.
case: P cp szP => [|c tl] // /andP[dc _] _; by exists c.
Qed.
