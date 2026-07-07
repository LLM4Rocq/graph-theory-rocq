(** * Digraph.conjectures.X2 -- v2 milestone X2, clean arXiv statement wave

    This file states the first clean X2 batch: the eleven open arXiv rows whose
    statements are self-contained enough to author before the bounded /
    needs-primitive followups.  The missing-statement row arXiv:2602.16333#03
    is intentionally not represented here. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import automorphism domination strong.
From Digraph Require Import classic_core heroes chi_bounded dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Generic embeddings and directed subdivisions **************************)

(** Non-induced subdigraph containment: arcs of [H] are preserved injectively in
    [D].  This is the containment notion for path/tree appearances, distinct from
    [heroes.ind_subdigraph], which is induced. *)
Definition subdigraph_embed (H D : diGraphType) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u --> v -> f u --> f v.

Section SubdivisionModel.
Variables (F D : diGraphType) (branch : F -> D).

Definition x2_path_vertices (x : D) (s : seq D) : {set D} :=
  [set y | y \in x :: s].

Definition x2_branch_set : {set D} :=
  [set y | [exists x : F, branch x == y]].

Definition x2_path_internal (u v : F) (s : seq D) : {set D} :=
  x2_path_vertices (branch u) s :\: [set branch u; branch v].

End SubdivisionModel.

(** A subdivision model maps each vertex of [F] to a branch vertex of [D] and
    replaces every arc [u -> v] of [F] by a directed path from [u]'s branch to
    [v]'s branch.  The internal vertices of all replacement paths are
    vertex-disjoint and avoid every branch vertex. *)
Definition contains_subdivision (F D : diGraphType) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u --> v ->
        [/\ (0 < size (paths u v))%N,
            dipath (branch u) (paths u v),
            last (branch u) (paths u v) = branch v
          & [disjoint x2_path_internal branch u v (paths u v)
             & x2_branch_set branch]]) /\
      (forall u v x y : F, u --> v -> x --> y ->
        ((u != x) || (v != y)) ->
        [disjoint x2_path_internal branch u v (paths u v)
         & x2_path_internal branch x y (paths x y)]).

Definition min_outdegree_at_least (D : diGraphType) (m : nat) : Prop :=
  forall v : D, (m <= outdeg v)%N.

Definition min_semidegree_at_least (D : diGraphType) (m : nat) : Prop :=
  forall v : D, (m <= outdeg v)%N /\ (m <= indeg v)%N.

Definition mader_delta_plus_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, min_outdegree_at_least D m -> contains_subdivision F D.

Definition mader_delta_zero_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, min_semidegree_at_least D m -> contains_subdivision F D.

Definition delta_plus_maderian (F : diGraphType) : Prop :=
  exists m : nat, mader_delta_plus_bound F m.

Definition least_mader_delta_zero (F : diGraphType) (m : nat) : Prop :=
  mader_delta_zero_bound F m /\
  forall c : nat, mader_delta_zero_bound F c -> (m <= c)%N.

(** arXiv:1610.00876, Conjecture 3. *)
Definition mader_delta0_transitive_tournament_statement : Prop :=
  forall k : nat, exists m : nat, least_mader_delta_zero (TT k) m.

Definition oriented_tree (F : orientedDigraph) : Prop :=
  [/\ (0 < #|F|)%N,
      chi_bounded.oriented_dg F,
      is_forest [set: chi_bounded.underlying F]
    & connected [set: chi_bounded.underlying F]].

(** arXiv:1610.00876, Conjecture 4. *)
Definition oriented_trees_delta_plus_maderian_statement : Prop :=
  forall F : orientedDigraph, oriented_tree F -> delta_plus_maderian F.

Section DisjointUnion.
Variables D1 D2 : diGraphType.

Definition x2_disjoint_union : Type := (D1 + D2)%type.
HB.instance Definition _ := Finite.on x2_disjoint_union.

Definition x2_disjoint_union_rel (x y : D1 + D2) : bool :=
  match x, y with
  | inl a, inl b => a --> b
  | inr a, inr b => a --> b
  | _, _ => false
  end.

HB.instance Definition _ := HasArc.Build x2_disjoint_union x2_disjoint_union_rel.

End DisjointUnion.

(** arXiv:1610.00876, Conjecture 7. *)
Definition delta_plus_maderian_disjoint_union_statement : Prop :=
  forall F1 F2 : diGraphType,
    delta_plus_maderian F1 -> delta_plus_maderian F2 ->
    delta_plus_maderian (x2_disjoint_union F1 F2).

(** ** Dominating-number tournament problems *******************************)

Fixpoint Si_tournament (i : nat) : diGraphType -> Prop :=
  match i with
  | 0 => fun _ => False
  | i'.+1 =>
      match i' with
      | 0 => fun S => dgiso S K1
      | _ => fun S => exists P : diGraphType,
          Si_tournament i' P /\ dgiso S (c3sub P P K1)
      end
  end.

Definition contains_Si (T : tournament) (i : nat) : Prop :=
  exists S : diGraphType, Si_tournament i S /\ ind_subdigraph S T.

(** arXiv:1702.01607, Problem 3. *)
Definition large_domination_contains_Si_statement : Prop :=
  forall i : nat, (1 <= i)%N ->
    exists f : nat,
      forall T : tournament, (f <= domnum T)%N -> contains_Si T i.

(** arXiv:1702.01607, Problem 4. *)
Definition large_domination_contains_large_dom_subtournament_statement : Prop :=
  forall k : nat, (1 <= k)%N ->
    exists K ell : nat,
      forall T : tournament, (K <= domnum T)%N ->
        exists S : {set T},
          #|S| = ell /\ (k <= domnum (sub_tournament S))%N.

(** ** Directed Kneser existence ********************************************)

Definition bsubset (k b : nat) := {S : {set 'I_k} | #|S| == b}.

Section KneserDigraph.
Variables (k b : nat) (R : rel (bsubset k b)).

Definition kneser_digraph : Type := bsubset k b.
HB.instance Definition _ := Finite.on kneser_digraph.
HB.instance Definition _ := HasArc.Build kneser_digraph R.

Definition common_intersection_nonempty (X : {set kneser_digraph}) : Prop :=
  exists i : 'I_k, forall B : kneser_digraph, B \in X -> i \in val B.

Definition directed_kneser_property : Prop :=
  forall X : {set kneser_digraph},
    acyclicb (induced_digraph X) <-> common_intersection_nonempty X.

End KneserDigraph.

(** arXiv:1812.02420, Problem 5.40. *)
Definition directed_kneser_existence_statement : Prop :=
  forall k b : nat, (0 < b)%N -> (b <= k)%N ->
    exists R : rel (bsubset k b), directed_kneser_property R.

(** ** Same-vertex graph/tournament local chromatic questions ***************)

Definition x2_sgraph (T : finType) (E : rel T)
    (Esym : symmetric E) (Eirr : irreflexive E) : sgraph :=
  SGraph Esym Eirr.

Section X2InducedSGraph.
Variables (T : finType) (E : rel T)
          (Esym : symmetric E) (Eirr : irreflexive E) (S : {set T}).

Definition x2_induced_rel (x y : {x : T | x \in S}) : bool :=
  E (val x) (val y).

Lemma x2_induced_sym : symmetric x2_induced_rel.
Proof. by move=> x y; rewrite /x2_induced_rel Esym. Qed.

Lemma x2_induced_irrefl : irreflexive x2_induced_rel.
Proof. by move=> x; rewrite /x2_induced_rel Eirr. Qed.

Definition x2_induced_sgraph : sgraph :=
  SGraph x2_induced_sym x2_induced_irrefl.

End X2InducedSGraph.

Definition sg_degeneracy_at_least (G : sgraph) (d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\ forall x : G, x \in S -> (d <= #|N(x) :&: S|)%N.

Definition sg_has_cycle (G : sgraph) : Prop :=
  exists c : seq G, ucycle (--) c /\ (2 < size c)%N.

(** arXiv:2305.15585, Question 10. *)
Definition tournament_outneighborhood_degeneracy_statement : Prop :=
  forall d : nat, exists C : nat,
    forall (T : tournament) (E : rel T)
           (Esym : symmetric E) (Eirr : irreflexive E),
      (C <= χ([set: x2_sgraph Esym Eirr]))%N ->
      exists v : T,
        sg_degeneracy_at_least
          (x2_induced_sgraph Esym Eirr (N_out v)) d.

(** arXiv:2305.15585, Conjecture 11. *)
Definition tournament_outneighborhood_cycle_statement : Prop :=
  exists C : nat,
    forall (T : tournament) (E : rel T)
           (Esym : symmetric E) (Eirr : irreflexive E),
      (C <= χ([set: x2_sgraph Esym Eirr]))%N ->
      exists v : T,
        sg_has_cycle (x2_induced_sgraph Esym Eirr (N_out v)).

(** ** Strong 2-kernels in split digraphs **********************************)

Definition x2_arc_stable (D : diGraphType) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u --> v)]].

Definition x2_tournament_on (D : diGraphType) (S : {set D}) : Prop :=
  forall u v : D, u \in S -> v \in S -> u != v -> (u --> v) (+) (v --> u).

Definition split_partition (D : diGraphType) (Tpart : {set D}) : Prop :=
  x2_tournament_on Tpart /\ x2_arc_stable (~: Tpart).

(** The paper's split digraphs are ORIENTED (loopless and digon-free;
    Nguyen–Scott–Seymour "Distant digraph domination", §1).  [diGraphType]
    enforces neither (irreflexivity/asymmetry live only in [orientedDigraph],
    which the [{set D}]-parameterised helpers here do not use), so the statement
    below carries this as an explicit guard.  Without it the conjecture is
    provably FALSE, e.g. the directed triangle with a self-loop at every vertex
    satisfies [split_partition] but admits no strong 2-kernel (every loop vertex
    is barred from [K] by [x2_arc_stable], forcing [K = set0]). *)
Definition x2_oriented (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> (u != v) /\ ~~ (v --> u).

(** A vertex is a source when it has no in-neighbour.  A distinct in-neighbour
    is required so that (absent [x2_oriented]) a self-loop does not spuriously
    make a vertex a non-source. *)
Definition no_sources (D : diGraphType) : Prop :=
  forall v : D, [exists u : D, (u != v) && (u --> v)].

Definition x2_covers1 (D : diGraphType) (K : {set D}) (v : D) : bool :=
  (v \in K) || [exists k in K, k --> v].

Definition x2_covers2 (D : diGraphType) (K : {set D}) (v : D) : bool :=
  x2_covers1 K v || [exists k in K, [exists u : D, (k --> u) && (u --> v)]].

Definition two_kernel (D : diGraphType) (K : {set D}) : Prop :=
  x2_arc_stable K /\ forall v : D, x2_covers2 K v.

Definition strong_two_kernel (D : diGraphType) (Tpart K : {set D}) : Prop :=
  two_kernel K /\
  forall v : D, v \in Tpart ->
    x2_covers1 K v ||
    [exists k in K :&: Tpart, [exists u : D, (k --> u) && (u --> v)]].

(** arXiv:2409.05039, open question on strong 2-kernels in split digraphs. *)
Definition split_digraph_strong_two_kernel_statement : Prop :=
  forall (D : diGraphType) (Tpart : {set D}),
    x2_oriented D ->
    split_partition Tpart -> no_sources D ->
    exists K : {set D},
      strong_two_kernel Tpart K /\ (2 * #|K| <= #|D|)%N.

(** ** Oriented paths at the semidegree threshold ***************************)

Definition consecutive_in (D : finType) (p : seq D) (u v : D) : Prop :=
  exists i : nat,
    i.+1 < size p /\
    (((u == nth u p i) && (v == nth u p i.+1)) ||
     ((u == nth u p i.+1) && (v == nth u p i))).

Definition listed_path_underlying (P : diGraphType) (k : nat) (p : seq P) : Prop :=
  [/\ uniq p,
      size p = k.+1,
      (forall v : P, v \in p)
    & forall u v : P, u != v ->
        (chi_bounded.urel u v <-> consecutive_in p u v)].

Definition oriented_path (P : orientedDigraph) (k : nat) : Prop :=
  exists p : seq P, @listed_path_underlying P k p.

Definition antidirected_path (P : diGraphType) : Prop :=
  forall v : P, indeg v = 0 \/ outdeg v = 0.

Definition min_semidegree_half (D : diGraphType) (k : nat) : Prop :=
  forall v : D, (k <= 2 * outdeg v)%N /\ (k <= 2 * indeg v)%N.

(** arXiv:2503.23191, Question 5.1. *)
Definition semidegree_oriented_paths_statement : Prop :=
  forall (k : nat) (G : orientedDigraph),
    min_semidegree_half G k ->
    forall P : orientedDigraph,
      oriented_path P k -> ~ antidirected_path P -> subdigraph_embed P G.

(** ** Longest directed cycles in vertex-transitive digraphs ****************)

Definition weakly_connected (D : diGraphType) : Prop :=
  forall u v : D, connect (@chi_bounded.urel D) u v.

Definition longest_dicycle (D : diGraphType) (c : seq D) : Prop :=
  dicycle c /\ forall c' : seq D, dicycle c' -> (size c' <= size c)%N.

(** arXiv:2602.16333, Question 4.3. *)
Definition vertex_transitive_longest_dicycles_intersect_statement : Prop :=
  forall D : diGraphType,
    weakly_connected D -> vertex_transitiveb D ->
    forall c1 c2 : seq D,
      longest_dicycle c1 -> longest_dicycle c2 ->
      exists v : D, v \in c1 /\ v \in c2.
