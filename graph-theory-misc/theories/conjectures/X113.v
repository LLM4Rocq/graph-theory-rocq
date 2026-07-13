(** * GTMisc.conjectures.X113 -- v2 coarse Erdos-Posa (cycles/forest) row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X113 vocabulary ***********************************************

    Coarse metric vocabulary, mirroring
    [GTMisc.conjectures.X39] so this file is self-contained.
    [x113_ball r x] is the closed [r]-ball around [x] (all vertices at graph
    distance at most [r]); [x113_set_ball r S] is the union of the [r]-balls
    over a vertex set [S].  A "cycle" is a genuine simple cycle (a uniform
    closed walk on at least three vertices, following adjacency [--]),
    encoded exactly as in base's [girth]/[exact_girth] via
    [ucycle (--) c /\ 2 < size c]. *)

Fixpoint x113_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x113_ball r' x :|: \bigcup_(z in x113_ball r' x) N(z)
  else [set x].

Definition x113_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x113_ball r x.

Definition x113_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

(** A genuine cycle: a uniform closed adjacency-walk on at least 3 vertices. *)
Definition x113_is_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

(** Cycles [p], [q] are at distance greater than [d] iff the closed [d]-ball
    around one avoids the vertex set of the other.  For [d >= 1] this already
    forces the two cycles to be vertex-disjoint. *)
Definition x113_pairwise_distant_cycles
    (G : sgraph) (d : nat) (cs : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in cs -> q \in cs -> p != q ->
    [disjoint x113_set_ball d (x113_path_vertices p) & x113_path_vertices q].

(** [k] distinct genuine cycles that are pairwise at distance greater than [d]. *)
Definition x113_has_k_distant_cycles
    (G : sgraph) (d k : nat) : Prop :=
  exists cs : seq (seq G),
    size cs = k /\
    uniq cs /\
    (forall c : seq G, c \in cs -> x113_is_cycle c) /\
    x113_pairwise_distant_cycles d cs.

(** [G] minus the vertex set [A] is a forest, i.e. the subgraph induced on the
    remaining vertices is acyclic: no genuine cycle of [G] avoids [A].  (Because
    [--] is inherited by induced subgraphs, a genuine cycle whose vertices all
    miss [A] is exactly a cycle of [G - A].) *)
Definition x113_is_forest_after
    (G : sgraph) (A : {set G}) : Prop :=
  forall c : seq G,
    x113_is_cycle c ->
    [disjoint x113_path_vertices c & A] ->
    False.

(** ** X113 statement *****************************************************)

(** Coarse Erdos-Posa property for cycles (Chudnovsky-Seymour): there exist
    functions [f], [g] such that for every [k, d >= 1] and every graph [G],
    either [G] contains [k] cycles pairwise at distance greater than [d], or a
    set [X] of at most [f k] vertices can be found whose closed [g d]-ball meets
    every cycle -- deleting that ball leaves a forest.  The two functions are
    chosen up front (uniformly in [G, k, d]), matching the [exists f g, forall
    ...] shape of the coarse Erdos-Posa duality. *)
Definition coarse_erdos_posa_cycles_forest_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph),
      1 <= k -> 1 <= d ->
      x113_has_k_distant_cycles G d k \/
      exists X : {set G},
        #|X| <= f k /\
        x113_is_forest_after (x113_set_ball (g d) X).
