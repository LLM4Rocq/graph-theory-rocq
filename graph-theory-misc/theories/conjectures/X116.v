(** * GTMisc.conjectures.X116 -- v2 coarse Menger (bounded-separator) row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X116 vocabulary ***********************************************

    Coarse metric / path vocabulary, mirroring
    [GTMisc.conjectures.X39] so this file is self-contained.
    [x116_ball r x] / [x116_set_ball r S] are the closed [r]-ball around a
    vertex / vertex set; [x116_path_vertices p] is the vertex set of a walk;
    [x116_ST_path S T p] is a simple path from [S] to [T]. *)

Fixpoint x116_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x116_ball r' x :|: \bigcup_(z in x116_ball r' x) N(z)
  else [set x].

Definition x116_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x116_ball r x.

Definition x116_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x116_ST_path (G : sgraph) (S T : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in S /\ last x q \in T /\ uniq p /\ path (--) x q
  end.

(** Two paths are at distance at least [d] iff, in addition to being
    vertex-disjoint, the closed [d.-1]-ball around one avoids the vertex set of
    the other (no vertex of one lies within distance [d-1] of the other). *)
Definition x116_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x116_path_vertices p & x116_path_vertices q] /\
    [disjoint x116_set_ball (d.-1) (x116_path_vertices p) & x116_path_vertices q].

(** [k] distinct [S]-[T] paths that are pairwise at distance at least [d]. *)
Definition x116_has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x116_ST_path S T p) /\
    x116_pairwise_distant_paths d paths.

(** ** X116 statement *****************************************************)

(** Coarse Menger conjecture, bounded-separator form (Albrechtsen-Huynh-Jacobs-
    Knappe-Wollan / Georgakopoulos-Papasoglu): for all [k, d >= 1] there is an
    [l > 0] such that for every graph [G] and every pair of vertex sets [S], [T],
    either there are [k] paths from [S] to [T] pairwise at distance at least [d],
    or there is a set [X] of at most [k-1] vertices whose closed [l]-ball meets
    every [S]-[T] path (every such path has a vertex within distance [l] of [X]).

    Distinct from [GTMisc.conjectures.X39] (Georgakopoulos-Papasoglu ball-separator
    form): there the separator radius is [c * d] for a single constant [c] chosen
    with [forall k, exists c, forall d]; here [l] is an arbitrary function of both
    [k] and [d] ([forall k d, exists l]), and the separator is stated as "every
    [S]-[T] path meets the [l]-ball of [X]" with [#|X| <= k-1]. *)
Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        x116_has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            x116_ST_path S T p ->
            exists v : G,
              v \in x116_path_vertices p /\ v \in x116_set_ball l X.
