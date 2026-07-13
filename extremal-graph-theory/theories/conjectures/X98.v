(** * Extremal.conjectures.X98 -- v2 polynomial Kuhn-Osthus row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X59.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X98 vocabulary ************************************************)

Definition x98_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x98_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x98_consecutive_in_path p u v
  end.

(** An internal (non-endpoint) vertex of a candidate edge-path [p] whose
    endpoints are [a] and [b]. *)
Definition x98_internal (G : sgraph) (p : seq G) (a b x : G) : Prop :=
  x \in p /\ x != a /\ x != b.

(** A vertex of the whole subdivision model: a branch vertex, or a vertex
    lying on some edge-path. *)
Definition x98_model_vertex (H G : sgraph)
    (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop :=
  (exists h : H, br h = x) \/ (exists u v : H, u -- v /\ x \in ep u v).

Record x98_induced_subdivision_model (H G : sgraph) := X98Model {
  x98_branch : H -> G;
  x98_branch_injective : injective x98_branch;
  x98_edge_path : H -> H -> seq G;
  x98_edge_path_valid :
    forall u v : H,
      u -- v ->
      x98_induced_path_between
        (x98_branch u) (x98_branch v) (x98_edge_path u v);
  (** internal path vertices avoid every branch vertex *)
  x98_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x != x98_branch w;
  (** edge-paths are pairwise internally vertex-disjoint (a shared internal
      vertex forces the two undirected edges to coincide) *)
  x98_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x98_internal (x98_edge_path u' v') (x98_branch u') (x98_branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  (** global inducedness: the only G-edges among model vertices join two
      consecutive vertices of a single subdivision path *)
  x98_global_induced :
    forall x y : G,
      x98_model_vertex x98_branch x98_edge_path x ->
      x98_model_vertex x98_branch x98_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ x98_consecutive_in_path (x98_edge_path u v) x y
}.

Definition x98_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (x98_induced_subdivision_model H G).

(** ** X98 statements ******************************************************)

(** Studies slice: Bonamy et al. polynomial Kuhn-Osthus conjecture: for every
    fixed graph H, a polynomial in s average-degree threshold forces an induced
    subdivision of H in every K_{s,s}-free graph. *)
Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        x98_induced_subdivision H G.
