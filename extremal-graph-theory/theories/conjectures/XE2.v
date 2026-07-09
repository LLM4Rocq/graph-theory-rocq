(** * Extremal.conjectures.XE2 -- Erdos solved clean/bounded rows *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

Definition xe2_edge_disjoint_triangles (G : sgraph) (ts : seq {set G}) : Prop :=
  uniq ts /\
  (forall T : {set G}, T \in ts -> x4_triangle_set T) /\
  forall T U : {set G}, T \in ts -> U \in ts -> T != U ->
    [disjoint xe2_tri_edges T & xe2_tri_edges U].

Definition xe2_superlinear_edge_threshold
    (eps_num eps_den n m : nat) : Prop :=
  n ^ (eps_den + eps_num) <= m ^ eps_den.

Definition xe2_saturated_planar (G : sgraph) : Prop :=
  3 < #|G| /\ wagner_planar G /\ x4_edge_count G = 3 * #|G| - 6.

Definition xe2_paths_cover_vertices (G : sgraph) (m : nat) (P : 'I_m -> seq G) : Prop :=
  forall v : G, exists i : 'I_m, v \in P i.

Definition xe2_path_in_graph (G : sgraph) (p : seq G) : Prop :=
  if p is x :: q then path (--) x q else true.

Definition xe2_monochromatic_path
    (G : sgraph) (col : rel G) (b : bool) (p : seq G) : Prop :=
  if p is x :: q then
    uniq (x :: q) /\
    path (--) x q /\
    forall e : G * G, e \in zip p (behead p) -> col e.1 e.2 = b
  else false.

Definition xe2_induced_ramsey_number (H : sgraph) (m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = m /\
      forall col : rel G, symmetric col ->
        exists (b : bool) (f : H -> G),
          injective f /\
          (forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y) = b) /\
          forall x y : H, x != y -> ~~ (x -- y) -> ~~ (f x -- f y)) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = m' /\
      forall col : rel G, symmetric col ->
        exists (b : bool) (f : H -> G),
          injective f /\
          (forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y) = b) /\
          forall x y : H, x != y -> ~~ (x -- y) -> ~~ (f x -- f y)) -> m <= m'.

Definition xe2_bipartite_plus_bounded_degree (G : sgraph) (d : nat) : Prop :=
  exists F : {set {set G}},
    F \subset x4_edge_set G /\
    bipartite (@xe1_delete_edges G F) /\
    forall v : G, #|[set e in F | v \in e]| < d.

Definition xe2_diameter_critical_two (G : sgraph) : Prop :=
  xe1_diameter_at_most G 2 /\
  ~ xe1_diameter_at_most G 1 /\
  forall e : {set G}, e \in x4_edge_set G ->
    ~ xe1_diameter_at_most (@xe1_delete_edges G [set e]) 2.

Definition xe2_path_length3 (G : sgraph) (x y : G) : Prop :=
  exists a b : G, uniq [:: x; a; b; y] /\ x -- a /\ a -- b /\ b -- y.

Definition xe2_bipartition_sizes (G : sgraph) (a b : nat) : Prop :=
  exists A B : {set G},
    [disjoint A & B] /\
    A :|: B = [set: G] /\
    #|A| = a /\
    #|B| = b /\
    forall x y : G, x -- y ->
      (x \in A /\ y \in B) \/ (x \in B /\ y \in A).

Definition xe2_cube_square_floor (n a : nat) : Prop :=
  a ^ 3 <= n ^ 2 /\ forall b : nat, b ^ 3 <= n ^ 2 -> b <= a.

Definition xe2_min_degree (G : sgraph) (d : nat) : Prop :=
  (exists v : G, #|N(v)| = d) /\
  forall v : G, d <= #|N(v)|.

Definition xe2_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe2_cycle_diagonal_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ x4_consecutive_in_cycle c p.1 p.2]]|.

Definition xe2_incident_cycle_chord_count (G : sgraph) (c : seq G) (v : G) : nat :=
  #|[set u : G |
      [&& u \in c, v \in c, u != v, v -- u
        & ~~ x4_consecutive_in_cycle c v u]]|.

Definition xe2_no_cycle_with_incident_chords (G : sgraph) (k : nat) : Prop :=
  forall c : seq G, xe2_cycle c ->
    forall v : G, v \in c -> xe2_incident_cycle_chord_count c v < k.

Definition xe2_incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m /\
      xe2_no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m' /\
      xe2_no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition xe2_internal_path_vertices (G : sgraph) (x y : G) (p : seq G) : {set G} :=
  [set v : G | [&& v \in p, v != x & v != y]].

Definition xe2_paths_internally_disjoint
    (G : sgraph) (m : nat) (x y : G) (P : 'I_m -> seq G) : Prop :=
  forall i j : 'I_m, i != j ->
    [disjoint xe2_internal_path_vertices x y (P i)
            & xe2_internal_path_vertices x y (P j)].

Definition xe2_path_edge_set (G : sgraph) (p : seq G) : {set {set G}} :=
  [set e : {set G} |
      [exists xy : G * G, (xy \in zip p (behead p)) && (e == [set xy.1; xy.2])]].

Definition xe2_paths_edge_disjoint
    (G : sgraph) (m : nat) (P : 'I_m -> seq G) : Prop :=
  forall i j : 'I_m, i != j ->
    [disjoint xe2_path_edge_set (P i) & xe2_path_edge_set (P j)].

(** Erdos Problems #1009. *)
Definition erdos_1009_statement : Prop :=
  forall cnum cden : nat, 0 < cnum -> 0 < cden -> exists f : nat,
    forall (n k : nat) (G : sgraph),
      #|G| = n ->
      x4_edge_count G >= (n ^ 2) %/ 4 + k ->
      cden * k < cnum * n ->
      exists ts : seq {set G},
        xe2_edge_disjoint_triangles ts /\ k <= size ts + f.

(** Erdos Problems #1018. *)
Definition erdos_1018_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists C N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n ->
        xe2_superlinear_edge_threshold eps_num eps_den n (x4_edge_count G) ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| <= C /\ ~ wagner_planar H.

(** Erdos Problems #1019. *)
Definition erdos_1019_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    x4_edge_count G = (n ^ 2) %/ 4 + (n.+1 %/ 2) ->
    exists H : sgraph, xe1_subgraph_of H G /\ xe2_saturated_planar H.

(** Erdos Problems #1080. *)
Definition erdos_1080_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (n : nat) (G : sgraph),
      #|G| = n ->
      (exists a b : nat, xe2_cube_square_floor n a /\ xe2_bipartition_sizes G a b) ->
      cden * x4_edge_count G >= cnum * n ->
      xe1_subgraph_of (cycle_graph 6) G.

(** Erdos Problems #22. *)
Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * x4_edge_count G >= n ^ 2 /\
          ~ xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

(** Erdos Problems #518. *)
Definition erdos_518_statement : Prop :=
  forall n : nat, exists m : nat, m ^ 2 <= n /\
    forall col : rel 'I_n,
      symmetric col ->
      exists (b : bool) (P : 'I_m -> seq 'I_n),
        (forall i : 'I_m, @xe2_monochromatic_path 'K_n col b (P i)) /\
        @xe2_paths_cover_vertices 'K_n m P.

(** Erdos Problems #547. *)
(** Guard [2 <= n]: for n = 1 the one-vertex graph is a tree with R = 1, but
    2*1-2 = 0 in nat, so the bound is false there.  A tree "on n vertices" in
    the conjecture means n >= 2. *)
Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    xe1_tree T -> #|T| = n ->
    xe1_diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

(** Erdos Problems #549. *)
Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> xe2_bipartition_sizes T k (2 * k) ->
    xe1_diagonal_ramsey_number T R ->
    R = 4 * k - 1.

(** Erdos Problems #559. *)
Definition erdos_559_statement : Prop :=
  forall d : nat, exists C : nat,
    forall (G : sgraph) (n m : nat),
      #|G| = n -> Delta G <= d ->
      xe1_size_ramsey_number G G m ->
      m <= C * n.

(** Erdos Problems #565. *)
Definition erdos_565_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n m : nat),
      #|G| = n ->
      xe2_induced_ramsey_number G m ->
      m <= 2 ^ (C * n).

(** Erdos Problems #570. *)
Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

(** Erdos Problems #613. *)
Definition erdos_613_statement : Prop :=
  forall (n : nat) (G : sgraph),
    3 <= n ->
    x4_edge_count G = 'C(2 * n + 1, 2) - 'C(n, 2) - 1 ->
    xe2_bipartite_plus_bounded_degree G n.

(** Erdos Problems #73. *)
Definition erdos_73_statement : Prop :=
  forall k : nat, exists C : nat,
    forall G : sgraph,
      (forall S : {set G}, exists A : {set G},
          A \subset S /\ xe1_stable_set A /\ 2 * #|A| + k >= #|S|) ->
      exists X : {set G}, #|X| <= C /\ bipartite (induced (~: X)).

(** Erdos Problems #742. *)
Definition erdos_742_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    xe2_diameter_critical_two G ->
    4 * x4_edge_count G <= n ^ 2.

(** Erdos Problems #767. *)
Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      xe2_incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

(** Erdos Problems #800. *)
Definition erdos_800_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n R : nat),
      #|G| = n ->
      (forall x y : G, x -- y -> #|N(x)| < 3 \/ #|N(y)| < 3) ->
      xe1_diagonal_ramsey_number G R ->
      R <= C * n.

(** Erdos Problems #801. *)
Definition erdos_801_statement : Prop :=
  exists C N : nat,
    0 < C /\
    forall (G : sgraph) (n s : nat),
      N <= n ->
      #|G| = n ->
      xe1_sqrt_floor n s ->
      (forall A : {set G}, xe1_stable_set A -> #|A| <= s) ->
      exists S : {set G},
        #|S| <= s /\ C * x4_edge_count (induced S) >= s * trunc_log 2 n.

(** Erdos Problems #803. *)
(** [trunc_log 2] (mathcomp floor-log2) is the intended logarithm; [logn 2] is
    the 2-adic valuation.  The [1 <= m] guard matches "for every m >= 1": at
    m = 0 the required H would be the empty graph, which cannot satisfy the
    minimum-degree clause ([xe2_min_degree] needs a vertex), making the m = 0
    instance vacuously unsatisfiable and the whole statement false. *)
Definition erdos_803_statement : Prop :=
  exists D C : nat,
    forall m : nat, 1 <= m -> exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n -> #|G| = n -> n * trunc_log 2 n <= x4_edge_count G ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ #|H| = m /\
          (exists d : nat, xe2_min_degree H d /\ Delta H <= D * d) /\
          C * x4_edge_count H >= m * trunc_log 2 m.

(** Erdos Problems #814. *)
Definition erdos_814_statement : Prop :=
  forall k : nat, 2 <= k ->
    exists c d : nat,
      0 < c /\ c < d /\
      forall (n : nat) (G : sgraph),
        k - 1 <= n ->
        #|G| = n ->
        x4_edge_count G =
          (k - 1) * (n - k + 2) + 'C(k - 2, 2) + 1 ->
        exists S : {set G},
          0 < #|S| /\
          d * #|S| <= (d - c) * n /\
          forall v : induced S, k <= #|N(v)|.

(** Erdos Problems #816. *)
Definition erdos_816_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = 2 * n + 1 ->
    x4_edge_count G = n ^ 2 + n + 1 ->
    exists x y : G,
      x != y /\ #|N(x)| = #|N(y)| /\ @xe2_path_length3 G x y.

(** Erdos Problems #915. *)
Definition erdos_915_statement : Prop :=
  forall (n m : nat) (G : sgraph),
    #|G| = 1 + n * (m - 1) ->
    x4_edge_count G = 1 + n * 'C(m, 2) ->
    exists x y : G, exists P : 'I_m -> seq G,
      x != y /\
      (forall i : 'I_m,
        if P i is z :: p then z = x /\ last z p = y /\ path (--) z p else False) /\
      xe2_paths_internally_disjoint x y P /\
      xe2_paths_edge_disjoint P.
