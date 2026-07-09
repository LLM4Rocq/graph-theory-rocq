(** * Extremal.conjectures.XE1 -- Erdos open clean/bounded rows *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition xe1_has_independent_set (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, xe1_stable_set S /\ #|S| = k.

Definition xe1_no_isolated_vertices (G : sgraph) : Prop :=
  forall v : G, 0 < #|N(v)|.

Definition xe1_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma xe1_complement_sym (G : sgraph) : symmetric (@xe1_complement_rel G).
Proof. by move=> x y; rewrite /xe1_complement_rel eq_sym sgP. Qed.

Lemma xe1_complement_irrefl (G : sgraph) : irreflexive (@xe1_complement_rel G).
Proof. by move=> x; rewrite /xe1_complement_rel eqxx. Qed.

Definition xe1_complement_graph (G : sgraph) : sgraph :=
  SGraph (@xe1_complement_sym G) (@xe1_complement_irrefl G).

Definition xe1_graph_ramsey (H K : sgraph) (R : nat) : Prop :=
  forall G : sgraph, #|G| = R ->
    xe1_subgraph_of H G \/ xe1_subgraph_of K (xe1_complement_graph G).

Definition xe1_graph_ramsey_number (H K : sgraph) (R : nat) : Prop :=
  xe1_graph_ramsey H K R /\
  forall R' : nat, xe1_graph_ramsey H K R' -> R <= R'.

Definition xe1_diagonal_ramsey_number (H : sgraph) (R : nat) : Prop :=
  xe1_graph_ramsey_number H H R.

Definition xe1_size_ramsey (H K : sgraph) (m : nat) : Prop :=
  exists G : sgraph,
    x4_edge_count G = m /\
    forall col : rel G, symmetric col ->
      (exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y /\ col (f x) (f y)) \/
      (exists f : K -> G, injective f /\ forall x y : K, x -- y -> f x -- f y /\ ~~ col (f x) (f y)).

Definition xe1_size_ramsey_number (H K : sgraph) (m : nat) : Prop :=
  xe1_size_ramsey H K m /\
  forall m' : nat, xe1_size_ramsey H K m' -> m <= m'.

Definition xe1_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma xe1_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@xe1_delete_edges_rel G F).
Proof. by move=> x y; rewrite /xe1_delete_edges_rel sgP setUC. Qed.

Lemma xe1_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@xe1_delete_edges_rel G F).
Proof. by move=> x; rewrite /xe1_delete_edges_rel sg_irrefl. Qed.

Definition xe1_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@xe1_delete_edges_sym G F) (@xe1_delete_edges_irrefl G F).

Fixpoint xe1_hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (xe1_hypercube d')
  end.

Definition xe1_tree (T : sgraph) : Prop :=
  is_forest [set: T] /\ connected [set: T].

Definition xe1_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition xe1_every_k_set_sparse (G : sgraph) (k : nat) : Prop :=
  forall S : {set G}, #|S| = k -> x4_edge_count (induced S) <= 2 * k - 3.

Definition xe1_diameter_at_most (G : sgraph) (r : nat) : Prop :=
  forall x y : G, y \in ball r x.

Definition xe1_triangle_free_diameter_completion_edges
    (G : sgraph) (r h : nat) : Prop :=
  exists F : {set {set G}},
    #|F| = h /\
    F \subset [set e : {set G} | #|e| == 2] /\
    triangle_free (@xe1_delete_edges G set0) /\
    xe1_diameter_at_most (@xe1_delete_edges G set0) r.

Definition xe1_c4_forcing_min_degree (n f : nat) : Prop :=
  (forall G : sgraph, #|G| = n -> xe1_min_degree_at_least G f -> xe1_subgraph_of (cycle_graph 4) G) /\
  forall f' : nat,
    (forall G : sgraph, #|G| = n -> xe1_min_degree_at_least G f' -> xe1_subgraph_of (cycle_graph 4) G) ->
    f <= f'.

Definition xe1_sqrt_floor (n s : nat) : Prop :=
  s ^ 2 <= n /\ forall t : nat, t ^ 2 <= n -> t <= s.

Definition xe1_complete_plus_vertex (H : sgraph) (n t : nat) : Prop :=
  exists x : H, exists K : {set H},
    x \notin K /\
    K :|: [set x] = [set: H] /\
    #|K| = n /\
    clique K /\
    #|N(x) :&: K| = t /\
    forall y z : H, y -- z ->
      (y \in K /\ z \in K) \/
      (y = x /\ z \in K /\ z \in N(x)) \/
      (z = x /\ y \in K /\ y \in N(x)).

Definition xe1_h5_graph (G : sgraph) : Prop :=
  exists c : seq G, exists e1 e2 : {set G},
    #|G| = 5 /\
    (forall v : G, v \in c) /\
    ucycle (--) c /\
    size c = 5 /\
    #|e1| = 2 /\ #|e2| = 2 /\
    e1 \in x4_edge_set G /\
    e2 \in x4_edge_set G /\
    [disjoint e1 & e2] /\
    e1 \subset [set v : G | v \in c] /\
    e2 \subset [set v : G | v \in c] /\
    (forall x y : G, [set x; y] = e1 -> ~~ x4_consecutive_in_cycle c x y) /\
    (forall x y : G, [set x; y] = e2 -> ~~ x4_consecutive_in_cycle c x y) /\
    (forall x y : G, x -- y ->
      x4_consecutive_in_cycle c x y \/ [set x; y] = e1 \/ [set x; y] = e2).

Definition xe1_sqrt_ceil (n s : nat) : Prop :=
  n <= s ^ 2 /\ forall t : nat, n <= t ^ 2 -> s <= t.

Definition xe1_colour_k_free_on
    (N k r : nat) (col : {set 'I_N} -> 'I_r)
    (colour : 'I_r) (S : {set 'I_N}) : Prop :=
  forall K : {set 'I_N}, K \subset S -> #|K| = k ->
    exists e : {set 'I_N}, e \subset K /\ #|e| = 2 /\ col e != colour.

Definition xe1_multicolour_missing_clique_ramsey
    (n k r R : nat) : Prop :=
  forall col : {set 'I_R} -> 'I_r,
    exists S : {set 'I_R}, exists colour : 'I_r,
      #|S| = n /\ @xe1_colour_k_free_on R k r col colour S.

Definition xe1_multicolour_missing_clique_ramsey_number
    (n k r R : nat) : Prop :=
  xe1_multicolour_missing_clique_ramsey n k r R /\
  forall R' : nat, xe1_multicolour_missing_clique_ramsey n k r R' -> R <= R'.

Definition xe1_complete_multipartite_with_sizes
    (G : sgraph) (k : nat) (sizes : 'I_k -> nat) : Prop :=
  exists P : 'I_k -> {set G},
    (forall i : 'I_k, #|P i| = sizes i) /\
    (forall i j : 'I_k, i != j -> [disjoint P i & P j]) /\
    (forall v : G, exists i : 'I_k, v \in P i) /\
    forall x y : G,
      x -- y =
        [exists i : 'I_k,
          [exists j : 'I_k,
            (i != j) && (x \in P i) && (y \in P j)]].

Definition xe1_two_smallest_part_sizes
    (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat) : Prop :=
  exists i j : 'I_k,
    i != j /\
    sizes i = m1 /\
    sizes j = m2 /\
    forall h : 'I_k, m1 <= sizes h /\ (h != i -> m2 <= sizes h).

Definition xe1_monochromatic_copy_in_complete
    (k : nat) (H : sgraph) (R : nat)
    (col : {set 'I_R} -> 'I_k) : Prop :=
  exists colour : 'I_k, exists f : H -> 'I_R,
    injective f /\
    forall x y : H, x -- y -> col [set f x; f y] = colour.

Definition xe1_multicolour_graph_ramsey (k : nat) (H : sgraph) (R : nat) : Prop :=
  forall col : {set 'I_R} -> 'I_k,
    @xe1_monochromatic_copy_in_complete k H R col.

Definition xe1_multicolour_graph_ramsey_number
    (k : nat) (H : sgraph) (R : nat) : Prop :=
  xe1_multicolour_graph_ramsey k H R /\
  forall R' : nat, xe1_multicolour_graph_ramsey k H R' -> R <= R'.

Definition xe1_positive_sequence (s : seq nat) : Prop :=
  forall x : nat, x \in s -> 0 < x.

Definition xe1_nonincreasing_sequence (s : seq nat) : Prop :=
  forall i j : nat, i < j -> j < size s -> nth 0 s j <= nth 0 s i.

Definition xe1_star_on_set (G : sgraph) (S : {set G}) (leaves : nat) : Prop :=
  exists c : G,
    c \in S /\
    #|S| = leaves.+1 /\
    forall x y : G,
      x \in S -> y \in S ->
      x -- y =
        (((x == c) && (y \in S) && (y != c)) ||
         ((y == c) && (x \in S) && (x != c))).

Definition xe1_star_forest_with_leaves (G : sgraph) (leaves : seq nat) : Prop :=
  exists C : 'I_(size leaves) -> {set G},
    (forall i : 'I_(size leaves), xe1_star_on_set (C i) (nth 0 leaves i)) /\
    (forall i j : 'I_(size leaves), i != j -> [disjoint C i & C j]) /\
    (forall v : G, exists i : 'I_(size leaves), v \in C i) /\
    forall x y : G, x -- y ->
      exists i : 'I_(size leaves), x \in C i /\ y \in C i.

Definition xe1_star_formula_term
    (ns ms : seq nat) (q l : nat) : Prop :=
  (exists i j : nat,
      i < size ns /\ j < size ms /\ i.+1 + j.+1 = q /\
      l = nth 0 ns i + nth 0 ms j - 1) /\
  forall i j : nat, i < size ns -> j < size ms -> i.+1 + j.+1 = q ->
    nth 0 ns i + nth 0 ms j - 1 <= l.

Definition xe1_star_forest_formula (ns ms : seq nat) (value : nat) : Prop :=
  exists l : nat -> nat,
    (forall q : nat, 2 <= q -> q <= size ns + size ms ->
      xe1_star_formula_term ns ms q (l q)) /\
    value = \sum_(q <- iota 2 ((size ns + size ms).-1)) l q.

Definition xe1_add_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x != y) && ((x -- y) || ([set x; y] \in F)).

Lemma xe1_add_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@xe1_add_edges_rel G F).
Proof. by move=> x y; rewrite /xe1_add_edges_rel eq_sym sgP setUC. Qed.

Lemma xe1_add_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@xe1_add_edges_rel G F).
Proof. by move=> x; rewrite /xe1_add_edges_rel eqxx. Qed.

Definition xe1_add_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@xe1_add_edges_sym G F) (@xe1_add_edges_irrefl G F).

Definition xe1_triangle_free_diameter_completion_number
    (G : sgraph) (r h : nat) : Prop :=
  (exists F : {set {set G}},
      #|F| = h /\
      F \subset [set e : {set G} | #|e| == 2] /\
      [disjoint F & x4_edge_set G] /\
      triangle_free (@xe1_add_edges G F) /\
      xe1_diameter_at_most (@xe1_add_edges G F) r) /\
  forall h' : nat,
    (exists F : {set {set G}},
      #|F| = h' /\
      F \subset [set e : {set G} | #|e| == 2] /\
      [disjoint F & x4_edge_set G] /\
      triangle_free (@xe1_add_edges G F) /\
      xe1_diameter_at_most (@xe1_add_edges G F) r) ->
    h <= h'.

Definition xe1_turan_number_for_graph (F : sgraph) (n m : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ x4_edge_count G = m /\ ~ xe1_subgraph_of F G) /\
  forall m' : nat,
    (exists G : sgraph, #|G| = n /\ x4_edge_count G = m' /\ ~ xe1_subgraph_of F G) ->
    m' <= m.

Definition xe1_min_turan_over_size_edges (k l n a : nat) : Prop :=
  (exists F : sgraph,
      #|F| = k /\ x4_edge_count F = l /\ xe1_turan_number_for_graph F n a) /\
  forall b : nat,
    (exists F : sgraph,
      #|F| = k /\ x4_edge_count F = l /\ xe1_turan_number_for_graph F n b) ->
    a <= b.

Definition xe1_every_7_set_has_triangle (G : sgraph) : Prop :=
  forall S : {set G}, #|S| = 7 ->
    exists T : {set G}, T \subset S /\ x4_triangle_set T.

Definition xe1_seven_triangle_clique_property (n h : nat) : Prop :=
  forall G : sgraph,
    #|G| = n ->
    xe1_every_7_set_has_triangle G ->
    exists K : {set G}, clique K /\ h <= #|K|.

Definition xe1_seven_triangle_clique_guarantee (n h : nat) : Prop :=
  xe1_seven_triangle_clique_property n h /\
  forall h' : nat, xe1_seven_triangle_clique_property n h' -> h' <= h.

Definition xe1_between_rational_power_bounds
    (n h a1 b1 a2 b2 C1 C2 : nat) : Prop :=
  n ^ (b1 + 3 * a1) <= C1 * h ^ (3 * b1) /\
  h ^ (2 * b2) <= C2 * n ^ (b2 - 2 * a2).

(** Erdos Problems #1035. *)
Definition erdos_1035_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall n : nat, forall G : sgraph,
      #|G| = 2 ^ n ->
      (forall v : G, d * #|N(v)| > (d - c) * 2 ^ n) ->
      xe1_subgraph_of (xe1_hypercube n) G.

(** Erdos Problems #128. *)
Definition erdos_128_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    (forall S : {set G}, n %/ 2 <= #|S| -> n ^ 2 < 50 * x4_edge_count (induced S)) ->
    exists T : {set G}, x4_triangle_set T.

(** Erdos Problems #129. *)
Definition erdos_129_statement : Prop :=
  forall r : nat, 1 <= r -> exists C : nat,
    1 < C /\
    forall n R : nat,
      xe1_multicolour_missing_clique_ramsey_number n 3 r R ->
      exists s : nat, xe1_sqrt_ceil n s /\ R < C ^ s.

(** Erdos Problems #23. *)
Definition erdos_23_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = 5 * n ->
    triangle_free G ->
    exists F : {set {set G}},
      F \subset x4_edge_set G /\
      #|F| <= n ^ 2 /\
      bipartite (@xe1_delete_edges G F).

(** Erdos Problems #545. *)
Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    xe1_graph_ramsey_number G G RG ->
    xe1_graph_ramsey_number H H RH ->
    RG <= RH.

(** Erdos Problems #548. *)
Definition erdos_548_statement : Prop :=
  forall (n k : nat) (G T : sgraph),
    k.+1 <= n ->
    #|G| = n -> #|T| = k.+1 -> xe1_tree T ->
    2 * x4_edge_count G >= (k - 1) * n + 2 ->
    xe1_subgraph_of T G.

(** Erdos Problems #550. *)
Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      xe1_graph_ramsey_number T (KB m1 m2) RTB ->
      xe1_graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

(** Erdos Problems #552. *)
Definition erdos_552_statement : Prop :=
  forall c M : nat, exists n R s : nat,
    M <= n /\
    xe1_sqrt_floor n s /\
    xe1_graph_ramsey_number (cycle_graph 4) (KB 1 n) R /\
    R + c <= n + s.

(** Erdos Problems #557. *)
Definition erdos_557_statement : Prop :=
  forall k : nat, 1 <= k -> exists C : nat,
    forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n ->
      xe1_multicolour_graph_ramsey_number k T R ->
      R <= k * n + C.

(** Erdos Problems #561. *)
Definition erdos_561_statement : Prop :=
  forall (ns ms : seq nat) (F1 F2 : sgraph) (m formula : nat),
    0 < size ns -> 0 < size ms ->
    xe1_positive_sequence ns -> xe1_positive_sequence ms ->
    xe1_nonincreasing_sequence ns -> xe1_nonincreasing_sequence ms ->
    xe1_star_forest_with_leaves F1 ns ->
    xe1_star_forest_with_leaves F2 ms ->
    xe1_star_forest_formula ns ms formula ->
    xe1_size_ramsey_number F1 F2 m ->
    m = formula.

(** Erdos Problems #566. *)
Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, xe1_every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

(** Erdos Problems #567. *)
Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

(** Erdos Problems #568. *)
Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> xe1_graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      xe1_graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      xe1_graph_ramsey_number G H R ->
      R <= C * m.

(** Erdos Problems #619. *)
Definition erdos_619_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall (G : sgraph) (n h : nat),
      connected [set: G] -> #|G| = n -> triangle_free G ->
      xe1_triangle_free_diameter_completion_number G 4 h ->
      d * h < (d - c) * n.

(** Erdos Problems #766. *)
Definition erdos_766_statement : Prop :=
  forall k l : nat, k < l -> 4 * l.+1 <= k ^ 2 ->
    exists N : nat,
      forall n a b : nat,
        N <= n ->
        xe1_min_turan_over_size_edges k l n a ->
        xe1_min_turan_over_size_edges k l.+1 n b ->
        a < b.

(** Erdos Problems #802. *)
(** The hypothesis is average degree (at most) t: [\sum_v #|N(v)| = 2|E| <= t*n],
    i.e. average degree <= t.  Encoding it as [average_degree_geq G t 1] (a LOWER
    bound) is wrong: since log t / t is decreasing, a graph of much larger degree
    would make the target unattainable.  The logarithm is [trunc_log 2] (mathcomp
    floor-log2, as in D2pr.v); [logn 2] is the 2-adic valuation, a different
    object that vanishes on odd t. *)
Definition erdos_802_statement : Prop :=
  forall r : nat, exists C : nat,
    0 < C /\
    forall (G : sgraph) (n t : nat),
      ~ xe1_subgraph_of 'K_r G ->
      #|G| = n ->
      \sum_(v in G) #|N(v)| <= t * #|G| ->
      exists A : {set G},
        xe1_stable_set A /\ C * t * #|A| >= n * trunc_log 2 t.

(** Erdos Problems #812. *)
Definition erdos_812_statement : Prop :=
  (exists cnum cden N : nat, 0 < cnum /\ 0 < cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      xe1_graph_ramsey_number 'K_n 'K_n Rn ->
      xe1_graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      cden * Rn1 >= (cden + cnum) * Rn) /\
  (exists Cnum Cden N : nat, 0 < Cnum /\ 0 < Cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      xe1_graph_ramsey_number 'K_n 'K_n Rn ->
      xe1_graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      Cden * Rn + Cnum * n ^ 2 <= Cden * Rn1).

(** Erdos Problems #813. *)
Definition erdos_813_statement : Prop :=
  exists a1 b1 a2 b2 C1 C2 N : nat,
    0 < a1 /\ 0 < b1 /\ 0 < a2 /\ 0 < b2 /\
    0 < C1 /\ 0 < C2 /\ 2 * a2 < b2 /\
    forall (n h : nat),
      N <= n ->
      xe1_seven_triangle_clique_guarantee n h ->
      xe1_between_rational_power_bounds n h a1 b1 a2 b2 C1 C2.

(** Erdos Problems #85. *)
Definition erdos_85_statement : Prop :=
  exists N : nat,
    forall n fn fn1 : nat,
      N <= n -> 4 <= n ->
      xe1_c4_forcing_min_degree n fn ->
      xe1_c4_forcing_min_degree n.+1 fn1 ->
      fn <= fn1.

(** Erdos Problems #87. *)
Definition erdos_87_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall (k RG RK : nat) (G : sgraph),
      N <= k ->
      χ([set: G]) = k ->
      xe1_diagonal_ramsey_number G RG ->
      xe1_graph_ramsey_number 'K_k 'K_k RK ->
      cden * RG >= cnum * RK.
