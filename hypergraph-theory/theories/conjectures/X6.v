(** * Hypergraph.conjectures.X6 -- v2 milestone X6, clean hypergraph rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local hypergraph vocabulary *****************************************)

Definition x6_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x6_r_partite_uniform
    (T : finType) (r : nat) (part : T -> 'I_r) (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E ->
    forall j : 'I_r, #|[set v in e | part v == j]| = 1.

Definition x6_matching (T : finType) (M E : {set {set T}}) : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

Definition x6_matching_number (T : finType) (E : {set {set T}}) (nu : nat) : Prop :=
  (exists M : {set {set T}}, x6_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, x6_matching M E -> #|M| <= nu).

Definition x6_no_k_matching (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall M : {set {set T}}, x6_matching M E -> #|M| < k.

Definition x6_extremal_no_k_matching (n r k m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
     [/\ #|T| = n, x6_uniform E r, #|E| = m & x6_no_k_matching E k]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
       [/\ #|T| = n, x6_uniform E r, #|E| = m' & x6_no_k_matching E k]) ->
    m' <= m.

Definition x6_delete_vertices (T : finType) (E : {set {set T}}) (X : {set T})
  : {set {set T}} :=
  [set e in E | [disjoint e & X]].

Definition x6_edges_on (T : finType) (E : {set {set T}}) (S : {set T}) : nat :=
  #|[set e in E | e \subset S]|.

Definition x6_hg_degree (T : finType) (E : {set {set T}}) (v : T) : nat :=
  #|[set e in E | v \in e]|.

Definition x6_proper_coloring
    (T C : finType) (E : {set {set T}}) (col : T -> C) : Prop :=
  forall e : {set T}, e \in E ->
    exists x y : T, [/\ x \in e, y \in e & col x != col y].

Definition x6_chromatic_number (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  (exists col : T -> 'I_k, x6_proper_coloring E col) /\
  forall k' : nat, (exists col : T -> 'I_k', x6_proper_coloring E col) -> k <= k'.

Definition x6_vertex_delete (T : finType) (E : {set {set T}}) (v : T)
  : {set {set T}} :=
  [set e in E | v \notin e].

Definition x6_edge_delete (T : finType) (E : {set {set T}}) (e : {set T})
  : {set {set T}} :=
  E :\ e.

Definition x6_chromatic_edge_critical (T : finType) (E : {set {set T}}) (k : nat)
  : Prop :=
  x6_chromatic_number E k /\
  forall e : {set T}, e \in E -> x6_chromatic_number (x6_edge_delete E e) k.-1.

(** ** X6 statements *******************************************************)

(** Studies slice: Lovasz r-partite hypergraph matching conjecture. *)
Definition lovasz_r_partite_matching_deletion_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    x6_r_partite_uniform part E ->
    x6_matching_number E nu ->
    exists X : {set T}, #|X| = r - 1 /\
      exists nu' : nat,
        x6_matching_number (x6_delete_vertices E X) nu' /\ nu' < nu.

(** arXiv:2505.05339, Conjecture 4.3. *)
Definition r_partite_matching_deletion_tradeoff_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu : nat),
    1 < r ->
    E != set0 ->
    x6_r_partite_uniform part E ->
    x6_matching_number E nu ->
    exists (k : nat) (X : {set T}),
      1 <= k /\ k <= r - 1 /\
      #|X| = k * (r - 1) /\
      exists nu' : nat,
        x6_matching_number (x6_delete_vertices E X) nu' /\ nu' + k <= nu.

(** Erdos Problems #1020. *)
Definition erdos_matching_extremal_formula_statement : Prop :=
  forall n r k m : nat,
    3 <= r -> 1 <= k ->
    r * k - 1 <= n ->
    x6_extremal_no_k_matching n r k m ->
    m = maxn 'C(r * k - 1, r) ('C(n, r) - 'C(n - k + 1, r)).

(** Erdos Problems #794. *)
Definition three_uniform_hypergraph_dense_small_configuration_statement : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    x6_uniform E 3 ->
    #|T| = 3 * n ->
    n ^ 3 + 1 <= #|E| ->
    (exists S : {set T}, #|S| = 4 /\ 3 <= x6_edges_on E S) \/
    (exists S : {set T}, #|S| = 5 /\ 7 <= x6_edges_on E S).

(** Erdos Problems #834. *)
Definition critical_three_uniform_min_degree_seven_statement : Prop :=
  exists (T : finType) (E : {set {set T}}),
    x6_uniform E 3 /\
    x6_chromatic_edge_critical E 3 /\
    (forall v : T, 7 <= x6_hg_degree E v).

(** Erdos Problems #835. *)
Definition subset_kneser_full_palette_statement : Prop :=
  exists k : nat,
    2 < k /\
    exists col : {set 'I_(2 * k)} -> 'I_(k.+1),
      forall A : {set 'I_(2 * k)}, #|A| = k.+1 ->
        forall c : 'I_(k.+1),
          exists B : {set 'I_(2 * k)}, B \subset A /\ #|B| = k /\ col B = c.
