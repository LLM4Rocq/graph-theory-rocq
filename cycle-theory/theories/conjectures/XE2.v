(** * Cycle.conjectures.XE2 -- Erdős solved clean/bounded rows *)

From Cycle.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe2_same_vertex_set (G : sgraph) (c d : seq G) : Prop :=
  [set v : G | v \in c] = [set v : G | v \in d].

Definition xe2_edge_disjoint_cycles
    (G : sgraph) (k : nat) (C : 'I_k -> seq G) : Prop :=
  forall i j : 'I_k, i != j ->
    [disjoint xe1_cycle_edges (C i) & xe1_cycle_edges (C j)].

Definition xe2_cycle_lengths (G : sgraph) (L : seq nat) : Prop :=
  uniq L /\
  forall ell : nat,
    ell \in L <->
    exists c : seq G, xe1_cycle c /\ size c = ell.

Definition xe2_min_degree_at_least (G : sgraph) (k : nat) : Prop :=
  forall v : G, k <= #|N(v)|.

Definition xe2_distinct_cycle_lengths_at_least (G : sgraph) (q : nat) : Prop :=
  exists L : seq nat, xe2_cycle_lengths G L /\ q <= size L.

Definition xe2_arithmetic_progression (P : nat -> Prop) : Prop :=
  exists a d : nat,
    0 < d /\ forall n : nat, P n <-> exists i : nat, n = a + d * i.

Definition xe2_contains_even (P : nat -> Prop) : Prop :=
  exists n : nat, P n /\ ~~ odd n.

Definition xe2_all_cycle_lengths_in (G : sgraph) (P : nat -> Prop) : Prop :=
  exists c : seq G, xe1_cycle c /\ P (size c).

Definition xe2_proper_induced_subgraphs_min_degree_le2 (G : sgraph) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] ->
    exists v : G, v \in S /\ #|N(v) :&: S| <= 2.

(** Erdős Problems #641. *)
Definition erdos_641_statement : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      1 <= k ->
      f k <= χ([set: G]) ->
      exists C : 'I_k -> seq G,
        (forall i : 'I_k, xe1_cycle (C i)) /\
        (forall i j : 'I_k, xe2_same_vertex_set (C i) (C j)) /\
        xe2_edge_disjoint_cycles C.

(** Erdős Problems #71. *)
Definition erdos_71_statement : Prop :=
  forall P : nat -> Prop,
    xe2_arithmetic_progression P ->
    xe2_contains_even P ->
    exists c : nat,
      forall G : sgraph,
        0 < #|G| ->
        average_degree_geq G c 1 ->
        xe2_all_cycle_lengths_in G P.

(** Erdős Problems #752.

    "Minimum degree [k] and girth [> 2s] (no cycle of length [<= 2s]) forces
    [≫ k^s] distinct cycle lengths."  Here [≫] is Vinogradov/Ω: for FIXED [s]
    the number of distinct cycle lengths is [>= c(s) * k^s] for some constant
    [c(s) > 0] and all large enough [k].  Faithful ℕ encoding:

    - The hidden constant [c = 1 / C] sits on the RHS as a DIVISOR, i.e. the
      bound is [k ^ s <= C * #(distinct lengths)].  The multiplicative reading
      [#lengths >= C * k^s] would force [c >= 1] and is provably FALSE: the
      complete graph ['K_(k+1)] has only [k-1 < k = k^1] distinct cycle lengths
      (refuting [s = 1], any [k >= 2], any [C >= 1]), and a near-Moore graph of
      min degree [k] and girth [> 2s] has only [~ (k-1)^s < k^s] vertices, hence
      [< k^s] cycle lengths.
    - [C] and the min-degree threshold [k0] are chosen PER [s]: Ω is asymptotic
      in [k] for fixed [s], and no single [C] works for all [s] since [c(s)] may
      tend to 0.  [k0] excludes the low-degree pathologies (a min-degree-1 tree
      or a single long high-girth cycle has too few cycle lengths).
    - [0 < #|G|] rules out the vacuous empty graph ['K_0], which satisfies
      [xe2_min_degree_at_least] and [girth_geq] vacuously yet has no cycle. *)
Definition erdos_752_statement : Prop :=
  forall s : nat, 1 <= s ->
    exists C k0 : nat,
      0 < C /\
      forall (k : nat) (G : sgraph),
        0 < #|G| ->
        k0 <= k ->
        xe2_min_degree_at_least G k ->
        girth_geq G (2 * s).+1 ->
        exists L : seq nat, xe2_cycle_lengths G L /\ k ^ s <= C * size L.

(** Erdős Problems #815. *)
Definition erdos_815_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        #|xe1_edge_set G| = 2 * n - 2 ->
        xe2_proper_induced_subgraphs_min_degree_le2 G ->
        exists c : seq G, xe1_cycle c /\ size c = k.

