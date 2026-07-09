(** * Chromatic.conjectures.XE2 -- Erdős solved clean/bounded rows *)

From Chromatic.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local XE2 vocabulary ************************************************)

Definition xe2_odd_cycle_lengths_bounded (G : sgraph) (k : nat) : Prop :=
  exists L : seq nat,
    uniq L /\ size L <= k /\
    forall c : seq G, xe1_cycle c -> odd (size c) -> size c \in L.

Definition xe2_ab_choosable (G : sgraph) (a b : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, #|L v| = a) ->
    exists S : G -> {set C},
      (forall v : G, S v \subset L v /\ #|S v| = b) /\
      forall x y : G, x -- y -> [disjoint S x & S y].

Definition xe2_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma xe2_complement_sym (G : sgraph) : symmetric (@xe2_complement_rel G).
Proof. by move=> x y; rewrite /xe2_complement_rel eq_sym sgP. Qed.

Lemma xe2_complement_irrefl (G : sgraph) : irreflexive (@xe2_complement_rel G).
Proof. by move=> x; rewrite /xe2_complement_rel eqxx. Qed.

Definition xe2_complement_graph (G : sgraph) : sgraph :=
  SGraph (@xe2_complement_sym G) (@xe2_complement_irrefl G).

Definition xe2_sqrt_lower (n s : nat) : Prop :=
  s ^ 2 <= n /\ forall t : nat, t ^ 2 <= n -> t <= s.

Definition xe2_above_half_plus_rational_power
    (n cnum cden b : nat) : Prop :=
  n ^ (cden + 2 * cnum) < b ^ (2 * cden).

Definition xe2_cochromatic_colouring (G : sgraph) (k : nat) : Prop :=
  exists col : G -> 'I_k,
    forall i : 'I_k,
      let S := [set v : G | col v == i] in
      clique S \/ xe1_stable_set S.

Definition xe2_cochromatic_number (G : sgraph) (k : nat) : Prop :=
  xe2_cochromatic_colouring G k /\
  forall j : nat, xe2_cochromatic_colouring G j -> k <= j.

Definition xe2_max_cochromatic_on_n (n z : nat) : Prop :=
  (exists G : sgraph, #|G| = n /\ xe2_cochromatic_number G z) /\
  forall z' : nat,
    (exists G : sgraph, #|G| = n /\ xe2_cochromatic_number G z') -> z' <= z.

Definition xe2_cycle_lengths_separated (G : sgraph) (gap : nat) : Prop :=
  forall c d : seq G,
    xe1_cycle c -> xe1_cycle d -> size c != size d ->
    gap <= (size c - size d) + (size d - size c).

Definition xe2_triangles_plus_hamilton_cycle (G : sgraph) (n : nat) : Prop :=
  exists (T : 'I_n -> {set G}) (c : seq G),
    #|G| = 3 * n /\
    (forall i : 'I_n, clique (T i) /\ #|T i| = 3) /\
    (forall i j : 'I_n, i != j -> [disjoint T i & T j]) /\
    ucycle (--) c /\
    size c = 3 * n /\
    (forall v : G, v \in c) /\
    (forall (i : 'I_n) (x y : G),
        x \in T i -> y \in T i -> x != y ->
        ~~ xe1_consecutive_in_cycle c x y) /\
    forall x y : G, x -- y ->
      (exists i : 'I_n, x \in T i /\ y \in T i) \/
      xe1_consecutive_in_cycle c x y.

(** ** XE2 statements ******************************************************)

(** Erdős Problems #1091. *)
Definition erdos_1091_statement : Prop :=
  (forall G : sgraph,
    ~ xe1_subgraph_of 'K_4 G ->
    χ([set: G]) = 4 ->
    xe1_odd_cycle_with_diagonals G 2) /\
  exists f : nat -> nat,
    xe1_unbounded f /\
    forall (r : nat) (G : sgraph),
      ~ xe1_subgraph_of 'K_4 G ->
      χ([set: G]) = 4 ->
      xe1_induced_subgraph_chi_le G r 3 ->
      xe1_odd_cycle_with_diagonals G (f r).

(** Erdős Problems #58. *)
Definition erdos_58_statement : Prop :=
  forall (G : sgraph) (k : nat),
    xe2_odd_cycle_lengths_bounded G k ->
    χ([set: G]) <= 2 * k + 2 /\
    (χ([set: G]) = 2 * k + 2 <-> xe1_subgraph_of 'K_(2 * k + 2) G).

(** Erdős Problems #630. *)
Definition erdos_630_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> bipartite G -> choosable G 3.

(** Erdős Problems #632. *)
Definition erdos_632_statement : Prop :=
  forall (G : sgraph) (a b m : nat),
    1 <= m ->
    xe2_ab_choosable G a b ->
    xe2_ab_choosable G (a * m) (b * m).

(** Erdős Problems #751. *)
Definition erdos_751_statement : Prop :=
  forall gap g : nat,
    exists G : sgraph,
      χ([set: G]) = 4 /\
      girth_geq G g /\
      xe2_cycle_lengths_separated G gap.

(** Erdős Problems #753. *)
Definition erdos_753_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (G : sgraph) (n chG chGc : nat),
      #|G| = n ->
      0 < n ->
      is_choice_number G chG ->
      is_choice_number (xe2_complement_graph G) chGc ->
      xe2_above_half_plus_rational_power n cnum cden (chG + chGc).

(** Erdős Problems #758. *)
Definition erdos_758_statement : Prop :=
  xe2_max_cochromatic_on_n 12 4.

(** Erdős Problems #762. *)
Definition erdos_762_statement : Prop :=
  forall (G : sgraph) (z : nat),
    ~ xe1_subgraph_of 'K_5 G ->
    xe2_cochromatic_number G z ->
    4 <= z ->
    χ([set: G]) <= z + 2.

(** Erdős Problems #842. *)
Definition erdos_842_statement : Prop :=
  forall (n : nat) (G : sgraph),
    xe2_triangles_plus_hamilton_cycle G n ->
    χ([set: G]) <= 3.

(** Erdős Problems #922. *)
Definition erdos_922_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (forall S : {set G}, exists A : {set G},
        A \subset S /\ xe1_stable_set A /\
        2 * #|A| + k >= #|S|) ->
    χ([set: G]) <= k + 2.

(** Erdős Problems #923. *)
Definition erdos_923_statement : Prop :=
  forall k : nat, exists f : nat,
    forall G : sgraph,
      f <= χ([set: G]) ->
      exists H : sgraph,
        xe1_subgraph_of H G /\ triangle_free H /\ k <= χ([set: H]).
