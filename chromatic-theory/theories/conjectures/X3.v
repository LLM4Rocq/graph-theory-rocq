(** * Chromatic.conjectures.X3 -- v2 milestone X3, clean chi-boundedness wave

    This file states the first clean X3 sub-batch: undirected chi-boundedness /
    Gyarfas-Sumner rows whose source statements use standard finite graph
    vocabulary or definitions already recovered in the manifest context.  B3
    paper-local terms and the tournament out-neighbourhood followup are
    intentionally deferred. *)

From Chromatic.conjectures Require Import U8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local finite-graph vocabulary ****************************************)

(** Consecutive vertices on a listed cycle/path, stated without [nth] defaults
    so the definitions also behave over empty carriers. *)
Definition x3_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : Prop :=
  ((u, v) \in zip c (rot 1 c)) \/ ((v, u) \in zip c (rot 1 c)).

Definition x3_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  ((u, v) \in zip p (behead p)) \/ ((v, u) \in zip p (behead p)).

(** A hole is an induced cycle of length at least four.  [ucycle] supplies the
    closed walk and vertex uniqueness; the final clause rules out chords. *)
Definition x3_hole (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 3 < size c &
      forall u v : G,
        u \in c -> v \in c -> u != v -> u -- v ->
        x3_consecutive_in_cycle c u v].

Definition x3_has_hole_length (G : sgraph) (L : nat) : Prop :=
  exists c : seq G, x3_hole c /\ size c = L.

Definition x3_holes_of_consecutive_lengths (G : sgraph) (ell : nat) : Prop :=
  exists t : nat,
    forall i : nat, 1 <= i -> i <= ell -> x3_has_hole_length G (t + i).

Definition x3_proper_colouring (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall u v : G, u -- v -> col u != col v.

Definition x3_rainbow_hole_run
    (G : sgraph) (C : finType) (col : G -> C) (s : nat) : Prop :=
  exists (c : seq G) (r : nat),
    x3_hole c /\ s <= size c /\ uniq (map col (take s (rot r c))).

Definition x3_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall u v : G, u \in S -> v \in S -> u -- v -> False.

Definition x3_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x3_induced_path (G : sgraph) (p : seq G) : Prop :=
  [/\ uniq p,
      (if p is u :: q then path (--) u q else true)
    & forall u v : G,
        u \in p -> v \in p -> u != v -> u -- v ->
        x3_consecutive_in_path p u v].

Definition x3_family_covers_vertices
    (G : sgraph) (I : finType) (A : I -> {set G}) : Prop :=
  forall v : G, exists i : I, v \in A i.

Definition x3_uniquely_covers_path_vertex
    (G : sgraph) (I : finType) (A : I -> {set G}) (p : seq G) (v : G) : Prop :=
  exists i : I, A i :&: x3_path_vertices p = [set v].

Definition x3_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x3_bounded_chromatic (F : sgraph -> Prop) : Prop :=
  exists c : nat, forall G : sgraph, F G -> χ([set: G]) <= c.

Definition x3_complete_graph (G : sgraph) : Prop := clique [set: G].

Definition x3_two_forbidden_class (F1 F2 G : sgraph) : Prop :=
  ~ has_induced F1 G /\ ~ has_induced F2 G.

Definition x3_iso (G H : sgraph) : Prop := inhabited (G ≃ H).

Definition x3_iso_closed (F : sgraph -> Prop) : Prop :=
  forall G H : sgraph, x3_iso G H -> F G -> F H.

Definition x3_hereditary_class (F : sgraph -> Prop) : Prop :=
  x3_iso_closed F /\ forall (G : sgraph) (S : {set G}), F G -> F (induced S).

Fixpoint x3_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x3_poly_eval q x else 0.

Definition x3_polynomially_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, F G -> χ([set: G]) <= x3_poly_eval p (ω([set: G])).

Definition x3_positive_integer_set (F : nat -> Prop) : Prop :=
  forall n : nat, F n -> 0 < n.

Definition x3_infinite_integer_set (F : nat -> Prop) : Prop :=
  forall n : nat, exists m : nat, n <= m /\ F m.

Definition x3_bounded_gaps (F : nat -> Prop) : Prop :=
  exists b : nat,
    0 < b /\ forall n : nat, exists m : nat, n <= m /\ m < n + b /\ F m.

Definition x3_k_constricting (F : nat -> Prop) (k : nat) : Prop :=
  exists n : nat,
    forall G : sgraph,
      n <= χ([set: G]) ->
      k <= ω([set: G]) \/ exists L : nat, F L /\ x3_has_hole_length G L.

Definition x3_constricting (F : nat -> Prop) : Prop :=
  forall k : nat, x3_k_constricting F k.

Definition x3_complement_rel (G : sgraph) : rel G :=
  fun u v => (u != v) && ~~ (u -- v).

Lemma x3_complement_sym (G : sgraph) : symmetric (@x3_complement_rel G).
Proof. by move=> u v; rewrite /x3_complement_rel eq_sym sgP. Qed.

Lemma x3_complement_irrefl (G : sgraph) : irreflexive (@x3_complement_rel G).
Proof. by move=> u; rewrite /x3_complement_rel eqxx. Qed.

Definition x3_complement_graph (G : sgraph) : sgraph :=
  SGraph (@x3_complement_sym G) (@x3_complement_irrefl G).

Definition x3_complement_image (C : sgraph -> Prop) (G : sgraph) : Prop :=
  exists H : sgraph, C H /\ x3_iso G (x3_complement_graph H).

Definition x3_chi_omega_plus_bound (C : sgraph -> Prop) (c : nat) : Prop :=
  forall G : sgraph, C G ->
    forall S : {set G}, χ([set: induced S]) <= ω([set: induced S]) + c.

Definition x3_alpha_omega_large_class (G : sgraph) : Prop :=
  forall S : {set G},
    #|S| <= α([set: induced S]) * ω([set: induced S]) + 1.

Definition x3_triangle_free_induced_subgraphs_chi_le3 (G : sgraph) : Prop :=
  forall S : {set G}, triangle_free (induced S) -> χ([set: induced S]) <= 3.

(** ** X3 statements *******************************************************)

(** arXiv:1509.06563, informal conjecture generalising Theorem 1.3. *)
Definition bounded_clique_consecutive_hole_lengths_statement : Prop :=
  forall nu k : nat, 0 < nu -> 3 <= k ->
    exists n : nat,
      forall G : sgraph,
        ω([set: G]) < k -> n <= χ([set: G]) ->
        x3_holes_of_consecutive_lengths G nu.

(** arXiv:1509.06563, Conjecture 1.5. *)
Definition bounded_gaps_sets_are_constricting_statement : Prop :=
  forall F : nat -> Prop,
    x3_positive_integer_set F ->
    x3_infinite_integer_set F ->
    x3_bounded_gaps F ->
    x3_constricting F.

(** arXiv:1702.01094, rainbow-hole question. *)
Definition rainbow_consecutive_vertices_in_hole_statement : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      x3_proper_colouring col ->
      x3_rainbow_hole_run col s.

(** arXiv:1702.01094, stable-cover induced-path question. *)
Definition stable_cover_unique_induced_path_statement : Prop :=
  forall s : nat, exists n : nat,
    forall (G : sgraph) (I : finType) (A : I -> {set G}),
      triangle_free G ->
      n <= χ([set: G]) ->
      (forall i : I, x3_stable_set (A i)) ->
      x3_family_covers_vertices A ->
      exists p : seq G,
        size p = s /\
        x3_induced_path p /\
        forall v : G, v \in p -> x3_uniquely_covers_path_vertex A p v.

(** arXiv:1705.04609, Conjecture 1.8. *)
Definition clique_or_consecutive_holes_statement : Prop :=
  forall kappa ell : nat, exists c : nat,
    forall G : sgraph,
      c < χ([set: G]) ->
      kappa <= ω([set: G]) \/ x3_holes_of_consecutive_lengths G ell.

(** arXiv:1910.00697, open problem on chi-bounded but not polynomially
    chi-bounded hereditary classes. *)
Definition hereditary_chi_bounded_not_polynomial_statement : Prop :=
  exists F : sgraph -> Prop,
    x3_hereditary_class F /\
    chi_bounded F /\
    ~ x3_polynomially_chi_bounded F.

(** arXiv:2110.00278, Conjecture 1.3. *)
Definition polynomial_gyarfas_sumner_statement : Prop :=
  forall H : sgraph, is_forest [set: H] ->
    exists c : nat,
      0 < c /\
      forall G : sgraph,
        ~ has_induced H G ->
        χ([set: G]) <= (ω([set: G])) ^ c.

(** arXiv:2201.08204, Question 3.1. *)
Definition omega3_large_chi_triangle_free_induced_subgraphs_statement : Prop :=
  forall n : nat, exists G : sgraph,
    n <= χ([set: G]) /\
    ω([set: G]) = 3 /\
    x3_triangle_free_induced_subgraphs_chi_le3 G.

(** Erdos Problems #1111. *)
Definition erdos_anticomplete_pairs_statement : Prop :=
  forall t c : nat, 1 <= t -> 1 <= c ->
    exists d : nat,
      1 <= d /\
      forall G : sgraph,
        d <= χ([set: G]) -> ω([set: G]) < t ->
        exists A B : {set G},
          x3_anticomplete A B /\
          c <= χ(B) /\ χ(B) <= χ(A).

(** Studies slice: Galvin-Rodl conjecture. *)
Definition galvin_rodl_induced_omega2_subgraph_statement : Prop :=
  forall k r : nat, exists n : nat,
    forall G : sgraph,
      n <= χ([set: G]) -> ω([set: G]) <= k ->
      exists S : {set G},
        r <= χ([set: induced S]) /\ ω([set: induced S]) = 2.

(** Studies slice: Gyarfas complementation conjecture. *)
Definition gyarfas_complementation_chi_bounded_statement : Prop :=
  forall (c : nat) (C : sgraph -> Prop),
    x3_chi_omega_plus_bound C c ->
    chi_bounded (x3_complement_image C).

(** Studies slice: Gyarfas Conjecture 6.8. *)
Definition gyarfas_alpha_omega_chi_bounded_statement : Prop :=
  chi_bounded x3_alpha_omega_large_class.

(** Studies slice: base Gyarfas-Sumner two-forbidden-graphs conjecture. *)
Definition gyarfas_sumner_two_forbidden_statement : Prop :=
  forall F1 F2 : sgraph,
    x3_bounded_chromatic (x3_two_forbidden_class F1 F2) <->
    ((x3_complete_graph F1 /\ is_forest [set: F2]) \/
     (x3_complete_graph F2 /\ is_forest [set: F1])).
