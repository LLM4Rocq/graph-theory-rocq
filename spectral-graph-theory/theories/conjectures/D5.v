(** * Spectral.conjectures.D5 — milestone D5 open-problem statements (Spectral)

    Statement-only formalisation (plan v4, namespace [Spectral]) of five deferred open
    problems / conjectures in algebraic & spectral graph theory.  Each node is a single
    [Definition <formal_name> : Prop]; the carrier type is chosen per row (NOT a blanket
    [forall G : sgraph]).  No axioms, no [Admitted], no [Conjecture]/[Parameter].

    Sources (verbatim, from the OPG corpus):
    - triangle_free_strongly_regular_graphs:
        "Is there an eighth triangle free strongly regular graph?"
    - signing_a_graph_to_have_small_magnitude_eigenvalues (SOLVED, Marcus–Spielman–
        Srivastava 2015; stated as a Definition only):
        "If A is the adjacency matrix of a d-regular graph, then there is a symmetric
        signing of A ... so that the resulting matrix has all eigenvalues of magnitude
        at most 2*sqrt(d-1)."
    - are_almost_all_graphs_determined_by_their_spectrum:
        "Are almost all graphs uniquely determined by the spectrum of their adjacency
        matrix?"
    - does_the_symmetric_chromatic_function_distinguish_trees:
        "Do there exist non-isomorphic trees which have the same chromatic symmetric
        function?"
    - laplacian_degrees_of_a_graph:
        "If G is a connected graph on n vertices, then c_k(G) >= d_k(G) for
        k = 1, 2, ..., n-1."

    Spectral matrix vocabulary is imported from [Spectral.foundations.spectral]
    (area-local).  Combinatorial primitives that only ONE row needs (strongly regular
    graphs, Stanley's chromatic symmetric function) are defined locally here. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** ** Row 1 — Triangle-free strongly regular graphs (Algebraic Graph Theory, OPEN)

    Area-specific primitive [strongly_regular]: combinatorial (int/nat, no matrices).
    A graph is strongly regular when it is connected, [k]-regular with [0 < k < n-1],
    every pair of adjacent vertices has exactly [lam] common neighbours, and every pair
    of distinct non-adjacent vertices has exactly [mu] common neighbours.  (Triangle-
    freeness forces [lam = 0].)

    PRIMITIVITY GUARDS (faithfulness): [connected [set: G]] together with [0 < k] and
    [k < (#|G|).-1] is the standard PRIMITIVE definition.  Without them an edgeless graph
    ([regular G 0], vacuous [lam] clause, forced [mu = 0]), a complete graph, or a
    disjoint union of cliques would trivially satisfy the predicate, making the "eighth
    SRG" question vacuously provable.  [0 < k] guarantees an adjacent pair exists (so
    [lam] is genuinely constrained); [k < (#|G|).-1] guarantees a distinct non-adjacent
    pair exists (so [mu] is genuinely constrained) and rules out complete graphs.

    "Is there an EIGHTH triangle-free strongly regular graph?" — exactly seven such
    graphs are known, so the proposition is: there exist eight pairwise non-isomorphic
    triangle-free strongly regular graphs.  Combined with the seven known examples this
    is equivalent to the existence of an eighth. *)
Definition strongly_regular (G : sgraph) : Prop :=
  exists k lam mu : nat,
    [/\ connected [set: G],
        (0 < k)%N /\ (k < (#|G|).-1)%N,
        regular G k,
        (forall u v : G, u -- v -> #|common_nbr u v| = lam) &
        (forall u v : G, u != v -> ~~ (u -- v) -> #|common_nbr u v| = mu)].

Definition triangle_free_strongly_regular_graphs_statement : Prop :=
  exists g : 'I_8 -> sgraph,
    (forall i, triangle_free (g i) /\ strongly_regular (g i)) /\
    (forall i j, i != j -> ~ inhabited (g i ≃ g j)).

(** ** Row 2 — Signing a graph to small-magnitude eigenvalues (Graph Theory, SOLVED)

    Bilu–Linial signing -> bipartite Ramanujan (Marcus–Spielman–Srivastava 2015).
    Stated here as a Definition only (statement-level; proof is out of scope).

    For every [d]-regular graph there is a symmetric signing of its adjacency matrix
    (replace some [+1] entries by [-1]) all of whose eigenvalues have magnitude at most
    [2*sqrt(d-1)].  Quantified over an abstract real-closed field [R].  Guards: the graph
    is non-empty, and [2 <= d] — the regime where [2*sqrt(d-1)] is the intended
    non-trivial Ramanujan bound.  (For [d <= 1] the nat predecessor makes the bound
    [2*sqrt(d-1)] collapse to [0], which a matching's signing cannot meet; the MSS result
    is stated for [d >= 2].) *)
Definition signing_a_graph_to_have_small_magnitude_eigenvalues_statement : Prop :=
  forall (R : rcfType) (G : sgraph) (d : nat),
    regular G d -> (2 <= d)%N -> (0 < #|G|)%N ->
    exists S : 'M[R]_(#|G|),
      is_signing S /\ spectral_radius_le S (2%:R * Num.sqrt (d.-1)%:R).

(** ** Row 3 — Almost all graphs determined by their spectrum (Graph Theory, OPEN)

    "Are ALMOST ALL graphs uniquely determined by the spectrum of their adjacency
    matrix?"  Encoded as a density limit over labelled [n]-graphs (foundations):
    the fraction [determined_count n / total_count n] tends to [1].  Stated over [nat]
    (no reals): for every [m > 0], eventually at most a [1/m] fraction of [n]-graphs
    fail to be spectrally determined.  ([total_count n >= 1] always — the empty graph —
    so the ratio is non-vacuous.) *)
Definition are_almost_all_graphs_determined_by_their_spectrum_statement : Prop :=
  forall m : nat, (0 < m)%N ->
    exists N : nat, forall n : nat, (N <= n)%N ->
      (m * (total_count n - determined_count n) <= total_count n)%N.

(** ** Row 4 — Symmetric chromatic function distinguishing trees (Alg. Graph Th., OPEN)

    Stanley's CHROMATIC SYMMETRIC function (a generating function over proper colourings,
    NOT eigenvalues).  [csf_coeff G k a] counts the proper [k]-colourings of [G] whose
    colour-class sizes are exactly [a] (the monomial-symmetric-function data of X_G);
    [same_csf G H] means [G] and [H] have equal chromatic symmetric function.

    "Do there exist non-isomorphic TREES with the same chromatic symmetric function?" *)
Definition proper_colb (G : sgraph) (k : nat) (c : {ffun G -> 'I_k}) : bool :=
  [forall x, [forall y, (x -- y) ==> (c x != c y)]].

Definition csf_coeff (G : sgraph) (k : nat) (a : 'I_k -> nat) : nat :=
  #|[set c : {ffun G -> 'I_k} |
       proper_colb c && [forall b : 'I_k, #|[set x | c x == b]| == a b]]|.

Definition same_csf (G H : sgraph) : Prop :=
  forall (k : nat) (a : 'I_k -> nat), csf_coeff G a = csf_coeff H a.

Definition does_the_symmetric_chromatic_function_distinguish_tr_statement : Prop :=
  exists T1 T2 : sgraph,
    [/\ is_tree [set: T1], is_tree [set: T2],
        ~ inhabited (T1 ≃ T2) & same_csf T1 T2].

(** ** Row 5 — Laplacian degrees of a graph (Algebraic Graph Theory, OPEN)

    [c_k(G)] = the [k]-th largest Laplacian eigenvalue (counted with multiplicity);
    [d_k(G)] = the [k]-th largest vertex degree.  Conjecture (Brouwer–Haemers / Grone–
    Merris-style majorisation): for a connected graph on [n] vertices,
    [c_k(G) >= d_k(G)] for [k = 1, ..., n-1].

    Quantified over an abstract real-closed field [R]; [s] is any non-increasing
    Laplacian spectrum of [G] (unique up to order, hence the [forall] is faithful) and
    [d] any non-increasing degree sequence.  Indices are 0-based, so [k = 1..n-1]
    becomes [k < n-1] reading [s`_k]/[d`_k]. *)
Definition laplacian_degrees_of_a_graph_statement : Prop :=
  forall (R : rcfType) (G : sgraph),
    connected [set: G] -> (0 < #|G|)%N ->
    forall s : seq R, is_spectrum (Lapmx R G) s ->
    forall d : seq nat, is_deg_sorted G d ->
    forall k : nat, (k < (#|G|).-1)%N -> (nth 0%N d k)%:R <= nth 0 s k.
