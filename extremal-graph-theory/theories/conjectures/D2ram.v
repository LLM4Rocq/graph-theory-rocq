(** * Extremal.conjectures.D2ram — milestone D2ram open-problem statements (Extremal)

    Statement-only formalisation (plan v4, namespace [Extremal]) of five deferred open
    problems / conjectures in Ramsey-flavoured extremal & structural graph theory.  Each
    node is a single [Definition <formal_name> : Prop]; the carrier type is chosen PER ROW
    from the row's [rocq_idiom] (NOT a blanket [forall G : sgraph]).  No axioms, no
    [Admitted], no [Conjecture]/[Parameter].

    Sources (verbatim, from the OPG corpus):

    - multicolour_erdos_hajnal_statement (Conjecture, OPEN):
        "For every fixed k>=2 and fixed colouring chi of E(K_k) with m colours, there
         exists eps>0 such that every colouring of the edges of K_n contains either k
         vertices whose edges are coloured according to chi or n^eps vertices whose edges
         are coloured with at most m-1 colours."
        CARRIER: edge-colourings of complete graphs = symmetric maps
        [col : 'I_n -> 'I_n -> 'I_m] (the colour of the K_n-edge {x,y}); the pattern chi
        is a symmetric [chi : 'I_k -> 'I_k -> 'I_m] using all m colours.

    - complete_bipartite_subgraphs_of_perfect_graphs_statement (Problem, OPEN):
        "Let G be a perfect graph on n vertices.  Is it true that either G or G-bar
         contains a complete bipartite subgraph with bipartition (A,B) so that
         |A|,|B| >= n^{1 - o(1)}?"
        CARRIER: [sgraph] (and its complement [compl G], same vertex type).

    - chromatic_number_of_common_graphs_statement (Question, OPEN; PARTIAL):
        "Do common graphs have bounded chromatic number?"
        CARRIER: [sgraph] (the graph H), with 2-edge-colourings of K_n as [rel 'I_n].

    - ramsey_properties_of_cayley_graphs_statement (Conjecture, OPEN):
        "There exists a fixed constant c so that every abelian group G has a subset
         S ⊆ G with -S = S so that the Cayley graph Cayley(G,S) has no clique or
         independent set of size > c log|G|."
        CARRIER: a finite (abelian) group [gT : finGroupType] and a connection set
        [S : {set gT}]; the Cayley graph is the [sgraph] built below.

    - the_erdos_hajnal_statement (Conjecture, OPEN):
        "For every fixed graph H, there exists a constant delta(H), so that every graph G
         without an induced subgraph isomorphic to H contains either a clique or an
         independent set of size |V(G)|^{delta(H)}."
        CARRIER: [sgraph] (both H and G).

    Cross-area primitives are REUSED verbatim from [GTBase.base] / coq-graph-theory:
    [χ(_)] / [ω(_)] / [α(_)] (the chromatic / clique / independence numbers, subset-
    relative), [compl] (the complement sgraph), [_ ⇀ _] = [isubgraph] (an induced-subgraph
    embedding: injective + adjacency-MONO, i.e. "G contains an induced copy of H"), and
    coq-graph-theory's [E(_)] = [sg_edge_set] (underlying [edge_count]).  Genuinely NEW area-specific
    primitives are defined locally; [cayley_graph] (an undirected Cayley sgraph over a
    finite group) and the edge-colouring / common-graph counting layers are tagged below.

    ASYMPTOTIC ROWS use the eventual-bound / cross-multiplied integer formulation over
    [nat] (never an informal o/O/log token):
      - "size n^eps", eps = a/b > 0  ↦  [n^a <= |A|^b]  (a/b-th power, log-free);
      - "no clique/indep of size > c·log|G|"  ↦  [2^ω <= |G|^c]  (since ω <= c·log₂|G|
        ⟺ 2^ω <= |G|^c), and dually for α;
      - "size n^{1-o(1)}"  ↦  ∀ a<b, ∃N, ∀ n>=N, [n^(b-a) <= |A|^b]  (exponent (b-a)/b
        ranging over all values < 1);
      - "size |V(G)|^{delta(H)}", delta = a/b ∈ (0,1]  ↦  [|G|^a <= max(ω,α)^b].

    PARTIAL row: [chromatic_number_of_common_graphs_statement] hinges on the analytic
    notion "common graph" (the monochromatic-copy count of H in any 2-edge-colouring of
    K_n is asymptotically minimised by the random colouring — a graph-limit / homomorphism-
    density statement).  With no graphon / hom-density / probability layer here we render
    the cleanest faithful FINITE core as an EVENTUAL bound: H is [common_graph] when there
    is a threshold N so that, for every n >= N and every 2-colouring of K_n, the number of
    monochromatic homomorphic copies of H is at least [n^{|V(H)|} / 2^{|E(H)|}] (cross-
    multiplied to [n^{|V(H)|} <= mono_copies · 2^{|E(H)|}]).  This is a lower bound of the
    random-colouring order (the random expectation is [≈ n^{|V(H)|} · 2^{1-|E(H)|}]); the
    eventual quantifier removes the small-n degeneracy and the unit leading factor keeps
    EDGELESS graphs (genuinely common, χ = 1) inside the class.  MISSING: the genuine
    asymptotic (1+o(1)) factor / graphon formulation; see the note at that row. *)

From mathcomp Require Import all_boot all_fingroup.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared sgraph edge count

    [edge_count G] = |E(G)|, REUSING coq-graph-theory's [E(_)] = [sg_edge_set] (the set of
    undirected edges [ [set x; y] ] with [x -- y]); it counts each undirected edge once.
    This is the cross-area quantity |E(G)| imported verbatim, not re-derived. *)
Definition edge_count (G : sgraph) : nat := #|E(G)|.

(** ============================================================================ *)
(** ** Row 1 — Multicolour Erdős–Hajnal conjecture (OPEN)

    CARRIER: an edge-colouring of the complete graph K_n is a symmetric function
    [col : 'I_n -> 'I_n -> 'I_m] assigning each pair {x,y} one of m colours.  The fixed
    pattern is a symmetric [chi : 'I_k -> 'I_k -> 'I_m] that USES all m colours.

    AREA-SPECIFIC primitives:
    - [uses_all_colours chi]   : every colour in 'I_m occurs on some edge of the pattern
                                 (so m is genuinely the number of colours of chi);
    - [contains_pattern chi col]: some injection g : 'I_k -> 'I_n places k vertices whose
                                 induced colouring matches chi exactly (a chi-coloured K_k);
    - [palette_on col A]       : the set of colours appearing on the edges inside A.

    Conjecture: for fixed k>=2 and chi (with m colours), there is eps>0 so that EVERY
    K_n-colouring contains either a chi-coloured K_k, or n^eps vertices spanning <= m-1
    colours.  eps = a/b > 0; "n^eps vertices" ↦ [n^a <= |A|^b]. *)

Section MulticolourEH.

(** [@MOVE-to-base] area-specific (edge-colouring pattern vocabulary). *)
Definition uses_all_colours (k m : nat) (chi : 'I_k -> 'I_k -> 'I_m) : Prop :=
  forall c : 'I_m, exists i j : 'I_k, i != j /\ chi i j = c.

Definition contains_pattern (n k m : nat)
    (chi : 'I_k -> 'I_k -> 'I_m) (col : 'I_n -> 'I_n -> 'I_m) : Prop :=
  exists g : 'I_k -> 'I_n,
    injective g /\ forall i j : 'I_k, i != j -> col (g i) (g j) = chi i j.

Definition palette_on (n m : nat) (col : 'I_n -> 'I_n -> 'I_m) (A : {set 'I_n}) : {set 'I_m} :=
  [set c : 'I_m | [exists x : 'I_n, [exists y : 'I_n,
        [&& x \in A, y \in A, x != y & col x y == c]]]].

End MulticolourEH.

Definition multicolour_erdos_hajnal_statement : Prop :=
  forall (k m : nat) (chi : 'I_k -> 'I_k -> 'I_m),
    (2 <= k)%N -> (0 < m)%N ->
    (forall i j : 'I_k, chi i j = chi j i) -> uses_all_colours chi ->
    exists a b : nat, (0 < a)%N /\ (0 < b)%N /\
      forall (n : nat) (col : 'I_n -> 'I_n -> 'I_m),
        (forall x y : 'I_n, col x y = col y x) ->
        contains_pattern chi col \/
        (exists A : {set 'I_n},
           (n ^ a <= #|A| ^ b)%N /\ (#|palette_on col A| <= m - 1)%N).

(** ============================================================================ *)
(** ** Row 2 — Complete bipartite subgraphs of perfect graphs (OPEN)

    CARRIER: [sgraph] (and its complement [compl G], which has the SAME vertex type, so
    [A B : {set G}] serve as vertex sets in both G and [compl G]).

    AREA-SPECIFIC primitives:
    - [perfect_graph G]         : χ(A) = ω(A) for every induced subgraph (every A ⊆ V) —
                                  the Lovász characterisation, using base's χ / ω;
    - [complete_bipartite_sub G A B]: A,B are disjoint and every A–B pair is adjacent (a
                                  complete bipartite SUBGRAPH with parts A,B).

    Problem: is it true that for every perfect G on n vertices, G or G-bar contains a
    complete bipartite subgraph with |A|,|B| >= n^{1-o(1)}?  "n^{1-o(1)}" is rendered as
    the eventual bound: for every exponent (b-a)/b < 1 (i.e. a<b), eventually
    [n^(b-a) <= |A|^b] and [n^(b-a) <= |B|^b]. *)

Definition perfect_graph (G : sgraph) : Prop := forall A : {set G}, χ(A) = ω(A).

Definition complete_bipartite_sub (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\ (forall a b : G, a \in A -> b \in B -> a -- b).

Definition complete_bipartite_subgraphs_of_perfect_graphs_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (a < b)%N ->
    exists N : nat, forall (G : sgraph) (n : nat),
      #|G| = n -> (N <= n)%N -> perfect_graph G ->
      exists A B : {set G},
        (complete_bipartite_sub A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N)
        \/
        (@complete_bipartite_sub (compl G) A B
           /\ (n ^ (b - a) <= #|A| ^ b)%N /\ (n ^ (b - a) <= #|B| ^ b)%N).

(** ============================================================================ *)
(** ** Row 3 — Chromatic number of common graphs (OPEN; PARTIAL)

    CARRIER: [sgraph] (the graph H); 2-edge-colourings of K_n are [col : rel 'I_n]
    (symmetric booleans).

    PARTIAL: "common" is an analytic / graph-limit notion (the random 2-colouring
    asymptotically minimises the count of monochromatic copies of H).  Faithful finite
    core, no graphons:
    - [mono_copies H col]  : the number of homomorphic copies f : H -> K_n all of whose
                             edges receive one common colour under [col] (and join DISTINCT
                             vertices, so each maps to a genuine K_n-edge);
    - [common_graph H]     : EVENTUAL bound — there is a threshold N so that for every
                             n >= N and every 2-colouring of K_n, [mono_copies] is at least
                             [n^{|V(H)|}/2^{|E(H)|}], cross-multiplied to
                             [n^{|V(H)|} <= mono_copies·2^{|E(H)|}].
    The unit leading factor (NOT 2) keeps edgeless H — which are genuinely common with
    χ = 1 — inside the class (for edgeless H, [mono_copies = n^{|V(H)|}] and [|E(H)| = 0],
    so the bound is an equality), and the eventual [N <= n] quantifier removes the n = 1
    degeneracy that an all-n bound would impose.  MISSING (out of scope): the genuine
    (1+o(1)) asymptotic / graphon / hom-density form; the finite eventual inequality is the
    cleanest faithful approximation.

    Question: do common graphs have bounded chromatic number?  ↦  ∃k, ∀ H common,
    χ(H) <= k. *)

(** [@MOVE-to-base] area-specific (monochromatic-copy counting). *)
Definition mono_copies (H : sgraph) (n : nat) (col : rel 'I_n) : nat :=
  #|[set f : {ffun H -> 'I_n} | [exists b : bool,
       [forall x : H, [forall y : H,
          (x -- y) ==> ((f x != f y) && (col (f x) (f y) == b))]]]]|.

Definition common_graph (H : sgraph) : Prop :=
  exists N : nat, forall (n : nat) (col : rel 'I_n), symmetric col -> (N <= n)%N ->
    (n ^ #|H| <= mono_copies H col * 2 ^ edge_count H)%N.

Definition chromatic_number_of_common_graphs_statement : Prop :=
  exists k : nat,
    forall H : sgraph, (0 < #|H|)%N -> common_graph H -> (χ([set: H]) <= k)%N.

(** ============================================================================ *)
(** ** Row 4 — Ramsey properties of Cayley graphs (OPEN)

    CARRIER: a finite group [gT : finGroupType] with [abelian [set: gT]] and a connection
    set [S : {set gT}].  The undirected Cayley graph [cayley_graph S] has the group
    elements as vertices, with [x] adjacent to [y] iff [x != y] and [x⁻¹y ∈ S] (or, to be
    symmetric unconditionally, [y⁻¹x ∈ S]); under the conjecture's [-S = S] hypothesis the
    two disjuncts coincide and this is exactly the standard Cayley graph.

    AREA-SPECIFIC primitive [cayley_graph] (NEW; tagged [@MOVE-to-base]): an undirected
    Cayley [sgraph] over a finite group — the natural undirected analogue of digraph-
    theory's directed [cayley].

    Conjecture: a fixed c works for all abelian G — there is a symmetric [S] ([-S = S],
    spelled [x ∈ S ⟺ x⁻¹ ∈ S]) whose Cayley graph has neither a clique nor an independent
    set of size > c·log|G|.  "size > c·log|G|" forbidden ↦ ω <= c·log₂|G| and
    α <= c·log₂|G|, i.e. [2^ω <= |G|^c] and [2^α <= |G|^c].  Guard [1 < |G|] excludes the
    trivial group (log|G| = 0). *)

Section CayleyGraph.
Variables (gT : finGroupType) (S : {set gT}).

(** [@MOVE-to-base] undirected Cayley graph over a finite group. *)
Definition cayley_adj : rel gT :=
  fun x y => (x != y) && (((x^-1 * y)%g \in S) || ((y^-1 * x)%g \in S)).

Lemma cayley_adj_sym : symmetric cayley_adj.
Proof. by move=> x y; rewrite /cayley_adj eq_sym orbC. Qed.

Lemma cayley_adj_irrefl : irreflexive cayley_adj.
Proof. by move=> x; rewrite /cayley_adj eqxx. Qed.

Definition cayley_graph : sgraph := SGraph cayley_adj_sym cayley_adj_irrefl.

End CayleyGraph.

Definition ramsey_properties_of_cayley_graphs_statement : Prop :=
  exists c : nat, (0 < c)%N /\
    forall gT : finGroupType, abelian [set: gT] -> (1 < #|gT|)%N ->
      exists S : {set gT},
        (forall x : gT, (x \in S) = ((x^-1)%g \in S)) /\
        (2 ^ ω([set: cayley_graph S]) <= #|gT| ^ c)%N /\
        (2 ^ α([set: cayley_graph S]) <= #|gT| ^ c)%N.

(** ============================================================================ *)
(** ** Row 5 — The Erdős–Hajnal conjecture (OPEN)

    CARRIER: [sgraph] (both the forbidden H and the host G).

    AREA-SPECIFIC primitive:
    - [has_induced_copy H G] : G contains an induced subgraph isomorphic to H — REUSING
      coq-graph-theory's [_ ⇀ _] = [isubgraph] (injective + adjacency-mono embedding),
      wrapped in [inhabited] to land in [Prop].  "H-induced-free" is its negation.

    Conjecture: for every fixed H there is delta(H) > 0 with: every H-induced-free G has a
    clique or an independent set of size |V(G)|^{delta}.  delta = a/b ∈ (0,1] (so 0<a<=b);
    "max(ω,α) >= |G|^delta" ↦ [|G|^a <= (max(ω,α))^b].  Guard [0 < |G|]. *)

Definition has_induced_copy (H G : sgraph) : Prop := inhabited (H ⇀ G).

Definition the_erdos_hajnal_statement : Prop :=
  forall H : sgraph, exists a b : nat, (0 < a)%N /\ (a <= b)%N /\
    forall G : sgraph, (0 < #|G|)%N -> ~ has_induced_copy H G ->
      (#|G| ^ a <= (maxn ω([set: G]) α([set: G])) ^ b)%N.
