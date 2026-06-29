(** * Infinite.conjectures.D4doa — milestone D4doa (namespace Infinite, plan v4)

    Statement-only formalizations of two OPEN problems from the infinite /
    asymptotic graph-theory bucket.  Carriers are chosen PER ROW (no blanket
    [sgraph]).

    AXIOM DISCIPLINE: the file declares NO top-level Conjecture/Axiom/Parameter/
    Admitted.  Row 2 is closed under the global context.  Row 1 inherits the
    standard Stdlib classical-reals axioms (Classical_Prop.classic,
    FunctionalExtensionality.functional_extensionality_dep,
    ClassicalDedekindReals.sig_forall_dec / sig_not_dec) transitively through
    [R] / [Rpower] / [INR]; this is inherent to the chosen real-analysis idiom,
    not a locally-declared assumption.

    Row 1 — counting_3_colorings_of_the_hex_lattice
      "Find lim_{n->oo} (chi(H_n,3))^(1/|V(H_n)|)."
      A THERMODYNAMIC LIMIT (entropy per site) over the *finite* hexagonal tori
      H_n.  Here chi(H_n,3) is the chromatic polynomial of H_n evaluated at 3 =
      the number of proper 3-colourings.  Carrier: a concrete FINITE [sgraph]
      honeycomb torus [hex_torus n] (no infinite carrier needed).  The limit is
      a real number, so the statement asserts (eps-N idiom) that the sequence of
      per-site values converges; "Find the limit" is rendered as "the limit
      exists".  AREA-LOCAL primitives: [n3colorings] (chromatic-polynomial at 3),
      [converges] (lattice/thermodynamic limit).

    Row 2 — exact_colorings_of_graphs
      "P(c,m): every exact c-colouring of the edges of K_omega has an exactly
      m-coloured countably infinite complete subgraph.  P(c,m) iff m=1, m=2, or
      c=m."  Carrier: K_omega = the countable complete graph (iV := nat, edge :=
      distinctness), defined in [Infinite.foundations.igraph].  The exact-colouring
      / exactly-m-coloured-subgraph vocabulary lives in that foundations module
      ([Kedge_coloring], [sym_coloring], [exact_coloring], [exactly_m_colored]);
      this file only assembles the biconditional
      [Pcm c m <-> (m=1 \/ m=2 \/ c=m)].

    No new cross-area (base) primitives are introduced. *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Row 1 : the hexagonal-lattice torus and its 3-colour count *)

(** *** A concrete honeycomb torus [hex_torus n]

    Vertices are [('I_n.+1 * 'I_n.+1) * bool]: a cell index [(i,j)] on the
    discrete torus Z_{n+1} x Z_{n+1} together with a sublattice flag
    ([true] = A-vertex, [false] = B-vertex).  The A-vertex of cell [(i,j)] is
    joined to the B-vertices of cells [(i,j)], [(i+1,j)] and [(i,j+1)] (indices
    mod [n+1]).  This is the standard 3-regular bipartite hexagonal lattice
    wrapped on a torus. *)

Section HexTorus.
Variable n : nat.

Definition hvertex := (('I_n.+1 * 'I_n.+1) * bool)%type.

Definition hadj (x y : hvertex) : bool :=
  let: (xij, xs) := x in let: (xi, xj) := xij in
  let: (yij, ys) := y in let: (yi, yj) := yij in
  (xs != ys) &&
  (let: (ai, aj, bi, bj) :=
     if xs then (val xi, val xj, val yi, val yj)
           else (val yi, val yj, val xi, val xj) in
   ((bi == ai) && (bj == aj))
   || ((bi == (ai + 1) %% n.+1) && (bj == aj))
   || ((bi == ai) && (bj == (aj + 1) %% n.+1))).

Lemma hadj_sym : symmetric hadj.
Proof.
move=> [[xi xj] xs] [[yi yj] ys]; rewrite /hadj.
by case: xs; case: ys; rewrite //= ?andbF.
Qed.

Lemma hadj_irr : irreflexive hadj.
Proof. by move=> [[i j] s]; rewrite /hadj eqxx. Qed.

Definition hex_torus : sgraph := SGraph hadj_sym hadj_irr.

End HexTorus.

(** *** Proper 3-colourings and the chromatic polynomial at 3

    [is_proper3 c]: the [{ffun _ -> 'I_3}] is a proper 3-colouring (adjacent
    vertices get distinct colours).  [n3colorings G] counts them = chi(G,3),
    the chromatic polynomial of [G] evaluated at 3. *)

Definition is_proper3 (G : sgraph) (c : {ffun G -> 'I_3}) : bool :=
  [forall x, [forall y, (x -- y) ==> (c x != c y)]].

(** [n3colorings G] is the chromatic polynomial of [G] evaluated at 3; it has
    no graph-theory-base counterpart (base's [coloring] is a partition
    predicate, not a count of proper homomorphisms into 'I_3). *)
Definition n3colorings (G : sgraph) : nat :=
  #|[set c : {ffun G -> 'I_3} | is_proper3 c]|.

(** *** The thermodynamic / lattice limit, stated AXIOM-FREE.

    The conjecture asks whether [lim (n3colorings)^(1/|V|)] EXISTS.  Stdlib's
    [Reals] would make this pull in classical/Dedekind axioms, so instead we
    state it over an arbitrary real-closed field [R] (mathcomp, axiom-free): the
    per-site values [s_n] — the [|V_n|]-th roots of the 3-colouring counts — form
    a CAUCHY sequence (existence of the limit, which lives in the completion of
    [R]).  The roots are quantified by their defining power
    [s_n ^+ |V_n| = count_n] (no explicit n-th-root function needed); they exist
    and are [>= 1] in every [rcfType] since [n3colorings (hex_torus n) >= 1]
    (every bipartite torus is properly 3-colourable), so the statement is
    non-vacuous and rules out a degenerate reading. *)
Definition persite_cauchy (count vsize : nat -> nat) : Prop :=
  forall (R : rcfType) (eps : R), (0 < eps)%R ->
    exists N : nat, forall m k : nat, (N <= m)%N -> (N <= k)%N ->
      forall sm sk : R, (0 <= sm)%R -> (0 <= sk)%R ->
        (sm ^+ (vsize m) = (count m)%:R)%R -> (sk ^+ (vsize k) = (count k)%:R)%R ->
        (`| sm - sk | < eps)%R.

Definition counting_3_colorings_of_the_hex_lattice_statement : Prop :=
  persite_cauchy (fun k => n3colorings (hex_torus k)) (fun k => #|hex_torus k|).

(** ================================================================= *)
(** ** Row 2 : exact colourings of K_omega

    [Pcm c m] : every symmetric exact [c]-colouring of the edges of K_omega
    contains a countably infinite complete subgraph that is exactly
    [m]-coloured.  (Carrier and the colouring vocabulary are from
    [Infinite.foundations.igraph]; the subgraph is given by an injective
    sequence of vertices of [Komega], whose image is a complete subgraph since
    in K_omega all distinct vertices are adjacent.)

    Antecedent non-vacuity: for every [c >= 1] a symmetric exact [c]-colouring
    of K_omega exists (see [grounding_D4doa]), so the universally-quantified
    premise is not empty and the biconditional is not silently satisfiable. *)

Definition Pcm (c m : nat) : Prop :=
  forall col : Kedge_coloring c,
    sym_coloring col -> exact_coloring col ->
    exists s : nat -> nat, injective s /\ exactly_m_colored col s m.

(** The conjecture: for c >= m >= 1, P(c,m) holds iff m = 1, m = 2, or c = m. *)
Definition exact_colorings_of_graphs_statement : Prop :=
  forall c m : nat, (1 <= m)%nat -> (m <= c)%nat ->
    (Pcm c m <-> (m = 1 \/ m = 2 \/ c = m)).
