(** * Digraph.conjectures.colouring_variants — P11: colouring variants

    Three families of "colouring" conjectures over digraphs, stated (not proved)
    on top of the core HB DiGraph -> Oriented -> Tournament stack and the
    dichromatic / stable machinery:

      1. MAJORITY COLOURING (Kreutzer, Oum, Seymour, van der Zypen, Wood,
         arXiv:1608.03040). A vertex k-colouring is "majority" when no vertex has
         more than half of its out-neighbours in its own colour class.
           - [majority_3col_statement]  (Conj 2): every digraph has one with 3 cols;
           - [majority_k1col_statement]  (Conj 9): the (k+1)-colour, (1/k)·deg⁺ form;
           - [majority_3col_tournament_statement] (Open Pb 2) and
             [majority_3col_eulerian_statement]   (Open Pb 3), the cheap variants.

      2. ORIENTED CHROMATIC NUMBER / DIGRAPH HOMOMORPHISM (Courcelle; Sopena). A
         digraph homomorphism [dhom] is an arc-preserving map; an oriented
         colouring is a [dhom] onto a tournament on the colour set, and the
         oriented chromatic number is bounded over planar oriented graphs
         ([oriented_chromatic_planar_bounded_statement]; planarity reuses
         [two_extremal.planar_sg] on the underlying simple graph).

      3. ARC-COLOURING / MONOCHROMATIC REACHABILITY (Sands–Sauer–Woodrow and the
         tournament rainbow-triangle variant). An arc colouring colours each arc;
         a monochromatic directed path is a [connect] in one colour's sub-relation.
           - [mono_reach_or_rainbow_statement] (3-arc-coloured tournament: rainbow
             triangle or a monochromatic-reachability root);
           - [sands_sauer_woodrow_statement]   (k-arc-coloured digraph: bounded
             union of stable sets reachable monochromatically from everywhere).

    All "for all X" statements guard the empty digraph where vacuity would make
    them trivially (and unfaithfully) true. Relative edges connecting the
    statements are proved as [Theorem ... Qed].
    See docs/CONJECTURES_FORMALIZATION_PLAN.md (P11). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath.
From Digraph Require Import dichromatic two_extremal classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** 1. Majority colouring ************************************************** *)

(** The set of out-neighbours of [v] that share [v]'s colour, under a vertex
    colouring [col]. Pure function over the arc relation; works for any
    digraph. *)
Definition same_col_outnb {D : diGraphType} {k : nat}
    (col : D -> 'I_k) (v : D) : {set D} :=
  [set w | (v --> w) && (col w == col v)].

(** [col] is a MAJORITY colouring: at every vertex at most half of the
    out-neighbours share its colour. Written [2 * (#same) <= outdeg] to stay in
    [nat] (no division). *)
Definition majority_col {D : diGraphType} {k : nat} (col : D -> 'I_k) : bool :=
  [forall v : D, 2 * #|same_col_outnb col v| <= outdeg v].

(** The parametric "(1/k)·deg⁺" bound of Conjecture 9, again cleared of
    fractions: at most [outdeg v / k] same-coloured out-neighbours, i.e.
    [k * (#same) <= outdeg v]. (At [k = 2] this is exactly [majority_col].) *)
Definition kmajority_col {D : diGraphType} {m : nat} (k : nat)
    (col : D -> 'I_m) : bool :=
  [forall v : D, k * #|same_col_outnb col v| <= outdeg v].

Lemma kmajority_col2 (D : diGraphType) (col : D -> 'I_2) :
  kmajority_col 2 col = majority_col col.
Proof. by []. Qed.

(** Conjecture 2 (1608.03040): every digraph admits a majority 3-colouring. *)
Definition majority_3col_statement : Prop :=
  forall D : diGraphType, exists col : D -> 'I_3, majority_col col.

(** Conjecture 9 (1608.03040): for every [k >= 2], every digraph admits a
    (k+1)-colouring with at most [(1/k)·deg⁺] same-coloured out-neighbours. *)
Definition majority_k1col_statement : Prop :=
  forall (k : nat), 2 <= k ->
    forall D : diGraphType, exists col : D -> 'I_k.+1, kmajority_col k col.

(** Open Problem 2 (1608.03040): does every tournament have a majority
    3-colouring? *)
Definition majority_3col_tournament_statement : Prop :=
  forall T : tournament, exists col : T -> 'I_3, majority_col col.

(** A digraph is EULERIAN when in-degree equals out-degree at every vertex. *)
Definition indeg (D : diGraphType) (v : D) : nat := #|[set u | u --> v]|.
Definition eulerian (D : diGraphType) : bool :=
  [forall v : D, indeg v == outdeg v].

(** Open Problem 3 (1608.03040): does every Eulerian digraph have a majority
    3-colouring? *)
Definition majority_3col_eulerian_statement : Prop :=
  forall D : diGraphType, eulerian D ->
    exists col : D -> 'I_3, majority_col col.

(** *** Relative edges among the majority statements *)

(** Conjecture 9 at [k = 2] gives a 3-colouring with [2·(#same) <= deg⁺], which
    is exactly the majority condition: Conj 9 ⇒ Conj 2. *)
Theorem majority_k1col_implies_majority_3col :
  majority_k1col_statement -> majority_3col_statement.
Proof.
move=> H9 D; have [col Hcol] := H9 2 (leqnn 2) D.
by exists col; exact: Hcol.
Qed.

(** The general digraph statement specialises to tournaments. *)
Theorem majority_3col_implies_tournament :
  majority_3col_statement -> majority_3col_tournament_statement.
Proof. by move=> H T; apply: (H T). Qed.

(** The general digraph statement specialises to Eulerian digraphs. *)
Theorem majority_3col_implies_eulerian :
  majority_3col_statement -> majority_3col_eulerian_statement.
Proof. by move=> H D _; apply: H. Qed.

(** ** 2. Oriented chromatic number / digraph homomorphism ******************* *)

(** A digraph HOMOMORPHISM [H -> T] is an arc-preserving map (every arc of [H]
    maps to an arc of [T]). Note: not required injective, not arc-reflecting —
    this is the right notion for colouring (unlike the induced embedding
    [heroes.ind_subdigraph]). *)
Definition dhom (H T : diGraphType) : Prop :=
  exists f : H -> T, forall u v : H, u --> v -> f u --> f v.

Lemma dhom_id (D : diGraphType) : dhom D D.
Proof. by exists id. Qed.

Lemma dhom_trans (D1 D2 D3 : diGraphType) :
  dhom D1 D2 -> dhom D2 D3 -> dhom D1 D3.
Proof.
case=> f Hf [g Hg]; exists (g \o f) => u v uv.
by apply: Hg; apply: Hf.
Qed.

(** [D] has an ORIENTED [k]-COLOURING when it maps homomorphically onto SOME
    tournament on [k] vertices. (A homomorphism to a tournament forces (i) a
    proper colouring of the underlying graph, since a digon would need a digon
    in the loopless tournament image, and (ii) the "no two arcs with swapped
    colour endpoints" condition, since the image arcs are consistently
    oriented.) The colour set being a tournament is the standard reformulation
    of oriented colouring. *)
Definition oriented_kcolouring (D : diGraphType) (k : nat) : Prop :=
  exists T : tournament, #|T| = k /\ dhom D T.

(** The oriented chromatic number is at most [k] (the least such [k] is the
    oriented chromatic number proper). *)
Definition ochi_le (D : diGraphType) (k : nat) : Prop :=
  oriented_kcolouring D k.

(** Oriented colourings are downward inherited by homomorphic preimages:
    if [D -> D'] and [D'] has an oriented [k]-colouring, so does [D]. *)
Theorem ochi_le_dhom (D D' : diGraphType) (k : nat) :
  dhom D D' -> ochi_le D' k -> ochi_le D k.
Proof.
move=> dDD' [T [Tk hom']]; exists T; split=> //.
exact: dhom_trans dDD' hom'.
Qed.

(** Courcelle / Sopena: the oriented chromatic number is BOUNDED over all
    orientations of planar graphs. We range over oriented digraphs whose
    underlying simple graph (built via [two_extremal.underlyingG], which needs
    looplessness) is planar in the Wagner sense [two_extremal.planar_sg], and
    assert a single [k] orienting-colours them all. Guarded against the empty
    universe by the [(0 < #|D|)%N] presence (the bound must hold for nonempty
    members too — vacuity is impossible since [k] is uniform). *)
Definition oriented_chromatic_planar_bounded_statement : Prop :=
  exists k : nat,
    forall (D : diGraphType) (llD : loopless D),
      planar_sg (underlyingG llD) -> oriented_kcolouring D k.

(** ** 3. Arc-colouring / monochromatic reachability ************************* *)

(** A [k]-ARC-COLOURING of [D] assigns a colour in ['I_k] to each ordered pair;
    it is only consulted on actual arcs. *)
Definition arc_colouring (D : diGraphType) (k : nat) := D -> D -> 'I_k.

(** The sub-relation of arcs that carry colour [i]. *)
Definition mono_rel (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (i : 'I_k) : rel D :=
  fun u v => (u --> v) && (c u v == i).

(** [v] reaches [w] by a MONOCHROMATIC directed path in colour [i]: the
    reflexive-transitive closure of [mono_rel c i]. (Reflexive: every vertex
    reaches itself by the empty path, as in the standard convention.) *)
Definition mono_reach (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (i : 'I_k) (v w : D) : bool :=
  connect (mono_rel c i) v w.

(** [v] reaches [w] by a monochromatic path of SOME colour. *)
Definition mono_reach_any (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (v w : D) : bool :=
  [exists i : 'I_k, mono_reach c i v w].

Lemma mono_reach_refl (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (i : 'I_k) (v : D) : mono_reach c i v v.
Proof. exact: connect0. Qed.

(** A monochromatic-reachability ROOT: a vertex from which every vertex is
    reachable by a single-colour directed path (colours may differ per target). *)
Definition mono_root (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (v : D) : bool :=
  [forall w : D, mono_reach_any c v w].

(** A RAINBOW directed triangle in a 3-arc-coloured digraph: a directed
    3-cycle [a -> b -> c -> a] whose three arcs carry three DISTINCT colours. *)
Definition rainbow_triangle (D : diGraphType) (c : arc_colouring D 3) : Prop :=
  exists a b c0 : D,
    [/\ a --> b, b --> c0, c0 --> a
      & uniq [:: c a b; c b c0; c c0 a]].

(** Monochromatic reachability OR rainbow triangles (Sands–Sauer–Woodrow
    variant; Bang-Jensen / Aharoni et al.): every 3-arc-coloured tournament has
    a rainbow triangle or a monochromatic-reachability root. Guarded with
    [(0 < #|T|)%N] so the root quantifier is not vacuous. *)
Definition mono_reach_or_rainbow_statement : Prop :=
  forall (T : tournament) (c : arc_colouring T 3),
    (0 < #|T|)%N ->
    rainbow_triangle c \/ exists v : T, mono_root c v.

(** A [stable] set has no arc inside it (reuse [classic_core.stable]). A subset
    [S] is a union of at most [m] stable sets when it is covered by [m] stable
    parts. *)
Definition union_of_stables (D : diGraphType) (m : nat) (S : {set D}) : Prop :=
  exists parts : seq {set D},
    [/\ size parts <= m,
        all (fun P => stable P) parts
      & S = \bigcup_(P <- parts) P].

(** Sands–Sauer–Woodrow (general digraph version): for every number of colours
    [k] there is a bound [f] such that every [k]-arc-coloured digraph has a set
    [S], a union of at most [f] stable sets, with every vertex reaching [S]
    monochromatically. *)
Definition sands_sauer_woodrow_statement : Prop :=
  forall k : nat, exists f : nat,
    forall (D : diGraphType) (c : arc_colouring D k),
      exists S : {set D},
        [/\ union_of_stables f S
          & forall v : D, exists2 s : D, s \in S & mono_reach_any c v s].

(** *** A cheap sanity edge: the FULL vertex set is always a witnessing target
    set for monochromatic reachability, since every vertex reaches itself by the
    empty (length-0) monochromatic path. (This shows the SSW reachability clause
    is non-vacuous; the conjecture's content is bounding the target set by [f(k)]
    STABLE sets, which [setT] does not satisfy in general.) The dual statement —
    that a monochromatic-reachability ROOT [v] reaches every vertex — is recorded
    too, since it is the defining property of [mono_root]. *)
Theorem setT_is_reach_set (D : diGraphType) (k : nat) (c : arc_colouring D k) :
  (0 < k)%N ->
  forall w : D, exists2 s : D, s \in [set: D] & mono_reach_any c w s.
Proof.
move=> k_gt0 w; exists w; first by rewrite inE.
by apply/existsP; exists (Ordinal k_gt0); exact: mono_reach_refl.
Qed.

Theorem mono_root_reaches_all (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (v : D) :
  mono_root c v -> forall w : D, mono_reach_any c v w.
Proof. by move=> /forallP. Qed.
