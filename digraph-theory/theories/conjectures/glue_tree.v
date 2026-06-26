(** * Digraph.conjectures.glue_tree — RECURSIVE FOLD realisation of the 2-Hajós
      TREE join (Def 9.1) by structural recursion over the plane tree

    Aboulker–Aubian–Charbit, "Digraph Colouring and Arc-Connectivity"
    (arXiv:2304.04690), §9.  This file attacks the LAST parametric piece of the
    concrete Conjecture 9.2 ([two_extremal_hajos.conj_9_2_concrete]): the
    [realises] relation that maps a Def-9.1 plane tree to a single glued
    [diGraphType].  [two_extremal_glue.v] supplied the CONCRETE binary
    vertex-amalgamation [vglue] and the concrete rim [di_cycle], but left the
    GENERAL recursive assembly along an arbitrary plane tree — and the proof that
    the assembled digon graph is the full tree-forest — explicitly OPEN.  This
    file builds that recursive assembly CONCRETELY and proves the two structural
    invariants of the assignment by induction on the plane tree.

    WHAT THIS FILE MAKES CONCRETE (faithfulness ledger):

    - §1 — two FOUNDATIONAL preservation lemmas for the committed [vglue] glue:
      [vglue_loopless] (the binary amalgam of two loopless digraphs is loopless)
      and [vglue_digonfree] (the binary amalgam of two DIGON-FREE digraphs is
      digon-free — there are no arcs across the sum, so an antiparallel pair must
      live entirely inside one block).  Both are PROVED with [Qed] directly from
      [vglue]'s defining arc equation [vglue_arcE].

    - §2 — the CONCRETE recursive fold [glue_tree : ptree -> adigraph].  An
      [adigraph] is a [diGraphType] packaged with a designated ANCHOR vertex (the
      interface vertex along which the parent glues this block).  [glue_tree]
      folds the committed binary [vglue] (via [glue_one]) over the children of a
      node in PLANE (left-to-right) order, starting from the concrete base block
      [leaf_block := di_cycle 3] at each leaf.  This is exactly the
      assignment's RECURSIVE FOLD: realise each child subtree, then amalgamate it
      to the parent across the interface vertex.

    - §3 — the two structural invariants, PROVED by induction on the plane tree
      ([ptree_ind']): [glue_tree_loopless] (every assembled digraph is loopless)
      and [glue_tree_digonfree] (every assembled digraph is digon-free).  From the
      latter and the committed general lemma [digonfree_forest] we obtain THE HARD
      ONE — [glue_tree_digonG_forest]: the digon graph of the WHOLE assembly is a
      forest, for any chosen looplessness witness.  This is the
      [realises_digonG_forest] constraint that [two_extremal_hajos] flagged as the
      hardest, here discharged for the full recursive assembly with [Qed].

    - §4 — the connection to the committed concrete membership/conjecture.  We
      prove that for any LEGAL Def-9.1 datum [t] whose assembly is Eulerian,
      [glue_tree t] realises [t] under the committed [realises_W]
      ([glue_tree_realises_W]); is therefore a [is_two_hajos_treejoin]
      ([glue_tree_is_treejoin]); and lies in the concrete class
      [in_H2_concrete realises_W] via the tree-join constructor
      ([glue_tree_in_H2]).  The LEAF (degenerate) case is UNCONDITIONAL
      ([glue_tree_realises_W_leaf]): a bare leaf assembles to [di_cycle 3], which
      is Eulerian outright.

    THE PRECISE REMAINING GAP (reported honestly, NOT faked — carried as the
    explicit hypothesis [Eulerian (glue_tree t)] wherever it is needed):

      The committed binary [vglue a b] identifies [inl a] with [inr b] inside the
      sum and lifts the arc relation through CANONICAL REPRESENTATIVES:
      [vglue_arc p q := sumarc (repr p) (repr q)].  At the merged class
      [{inl a, inr b}] the representative [repr] picks ONE side; the merged
      vertex therefore inherits the arcs of only THAT side, and the OTHER side's
      arcs incident to the interface vertex are dropped.  Consequently [vglue]
      does NOT add the two interface degrees at the merged vertex, and is NOT
      Eulerian-preserving in general (and neither is [glue_tree]; even
      [glue_tree canon_tree] is not Eulerian).  This is a STRUCTURAL property of
      the committed glue primitive, not a proof-search difficulty: a faithful,
      Eulerian-preserving amalgam would have to UNION both sides' incidences at
      the merged vertex (a different arc relation than the committed [vglue]).
      Looplessness and digon-freeness survive because they are insensitive to the
      representative choice (per-vertex / no-cross-arc facts); the Eulerian
      balance is not.  We therefore carry [Eulerian (glue_tree t)] as an explicit
      hypothesis — exactly the faithful pattern of [two_extremal_glue.realises_W],
      which itself records [Eulerian] as a conjunct rather than deriving it.

    Every theorem below is [Qed]-closed; nothing is [Admitted] or [Axiom]ed. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import generic_quotient.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core two_extremal.
From Digraph Require Import two_extremal_hajos two_extremal_glue.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.

(** ** §1 — foundational preservation lemmas for the committed binary glue [vglue]

    [vglue a b] is the categorical pushout identifying [inl a] with [inr b] inside
    [D₁ + D₂]; its arc relation is [vglue_arc p q = sumarc (repr p) (repr q)].
    Since [sumarc] has NO arcs across the sum ([inl/inr] cases are [false]), both
    looplessness and digon-freeness pass through the glue: a self-loop or an
    antiparallel pair on the glued carrier pulls back, via the representatives, to
    one entirely inside [D₁] or entirely inside [D₂]. *)

(** A self-loop on [vglue] would be a self-loop inside one block. *)
Lemma vglue_loopless (D1 D2 : diGraphType) (a : D1) (b : D2) :
  loopless D1 -> loopless D2 -> loopless (vglue a b).
Proof.
move=> l1 l2 p; rewrite vglue_arcE.
by case: (repr _) => x /=; [exact: l1 | exact: l2].
Qed.

(** A digon on [vglue] would be a digon inside one block (no cross arcs). *)
Lemma vglue_digonfree (D1 D2 : diGraphType) (a : D1) (b : D2) :
  (forall u v : D1, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : D2, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : vglue a b, ~~ ((u --> v) && (v --> u))).
Proof.
move=> df1 df2 u v; rewrite !vglue_arcE.
by case: (repr u) => x; case: (repr v) => y //=.
Qed.

(** ** §2 — the CONCRETE recursive fold [glue_tree]

    An [adigraph] is a digraph with a designated ANCHOR vertex (the interface
    vertex by which the parent glues this block).  [glue_one acc child] amalgamates
    [child] onto [acc] at their two anchors and keeps the image of [acc]'s anchor
    as the new anchor.  [glue_tree] folds [glue_one] over a node's children in
    PLANE order, starting from the base block [leaf_block := di_cycle 3] at each
    leaf — the assignment's recursive fold. *)

(** A digraph together with a designated anchor vertex.  [Set Implicit Arguments]
    would make the carrier field implicit in the constructor (inferable from the
    anchor's type), so we [clear implicits] to keep [ADigraph] taking the carrier
    explicitly — this is what lets us name [di_cycle 3] / [vglue ..] as the carrier
    directly. *)
Record adigraph := ADigraph { ad_car :> diGraphType ; ad_anchor : ad_car }.
Arguments ADigraph : clear implicits.

(** The base block placed at every leaf: the rim triangle [di_cycle 3], anchored
    at [ord0].  It is loopless, digon-free and Eulerian (committed facts). *)
Definition leaf_block : adigraph := ADigraph (di_cycle 3) (@ord0 2).

(** Glue [child] onto [acc] across their anchors; the new anchor is the image of
    [acc]'s anchor under the canonical projection [vinj ∘ inl]. *)
Definition glue_one (acc child : adigraph) : adigraph :=
  ADigraph (vglue (ad_anchor acc) (ad_anchor child))
           (@vinj acc child (ad_anchor acc) (ad_anchor child) (inl (ad_anchor acc))).

(** The recursive fold: amalgamate every child subtree onto the leaf base block,
    in plane order. *)
Fixpoint glue_tree (t : ptree) : adigraph :=
  foldr (fun p acc => glue_one acc (glue_tree p.2)) leaf_block (pt_children t).

(** A bare leaf assembles to the base block. *)
Lemma glue_tree_leaf t : pt_is_leaf t -> glue_tree t = leaf_block.
Proof. by case: t => ch; rewrite /pt_is_leaf /= => /nilP ->. Qed.

(** ** §3 — the structural invariants by induction on the plane tree

    [leaf_block] is loopless / digon-free / Eulerian (committed [di_cycle_*]).
    [glue_one] preserves looplessness and digon-freeness (§1).  Folding over the
    children with [ptree_ind'] propagates both invariants to the whole assembly;
    the digon-graph-forest invariant — THE HARD ONE — then follows from the
    committed general lemma [digonfree_forest]. *)

(** Base-block facts (specialisations of the committed [di_cycle_*]). *)
Lemma leaf_loopless : loopless leaf_block.
Proof. by apply: di_cycle_loopless. Qed.

Lemma leaf_digonfree : forall u v : leaf_block, ~~ ((u --> v) && (v --> u)).
Proof. by apply: di_cycle_digonfree. Qed.

Lemma leaf_Eulerian : Eulerian leaf_block.
Proof. by apply: di_cycle_Eulerian. Qed.

(** [glue_one] preserves looplessness and digon-freeness (the §1 lemmas, on the
    anchored wrapper). *)
Lemma glue_one_loopless (acc child : adigraph) :
  loopless acc -> loopless child -> loopless (glue_one acc child).
Proof. by move=> ? ?; apply: vglue_loopless. Qed.

Lemma glue_one_digonfree (acc child : adigraph) :
  (forall u v : acc, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : child, ~~ ((u --> v) && (v --> u))) ->
  (forall u v : glue_one acc child, ~~ ((u --> v) && (v --> u))).
Proof. by move=> ? ?; apply: vglue_digonfree. Qed.

(** INVARIANT 1 — the whole recursive assembly is loopless. *)
Lemma glue_tree_loopless (t : ptree) : loopless (glue_tree t).
Proof.
elim/ptree_ind': t => ch IH.
rewrite /glue_tree -/glue_tree /=.
elim: ch IH => [_ /=|[l p] s IHs] /=.
- exact: leaf_loopless.
- move=> [Hp Hrest]; apply: glue_one_loopless; [exact: IHs | exact: Hp].
Qed.

(** INVARIANT 2 — the whole recursive assembly is digon-free. *)
Lemma glue_tree_digonfree (t : ptree) :
  forall u v : glue_tree t, ~~ ((u --> v) && (v --> u)).
Proof.
elim/ptree_ind': t => ch IH.
rewrite /glue_tree -/glue_tree /=.
elim: ch IH => [_ /=|[l p] s IHs] /=.
- exact: leaf_digonfree.
- move=> [Hp Hrest]; apply: glue_one_digonfree; [exact: IHs | exact: Hp].
Qed.

(** INVARIANT 3 (THE HARD ONE) — the digon graph of the whole assembly is a
    FOREST, for any chosen looplessness witness.  Discharges the
    [realises_digonG_forest] constraint for [glue_tree] via the committed general
    lemma [digonfree_forest] applied to invariant 2. *)
Lemma glue_tree_digonG_forest (t : ptree) (llD : loopless (glue_tree t)) :
  is_forest [set: digonG llD].
Proof. by apply: digonfree_forest; exact: glue_tree_digonfree. Qed.

(** ** §4 — connection to the committed concrete membership and Conjecture 9.2

    [two_extremal_glue.realises_W t D] records (faithfully) that [D] is loopless,
    digon-free, Eulerian and digon-forest.  Invariants 1–3 supply three of the
    four conjuncts for [D := glue_tree t] outright; the fourth (Eulerian) is the
    precise remaining gap (header §"REMAINING GAP") and is carried as an explicit
    hypothesis.  In the LEAF case it is discharged outright. *)

(** For any plane tree whose assembly is Eulerian, [glue_tree t] realises [t]
    under the committed [realises_W].  Invariants 1–3 are unconditional; only the
    Eulerian conjunct is hypothesised. *)
Theorem glue_tree_realises_W (t : ptree) :
  Eulerian (glue_tree t) -> realises_W t (glue_tree t).
Proof.
move=> eul; exists (@glue_tree_loopless t); split.
- exact: glue_tree_digonfree.
- exact: eul.
- exact: glue_tree_digonG_forest.
Qed.

(** The LEAF case is UNCONDITIONAL: a bare leaf assembles to [di_cycle 3], whose
    Eulerianness is a committed fact. *)
Theorem glue_tree_realises_W_leaf (t : ptree) :
  pt_is_leaf t -> realises_W t (glue_tree t).
Proof.
move=> lf; apply: glue_tree_realises_W.
by rewrite (@glue_tree_leaf t lf); exact: leaf_Eulerian.
Qed.

(** For a LEGAL Def-9.1 datum with an Eulerian assembly, [glue_tree t] is a
    2-Hajós tree-join realisation under [realises_W]. *)
Theorem glue_tree_is_treejoin (t : ptree) :
  is_two_hajos_data (in_H2_concrete realises_W) t ->
  Eulerian (glue_tree t) ->
  is_two_hajos_treejoin (in_H2_concrete realises_W) realises_W (glue_tree t).
Proof.
by move=> hd eul; exists t; split; [exact: hd | exact: glue_tree_realises_W].
Qed.

(** Hence membership of the concrete class [in_H2_concrete realises_W] via the
    tree-join constructor, for a legal datum with an Eulerian assembly. *)
Theorem glue_tree_in_H2 (t : ptree) :
  is_two_hajos_data (in_H2_concrete realises_W) t ->
  Eulerian (glue_tree t) ->
  in_H2_concrete realises_W (glue_tree t).
Proof.
move=> hd eul.
by apply: (inH2_treejoin (t := t)); [exact: hd | exact: glue_tree_realises_W].
Qed.

(** A packaged summary: the three structural invariants of the recursive fold,
    proved unconditionally (the [realises_W] side conditions minus Eulerian). *)
Theorem glue_tree_invariants (t : ptree) (llD : loopless (glue_tree t)) :
  [/\ loopless (glue_tree t),
      (forall u v : glue_tree t, ~~ ((u --> v) && (v --> u)))
    & is_forest [set: digonG llD]].
Proof.
split.
- exact: glue_tree_loopless.
- exact: glue_tree_digonfree.
- exact: glue_tree_digonG_forest.
Qed.
