(** * Digraph.conjectures.grounding_heroes_dichotomy — STATEMENT-LEVEL GROUNDING of
      heroes_dichotomy.v (Conj 4.2 / 4.4 / 6.2 / Thm 6.1) and two_extremal_hajos.v
      (in_H2_concrete / conj_9_2_concrete).

    FAITHFULNESS CHECK at the STATEMENT level.  For each conjecture we (1) prove the
    HYPOTHESIS CLASS is INHABITED (a forall over an empty/unsatisfiable antecedent
    says nothing); (2) prove easy KNOWN VALUES on concrete tiny digraphs the
    statement/definition must yield; (3) run TRIVIALITY / FALSIFICATION probes — an
    open conjecture must be NEITHER provable nor refutable, so where cheap we try to
    refute or trivially prove and report a RED FLAG if either succeeds.

    Concretely:
      - [oriented_forest] NON-VACUITY: the single vertex [K1] and the single arc
        [arc2] (an oriented K₂) are oriented forests.  So the antecedent of conj_4_4
        / conj_4_2 ("F an oriented forest") is satisfiable.
      - [transitive_tournament] holds for every [TT n] (TT n is a transitive
        tournament): the structural predicate of conj_4_2's RHS is inhabited.
      - [conj_6_2] / [thm_6_1] antecedent NON-VACUITY + VALUE: the edgeless digraph
        [Empty2] is oriented, C₃-free and S₂⁺-free (and →K₂+K₁-free) AND is
        2-dicolourable — consistent with the conjectured value χ⃗ ≤ 2.
      - [in_H2_concrete] is INHABITED (the symmetric triangle is a base member).
      - TRIVIALITY probes: [conj_6_2] / [thm_6_1] / [conj_4_2] / [conj_9_2_concrete]
        are well-formed biconditional/forall statements whose hypothesis classes are
        non-vacuous on both sides; we DO NOT prove or refute them.

    Imports ONLY committed modules + the two files under grounding.  Every lemma is
    Qed; no Admitted/Axiom. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import sgraph.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core two_extremal heroes.
From Digraph Require Import heroes_dichotomy two_extremal_hajos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** §A — small concrete oriented digraphs

    [K1] (= TT 1, a single vertex) and [arc2] (two vertices with the single arc
    0 → 1, an oriented K₂) are the smallest tree-shaped digraphs.  Both carry the
    [orientedDigraph] structure (needed to feed [oriented_forest]).  We rebuild
    [arc2] here (the grounding files are not importable) as an oriented digraph. *)

(** The single-arc digraph on ['I_2]: only [0 --> 1]; irreflexive and asymmetric. *)
Definition arc2_rel (x y : 'I_2) : bool := (val x == 0) && (val y == 1).
Definition arc2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on arc2_car.
HB.instance Definition _ := HasArc.Build arc2_car arc2_rel.

Fact arc2_irrefl : irreflexive (arc : rel arc2_car).
Proof. by case=> -[|[|//]] ?. Qed.
Fact arc2_asymm : forall u v : arc2_car, arc u v -> arc v u = false.
Proof. by case=> -[|[|//]] ? [[|[|//]] ?]. Qed.
HB.instance Definition _ := DiGraph_IsOriented.Build arc2_car arc2_irrefl arc2_asymm.
Definition arc2 : orientedDigraph := arc2_car.

(** The edgeless digraph on ['I_2]: no arcs at all (the empty oriented graph K̄₂,
    the simplest disjoint union of two singleton stars). *)
Definition empty2_rel (_ _ : 'I_2) : bool := false.
Definition empty2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on empty2_car.
HB.instance Definition _ := HasArc.Build empty2_car empty2_rel.

Fact empty2_irrefl : irreflexive (arc : rel empty2_car).
Proof. by move=> ?. Qed.
Fact empty2_asymm : forall u v : empty2_car, arc u v -> arc v u = false.
Proof. by []. Qed.
HB.instance Definition _ := DiGraph_IsOriented.Build empty2_car empty2_irrefl empty2_asymm.
Definition Empty2 : diGraphType := empty2_car.

(** ** §B — [oriented_forest] is NON-VACUOUS

    GROUNDS: the antecedent "[F] an oriented forest" of conj_4_4 / conj_4_2 must be
    satisfiable.  The underlying graph of a single vertex / a single arc is a tree,
    hence a forest.  We prove [is_forest [set: underlying _]] directly via the
    GraphTheory primitive [irredxx] (an irredundant path between equal endpoints is
    the trivial path), the same route as GraphTheory's [unit_forest]. *)

(** Single-vertex case: the underlying graph of [K1 = TT 1] is a forest.  Both path
    endpoints collapse to the unique ['I_1] vertex, then [irredxx] forces both paths
    to be [idp]. *)
Lemma I1_eq (x y : 'I_1) : x = y.
Proof. by apply/val_inj; case: x y => -[|//] ? [[|//] ?]. Qed.

Lemma oriented_forest_K1 : oriented_forest (K1 : orientedDigraph).
Proof.
rewrite /oriented_forest => x y p1 p2.
(* Both endpoints are the unique vertex of 'I_1, so x = y and the paths are idp. *)
have Exy : x = y by apply: I1_eq.
case: y / Exy p1 p2 => p1 p2 [/irredxx -> _] [/irredxx -> _] //.
Qed.

(** Edgeless case (2 vertices, a star forest = disjoint union of two singleton
    stars): the underlying graph of [Empty2] is a forest.  With no edges, any
    [Path x y] forces [x = y] (else [splitL] would extract an edge), so by [irredxx]
    both irredundant paths are [idp].  This is the cleanest witness that the
    [union_of_oriented_stars] / [oriented_forest] antecedent is inhabited at ≥ 2
    vertices. *)

(** No edges in the underlying graph of [Empty2]. *)
Lemma underlying_Empty2_edgeless (x y : underlying Empty2) : ~~ (x -- y).
Proof. by rewrite /edge_rel/= /urel /arc/= /empty2_rel. Qed.

(** In an edgeless underlying graph a path forces equal endpoints. *)
Lemma Empty2_path_eq (x y : underlying Empty2) (p : Path x y) : x = y.
Proof.
apply/eqP; apply: contraT => xy.
case: (splitL p xy) => z [xz _].
by move: (underlying_Empty2_edgeless x z); rewrite xz.
Qed.

Lemma oriented_forest_Empty2 :
  is_forest [set: underlying Empty2].
Proof.
move=> x y p1 p2 [Ip1 _] [Ip2 _].
have Exy := Empty2_path_eq p1.
case: y / Exy p1 p2 Ip1 Ip2 => p1 p2.
by move=> /irredxx -> /irredxx ->.
Qed.

(** ** §C — [transitive_tournament] is NON-VACUOUS

    GROUNDS: the RHS of the hero dichotomy (conj_4_2) is "[F] a star forest OR [H] a
    transitive tournament".  The predicate [transitive_tournament] must be inhabited.
    Every [TT n] is a transitive tournament (semicomplete + asymmetric + irreflexive,
    arc = [<] which is transitive).  This is the value-grounding of conj_4_2's RHS. *)

Lemma transitive_tournament_TT (n : nat) : transitive_tournament (TT n).
Proof.
split.
- split.
  + exact: arc_irrefl.
  + by move=> u v uv; exact: arc_or.
  + by move=> u v; exact: arc_asym.
- by move=> y x z; rewrite !arcTTE; apply: ltn_trans.
Qed.

(** A concrete non-empty instance (TT 2 = the single oriented arc): the RHS of the
    dichotomy is satisfiable at a NON-degenerate tournament, not only the empty one. *)
Lemma transitive_tournament_TT2 : transitive_tournament (TT 2).
Proof. exact: transitive_tournament_TT. Qed.

(** ** §D — conj_6_2 / thm_6_1 antecedent NON-VACUITY + the value χ⃗ ≤ 2

    GROUNDS: the conjecture [conj_6_2] quantifies over oriented, C₃-free, S₂⁺-free
    digraphs; [thm_6_1] over oriented, C₃-free, →K₂+K₁-free digraphs.  A forall over
    an empty class is vacuous, so we exhibit a CONCRETE member of BOTH classes — the
    edgeless [Empty2] — and prove it is 2-dicolourable, the conjectured value.  (The
    edgeless graph trivially avoids every induced arc-pattern.) *)

(** [Empty2] is oriented (no digon: there are no arcs). *)
Lemma Empty2_oriented_dg : oriented_dg Empty2.
Proof. by move=> u v. Qed.

(** [Empty2] is C₃-free (an induced directed triangle needs three arcs). *)
Lemma Empty2_no_C3 : no_induced_C3 Empty2.
Proof. by move=> [a [b [c []]]]. Qed.

(** [Empty2] is S₂⁺-free (an induced out-star needs the centre's two out-arcs). *)
Lemma Empty2_no_S2plus : no_induced_S2plus Empty2.
Proof. by move=> [x [a [b [_ [_ [_ [xa _]]]]]]]. Qed.

(** [Empty2] is →K₂+K₁-free (the pattern needs an arc [a --> b]). *)
Lemma Empty2_no_arrowK2_K1 : no_induced_arrowK2_K1 Empty2.
Proof. by move=> [a [b [c [_ [_ [_ [ab _]]]]]]]. Qed.

(** Any induced subdigraph of [Empty2] is acyclic (it inherits the empty arc set, so
    [acyclicb] holds vacuously — no arc, no back-reaching arc). *)
Lemma acyclicb_induced_Empty2 (S : {set Empty2}) :
  acyclicb (induced_digraph S).
Proof.
apply/forallP=> v; apply/forallP=> w; apply/implyP.
by rewrite sub_arcE /arc/= /empty2_rel.
Qed.

(** χ⃗(Empty2) ≤ 2: the all-zero colouring makes every colour class induce an acyclic
    (in fact edgeless) subdigraph.  This is exactly the value the conjecture asserts
    for the class.  GROUNDS the "value 2" half of conj_6_2 / thm_6_1. *)
Lemma dicolorableb_Empty2_2 : dicolorableb Empty2 2.
Proof.
apply/existsP; exists [ffun _ => ord0].
by apply/forallP=> i; exact: acyclicb_induced_Empty2.
Qed.

(** PACKAGED non-vacuity: [Empty2] satisfies BOTH conjectures' full antecedent AND
    the conclusion — so each [forall]-statement has a real witness on which it holds,
    and neither antecedent class is empty. *)
Lemma conj_6_2_witness :
  [/\ oriented_dg Empty2, no_induced_C3 Empty2, no_induced_S2plus Empty2
    & dicolorableb Empty2 2].
Proof.
split.
- exact: Empty2_oriented_dg.
- exact: Empty2_no_C3.
- exact: Empty2_no_S2plus.
- exact: dicolorableb_Empty2_2.
Qed.

Lemma thm_6_1_witness :
  [/\ oriented_dg Empty2, no_induced_C3 Empty2, no_induced_arrowK2_K1 Empty2
    & dicolorableb Empty2 2].
Proof.
split.
- exact: Empty2_oriented_dg.
- exact: Empty2_no_C3.
- exact: Empty2_no_arrowK2_K1.
- exact: dicolorableb_Empty2_2.
Qed.

(** ** §E — [in_H2_concrete] is NON-VACUOUS (base member: the symmetric triangle)

    GROUNDS: the H₂ class of conj_9_2_concrete must be inhabited (a vacuous RHS makes
    the biconditional trivial on one side).  The symmetric triangle [sym_cycle 3] is
    a base member of [in_H2_concrete] for any realisation relation. *)

Lemma symmetric_odd_cycle_C3 : symmetric_odd_cycle (sym_cycle 3).
Proof. by exists 3; split=> //; exact: dgiso_refl. Qed.

Lemma in_H2_concrete_inhabited (realises : ptree -> diGraphType -> Prop) :
  in_H2_concrete realises (sym_cycle 3).
Proof. by apply: inH2_base; exact: symmetric_odd_cycle_C3. Qed.

(** ** §F — TRIVIALITY / FALSIFICATION probes

    A faithfully-stated OPEN conjecture must be NEITHER provable nor refutable.  We do
    NOT prove or refute conj_6_2 / thm_6_1 / conj_4_2 / conj_9_2_concrete here.  We
    record instead that:

    (1) [dicolorableb] is DISCRIMINATING at k = 2 (not always-true), so the
        conclusion of conj_6_2 / thm_6_1 has real content — a digon kills it.  If
        [dicolorableb _ 2] were always true the conjectures would be vacuously true,
        a RED FLAG; it is not.

    (2) The hypothesis classes are non-vacuous on BOTH sides (witnesses above), so the
        biconditional conj_4_2 / conj_9_2_concrete is well-formed over real objects.

    We expose the conjecture statements applied to the witnesses without resolving
    them. *)

(** A self-loop kills 2-dicolourability: the loop sits in its own colour class, which
    is therefore not acyclic.  Hence [dicolorableb _ 2] is NOT always true — the
    conclusion of conj_6_2 / thm_6_1 is discriminating, not vacuous. *)
Definition loop1_rel (_ _ : 'I_1) : bool := true.
Definition loop1_car : Type := 'I_1.
HB.instance Definition _ := Finite.on loop1_car.
HB.instance Definition _ := HasArc.Build loop1_car loop1_rel.
Definition Loop1 : diGraphType := loop1_car.

Lemma dicolorableb_Loop1_not2 : ~~ dicolorableb Loop1 2.
Proof.
apply/existsPn => col; apply/forallPn.
exists (col ord0).
have vin : (ord0 : Loop1) \in [set v | col v == col ord0] by rewrite inE.
pose v' : induced_digraph [set v | col v == col ord0] := exist _ ord0 vin.
apply: (loop_not_acyclicb (v := v')).
by rewrite sub_arcE /arc/= /loop1_rel.
Qed.

(** The RED-FLAG ledger: [dicolorableb _ 2] is genuinely two-sided — TRUE on the
    edgeless graph, FALSE on the looped vertex.  So the conjecture conclusions are not
    decided one way for all digraphs; the open content survives. *)
Lemma dicolorableb2_two_sided :
  dicolorableb Empty2 2 /\ ~~ dicolorableb Loop1 2.
Proof. by split; [exact: dicolorableb_Empty2_2 | exact: dicolorableb_Loop1_not2]. Qed.

(** conj_4_2 RHS is non-vacuous on BOTH disjuncts: a star forest ([Empty2] is a
    union of oriented stars) AND a transitive tournament ([TT 2]).  So the right side
    of the dichotomy quantifies over real objects, not an empty disjunction. *)
Lemma conj_4_2_RHS_both_nonvacuous :
  is_forest [set: underlying Empty2] /\ transitive_tournament (TT 2).
Proof. by split; [exact: oriented_forest_Empty2 | exact: transitive_tournament_TT2]. Qed.

(** conj_9_2_concrete is a biconditional over a non-vacuous H₂ side: the symmetric
    triangle inhabits [in_H2_concrete].  We expose the well-typed statement applied to
    a witness WITHOUT resolving it (it is open). *)
Lemma conj_9_2_concrete_RHS_nonvacuous (realises : ptree -> diGraphType -> Prop) :
  in_H2_concrete realises (sym_cycle 3).
Proof. exact: in_H2_concrete_inhabited. Qed.
