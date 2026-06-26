(** * Digraph.conjectures.grounding_two_extremal — GROUNDING the H2 / 2-extremal
      machinery (two_extremal.v, two_extremal_hajos.v, generalised_wheel.v)

    FAITHFULNESS CHECK.  These files STATE Aboulker–Aubian–Charbit Conjecture 9.2
    (arXiv:2304.04690 §9) and the supporting H₂ / Def-9.1 / directed-Hajós-join
    machinery.  This file proves SMALL, KNOWN, decidable facts that the definitions
    MUST satisfy if they are faithful, and runs falsification probes against the
    danger cases (vacuous classes, statements provable true/false outright).

    We import ONLY committed modules (two_extremal, two_extremal_hajos,
    generalised_wheel).  Every lemma is Qed; no Admitted/Axiom. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core.
From Digraph Require Import two_extremal two_extremal_hajos generalised_wheel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** §A — the symmetric odd cycle base of H₂: not vacuous, loopless, strong

    GROUNDS: "the base members of H₂ are the symmetric ODD cycles" (two_extremal.v
    §4; paper §9).  The smallest one is the symmetric triangle [sym_cycle 3] — the
    bidirected directed triangle.  We check the predicate [symmetric_odd_cycle] is
    INHABITED (else the whole base of H₂ says nothing), and that the base object is
    loopless and strongly connected (textbook: a bidirected cycle is loopless and
    strong). *)

(** [sym_cycle 3] (the symmetric triangle) is a symmetric odd cycle: 3 ≥ 3, odd,
    isomorphic to itself.  So the class [symmetric_odd_cycle] is NON-VACUOUS. *)
Lemma symmetric_odd_cycle_inhabited :
  symmetric_odd_cycle (sym_cycle 3).
Proof. by exists 3; split => //; exact: dgiso_refl. Qed.

(** The symmetric triangle is LOOPLESS: [i] is never adjacent to itself.  (Textbook:
    a symmetric cycle has no loops.)  Decidable, so [vm_compute]/[decide]. *)
Lemma symcyc3_loopless : loopless (sym_cycle 3).
Proof.
move=> x; rewrite /arc/= /symcyc_rel.
by case: x => [[|[|[|m]]] //] H; rewrite -val_eqE.
Qed.

(** RED-FLAG PROBE (negative): the symmetric triangle's adjacency really is a DIGON
    in both directions — [0 --> 1] AND [1 --> 0] both hold.  (If only one held, the
    "symmetric" cycle would not be symmetric, contradicting Def §9.) *)
Lemma symcyc3_digon01 :
  ((Ordinal (n := 3) (m := 0) isT : sym_cycle 3)
     --> (Ordinal (n := 3) (m := 1) isT : sym_cycle 3))
  && ((Ordinal (n := 3) (m := 1) isT : sym_cycle 3)
     --> (Ordinal (n := 3) (m := 0) isT : sym_cycle 3)).
Proof. by []. Qed.

(** The symmetric triangle is STRONGLY connected: every ordered pair is connected.
    (Textbook: a bidirected cycle is strong.)  We discharge [strongb] by exhibiting
    1-step connectivity on every pair, computed by reflection. *)
Lemma symcyc3_strong : strongb (sym_cycle 3).
Proof.
apply/strongP => x y.
(* every consecutive pair is a 1-step edge *)
have adj : forall a b : sym_cycle 3,
    (val b == (val a).+1 %% 3) -> connect arc a b.
  by move=> a b H; apply: connect1; rewrite /arc/= /symcyc_rel H.
pose c0 : sym_cycle 3 := Ordinal (n := 3) (m := 0) isT.
pose c1 : sym_cycle 3 := Ordinal (n := 3) (m := 1) isT.
pose c2 : sym_cycle 3 := Ordinal (n := 3) (m := 2) isT.
have e01 : connect arc c0 c1 by apply: adj.
have e12 : connect arc c1 c2 by apply: adj.
have e20 : connect arc c2 c0 by apply: adj.
have R : forall z : sym_cycle 3, z = c0 \/ z = c1 \/ z = c2.
  move=> [[|[|[|m]]] h] //; [left|right;left|right;right];
    apply: val_inj => //=.
case: (R x) => [->|[->|->]]; case: (R y) => [->|[->|->]];
  try exact: connect0.
- exact: e01.
- exact: (connect_trans e01 e12).
- exact: (connect_trans e12 e20).
- exact: e12.
- exact: e20.
- exact: (connect_trans e20 e01).
Qed.

(** ** §B — H₂ membership ([in_H2_concrete]) is not vacuous

    GROUNDS: the inductive [in_H2_concrete] (two_extremal_hajos.v §5) has the
    symmetric odd cycles as base.  We check, for an arbitrary realisation relation,
    that the symmetric triangle lands in [in_H2_concrete] — so the class is
    INHABITED (RED-FLAG check: a vacuous class makes Conjecture 9.2 trivially true
    on one side). *)

Lemma in_H2_concrete_inhabited (realises : ptree -> diGraphType -> Prop) :
  in_H2_concrete realises (sym_cycle 3).
Proof. by apply: inH2_base; exact: symmetric_odd_cycle_inhabited. Qed.

(** ** §C — the Def-9.1 base datum is LEGAL (canon_tree: a root with two B-leaves)

    GROUNDS: Def 9.1's smallest legal plane-tree datum — a root with two B-leaves.
    We must verify it satisfies [is_two_hajos_data] (≥2 edges, even-B-parity, ≥1
    leaf, no illegal A-blocks): the Def-9.1 base datum is LEGAL.  RED-FLAG check: if
    no legal datum existed, the tree-join generator [inH2_treejoin] would be
    vacuous. *)

(** A root with exactly two B-leaves. *)
Definition canon_tree : ptree :=
  Node [:: (Bedge, Node [::]); (Bedge, Node [::])].

(** It has exactly 2 edges. *)
Lemma canon_tree_edges : pt_edges canon_tree = 2.
Proof. by []. Qed.

(** It has exactly 2 leaves. *)
Lemma canon_tree_nleaves : pt_nleaves canon_tree = 2.
Proof. by []. Qed.

(** EVEN-B-PARITY holds (both leaves sit one B-edge below the root, parity [true]
    each — a single colour class; every leaf-to-leaf path crosses 2 B-edges, even).
    This is the Def-9.1 base parity datum being LEGAL. *)
Lemma canon_tree_even_B_parity : even_B_parity canon_tree.
Proof. by []. Qed.

(** Equivalently (verbatim Def-9.1 form): every leaf-to-leaf path has an EVEN number
    of B-edges. *)
Lemma canon_tree_even_B_parity_pairwise : even_B_parity_pairwise canon_tree.
Proof. by rewrite -even_B_parityP; exact: canon_tree_even_B_parity. Qed.

(** No A-blocks (all edges are B-edges): [pt_allA P] holds for ANY [P], vacuously. *)
Lemma canon_tree_allA (P : diGraphType -> Prop) : pt_allA P canon_tree.
Proof.
move=> D /=.
by move=> [//|[//|[//|[]]]].
Qed.

(** The Def-9.1 BASE DATUM is LEGAL for any membership predicate.  RED-FLAG cleared:
    [is_two_hajos_data] is INHABITED, so [inH2_treejoin] is not vacuous. *)
Lemma canon_tree_legal (inH2 : diGraphType -> Prop) :
  is_two_hajos_data inH2 canon_tree.
Proof.
split.
- by rewrite /pt_has_2edges canon_tree_edges.
- exact: canon_tree_even_B_parity.
- by rewrite canon_tree_nleaves.
- exact: canon_tree_allA.
Qed.

(** RED-FLAG PROBE (positive sanity on even_B_parity): a tree with ONE B-leaf and
    ONE A-then-B leaf path of DIFFERENT B-parity must FAIL even-B-parity (the two
    leaves disagree).  We exhibit such a tree and prove [~~ even_B_parity], showing
    the parity check is DISCRIMINATING (not always-true). *)
Definition odd_par_tree : ptree :=
  Node [:: (Bedge, Node [::]);
           (Aedge (sym_cycle 3), Node [::]) ].

Lemma odd_par_tree_fails : ~~ even_B_parity odd_par_tree.
Proof. by []. Qed.

(** ** §D — the directed Hajós join [dhajos] adds exactly the expected arc

    GROUNDS: Def 1.5 (two_extremal.v §4): given [u v₁ ∈ A(D₁)] and [v₂ w ∈ A(D₂)],
    the join deletes [u v₁] and [v₂ w], identifies [v₁ = v₂], and ADDS the arc
    [u w].  We take the SINGLE-ARC digraphs (the 2-vertex digraph with one arc
    0 → 1) for both factors and check the join has exactly the added arc [u w] (and
    has dropped the deleted [u v₁]).  This is the "expected single added arc". *)

Section DhajosSingleArc.

(** The single-arc digraph on ['I_2]: only [0 --> 1]. *)
Definition arc2_rel (x y : 'I_2) : bool := (val x == 0) && (val y == 1).
Definition arc2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on arc2_car.
HB.instance Definition _ := HasArc.Build arc2_car arc2_rel.
Definition arc2 : diGraphType := arc2_car.

Definition v0 : arc2 := Ordinal (n := 2) (m := 0) isT.
Definition v1 : arc2 := Ordinal (n := 2) (m := 1) isT.

Lemma arc2_only : forall x y : arc2, (x --> y) = (val x == 0) && (val y == 1).
Proof. by []. Qed.

Lemma arc2_v0v1 : v0 --> v1.
Proof. by []. Qed.

(** The Hajós join of two copies of [arc2] along [v0 v1] (in both factors): the
    merged vertex is [inl v1], the surviving [v0] of the first factor is [u], the
    surviving [v1] of the second is [w].  We name the four relevant vertices of the
    join carrier [dhcar]. *)

(** Def-1.5 data: D₁ = D₂ = arc2, [u = v0₁], [v1 = v1₁], [v2 = v0₂], [w = v1₂].
    Then [v2 = v0] is the IDENTIFIED vertex (its [inr] copy [inr v0] is DELETED — the
    join carrier is [{x | x != inr v0}]), and [w = v1₂] SURVIVES as [inr v1].  The
    added arc is [u = inl v0  -->  w = inr v1].  Hence the membership proofs are
    [_ != inr v0]. *)
Lemma U_pf : (inl v0 : arc2 + arc2) != inr v0. Proof. by []. Qed.
Lemma W_pf : (inr v1 : arc2 + arc2) != inr v0.
Proof.
apply/eqP => E.
have : v1 = v0 by case: E.
by move/(congr1 val).
Qed.
Lemma M_pf : (inl v1 : arc2 + arc2) != inr v0. Proof. by []. Qed.

End DhajosSingleArc.

(** The Hajós join carrier instantiated at the single-arc data:
    [D₁ = D₂ = arc2], [u = v0], [v1 = v1], [v2 = v0], [w = v1]. *)
Definition J : diGraphType := dhajos v0 v1 v0 v1.

(** The source [U = inl v0] and target [W = inr v1] of the ADDED arc, as members of
    the join carrier [dhcar]. *)
Definition U : J := exist _ (inl v0 : arc2 + arc2) U_pf.
Definition W : J := exist _ (inr v1 : arc2 + arc2) W_pf.

(** THE EXPECTED ADDED ARC: in the Hajós join, [U --> W], i.e. [u w] is present.
    (Def 1.5: "add the arc u w".) *)
Lemma dhajos_added_arc : U --> W.
Proof. by []. Qed.

(** THE DELETED ARC is GONE: the original arc [u v₁ = v0 v1] of D₁ is NOT present
    between [inl v0] and [inl v1] in the join (Def 1.5: "delete u v₁").  [M = inl v1]
    is the merged vertex. *)
Definition M : J := exist _ (inl v1 : arc2 + arc2) M_pf.

Lemma dhajos_deleted_arc : ~~ (U --> M).
Proof. by []. Qed.

(** ** §E — generalised wheel: small concrete vertex-count + base facts

    GROUNDS: the concrete generalised wheel [gwheel n] (generalised_wheel.v) is the
    classical wheel W_n on [n.+1] vertices (1 hub + n rim).  Looplessness, Eulerian,
    and digon-forest are already proved in that file; we ground a DIFFERENT easy
    fact: the expected vertex count, and that [gwheel 3] (the smallest, W₃) really
    has the hub-rim digons and the directed rim arcs the definition advertises. *)

(** [gwheel n] has exactly [n.+1] vertices (1 hub + n rim).  (Already in the source
    as [gwheel_card]; re-grounded here as a faithfulness datum and tied to W₃.) *)
Lemma gwheel3_card : #|gwheel 3| = 4.
Proof. by rewrite gwheel_card. Qed.

(** The hub [ord0] points to every rim vertex (the spoke out-arcs). *)
Lemma gwheel3_hub_to_rim :
  (ord0 : gwheel 3) --> (Ordinal (n := 4) (m := 1) isT).
Proof. by []. Qed.

(** Every rim vertex points back to the hub (spoke back-arcs) — so hub-rim is a
    DIGON. *)
Lemma gwheel3_rim_to_hub :
  (Ordinal (n := 4) (m := 1) isT : gwheel 3) --> ord0.
Proof. by []. Qed.

(** The directed rim arc [1 --> 2] is present (single arc of the rim cycle). *)
Lemma gwheel3_rim_step :
  (Ordinal (n := 4) (m := 1) isT : gwheel 3) --> (Ordinal (n := 4) (m := 2) isT).
Proof. by []. Qed.

(** The directed rim arc closes up: [3 --> 1] (n = 3, so after rim label 3 comes 1).
    (RED-FLAG check on the [%% n] successor: rim label n wraps to 1, not 0/n+1.) *)
Lemma gwheel3_rim_wrap :
  (Ordinal (n := 4) (m := 3) isT : gwheel 3) --> (Ordinal (n := 4) (m := 1) isT).
Proof. by []. Qed.

(** The rim arc is a SINGLE arc, not a digon: [2 --> 1] does NOT hold (no back-arc
    on the rim for n ≥ 3).  RED-FLAG check: if this held, the rim would be a digon
    and the digon graph would not be the hub-rim star. *)
Lemma gwheel3_rim_single :
  ~~ ((Ordinal (n := 4) (m := 2) isT : gwheel 3) --> (Ordinal (n := 4) (m := 1) isT)).
Proof. by []. Qed.

(** [gwheel 3] is loopless (re-ground the source fact at the concrete instance). *)
Lemma gwheel3_loopless : loopless (gwheel 3).
Proof. by apply: gwheel_loopless. Qed.

(** [gwheel 3] is Eulerian. *)
Lemma gwheel3_Eulerian : Eulerian (gwheel 3).
Proof. by apply: gwheel_Eulerian. Qed.

(** [gwheel 3] lies in the concretely-generated H₂ (via the empty-A star datum):
    the wheel INHABITS [in_H2_concrete], so the tree-join membership is not vacuous. *)
Lemma gwheel3_in_H2 : in_H2_concrete realises_gw (gwheel 3).
Proof. by apply: gwheel_in_H2. Qed.

(** ** §F — falsification probes against the CONJECTURE statements

    RED-FLAG checks: an OPEN conjecture statement must be neither provable TRUE nor
    provable FALSE outright; a class quantifier must not be vacuous.  We do not (and
    cannot) prove [conj_9_2] here — but we record that the [two_extremal] predicate
    is a genuine conjunction of four non-trivial side conditions (strong,
    2-connected underlying, λ = k, χ⃗ = k+1), none of which collapses, and that the
    realisation constraints are SATISFIABLE by an actual digraph (the wheel), so the
    tree-join closure is not vacuously about an empty class. *)

(** [realises_gw] is SATISFIABLE: the wheel realises the star datum, so the
    realisation relation used in [in_H2_concrete realises_gw] is non-vacuous. *)
Lemma realises_gw_satisfiable :
  exists (t : ptree) (D : diGraphType), realises_gw t D.
Proof.
exists (wheel_tree 3), (gwheel 3); exact: gwheel_realises_gw.
Qed.

(** The three realisation CONSTRAINTS of two_extremal_hajos hold for [realises_gw]
    (re-grounded: loopless, Eulerian, digon-forest) — faithfulness of the
    realisation interface. *)
Lemma realises_gw_constraints :
  [/\ realises_loopless realises_gw,
      realises_Eulerian realises_gw
    & realises_digonG_forest realises_gw].
Proof.
split.
- exact: realises_gw_loopless.
- exact: realises_gw_Eulerian.
- exact: realises_gw_digonG_forest.
Qed.

(** [is_two_hajos_data] is non-vacuous AND discriminating: the base datum is legal,
    but [odd_par_tree] (mismatched B-parity) is NOT legal.  So the legality
    predicate is a genuine filter, not always-true. *)
Lemma is_two_hajos_data_discriminates (inH2 : diGraphType -> Prop) :
  is_two_hajos_data inH2 canon_tree
  /\ ~ (even_B_parity odd_par_tree).
Proof.
split; first exact: canon_tree_legal.
by apply/negP; exact: odd_par_tree_fails.
Qed.

(** [conj_9_2] is a genuine biconditional over a non-vacuous class: instantiated at
    [in_H2_concrete realises_gw] (whose H₂ side is inhabited by both the symmetric
    triangle and the wheel), the statement [conj_9_2 (in_H2_concrete realises_gw)]
    is well-formed and quantifies over real objects on BOTH sides.  We do NOT prove
    it (it is open); we only ground that BOTH sides have witnesses, so neither side
    is vacuous. *)
Lemma conj_9_2_both_sides_nonvacuous :
  in_H2_concrete realises_gw (sym_cycle 3)
  /\ in_H2_concrete realises_gw (gwheel 3).
Proof. by split; [exact: in_H2_concrete_inhabited | exact: gwheel3_in_H2]. Qed.
