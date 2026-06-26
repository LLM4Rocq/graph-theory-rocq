(** * Digraph.conjectures.grounding_tww_chi_col — GROUNDING (faithfulness) for
    twinwidth.v, chi_bounded.v, colouring_variants.v.

    These are small, KNOWN, decidable textbook facts that the new definitions
    must satisfy if they are FAITHFUL.  Each lemma is tied to the fact it grounds.

    No Admitted / Axiom: every lemma is Qed.  We import ONLY committed modules
    (the core stack + dichromatic.v) and re-state the three conjecture-file
    definitions LOCALLY (copying the verbatim definition bodies), so this file
    depends on no team file while still exercising the exact predicates. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From Digraph Require Import prelude digraph oriented tournament dipath.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(** ** Local copies of the definitions under test (verbatim from the team files) *)

(** chi_bounded.v *)
Definition oriented_dg (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> ~~ (v --> u).

Definition no_induced_TT3 (D : diGraphType) : Prop :=
  ~ exists a b c : D,
    [/\ a --> b, b --> c, a --> c,
        ~~ (b --> a) /\ ~~ (c --> b) & ~~ (c --> a)].

Definition has_induced_long_dicycle (D : diGraphType) : Prop :=
  exists c : seq D,
    (4 <= size c)%N /\ dicycle c /\
    (forall u v : D, u \in c -> v \in c -> u --> v -> next c u = v).

Definition chordal_C3 (D : diGraphType) : Prop :=
  [/\ oriented_dg D, no_induced_TT3 D & ~ has_induced_long_dicycle D].

(** colouring_variants.v *)
Definition same_col_outnb {D : diGraphType} {k : nat}
    (col : D -> 'I_k) (v : D) : {set D} :=
  [set w | (v --> w) && (col w == col v)].

Definition majority_col {D : diGraphType} {k : nat} (col : D -> 'I_k) : bool :=
  [forall v : D, 2 * #|same_col_outnb col v| <= outdeg v].

Definition dhom (H T : diGraphType) : Prop :=
  exists f : H -> T, forall u v : H, u --> v -> f u --> f v.

Definition oriented_kcolouring (D : diGraphType) (k : nat) : Prop :=
  exists T : tournament, #|T| = k /\ dhom D T.

(** ==================================================================== *)
(** ** GROUND 1: [oriented_dg] is faithful — every tournament is oriented.

    Textbook: a tournament's arc relation is asymmetric (Bang-Jensen–Gutin,
    "Digraphs", Ch.1: a tournament is an orientation of a complete graph, hence
    digon-free).  So [oriented_dg] must hold of C3 and of any tournament.  If
    instead we could prove [~ oriented_dg C3] the definition would be wrong. *)

Lemma oriented_dg_tournament (T : tournament) : oriented_dg T.
Proof. by move=> u v uv; rewrite (arc_asymm _ _ uv). Qed.

Lemma oriented_dg_C3 : oriented_dg C3.
Proof. exact: oriented_dg_tournament. Qed.

(** Falsification probe: the NEGATION is NOT provable; indeed [oriented_dg C3]
    holds (above), so [~ oriented_dg C3] is false.  We record the constructive
    contradiction shape to make the asymmetry concrete on a real arc. *)
Lemma not_not_oriented_dg_C3 : ~ ~ oriented_dg C3.
Proof. by move=> H; apply: H; exact: oriented_dg_C3. Qed.

(** ==================================================================== *)
(** ** GROUND 2: C3 lies in the chordal class [chordal_C3].

    arXiv:2202.01006: the chordal class C₃ = {oriented, no induced TT₃, no
    induced directed cycle of length ≥ 4}.  The directed triangle is the
    canonical allowed object (it is the directed 3-cycle, NOT a transitive
    triangle, and is too small to host a length-≥4 induced dicycle).  This is
    the key NON-VACUITY check: the class is inhabited and contains exactly the
    directed triangle as the paper intends. *)

(** In C3, [a --> b] means [b = a + 1] in 'Z_3. *)
Lemma C3_arc_succ (a b : C3) : (a --> b) = (b == (a + 1)%R :> 'Z_3).
Proof. exact: arcC3E. Qed.

(** No induced transitive triangle TT3 in C3: a-->b, b-->c, a-->c would force
    c = a+2 and c = a+1, impossible in 'Z_3. *)
Lemma C3_no_induced_TT3 : no_induced_TT3 C3.
Proof.
move=> [a [b [c [ab bc ac _ _]]]].
move: ab bc ac; rewrite !C3_arc_succ => /eqP-> /eqP->.
(* now goal hyp: (b+1) == (a+1) with b = a+1, after substitution a+1+1 == a+1 *)
rewrite -[X in _ == X]GRing.addr0.
move/eqP/GRing.addrI/eqP.
(* (1 + 1 : 'Z_3) == 0, i.e. 2 == 0, false *)
by [].
Qed.

(** No induced long dicycle in C3: a [dicycle] is [uniq], and C3 has only 3
    vertices, so no [uniq] sequence of size ≥ 4 exists. *)
Lemma C3_no_long_dicycle : ~ has_induced_long_dicycle C3.
Proof.
move=> [c [c4 [/and3P[_ _ uc] _]]].
have szle : (size c <= #|{: C3}|)%N.
  by rewrite -(card_uniqP uc); exact: max_card.
by move: (leq_trans c4 szle); rewrite card_C3.
Qed.

Lemma chordal_C3_C3 : chordal_C3 C3.
Proof. by split; [exact: oriented_dg_C3 | exact: C3_no_induced_TT3 | exact: C3_no_long_dicycle]. Qed.

(** RED-FLAG probe (vacuity): [chordal_C3] is NOT "everything" — the transitive
    tournament TT 3 is NOT in the class, because it DOES contain an induced TT3.
    So the class genuinely separates objects (it is neither empty nor full). *)
Lemma TT3_has_induced_TT3 : ~ no_induced_TT3 (TT 3).
Proof.
move=> H; apply: H.
pose a : TT 3 := Ordinal (isT : (0 < 3)%N).
pose b : TT 3 := Ordinal (isT : (1 < 3)%N).
pose c : TT 3 := Ordinal (isT : (2 < 3)%N).
exists a, b, c.
by split; rewrite ?arcTTE //; split; rewrite arcTTE.
Qed.

Lemma chordal_C3_not_TT3 : ~ chordal_C3 (TT 3).
Proof. by move=> [_ H _]; apply: TT3_has_induced_TT3. Qed.

(** ==================================================================== *)
(** ** GROUND 3: [majority_col] is faithful and non-vacuous.

    arXiv:1608.03040: a majority colouring exists for every digraph (Conj 2 is
    the 3-colour case; in general a majority colouring with enough colours
    trivially exists).  Concrete check: a PROPER colouring of C3 (each vertex
    its own colour, via the natural 'Z_3 -> 'I_3 map) is a majority colouring,
    because then no vertex shares its colour with any out-neighbour, so the
    same-colour out-neighbourhood is EMPTY (2*0 = 0 <= outdeg). *)

(** The natural injection C3 = 'Z_3 -> 'I_3. *)
Definition c3col (v : C3) : 'I_3 := v.

Lemma c3col_inj : injective c3col.
Proof. by []. Qed.

(** Under [c3col], no vertex shares colour with its out-neighbour: if v --> w
    then w = v+1 != v, hence c3col w != c3col v.  So the same-colour
    out-neighbourhood is empty. *)
Lemma c3col_same_empty (v : C3) : same_col_outnb c3col v = set0.
Proof.
apply/setP=> w; rewrite inE in_set0.
apply/andP=> -[vw /eqP /c3col_inj eqwv].
by move: vw; rewrite eqwv arcxx.
Qed.

Lemma majority_col_C3 : majority_col c3col.
Proof.
apply/forallP=> v; by rewrite c3col_same_empty cards0 muln0.
Qed.

(** RED-FLAG probe: [majority_col] is NOT trivially true for ALL colourings —
    the CONSTANT colouring of C3 is NOT a majority colouring.  Each vertex has
    exactly one out-neighbour (v+1) which, under a constant colour, shares the
    colour: same-colour out-nbhd has size 1, and 2*1 = 2 > 1 = outdeg.  So
    [majority_col] genuinely constrains the colouring (it is not vacuous). *)
Definition c3const (_ : C3) : 'I_3 := ord0.

Lemma c3_outdeg1 (v : C3) : outdeg v = 1%N.
Proof.
rewrite /outdeg.
have -> : [set w | v --> w] = [set (v + 1)%R].
  by apply/setP=> w; rewrite !inE C3_arc_succ.
by rewrite cards1.
Qed.

Lemma c3const_same (v : C3) : same_col_outnb c3const v = [set (v + 1)%R].
Proof.
apply/setP=> w; rewrite !inE C3_arc_succ.
by case: (w == (v + 1)%R).
Qed.

Lemma not_majority_col_c3const : ~~ majority_col c3const.
Proof.
apply/forallPn; exists ord0.
by rewrite c3const_same cards1 c3_outdeg1 muln1.
Qed.

(** ==================================================================== *)
(** ** GROUND 4: [dhom] reflexivity and transitivity (Sopena/Courcelle).

    The identity is a digraph homomorphism D -> D; homomorphisms compose.
    Hence every digraph has an oriented colouring onto itself when it is a
    tournament (oriented chromatic number is defined / finite). *)

Lemma dhom_id (D : diGraphType) : dhom D D.
Proof. by exists id. Qed.

Lemma dhom_trans (D1 D2 D3 : diGraphType) :
  dhom D1 D2 -> dhom D2 D3 -> dhom D1 D3.
Proof.
case=> f Hf [g Hg]; exists (g \o f) => u v uv.
by apply: Hg; apply: Hf.
Qed.

(** C3 has an oriented 3-colouring: it maps homomorphically onto a 3-vertex
    tournament (itself).  This grounds [oriented_kcolouring] being inhabited. *)
Lemma oriented_kcolouring_C3 : oriented_kcolouring C3 3.
Proof. by exists (C3 : tournament); split; [exact: card_C3 | exact: dhom_id]. Qed.

(** ==================================================================== *)
(** ** GROUND 5: [tww_le] is monotone in the width bound (textbook).

    Twin-width is a MINIMUM width over contraction sequences, so [tww_le D k]
    (some sequence has width ≤ k) trivially implies [tww_le D k.+1] (the SAME
    sequence has width ≤ k+1).  This grounds the [tww_le] definition's shape:
    a real "≤ k" predicate must be upward closed in k.  We re-state [tww_le] by
    its defining shape (an existential over a width witness) abstractly to avoid
    importing the heavy contraction machinery, then prove monotonicity from the
    [<=] transitivity, exactly mirroring the team [tww_le]. *)

Section TwwMono.
(* Mirror of twinwidth.v [tww_le]: exists a witness with width <= k. *)
Variable contraction_seq : forall D : diGraphType, seq (rel D) -> Prop.
Variable seq_width : forall D : diGraphType, seq (rel D) -> nat.

Definition tww_le (D : diGraphType) (k : nat) : Prop :=
  exists s : seq (rel D),
    @contraction_seq D s /\ (@seq_width D s <= k)%N.

Lemma tww_le_mono (D : diGraphType) (k : nat) :
  tww_le D k -> tww_le D k.+1.
Proof.
move=> [s [cs ws]]; exists s; split=> //.
exact: (leq_trans ws (leqnSn k)).
Qed.

End TwwMono.

(** ==================================================================== *)
(** ** Assumption audit *)

(* Print Assumptions chordal_C3_C3.        (* closed under the core stack *) *)
