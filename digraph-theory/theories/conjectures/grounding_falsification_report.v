(** * Digraph.conjectures.grounding_falsification_report

    SYSTEMATIC TRIVIALITY / FALSIFICATION SWEEP over every conjecture [_statement]
    (and the named [conj_*] defs) in theories/conjectures/*.v.

    METHOD (the "open conjecture must be NEITHER provable NOR refutable" probe):
    for each statement we tried, on tiny/edgeless witnesses and with degenerate
    binder choices, to (a) prove the statement outright [Goal <stmt>], or
    (b) prove its negation [Goal ~ <stmt>], or (c) check the hypothesis class is
    vacuous.  If (a) or (b) closes cheaply the statement is MIS-ENCODED (says
    nothing / is wrong) — a RED FLAG, exactly the failure mode that previously
    caught the packing Bermond-Thomassen / Hoang-Reed empty-digraph bug.

    ===================================================================
    RED FLAGS FOUND (3) — ALL FIXED.  This sweep originally proved each of the three
    statements TRIVIALLY PROVABLE (the [*_is_trivial] theorems, Qed).  The source
    statements have since been CORRECTED (see the per-RF "FIX" notes below), so those
    refutations no longer type-check against the fixed statements — which is itself the
    confirmation that the fix landed — and have been removed from this file.
    ===================================================================

    [RF1] reals_growth.is_tvec is faithful (pins tv to the MAX, both an upper and an
          attained clause), BUT chi_bounded.tvec_core_statement is its weakened
          "core" and is TRIVIALLY PROVABLE with the constant binder [h := fun _ => 1]:

            tvec_core_statement :=
              exists h, forall n>0, exists D,
                [/\ #|D|=n, oriented_dg D, underlying_triangle_free D
                  & ~~ dicolorableb D (h n).-1].

          With [h n = 1] the last clause is [~~ dicolorableb D 0].  For a NONEMPTY
          digraph [dicolorableb D 0] is [false] (it needs a function into ['I_0],
          impossible since the domain is inhabited), so [~~ dicolorableb D 0] is
          [true] for FREE.  The edgeless digraph on ['I_n] is oriented &
          underlying-triangle-free of every order n, so the existential closes.
          ⇒ The statement says NOTHING about the conjectured growth of t⃗(n); the
          "attained" content evaporated through [.-1] at [h≡1].  Proven below as
          [tvec_core_is_trivial].  (FIX: state it as [is_tvec]-style, pinning the
          value, or drop the existential over [h] and bound [h n] below, e.g.
          [exists h, (forall n, n <= 2 -> ... ) /\ 2 <= h n /\ ...]; the real
          conjecture wants t⃗(n) = Θ(√(n/log n)), captured faithfully already in
          reals_growth.conj4_tvec_*_statement via [is_tvec].)

    [RF2] Symmetrically, chi_bounded.avec_core_statement is TRIVIALLY PROVABLE with
          [g := fun _ => 1]:

            avec_core_statement :=
              exists g, (forall n>0, 0 < g n) /\
                forall D, 0<#|D| -> oriented_dg D -> underlying_triangle_free D ->
                  acyclic_number_ge D (g #|D|).

          [g n = 1] satisfies [0 < g n], and [acyclic_number_ge D 1] holds for EVERY
          oriented (hence loopless) digraph: a singleton vertex set [ [set v] ]
          induces a one-vertex subdigraph whose only possible arc is a loop, excluded
          by irreflexivity, so it is [acyclicb].  ⇒ The lower-bound content (a⃗(n)
          GROWS) is lost; the binder [g] can be the constant 1.  Proven below as
          [avec_core_is_trivial].  (FIX: as RF1 — pin [g] to the true minimum
          acyclic number [is_avec], or force [g n -> ∞]; the genuine a⃗(n) =
          Θ(√(n·log n)) is faithfully reals_growth.conj3_avec_*_statement.)

    [RF3] classic_core.splitting_min_outdegree_statement (Alon's splitting
          conjecture) is TRIVIALLY PROVABLE with [f := fun d => d] and the
          DEGENERATE split [V1 := setT] (so V2 = ∅):

            splitting_min_outdegree_statement :=
              exists f, forall D d, (forall v, f d <= outdeg v) ->
                exists V1, (forall v in V1,  d <= outdeg_in V1 v) /\
                           (forall v notin V1, d <= outdeg_in (~:V1) v).

          With [V1 = setT]: the second clause is VACUOUS (no [v ∉ setT]); the first is
          [d <= outdeg_in setT v = outdeg v] (lemma [outdeg_inT]), given by the
          hypothesis at [f d = d].  ⇒ The statement is satisfied by the trivial
          "don't split at all" bipartition; the conjecture's content (a bipartition
          into two parts EACH inducing min out-degree ≥ d) is not enforced because the
          empty side's constraint is vacuous and [V1] is allowed to be the whole set.
          Proven below as [splitting_is_trivial].  (FIX: require BOTH sides nonempty,
          e.g. [V1 != set0 /\ V1 != setT], matching Alon's "split into two parts".)

    ===================================================================
    STATEMENTS THAT RESISTED BOTH PROBES (faithful as far as the sweep goes)
    ===================================================================
    For each below the cheap-proof and cheap-refute attempts both failed, and the
    hypothesis class is inhabited (non-vacuous).  [resisted] = neither [Goal <stmt>]
    nor [Goal ~ <stmt>] closed under a few tactics / tiny instances; this is the
    EXPECTED outcome for a faithfully-stated open problem (one cannot Qed
    "unprovable", so these carry no theorem here — only the note).

    classic_core.v
      - seymour_second_neighbourhood_statement   resisted (guarded 0<#|D|; ∀ oriented
            graph form, content is the Seymour vertex — open).
      - caccetta_haggkvist_statement             resisted (k=0 slice is vacuous via
            nat [r=0] excluded by [0<r]; the ⌈n/r⌉ bound is genuine).
      - caccetta_haggkvist_triangle_statement    resisted (small n make the degree
            hypothesis [#|D| <= 3·outdeg] UNSATISFIABLE, so those slices are vacuous,
            but the class is inhabited at larger n where it is the open CH triangle).
      - long_dicycle_diregular_statement         resisted.
      - jackson_hamilton_small_diregular_statement resisted (guarded 2<d).
      - stable_meeting_longest_dipaths_statement resisted (one stable set meeting ALL
            longest dipaths — Laborde–Payan–Xuong, open; setT is not stable, set0
            meets nothing).

    clique_cluster.v
      - conjecture_5_10_statement   resisted (∀k≥3 arbitrarily-large k-ω̄-critical T).
      - question_5_9_statement      resisted (the bound [ell] cannot be dodged:
            [f]/[ell] are functions of k while T is universal & unbounded).
      - conjecture_5_8_statement    resisted.
      - dom_omega_cluster_statement resisted (no choice of [f] makes [f k <= domnum T]
            vacuous — domnum is unbounded over tournaments).

    colouring_variants.v
      - majority_3col_statement / _tournament_ / _eulerian_ / majority_k1col_statement
            all resisted (∃ majority colouring per digraph — open; no constant colour
            trivially majority).
      - oriented_chromatic_planar_bounded_statement resisted (collapsing to one colour
            needs a loop in the tournament image — impossible; the constant k is the
            open Courcelle/Sopena content).
      - mono_reach_or_rainbow_statement  resisted.
      - sands_sauer_woodrow_statement    resisted as a whole: its [k=0] slice IS
            degenerate (for nonempty D no [arc_colouring D 0] exists ⇒ vacuous; for
            D=∅ pick f=0, S=∅) but the statement is [∀k, ∃f, …] so k≥1 carries the
            real content — NOT trivially provable overall.  (Noted, not a red flag.)

    chi_bounded.v
      - conj2_1605_statement / conj4_1605_statement / conj5_1605_statement resisted
            (χ-boundedness ⟺ forest; open).
      - chordal_not_dichromatic_bounded_statement resisted (a NEGATED boundedness —
            needs the unbounded-χ⃗ chordal family; not cheaply (dis)provable).
      - m3_landmark_statement resisted: it asks for a CONCRETE oriented triangle-free
            non-2-dicolourable digraph (the m(3) witness) — genuinely hard to PRODUCE
            (so not cheaply provable) and TRUE (so not refutable).  Faithful.  NOTE:
            this is the correctly-stated sibling of RF1 — here the witness must beat
            [dicolorableb D 2] (a real bound), with NO existential-binder escape; that
            is exactly why it resists while [tvec_core] (escape via [h≡1, .-1]) does
            not.  The contrast pinpoints RF1's defect.

    sad.v
      - bang_jensen_yeo_SAD_statement resisted (guarded 0<#|D|; ∃K — open).
      - WC3_statement                resisted (guarded 0<#|D|; the K=3 form).
      - CL1_statement                resisted (a SAD-from-SAD lifting; relative).

    packing.v
      - bermond_thomassen_statement / hoang_reed_statement resisted (now guarded
            0<#|D| — the previously-found empty-digraph bug; their k=0 slices are
            trivially witnessed by the empty packing [P=[::]], but [∀k] keeps k≥1
            content, so NOT trivially provable overall).
      - woodall_statement / linial_berge_statement / erdos_posa_long_dicycles_statement
            resisted (linial_berge: S=∅ forces [pp_knorm k Q = 0] requiring a
            path-partition of a NONEMPTY V with knorm 0 — impossible, so the empty
            certificate does not trivialize it; erdos_posa: the transversal [setT] has
            size #|D| which no fixed [t] bounds uniformly).

    reals_growth.v
      - conj3_avec_Theta_statement / conj3_avec_exists_statement
      - conj4_tvec_Theta_statement / conj4_tvec_exists_statement
            all resisted: these are the FAITHFUL Θ-envelope forms (they quantify over
            [is_avec]/[is_tvec], which pin the value to the genuine extremal min/max,
            and demand a two-sided real-Landau Θ bound).  This is precisely the right
            encoding that RF1/RF2's "core" forms failed to be.
      - ec_log_statement / ec_log_c6_statement resisted (guarded 3<=#|D|).
      - prob6_unvd_statement (= unvd.prob_6) resisted.

    path_fas.v
      - pathFAS_iff_LFO_statement / LFO_iff_34transversal_statement resisted (open
            reductions; both sides nontrivial).
      - matchingFAS_iff_dw1_statement resisted (a KNOWN equivalence stated as target).
      - minimal_LFO_no_infinite_statement resisted (∞-many vertex-minimal obstructions
            — open; no [N] bound).

    twinwidth.v / twinwidth_ordered.v
      - conj_3_12_statement / conj_3_12_classwise resisted ([f] is a fixed [nat->nat];
            [f(omegabar T)] cannot uniformly dominate the unbounded [#|T|]).
      - conj_3_13_statement / conj_3_16_statement resisted (parametric over abstract
            [otww_le]/[bst_order]; the binding [f] is open).
      - conj_3_13_concrete / conj_3_16_concrete / concrete_* resisted.

    unvd.v
      - conj_9 resisted (∃ absolute C; the unvd ratio bound is open).
      - prob_6 resisted (∀ rational α, ∃ polynomial bound; open).

    heroes_dichotomy.v / heroes.v
      - conj_6_2 / thm_6_1 resisted (2-dicolourability of the C₃/S₂⁺(resp. arrowK₂+K₁)
            free oriented class — open / proved-landmark target; not cheaply settled).
      - conj_4_4 / conj_4_2 resisted (heroic-set / hero dichotomy — open).
      - berger_characterization resisted (a ⟺ over χ⃗-boundedness; open target).

    two_extremal.v / two_extremal_hajos.v / two_extremal_glue.v / glue_*.v
      - conjecture_P, two_extremal_digonG_forest, three_connected_*, H6_no_full_cover,
        three_connected_generalised_wheel, conj_9_2 (parametric over [in_H2]),
        conj_9_2_concrete / conj_9_2_treejoin / conj_9_2_glued(_e) all resisted
            (these are biconditional 2-extremal⟺H₂ targets and their structural
            sub-lemmas, parametric over abstract gluing/membership predicates — no
            degenerate binder collapses them).

    generalised_wheel.v
      - generalised_wheel_pred / realises_gw resisted (structural predicates; not
            stand-alone Prop conjectures with a binder to collapse).

    long_dipath.v
      - cheng_keevash_conj1_statement resisted (ℓ(D) >= 2d under δ⁺ >= d; guarded
            0<#|D|; the δ=3 instance is separately PROVED, the general case open).

    ===================================================================
    SCOPE NOTE.  This file imports ONLY the committed modules needed for the three
    RED-FLAG proofs (the trivial-provability witnesses).  Every "resisted" entry was
    probed in throwaway files against the committed statements; no theorem is emitted
    for them (one cannot Qed "unprovable").  The three theorems below are axiom-free
    ([Print Assumptions] = "Closed under the global context").                       *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath.
From Digraph Require Import dichromatic heroes chi_bounded classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edgeless digraph on ['I_n] — an oriented, underlying-triangle-free witness of
       every order [n] (used by RF1).  Its arc relation is constantly [false]. *)
Section Edgeless.
Variable n : nat.
Definition Edg : Type := 'I_n.
HB.instance Definition _ := Finite.on Edg.
HB.instance Definition _ := HasArc.Build Edg [rel u v : 'I_n | false].
End Edgeless.

Lemma edg_card n : #|{: Edg n}| = n.
Proof. by rewrite card_ord. Qed.

Lemma edg_noarc n (u v : Edg n) : ~~ (u --> v).
Proof. by []. Qed.

Lemma edg_oriented n : oriented_dg (Edg n : diGraphType).
Proof. by move=> u v; rewrite (negbTE (edg_noarc u v)). Qed.

Lemma edg_tfree n : underlying_triangle_free (Edg n : diGraphType).
Proof.
rewrite /underlying_triangle_free /no_underlying_Kl => -[S [cardS clS]].
have h2 : (1 < #|S|)%N by rewrite cardS.
have [a [b [aS bS ab]]] := card_gt1P h2.
have hab : a -- b by apply: clS.
move: hab; rewrite /edge_rel/= /urel/=.
by rewrite !(negbTE (edg_noarc _ _)) /= andbF.
Qed.

(** ** [RF1]/[RF2]/[RF3] — FOUND BY THIS SWEEP, NOW FIXED.

    The three [*_is_trivial] refutations originally proved here (each [Qed], axiom-free)
    showed the source statements were trivially provable by a WRONG witness, hence
    mis-encoded:
      - [tvec_core_statement] held with [h := fun _ => 1] (the attained clause evaporated
        through [.-1]);
      - [avec_core_statement] held with [g := fun _ => 1] (the lower bound was met by a
        singleton acyclic set);
      - [splitting_min_outdegree_statement] held with [V1 := setT] (the complement-side
        constraint was vacuous).
    FIX (applied to the sources): [tvec_core]/[avec_core] now carry the matching
    upper/lower-bound clause pinning [h]/[g] to the true max/min t⃗(n)/a⃗(n) (the constant-1
    witness is rejected); [splitting_min_outdegree_statement] now requires [V1 != set0] and
    [V1 != [set: D]] (a genuine bipartition).  Consequently the three [*_is_trivial] proofs
    NO LONGER TYPE-CHECK against the fixed statements — that failure IS the confirmation the
    fix landed — so they have been removed.  We retain below the two genuinely-valid helper
    lemmas they used (correct standalone facts about acyclicity, not refutations). *)

(** A singleton induced subdigraph of an oriented (hence loopless) digraph is acyclic
    — its only candidate arc is a self-loop, excluded by irreflexivity. *)
Lemma acyclicb_singleton (D : diGraphType) (v : D) :
  oriented_dg D -> acyclicb (induced_digraph [set v]).
Proof.
move=> orD; apply/forallP => a; apply/forallP => b; apply/implyP.
rewrite sub_arcE => arcab.
have va : val a = v by apply/set1P; exact: (valP a).
have vb : val b = v by apply/set1P; exact: (valP b).
move: arcab; rewrite va vb => loop.
by have := orD v v loop; rewrite loop.
Qed.

Lemma acyclic_number_ge1 (D : diGraphType) (v : D) :
  oriented_dg D -> acyclic_number_ge D 1.
Proof.
move=> orD; rewrite /acyclic_number_ge /has_acyclic_set.
apply/existsP; exists [set v]; rewrite cards1 leqnn /=.
exact: acyclicb_singleton.
Qed.
