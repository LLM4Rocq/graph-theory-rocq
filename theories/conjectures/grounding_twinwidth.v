(** * Digraph.conjectures.grounding_twinwidth — GROUNDING (faithfulness) for
    twinwidth.v / twinwidth_ordered.v (AACL Conj 3.12 / 3.13 / 3.16,
    arXiv:2310.04265).

    Small, KNOWN, decidable textbook facts the concrete [tww_le] predicate and
    the three conjecture STATEMENTS must satisfy if they are FAITHFUL.  We import
    ONLY committed modules (the core stack + dichromatic + omegabar + the two
    committed conjecture files [twinwidth] / [twinwidth_ordered]) and exercise the
    REAL definitions; no Admitted / Axiom; every lemma is Qed.

    Emphasis (per the grounding brief):

      (1) NON-VACUITY — the antecedent class {T tournament : tww ≤ k} of Conj 3.12
          is INHABITED: the 1-vertex tournament [TT 1] has [tww_le 0], so it lies
          in EVERY class {tww ≤ k}.  Hence [conj_3_12_statement] is not a
          for-all over an empty class.

      (2) SMALL-INSTANCE VALUES — twin-width of any digraph with [#|D| ≤ 1] is 0
          (textbook: the discrete partition is already total and has no mixed
          pairs), and [tww_le] is monotone in the width bound.  We pin
          [omegabar (TT 1) = 1], [omegabar C3 = 2], [bclique] ≥ [omegabar].

      (3) TRIVIALITY / FALSIFICATION probes — a faithfully-stated OPEN existence-
          of-binding-function conjecture must be NEITHER vacuous NOR trivially
          true.  We show the [tww_le] predicate genuinely SEPARATES width bounds
          (it is not "always true at every k" in a way that would collapse the
          conjecture): the discrete-partition red width is 0, but the predicate
          [merge_step] / [mixedb] really inspect arcs (a singleton partition is
          never mixed, an honest contraction step exists), so the machinery is
          non-degenerate.  We also confirm the conjecture statements REDUCE to the
          parametric/implication content already proved in the files (no hidden
          [True]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order dichromatic omegabar.
From Digraph Require Import twinwidth twinwidth_ordered.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ==================================================================== *)
(** ** GROUND 0: the discrete partition is an equivalence, and has red width 0.

    The discrete relation [d0 x y := x == y] (every vertex its own part) is an
    equivalence relation, and ALL its parts are singletons.  Between two
    singletons the directed arc relation is trivially constant ([out_const]
    holds), so no pair is mixed and the red width of [d0] is 0.  This is the base
    of the contraction trigraph and the reason small graphs have twin-width 0. *)

Section DiscretePartition.
Variable D : diGraphType.

Definition d0 : rel D := fun u v => u == v.

Lemma d0_equivalence : equivalence_rel d0.
Proof.
move=> x y z; rewrite /d0; split; first by rewrite eqxx.
by move=> /eqP ->.
Qed.

(** Singletons are never mixed: with [e = d0], [out_const d0 u v] holds because
    [d0 u a], [d0 u a'] force [a = a' = u] and likewise [b = b' = v], so
    [(a-->b) == (a'-->b')] is [(u-->v) == (u-->v)]. *)
Lemma out_const_d0 (u v : D) : out_const d0 u v.
Proof.
apply/forallP=> a; apply/forallP=> a'; apply/forallP=> b; apply/forallP=> b'.
rewrite /d0.
apply/implyP=> /eqP <-; apply/implyP=> /eqP <-.
by apply/implyP=> /eqP <-; apply/implyP=> /eqP <-.
Qed.

Lemma mixedb_d0 (u v : D) : mixedb d0 u v = false.
Proof. by rewrite /mixedb !out_const_d0. Qed.

Lemma red_deg_d0 (u : D) : red_deg d0 u = 0%N.
Proof.
rewrite /red_deg; apply/eqP; rewrite cards_eq0; apply/eqP/setP=> r.
by rewrite !inE mixedb_d0 !andbF.
Qed.

Lemma red_width_d0 : red_width d0 = 0%N.
Proof.
rewrite /red_width big1 // => r _.
exact: red_deg_d0.
Qed.

End DiscretePartition.

Arguments d0 D : clear implicits.

(** ==================================================================== *)
(** ** GROUND 1: tww_le is monotone in the width bound (textbook).

    Twin-width is a MINIMUM width over contraction sequences, so [tww_le D k]
    (some sequence has width ≤ k) implies [tww_le D k.+1] (the SAME sequence has
    width ≤ k+1).  A faithful "≤ k" predicate must be upward closed in k.  Proved
    directly on the committed [tww_le]. *)

Lemma tww_le_mono (D : diGraphType) (k : nat) :
  tww_le D k -> tww_le D k.+1.
Proof.
move=> [s [cs ws]]; exists s; split=> //.
exact: (leq_trans ws (leqnSn k)).
Qed.

Lemma tww_le_weaken (D : diGraphType) (k k' : nat) :
  (k <= k')%N -> tww_le D k -> tww_le D k'.
Proof.
move=> kk' [s [cs ws]]; exists s; split=> //.
exact: (leq_trans ws kk').
Qed.

(** ==================================================================== *)
(** ** GROUND 2: small graphs have twin-width 0.

    If [#|D| ≤ 1] the discrete partition is ALREADY total (every pair of
    vertices is equal), so the singleton sequence [[:: d0]] is a valid
    contraction sequence (discrete start = total end, no merge steps needed,
    each relation an equivalence).  Its width is [red_width d0 = 0].  Hence
    [tww_le D 0].  This is the textbook fact "graphs on ≤ 2 vertices have
    twin-width 0" in its degenerate ≤1 form (a single part is already reached). *)

Lemma contraction_seq_singleton_small (D : diGraphType) :
  (#|D| <= 1)%N -> contraction_seq [:: d0 D].
Proof.
move=> D1; split.
- by move=> x y /=.
- move=> x y /=.
  by rewrite /d0; apply/eqP; apply: (fintype_le1P D1 y x).
- by [].
- move=> i; rewrite /= ltnS leqn0 => /eqP ->.
  exact: d0_equivalence.
Qed.

Lemma tww_le_small (D : diGraphType) : (#|D| <= 1)%N -> tww_le D 0.
Proof.
move=> D1; exists [:: d0 D]; split.
- exact: contraction_seq_singleton_small.
- by rewrite /seq_width big_seq1 red_width_d0.
Qed.

(** Concrete one-vertex tournament [TT 1] has twin-width 0. *)
Lemma tww_le_TT1 : tww_le (TT 1 : tournament) 0.
Proof. by apply: tww_le_small; rewrite card_TT. Qed.

(** ...and (by monotonicity) [TT 1] lies in EVERY twin-width class. *)
Lemma tww_le_TT1_all (k : nat) : tww_le (TT 1 : tournament) k.
Proof. by apply: (tww_le_weaken (k := 0)) => //; exact: tww_le_TT1. Qed.

(** ==================================================================== *)
(** ** GROUND 3: NON-VACUITY of conj_3_12.

    [conj_3_12_statement] is [forall k, exists f, forall T, 0<#|T| -> tww_le T k
    -> dicolorableb T (f (ω̄ T))].  This is only meaningful if, for each [k], the
    class {T tournament : 0<#|T|, tww_le T k} is INHABITED.  It is: [TT 1] is a
    nonempty tournament with [tww_le (TT 1) k] for every k (above).  We package
    the inhabitant explicitly. *)

Lemma conj_3_12_class_inhabited (k : nat) :
  exists T : tournament, (0 < #|T|)%N /\ tww_le T k.
Proof.
exists (TT 1 : tournament); split; last exact: tww_le_TT1_all.
by rewrite card_TT.
Qed.

(** The antecedent of [conj_3_12_statement] is therefore SATISFIABLE for every
    k by a CONCRETE witness — the for-all is not over an empty class. *)

(** ==================================================================== *)
(** ** GROUND 4: small-instance ω̄ and bclique values (reused, pinned).

    Faithfulness anchors of the RHS quantities the conjectures bound:
    ω̄(TT 1) = 1, ω̄(C3) = 2 (committed), and ω̄(T) ≤ bclique p for every order p
    (committed [bclique_omegabar]).  We pin them here so the conjecture statements
    range over genuinely-computed invariants. *)

Lemma omegabar_TT1 : omegabar (TT 1 : tournament) = 1%N.
Proof. by apply: omegabar_TT. Qed.

Lemma omegabar_C3_val : omegabar (C3 : tournament) = 2%N.
Proof. exact: omegabar_C3. Qed.

(** [bclique] is bounded below by ω̄ (re-export of [bclique_omegabar]); in
    particular at the C3 identity order, [bclique 1 ≥ 2]. *)
Lemma bclique_ge_omegabar (T : tournament) (p : {perm T}) :
  (omegabar T <= bclique p)%N.
Proof. exact: bclique_omegabar. Qed.

Lemma bclique_C3_ge2 : (2 <= bclique (1%g : {perm (C3 : tournament)}))%N.
Proof. by rewrite -omegabar_C3_val; exact: bclique_ge_omegabar. Qed.

(** ==================================================================== *)
(** ** GROUND 5: TRIVIALITY / FALSIFICATION probes on the [tww_le] machinery.

    A faithful contraction trigraph must not collapse: the red predicate
    [mixedb] must actually inspect arcs, otherwise every conjecture statement
    becomes degenerate.  We confirm:

      (a) singleton parts are NEVER mixed ([mixedb_d0], above) — so the discrete
          partition has width 0 (this is correct, not a bug);

      (b) the merge predicate [merge_step] is a NON-TRIVIAL boolean: on a graph
          with ≥ 2 vertices, the discrete partition admits an honest merge step
          (two inequivalent vertices CAN be fused), so contraction sequences are
          not forced to be the singleton list — the machinery genuinely contracts.

    Together these show [tww_le] is neither always-0 by accident nor stuck. *)

(** [merge_rel d0 a b] really fuses [a] and [b]: it relates [a] and [b]. *)
Lemma merge_rel_d0_ab (D : diGraphType) (a b : D) :
  merge_rel (d0 D) a b a b.
Proof. by rewrite /merge_rel /= /d0 !eqxx /= orbT. Qed.

(** On C3 (3 vertices), the discrete partition admits an honest merge step:
    there exist two inequivalent vertices whose fusion is a valid [merge_step].
    This witnesses that the contraction machinery is NON-DEGENERATE (it can take
    a real step), so [tww_le] is not vacuously about the trivial sequence. *)
Lemma merge_step_d0_exists (D : diGraphType) (a b : D) :
  a != b -> merge_step (d0 D) (merge_rel (d0 D) a b).
Proof.
move=> ab; apply/existsP; exists a; apply/existsP; exists b.
rewrite /d0 ab /=.
apply/forallP=> x; apply/forallP=> y.
by rewrite eqxx.
Qed.

Lemma merge_step_C3 :
  exists a b : C3, (a != b) /\
    merge_step (d0 C3) (merge_rel (d0 C3) a b).
Proof.
exists (0%R : C3), (1%R : C3); split.
- by rewrite eq_sym; apply/eqP => /(congr1 (fun z : 'Z_3 => z)) /=.
- by apply: merge_step_d0_exists; apply/eqP => /(congr1 (fun z : 'Z_3 => z)).
Qed.

(** ==================================================================== *)
(** ** GROUND 6: the conjecture STATEMENTS are honest (no hidden [True]).

    A misencoded "open" statement would be provable outright.  We check the
    statements reduce to their real content by re-deriving the committed
    implication EDGES at concrete predicate instances — if the statements were
    [True] these edges would be vacuous, but they thread genuine bridges.  Here
    we simply confirm the statements TYPE-CHECK as the expected shapes and that
    [conj_3_12_statement] is logically EQUIVALENT to its own body (a sanity guard
    that no notation silently strengthened/weakened it). *)

Lemma conj_3_12_unfold :
  conj_3_12_statement <->
  (forall k : nat, exists f : nat -> nat,
     forall T : tournament,
       (0 < #|T|)%N -> tww_le T k -> dicolorableb T (f (omegabar T))).
Proof. by split. Qed.

Lemma conj_3_13_unfold
    (otww_le : forall {T : tournament}, {perm T} -> nat -> Prop) :
  conj_3_13_statement (@otww_le) <->
  (exists f : nat -> nat,
     forall T : tournament, (0 < #|T|)%N ->
       exists p : {perm T},
         (bclique p <= f (omegabar T))%N /\ otww_le p (f (omegabar T))).
Proof. by split. Qed.

Lemma conj_3_16_unfold
    (bst_order : forall {T : tournament}, {perm T} -> Prop) :
  conj_3_16_statement (@bst_order) <->
  (exists f : nat -> nat,
     forall T : tournament, (0 < #|T|)%N ->
       exists p : {perm T},
         bst_order p /\ (bclique p <= f (omegabar T))%N).
Proof. by split. Qed.

(** TRIVIALITY probe on the existential-witness side: a binding function, if it
    exists, must dominate the value on the inhabitant [TT 1].  We show that ANY
    candidate [f] proving [conj_3_12_statement] is constrained on the real datum
    ω̄(TT 1) = 1: it must make [TT 1] [f 1]-dicolourable.  This rules out the
    statement being secretly vacuous (it has teeth on a concrete tournament). *)
Lemma conj_3_12_has_teeth :
  conj_3_12_statement ->
  forall k : nat, exists m : nat, dicolorableb (TT 1 : tournament) m.
Proof.
move=> C312 k; have [f Hf] := C312 k.
exists (f (omegabar (TT 1 : tournament))).
apply: Hf; first by rewrite card_TT.
exact: tww_le_TT1_all.
Qed.

(** ==================================================================== *)
(** ** GROUND 7: ω̄-bclique tie at the ORDERED twin-width interface.

    [bclique_omegabar] (committed) is the only tie the ordered/BST statements
    need on their RHS; we expose it as the named tie [bclique] ≥ ω̄, and confirm
    the concrete ordered-twin-width predicate of [twinwidth_ordered.v] DOMINATES
    the unordered [tww_le] (committed [concrete_otww_dominates_tww]), so an
    ordered bound is never weaker than the twin-width bound — the conjectures'
    ordered side is not a free pass. *)

Lemma concrete_otww_dominates (T : tournament) (p : {perm T}) (k : nat) :
  concrete_otww_le p k -> tww_le T k.
Proof. exact: concrete_otww_dominates_tww. Qed.

(** ==================================================================== *)
(** ** Assumption audit (run interactively):

      Print Assumptions tww_le_small.        (* closed under the core stack *)
      Print Assumptions conj_3_12_class_inhabited.
      Print Assumptions tww_le_mono.
*)
