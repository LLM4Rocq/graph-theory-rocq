(** * Hypergraph.conjectures.grounding_U12 — grounding lemmas for milestone U12

    Qed-closed, axiom-free sanity results for the hypergraph primitives
    introduced in [Hypergraph.conjectures.U12] (Frankl's [union_closed] /
    [k_uniform]; Turán's [complete_sub] / [contains_complete]; the Berge-acyclic
    forest vocabulary [berge_cycle] / [berge_acyclic] / [hg_connected] /
    [k_forest] / [k_tree] / [critical_k_forest]; Ryser's [r_partite_uniform] /
    [hg_matching] / [is_matching_number] / [hg_cover] / [is_cover_number]).  For
    each primitive we provide:
      - a SATISFIABLE witness (the predicate is inhabited / non-contradictory);
      - at least one textbook IDENTITY it must satisfy.

    Witness models used (all over small concrete [finType]s):
      - [set0 : {set {set T}}] (the empty hypergraph) — grounds the vacuous side
        of [k_uniform] / [berge_acyclic] / [k_forest] / [r_partite_uniform] /
        [hg_matching] / [is_matching_number] / [hg_cover] / [is_cover_number];
      - the full powerset [[set: {set T}]] — grounds [union_closed] /
        [complete_sub] / [contains_complete];
      - the single-edge family [[set e]] — grounds [hg_connected] /
        [berge_acyclic] (a singleton family has no Berge cycle);
      - the single-vertex hypergraph [[set [set: 'I_1]]] (one hyperedge, the whole
        one-vertex set) — the genuine non-vacuous [k_tree] / [critical_k_forest] /
        [k_uniform] / [r_partite_uniform] witness;
      - the 3-vertex family [[set setT; [set O3 0; O3 1]]] over ['I_3] — two
        hyperedges sharing the two vertices [O3 0], [O3 1] form a length-2 Berge
        cycle, the non-vacuity witness that [berge_cycle] is inhabited.

    Everything below is [Qed]-closed and (by [Print Assumptions]) closed under the
    global context — no [Axiom]/[Parameter]/[Admitted]. *)

From GTBase Require Import base.
From Hypergraph.conjectures Require Import U12.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation O3 i := (@Ordinal 3 i isT).

(** ================================================================= *)
(** ** [k_uniform] (Rows 1,2,3) : witness + identity *)

(** WITNESS: the one-edge hypergraph on a single vertex is 1-uniform. *)
Lemma k_uniform_I1 : k_uniform [set [set: 'I_1]] 1.
Proof. by move=> e; rewrite inE => /eqP->; rewrite cardsT card_ord. Qed.

(** IDENTITY: every two hyperedges of a [k]-uniform family have equal size. *)
Lemma k_uniform_card_eq (T : finType) (E : {set {set T}}) k (e f : {set T}) :
  k_uniform E k -> e \in E -> f \in E -> #|e| = #|f|.
Proof. by move=> H He Hf; rewrite (H _ He) (H _ Hf). Qed.

(** ================================================================= *)
(** ** Row 1 — [union_closed] : witness + identity *)

(** WITNESS: the full powerset is union-closed. *)
Lemma union_closed_setT (T : finType) : union_closed [set: {set T}].
Proof. by move=> A B _ _; rewrite inE. Qed.

(** IDENTITY: union-closure extends to (associated) triple unions. *)
Lemma union_closed3 (T : finType) (F : {set {set T}}) (A B C : {set T}) :
  union_closed F -> A \in F -> B \in F -> C \in F -> (A :|: B :|: C) \in F.
Proof. by move=> H HA HB HC; apply: (H (A :|: B) C (H A B HA HB) HC). Qed.

(** ================================================================= *)
(** ** Row 2 — [complete_sub] / [contains_complete] : witnesses + identities *)

(** WITNESS: the full powerset makes every vertex set spanning-complete. *)
Lemma complete_sub_setT (T : finType) (S : {set T}) k :
  complete_sub [set: {set T}] S k.
Proof. by move=> e _ _; rewrite inE. Qed.

(** IDENTITY: spanning-completeness is antitone in the spanned vertex set. *)
Lemma complete_sub_subset (T : finType) (E : {set {set T}}) (S S' : {set T}) k :
  complete_sub E S k -> S' \subset S -> complete_sub E S' k.
Proof. by move=> H sub e eS' ek; apply: H => //; apply: subset_trans eS' sub. Qed.

(** WITNESS: the full powerset contains a complete copy on [0] vertices. *)
Lemma contains_complete_setT0 (T : finType) k :
  contains_complete [set: {set T}] 0 k.
Proof. by exists set0; split; [exact: cards0 | exact: complete_sub_setT]. Qed.

(** IDENTITY: a spanning-complete vertex set [S] exhibits a [K_{#|S|}^{(k)}]. *)
Lemma contains_complete_of (T : finType) (E : {set {set T}}) (S : {set T}) k :
  complete_sub E S k -> contains_complete E #|S| k.
Proof. by move=> H; exists S. Qed.

(** ================================================================= *)
(** ** Row 3 — Berge cycles, acyclicity, connectivity, forests, trees *)

(** *** [berge_cycle] : witness + identities *)

(** The length-2 Berge-cycle witness lives over ['I_3]: two distinct hyperedges
    [ec0] (everything) and [ec1] (a 2-set) sharing the two vertices [O3 0],
    [O3 1]. *)
Definition Vc : finType := 'I_3.
Definition ec0 : {set Vc} := [set: Vc].
Definition ec1 : {set Vc} := [set (O3 0); (O3 1)].
Definition Ecyc : {set {set Vc}} := [set ec0; ec1].

(** WITNESS: [Ecyc] has a Berge cycle (vertices [O3 0], [O3 1] cyclically link
    the two hyperedges). *)
Lemma berge_cycle_Ecyc : berge_cycle Ecyc.
Proof.
exists [:: (O3 0); (O3 1)], [:: ec0; ec1]; split => //=.
- rewrite andbT mem_seq1; apply/eqP => /setP/(_ (O3 2)).
  by rewrite /ec0 /ec1 !inE -!val_eqE /=.
- by move=> e; rewrite !inE => /orP[]/eqP->; rewrite eqxx ?orbT.
- by rewrite /ec0 /ec1 !inE !eqxx ?orbT.
Qed.

(** IDENTITY: a Berge cycle survives adding hyperedges (monotone in [E]). *)
Lemma berge_cycle_mono (T : finType) (E E' : {set {set T}}) :
  E \subset E' -> berge_cycle E -> berge_cycle E'.
Proof.
move=> sub [vs [es [a b c Hmem d]]]; exists vs, es; split => //.
by move=> f /Hmem; apply: (subsetP sub).
Qed.

(** IDENTITY: a hypergraph carrying a Berge cycle is nonempty. *)
Lemma berge_cycle_neq0 (T : finType) (E : {set {set T}}) :
  berge_cycle E -> E != set0.
Proof.
move=> [vs [es [Hsz _ _ Hmem _]]].
case: es Hsz Hmem => [|x es'] // _ Hmem.
by apply/set0Pn; exists x; exact: (Hmem x (mem_head x es')).
Qed.

(** *** [berge_acyclic] : witnesses + identity *)

(** WITNESS: the empty hypergraph is Berge-acyclic (no hyperedges to cycle). *)
Lemma berge_acyclic_set0 (T : finType) : berge_acyclic (set0 : {set {set T}}).
Proof.
move=> [vs [es [Hsz _ _ Hmem _]]].
case: es Hsz Hmem => [|e es'] // _ Hmem.
by move: (Hmem e (mem_head e es')); rewrite in_set0.
Qed.

(** WITNESS: a single-hyperedge family is Berge-acyclic (a Berge cycle needs two
    distinct hyperedges). *)
Lemma berge_acyclic_set1 (T : finType) (e : {set T}) : berge_acyclic [set e].
Proof.
move=> [vs [es [Hsz _ /andP[_ Hue] Hmem _]]].
case: es Hsz Hue Hmem => [|x0 [|x1 es']] //= _ /andP[Hne _] Hmem.
have Hin0 : x0 \in [:: x0, x1 & es'] by rewrite mem_head.
have Hin1 : x1 \in [:: x0, x1 & es'] by rewrite !inE eqxx orbT.
move: (Hmem x0 Hin0) (Hmem x1 Hin1); rewrite !inE => /eqP E0 /eqP E1.
move: Hne; rewrite E0 E1 => /negP; apply; exact: mem_head.
Qed.

(** IDENTITY: Berge-acyclicity is antitone — a subfamily of an acyclic
    hypergraph is acyclic. *)
Lemma berge_acyclic_sub (T : finType) (E E' : {set {set T}}) :
  E \subset E' -> berge_acyclic E' -> berge_acyclic E.
Proof. by move=> sub Hac Hc; exact: (Hac (berge_cycle_mono sub Hc)). Qed.

(** *** [hg_connected] : witness + identity *)

(** WITNESS: a single-hyperedge family is (Berge-)connected. *)
Lemma hg_connected_single (T : finType) (e : {set T}) : hg_connected [set e].
Proof.
split; first by rewrite -card_gt0 cards1.
by move=> a b; rewrite !inE => /eqP-> /eqP->; exists [::]; split.
Qed.

(** IDENTITY: a connected hypergraph is nonempty. *)
Lemma hg_connected_neq0 (T : finType) (E : {set {set T}}) :
  hg_connected E -> E != set0.
Proof. by case. Qed.

(** *** [k_forest] : witness + identity *)

(** WITNESS: the empty hypergraph is a [k]-forest. *)
Lemma k_forest_set0 (T : finType) k : k_forest (set0 : {set {set T}}) k.
Proof. by split; [move=> e; rewrite in_set0 | exact: berge_acyclic_set0]. Qed.

(** IDENTITY: a [k]-forest is [k]-uniform. *)
Lemma k_forest_uniform (T : finType) (E : {set {set T}}) k :
  k_forest E k -> k_uniform E k.
Proof. by case. Qed.

(** *** [k_tree] : witness + identity *)

(** WITNESS: the single-vertex one-hyperedge hypergraph is a 1-tree. *)
Lemma k_tree_I1 : k_tree [set [set: 'I_1]] 1.
Proof.
split; first by split; [exact: k_uniform_I1 | exact: berge_acyclic_set1].
exact: hg_connected_single.
Qed.

(** IDENTITY: a [k]-tree is in particular a [k]-forest. *)
Lemma k_tree_forest (T : finType) (E : {set {set T}}) k :
  k_tree E k -> k_forest E k.
Proof. by case. Qed.

(** *** [critical_k_forest] : witness + identity *)

(** WITNESS: the single-vertex one-hyperedge hypergraph is a critical 1-forest
    (the unique 1-set [setT] is already present, so the maximality clause holds
    vacuously).  This same instance also satisfies [k_tree] ([k_tree_I1]), so the
    conjecture's conclusion is consistent here — the statement is non-vacuous. *)
Lemma critical_k_forest_I1 : critical_k_forest [set [set: 'I_1]] 1.
Proof.
split; first by split; [exact: k_uniform_I1 | exact: berge_acyclic_set1].
move=> e He; have -> : e = [set: 'I_1].
  by apply/eqP; rewrite eqEcard (subsetT e) cardsT card_ord He.
by rewrite inE eqxx.
Qed.

(** IDENTITY: a critical [k]-forest is in particular a [k]-forest. *)
Lemma critical_k_forest_forest (T : finType) (E : {set {set T}}) k :
  critical_k_forest E k -> k_forest E k.
Proof. by case. Qed.

(** ================================================================= *)
(** ** Row 4 — Ryser : partiteness, matchings, covers, their numbers *)

(** *** [r_partite_uniform] : witnesses + identity *)

(** WITNESS (vacuous): the empty hypergraph is [r]-partite-uniform for any
    part-assignment. *)
Lemma r_partite_uniform_set0 (T : finType) r (part : T -> 'I_r) :
  r_partite_uniform part (set0 : {set {set T}}).
Proof. by move=> e; rewrite in_set0. Qed.

(** WITNESS (non-vacuous): the single-vertex one-hyperedge hypergraph is
    1-partite-uniform (its one hyperedge meets the single part in one vertex). *)
Lemma r_partite_uniform_I1 :
  r_partite_uniform (fun _ : 'I_1 => (ord0 : 'I_1)) [set [set: 'I_1]].
Proof.
move=> e; rewrite inE => /eqP-> j.
have -> : [set v in [set: 'I_1] | (fun _ => (ord0 : 'I_1)) v == j] = [set: 'I_1].
  apply/setP => x; rewrite !inE.
  have -> : j = ord0 by apply: val_inj; case: j => -[|m] //.
  by rewrite eqxx andbT.
by rewrite cardsT card_ord.
Qed.

(** IDENTITY: every hyperedge of an [r]-partite-uniform family has exactly [r]
    vertices (one per part). *)
Lemma r_partite_card (T : finType) (r : nat) (part : T -> 'I_r)
  (E : {set {set T}}) (e : {set T}) :
  r_partite_uniform part E -> e \in E -> #|e| = r.
Proof.
move=> Hpart He.
rewrite -sum1_card (partition_big part predT) //=.
rewrite -[RHS](card_ord r) -sum1_card.
apply: eq_bigr => j _.
rewrite sum1dep_card -(Hpart e He j).
by apply: eq_card => v; rewrite !inE.
Qed.

(** *** [hg_matching] : witness + identity *)

(** WITNESS: the empty subfamily is a matching of any hypergraph. *)
Lemma hg_matching_set0 (T : finType) (E : {set {set T}}) : hg_matching set0 E.
Proof. by split; [exact: sub0set | move=> e f; rewrite in_set0]. Qed.

(** IDENTITY: a matching is a subfamily of the hyperedge set. *)
Lemma hg_matching_sub (T : finType) (M E : {set {set T}}) :
  hg_matching M E -> M \subset E.
Proof. by case. Qed.

(** *** [is_matching_number] : witness + identity *)

(** WITNESS: the empty hypergraph has matching number [0]. *)
Lemma is_matching_number_set0 (T : finType) :
  is_matching_number (set0 : {set {set T}}) 0.
Proof.
split; first by exists set0; split; [exact: hg_matching_set0 | exact: cards0].
by move=> M [Hsub _]; move: Hsub; rewrite subset0 => /eqP->; rewrite cards0.
Qed.

(** IDENTITY: the matching number is unique (well-defined). *)
Lemma is_matching_number_uniq (T : finType) (E : {set {set T}}) n1 n2 :
  is_matching_number E n1 -> is_matching_number E n2 -> n1 = n2.
Proof.
move=> [[M1 [Hm1 Hc1]] Hb1] [[M2 [Hm2 Hc2]] Hb2].
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -Hc1; apply: Hb2.
- by rewrite -Hc2; apply: Hb1.
Qed.

(** *** [hg_cover] : witness + identity *)

(** WITNESS: any vertex set covers the empty hypergraph. *)
Lemma hg_cover_set0 (T : finType) (X : {set T}) :
  hg_cover X (set0 : {set {set T}}).
Proof. by move=> e; rewrite in_set0. Qed.

(** IDENTITY: vertex covers are monotone — enlarging a cover keeps it a cover. *)
Lemma hg_cover_mono (T : finType) (X Y : {set T}) (E : {set {set T}}) :
  hg_cover X E -> X \subset Y -> hg_cover Y E.
Proof.
move=> HX sub e He; case/set0Pn: (HX e He) => x; rewrite inE => /andP[xX xe].
by apply/set0Pn; exists x; rewrite inE (subsetP sub _ xX) xe.
Qed.

(** *** [is_cover_number] : witness + identity *)

(** WITNESS: the empty hypergraph has cover number [0]. *)
Lemma is_cover_number_set0 (T : finType) :
  is_cover_number (set0 : {set {set T}}) 0.
Proof.
split; first by exists set0; split; [exact: hg_cover_set0 | exact: cards0].
by move=> X _; exact: leq0n.
Qed.

(** IDENTITY: the cover number is unique (well-defined). *)
Lemma is_cover_number_uniq (T : finType) (E : {set {set T}}) t1 t2 :
  is_cover_number E t1 -> is_cover_number E t2 -> t1 = t2.
Proof.
move=> [[X1 [Hx1 Hc1]] Hb1] [[X2 [Hx2 Hc2]] Hb2].
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -Hc2; apply: Hb1.
- by rewrite -Hc1; apply: Hb2.
Qed.
