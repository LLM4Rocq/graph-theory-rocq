(** * GTMisc.conjectures.grounding_D7 — grounding lemmas for milestone D7.

    SIMPLE, Qed-closed sanity results validating the NEW area-specific primitives
    introduced in [D7.v] (the shared abstract cost/algorithm layer, the MaxEDP
    routing vocabulary, the H-factor / abstract-complexity layer, the tournament
    feedback-arc-set vocabulary, and the edge-outerplanar layering proxy).  For
    (essentially) each new definition we record a SATISFIABLE witness and at
    least one textbook identity.  These are statement-validation lemmas, NOT the
    (open) conjectures themselves.

    Reusable carriers:
      - [K2] : the complete graph on 2 vertices (via [mk_sgraph] of the full
        relation) — the minimal carrier with an edge, used for the [walkb],
        [walk_uses] and [edge_outerplanar] witnesses;
      - [triv_problem] : the always-YES abstract decision problem, used for the
        [in_NP] witness.

    A reusable helper [minor_leq_card] (a minor has no more branch vertices than
    its host) lets us discharge [wagner_planar K2] = no [K5]/[K3,3] minor on a
    2-vertex graph purely by cardinality.

    Coverage notes (honest): every new primitive gets at least one Qed-closed
    identity, and almost all also get a satisfiable witness.  Two primitives are
    grounded by a projection identity only:
      - [maxedp_approx] (its full positive witness would require defining the
        exact MaxEDP optimum as a function and proving the ratio for ALL planar
        inputs — out of scope for a SIMPLE check);
      - [NP_hard] (a positive witness is a complete problem, i.e. a genuine
        NP-hardness proof — out of scope; we record the elimination identity).
    These match the deliberate machine-free abstraction of [D7.v]. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From GTMisc.conjectures Require Import D7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Helper: a minor has at most as many vertices as its host.
    ========================================================================== *)
Lemma minor_leq_card (G H : sgraph) : minor G H -> #|H| <= #|G|.
Proof.
case=> phi [Hsurj _ _].
have Hsurj' : forall y : H, exists x : G, phi x == Some y.
  by move=> y; case: (Hsurj y) => x Hx; exists x; rewrite Hx eqxx.
pose g (y : H) : G := xchoose (Hsurj' y).
have gP : forall y : H, phi (g y) == Some y.
  by move=> y; exact: (xchooseP (Hsurj' y)).
apply: (@leq_card _ _ g) => y1 y2 e.
by move: (gP y1) (gP y2) => /eqP H1 /eqP H2; rewrite e H2 in H1; case: H1.
Qed.

(** ============================================================================
    Reusable carrier [K2] (via a local [mk_sgraph]).
    ========================================================================== *)
Section Mk.
Variable V : finType.
Definition relAdj (r : rel V) : rel V := fun x y => (x != y) && (r x y || r y x).
Lemma relAdj_sym (r : rel V) : symmetric (relAdj r).
Proof. by move=> x y; rewrite /relAdj eq_sym orbC. Qed.
Lemma relAdj_irrefl (r : rel V) : irreflexive (relAdj r).
Proof. by move=> x; rewrite /relAdj eqxx. Qed.
Definition mk_sgraph (r : rel V) : sgraph := SGraph (@relAdj_sym r) (@relAdj_irrefl r).
End Mk.

Definition K2 : sgraph := @mk_sgraph 'I_2 (fun _ _ => true).

Lemma K2_edge (x y : K2) : (x -- y) = (x != y).
Proof. by rewrite /edge_rel/= /relAdj/= andbT. Qed.

Lemma cardK2 : #|K2| = 2.
Proof. by rewrite card_ord. Qed.

Lemma cardK33 : #|'K_3,3| = 6.
Proof. by rewrite card_sum !card_ord. Qed.

Lemma wagner_K2 : wagner_planar K2.
Proof.
split=> Hm.
- by move: (small_K_free (G := K2) (m := 4)); rewrite cardK2; apply.
- by move: (minor_leq_card Hm); rewrite cardK33 cardK2.
Qed.

(** ============================================================================
    Shared abstract cost / algorithm vocabulary.
    ========================================================================== *)

(** [decides]: the constant-true verdict decides the always-true predicate;
    a decider is sound. *)
Lemma decides_triv : decides (fun _ : nat => true) (fun _ => True).
Proof. by move=> x; split. Qed.

Lemma decides_sound (I : Type) (v : I -> bool) (P : I -> Prop) (x : I) :
  decides v P -> v x -> P x.
Proof. by move=> H; rewrite -H. Qed.

(** [runs_in_time]: the zero-cost function meets every bound; reflexivity. *)
Lemma runs_in_time_0 (I : Type) (bnd : I -> nat) : runs_in_time (fun _ => 0) bnd.
Proof. by move=> x. Qed.

Lemma runs_in_time_refl (I : Type) (c : I -> nat) : runs_in_time c c.
Proof. by move=> x. Qed.

(** [poly_bounded]: the zero-cost function is polynomially bounded by any size. *)
Lemma poly_bounded_0 (I : Type) (sz : I -> nat) : poly_bounded sz (fun _ => 0).
Proof. by exists 0, 0, 0 => x; rewrite mul0n. Qed.

(** ============================================================================
    Row 2 — MaxEDP routing vocabulary.
    ========================================================================== *)

(** [walkb]: a walk ends at its declared target; [K2] carries a 1-step walk. *)
Lemma walkb_last (G : sgraph) (s t : G) (p : seq G) : walkb s t p -> last s p = t.
Proof. by case/andP => _ /andP[_ /eqP ->]. Qed.

Lemma walkb_K2 : walkb (ord0 : K2) ord_max [:: ord_max].
Proof. by rewrite /walkb /pathp /= eqxx. Qed.

(** [walk_uses]: edge-usage is symmetric in its two endpoints (undirected
    edge); [K2]'s walk uses its only edge. *)
Lemma walk_uses_sym (G : sgraph) (s : G) (p : seq G) (u v : G) :
  walk_uses s p u v = walk_uses s p v u.
Proof. by rewrite /walk_uses orbC. Qed.

Lemma walk_uses_K2 : walk_uses (ord0 : K2) [:: ord_max] ord0 ord_max.
Proof. by rewrite /walk_uses /=. Qed.

(** [edp_feasible]: the empty demand-set is vacuously feasible. *)
Lemma edp_feasible_set0 (G : sgraph) (D : seq (G * G))
  (route : 'I_(size D) -> seq G) : edp_feasible (set0 : {set 'I_(size D)}) route.
Proof. by split=> [i|i j u v]; rewrite inE. Qed.

(** [edp_opt]: with no demands the MaxEDP optimum is [0]. *)
Lemma edp_opt_nil (G : sgraph) : edp_opt (G := G) [::] 0.
Proof.
split.
- exists set0, (fun _ => [::]); split; first exact: edp_feasible_set0.
  by rewrite cards0.
- by move=> S route _; move: (max_card S); rewrite card_ord.
Qed.

(** [edp_vsize]: it sums vertices and demands. *)
Lemma edp_vsize_E (G : sgraph) (D : seq (G * G)) :
  edp_vsize (existT _ G D) = #|G| + size D.
Proof. by []. Qed.

(** [maxedp_approx]: projection — an approximation has a poly-bounded cost. *)
Lemma maxedp_approx_cost (alg cost : edp_input -> nat) (rho : nat -> nat) :
  maxedp_approx alg cost rho -> poly_bounded edp_vsize cost.
Proof. by case. Qed.

(** [little_o_sqrt]: the constant-zero ratio is [o(sqrt n)]. *)
Lemma little_o_sqrt_0 : little_o_sqrt (fun _ => 0).
Proof. by move=> c; exists 0 => n _; rewrite expnS mul0n muln0. Qed.

(** ============================================================================
    Row 3 — H-factor and abstract-complexity vocabulary.
    ========================================================================== *)

(** [is_copy]: the identity is a copy of [G] in itself; a copy is injective. *)
Lemma is_copy_id (G : sgraph) : is_copy (@id G).
Proof. by split=> [|x y]; [exact: inj_id|]. Qed.

Lemma is_copy_inj (H G : sgraph) (f : H -> G) : is_copy f -> injective f.
Proof. by case. Qed.

(** [h_factor]: every graph has the trivial H-factor [G] = single copy of [G]. *)
Lemma h_factor_refl (G : sgraph) : h_factor G G.
Proof.
exists 1, (fun _ => [set: G]), (fun _ => id); split.
- by move=> v; exists ord0; rewrite in_setT.
- by move=> i j v _ _; rewrite (ord1 i) (ord1 j).
- by move=> i; exact: is_copy_id.
- move=> i; apply/setP => z; apply/idP/idP => _; last by rewrite in_setT.
  by apply/imsetP; exists z; rewrite ?in_setT.
Qed.

(** [mindeg_cn]: the [c = 0] (a = 0) min-degree constraint is vacuous. *)
Lemma mindeg_cn_0 (G : sgraph) (b : nat) : mindeg_cn G 0 b.
Proof. by move=> v; rewrite mul0n. Qed.

(** [problem]: the record projections compute on [triv_problem]. *)
Definition triv_problem : problem := Problem (fun _ : unit => 0) (fun _ => True).

Lemma triv_problem_size (u : unit) : @psize triv_problem u = 0.
Proof. by []. Qed.

(** [poly_reduces]: reflexivity (the identity reduction). *)
Lemma poly_reduces_refl (A : problem) : poly_reduces A A.
Proof.
exists id, (fun _ => 0), 1, 1, 0; split.
- by move=> x; exact: iff_refl.
- by move=> x; rewrite expn1 mul1n addn0.
- by move=> x; rewrite expn1 mul1n addn0.
Qed.

(** [in_NP]: the always-YES problem is in NP (empty certificate, constant
    verifier). *)
Lemma in_NP_triv : in_NP triv_problem.
Proof.
exists (fun _ _ => true), (fun _ _ => 0), 0, 0, 0; split.
- move=> x; split=> [_|_]; last by [].
  by exists [::]; split; rewrite ?mul0n.
- by move=> x cert; rewrite mul0n.
Qed.

(** [NP_hard]: elimination — NP-hardness yields a reduction from each NP
    problem.  (A positive witness is a genuine completeness proof, out of
    scope.) *)
Lemma NP_hard_elim (B A : problem) : NP_hard B -> in_NP A -> poly_reduces A B.
Proof. by move=> H; apply: H. Qed.

(** ============================================================================
    Row 4 — Tournament feedback-arc-set vocabulary.
    ========================================================================== *)

(** [is_tournament]: the 1-vertex relation is a tournament; tournaments are
    irreflexive. *)
Lemma is_tournament_triv : is_tournament (fun _ _ : 'I_1 => false).
Proof. by split=> [x|x y]; rewrite ?(ord1 x) ?(ord1 y) ?eqxx. Qed.

Lemma is_tournament_irrefl (T : finType) (r : rel T) :
  is_tournament r -> forall x : T, ~~ r x x.
Proof. by case. Qed.

(** [back_arcs]: the empty (arc-free) relation has no back arcs. *)
Lemma back_arcs_nil (T : finType) (pos : T -> nat) :
  back_arcs (fun _ _ : T => false) pos = 0.
Proof. by apply: eq_card0 => p; rewrite inE. Qed.

(** [fas_opt]: the arc-free tournament has optimum [0]. *)
Lemma fas_opt_nil : fas_opt (fun _ _ : 'I_2 => false) 0.
Proof.
split.
- by exists (@nat_of_ord 2); split; [exact: val_inj|exact: back_arcs_nil].
- by move=> pos _; rewrite back_arcs_nil.
Qed.

(** [t_vsize]: it counts vertices. *)
Lemma t_vsize_E (T : finType) (r : rel T) : t_vsize (existT _ T r) = #|T|.
Proof. by []. Qed.

(** ============================================================================
    Row 5 — Edge-outerplanar layering proxy.
    ========================================================================== *)

(** [edge_outerplanar]: [K2] admits the (trivial) depth-1 layering. *)
Lemma edge_outerplanar_K2 : edge_outerplanar K2 1.
Proof.
split; first exact: wagner_K2.
exists (fun _ _ => 0); split => //.
by exists ord0, ord_max; split=> //; rewrite K2_edge.
Qed.

(** [min_edge_outerplanar]: [K2]'s minimal edge-outerplanar depth is [1]
    (any depth realising an edge is at least [1]). *)
Lemma min_edge_outerplanar_K2 : min_edge_outerplanar K2 1.
Proof.
split; first exact: edge_outerplanar_K2.
move=> m [_ [elev [_ Hlt _ [x [y [Hxy Hxy0]]]]]].
by move: (Hlt x y Hxy); rewrite Hxy0.
Qed.
