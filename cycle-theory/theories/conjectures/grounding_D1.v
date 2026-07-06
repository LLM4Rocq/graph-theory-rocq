(** * Cycle.conjectures.grounding_D1 — grounding lemmas for milestone D1

    Qed-closed, axiom-free sanity results for the new primitives introduced in
    [Cycle.conjectures.D1].  For each new primitive we provide:
      - a SATISFIABLE witness (the predicate is inhabited / non-contradictory);
      - at least one textbook IDENTITY it must satisfy.

    Witness models used:
      - [U]: the one-vertex, edge-less multigraph (unit_graph) — grounds the
        connectivity / vacuous-flow primitives (every flow predicate whose
        nowhere-zero bound and Kirchhoff law range over [edge U = void] holds
        vacuously).
      - [V]: the empty multigraph (void_graph) — grounds the flow-polynomial
        primitives ([ncomp]/[nullity]/[flow_poly]) on the textbook base case
        [Phi(empty) = 1].
      - [Lp]: the single-loop graph (one vertex, one loop edge) — a genuine
        nonempty nowhere-zero flow: [phi == 1] is a nz 2-flow (and, with signs
        [+1,-1], a nz 2-biflow).  Conservation here is the trivial loop identity
        ([source]- and [target]-incidence coincide).
      - [Gd]: the digon (2 vertices, 2 oppositely oriented parallel edges) — a
        genuine nonempty 2-regular circuit; grounds [is_circuit].

    NOTE.  A nowhere-zero flow needs incidence symmetry to balance Kirchhoff;
    the loop [Lp] supplies it for vertex-flow rows, while bidirected balance on
    [Lp] needs opposite endpoint signs.  Primitives with no cheap concrete
    nonempty witness ([is_2t1_graph], [is_class1], [mtreewidth_le], [mg_minor])
    are grounded by their structural identities / monotonicities instead. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Import base.
From mathcomp Require Import all_algebra all_fingroup.
From Cycle.conjectures Require Import D1.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ================================================================= *)
(** ** Witness graphs *)

Definition U : mgraph := unit_graph tt.
Definition V : mgraph := void_graph unit unit.
Definition G0 : mgraph := two_graph tt tt.
Definition G1 : mgraph := mgraph.add_edge G0 (inl tt) (inr tt) tt.
Definition Gd : mgraph := mgraph.add_edge G1 (inr tt) (inl tt) tt.
Definition Lp : mgraph := mgraph.add_edge (unit_graph tt) tt tt tt.

Lemma card_edge_Gd : #|edge Gd| = 2.
Proof. by rewrite /Gd /G1 /G0 !card_option card_sum !card_void. Qed.

Lemma edges_at_U (v : U) : edges_at v = set0.
Proof. by apply/setP => -[]. Qed.

Lemma card_edgeU (A : {set edge U}) : #|A| = 0.
Proof. by apply/eqP; rewrite cards_eq0; apply/eqP/setP => -[]. Qed.

(** ================================================================= *)
(** ** Reused multigraph vocabulary: [mdeg]/[mreg]/[mDelta], [cut],
       connectivity, [is_circuit] (digon), [two_edge_connected] *)

Lemma mdeg_U (v : U) : mdeg v = 0.
Proof. by rewrite /mdeg edges_at_U cards0. Qed.

Lemma mreg_U : mreg U 0.
Proof. exact: mdeg_U. Qed.

Lemma mreg_mdeg (G : mgraph) (d : nat) : mreg G d -> forall v : G, mdeg v = d.
Proof. by []. Qed.

Lemma mDelta_U : mDelta U = 0.
Proof.
apply/eqP; rewrite eqn_leq leq0n andbT.
by apply/bigmax_leqP => v _; rewrite mdeg_U.
Qed.

Lemma cut_set0 (G : mgraph) : cut (@set0 G) = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

Lemma cut_setT (G : mgraph) : cut [set: G] = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

Lemma mconnected_U : mconnected U.
Proof. by move=> x y; exists [::]; case: x; case: y. Qed.

Lemma bridgeless_U : bridgeless U.
Proof. by case. Qed.

Lemma edge_connected0 (G : mgraph) : edge_connected G 0.
Proof. by move=> E; rewrite ltn0. Qed.

Lemma two_edge_connected_U : two_edge_connected U.
Proof. by split; [exact: mconnected_U | exact: bridgeless_U]. Qed.

Lemma two_edge_connected_bridgeless (G : mgraph) :
  two_edge_connected G -> bridgeless G.
Proof. by case. Qed.

(** The digon is a genuine 2-regular circuit. *)
Lemma inc_all (v : Gd) (e : edge Gd) : incident v e.
Proof.
rewrite /incident; apply/existsP.
by case: v => -[]; case: e => [[[[]|[]]|]|];
  [exists false|exists true|exists true|exists false].
Qed.

Lemma edges_at_Gd (v : Gd) : edges_at v = [set: edge Gd].
Proof. by apply/setP => e; rewrite !inE inc_all. Qed.

Lemma subdeg_Gd (H : {set edge Gd}) (v : Gd) : subdeg H v = #|H|.
Proof. by rewrite /subdeg edges_at_Gd setTI. Qed.

Lemma mdeg_Gd (v : Gd) : mdeg v = 2.
Proof. by rewrite /mdeg edges_at_Gd cardsT card_edge_Gd. Qed.

Lemma subgraph_kregular_Gd : subgraph_kregular (G:=Gd) [set: edge Gd] 2.
Proof. by move=> v; right; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

Lemma subgraph_connected_Gd : subgraph_connected (G:=Gd) [set: edge Gd].
Proof.
move=> x y _ _; case: x => -[]; case: y => -[].
- by exists [::].
- by exists [:: Some None]; rewrite /walk_in /= !inE.
- by exists [:: None]; rewrite /walk_in /= !inE.
- by exists [::].
Qed.

Lemma is_circuit_Gd : is_circuit (G:=Gd) [set: edge Gd].
Proof.
split.
- by rewrite -card_gt0 cardsT card_edge_Gd.
- exact: subgraph_kregular_Gd.
- exact: subgraph_connected_Gd.
Qed.

(** ================================================================= *)
(** ** Flow infrastructure: conservation, bounds, nz-flows *)

(** Identity: the zero weighting is Kirchhoff-conservative on any graph. *)
Lemma iconservative_const0 (G : mgraph) : iconservative (fun _ : edge G => 0).
Proof. by move=> v; rewrite !big1. Qed.

Lemma rconservative_const0 (G : mgraph) : rconservative (fun _ : edge G => 0).
Proof. by move=> v; rewrite !big1. Qed.

(** Identity: nowhere-zero bound forces nonzero weights. *)
Lemma int_bounded_neq0 (G : mgraph) (k : nat) (phi : edge G -> int) :
  int_bounded k phi -> forall e, phi e != 0.
Proof.
by move=> H e; have [H1 _] := H e; apply/negP => /eqP e0; rewrite e0 normr0 in H1.
Qed.

(** Conservation on the loop graph [Lp] ([source]/[target] incidence coincide). *)
Lemma iconservative_Lp1 : iconservative (G:=Lp) (fun _ => 1).
Proof. by move=> v; apply: eq_bigl => -[[]|]. Qed.

(** Witness (vacuous): the edge-less graph has a nz [k]-flow for any [k]. *)
Lemma has_nz_kflow_U (k : nat) : has_nz_kflow U k.
Proof. by exists (fun _ => 1); split=> [v|]; [rewrite !big1 | case]. Qed.

(** Witness (genuine): the single loop carries a nowhere-zero 2-flow. *)
Lemma has_nz_kflow_Lp2 : has_nz_kflow Lp 2.
Proof.
exists (fun _ => 1); split; first exact: iconservative_Lp1.
by move=> e; rewrite normr1; split.
Qed.

(** Witness (genuine): the single loop carries a nowhere-zero rational 2-flow. *)
Lemma has_nz_rflow_Lp2 : has_nz_rflow Lp 2.
Proof.
exists (fun _ => 1); split.
- by move=> v; apply: eq_bigl => -[[]|].
- by move=> e; rewrite normr1; split=> //; rewrite (_ : 2 - 1 = 1).
Qed.

(** Witness + identity: deleting all edges always leaves a (zero) nz flow. *)
Lemma has_nz_kflow_del_setT (G : mgraph) (k : nat) :
  @has_nz_kflow_del G [set: edge G] k.
Proof.
exists (fun _ => 0); split; [exact: iconservative_const0| by [] |].
by move=> e; rewrite in_setT.
Qed.

(** Witness: the edge-less graph meets every circular-flow-number bound. *)
Lemma circular_flow_number_le_U (c : rat) : circular_flow_number_le U c.
Proof. by move=> r _; exists (fun _ => 0); split=> [v|]; [rewrite !big1 | case]. Qed.

(** Identity: [(2t+1)]-graphs are [(2t+1)]-regular. *)
Lemma is_2t1_mreg (G : mgraph) (t : nat) :
  is_2t1_graph G t -> mreg G (2 * t + 1).
Proof. by case. Qed.

(** Identity: class-1 means [chi' = Delta]. *)
Lemma is_class1E (G : mgraph) : is_class1 G -> chromatic_index G = mDelta G.
Proof. by []. Qed.

(** ================================================================= *)
(** ** Bidirected graphs *)

Lemma is_sign_pm : is_sign 1 /\ is_sign (-1).
Proof. by split; rewrite /is_sign eqxx ?orbT. Qed.

(** Identity: the all-[+1] signature is bidirected on any graph. *)
Lemma is_bidirected_const1 (G : mgraph) :
  is_bidirected (G:=G) (fun _ => 1) (fun _ => 1).
Proof. by move=> e; rewrite /is_sign eqxx. Qed.

(** Identity: the zero flow has zero bidirected balance. *)
Lemma bnet0 (G : mgraph) (ss st : edge G -> int) (v : G) :
  bnet ss st (fun _ => 0) v = 0.
Proof. by rewrite /bnet !big1 // => e _; rewrite mulr0. Qed.

(** Witness (vacuous): the edge-less graph has a nz [k]-biflow. *)
Lemma has_nz_biflow_U (ss st : edge U -> int) (k : nat) :
  has_nz_biflow ss st k.
Proof.
exists (fun _ => 0); split; last by case.
by move=> v; rewrite /bnet !big1 // => -[].
Qed.

(** Witness (genuine): the loop with opposite endpoint signs has a nz 2-biflow. *)
Lemma has_nz_biflow_Lp2 :
  has_nz_biflow (G:=Lp) (fun _ => 1) (fun _ => -1) 2.
Proof.
exists (fun _ => 1); split.
- move=> v; rewrite /bnet.
  rewrite (eq_bigl (fun e => target e == v)); last by move=> -[[]|].
  by rewrite -big_split big1 //= => e _; rewrite mulr1 mulN1r addrN.
- by move=> e; rewrite normr1; split.
Qed.

(** ================================================================= *)
(** ** Cycle space of a simple graph and cycle-continuous maps *)

(** Identity: a cycle-space edge is a 2-element vertex set. *)
Lemma sedge_card2 (G : sgraph) (e : {set G}) : e \in sedge G -> #|e| = 2.
Proof.
rewrite inE => /existsP[x] /existsP[y] /andP[xy /eqP ->].
by rewrite cards2 (sg_edgeNeq xy).
Qed.

(** Witness: the Petersen graph has an edge (its cycle space is nonempty). *)
Lemma sedge_petersen_ne : sedge petersen != set0.
Proof.
apply/set0Pn; exists [set (ord0 : 'I_10); (inord 1 : 'I_10)].
rewrite inE; apply/existsP; exists ord0; apply/existsP; exists (inord 1).
rewrite eqxx andbT /edge_rel /=.
by rewrite /padj /pconn /= inordK //= andbT -(inj_eq val_inj) /= inordK.
Qed.

(** Witness: the empty even subgraph lies in the cycle space. *)
Lemma in_cycle_space_set0 (G : sgraph) : in_cycle_space (G:=G) set0.
Proof.
split; first exact: sub0set.
move=> v.
have heq : [set e in (set0 : {set {set G}}) | v \in e] = set0.
  by apply/setP => e; rewrite !inE andbC andbF.
by rewrite heq cards0.
Qed.

(** Identity: a cycle-space element is a subgraph. *)
Lemma in_cycle_space_sub (G : sgraph) (C : {set {set G}}) :
  in_cycle_space C -> C \subset sedge G.
Proof. by case. Qed.

(** Witness: the identity map is cycle-continuous. *)
Lemma cycle_continuous_id (G : sgraph) : cycle_continuous (@id {set G}).
Proof.
split; first by [].
move=> C [HC Hev]; have ->: [set e in sedge G | id e \in C] = C.
  apply/setP => e; rewrite inE.
  by apply/andb_idl => /(subsetP HC).
by split.
Qed.

(** Identity: a cycle-continuous map sends edges to edges. *)
Lemma cycle_continuous_sedge (G H : sgraph) (f : {set G} -> {set H}) :
  cycle_continuous f -> forall e, e \in sedge G -> f e \in sedge H.
Proof. by case. Qed.

(** ================================================================= *)
(** ** Minor model *)

(** Witness: the empty branch set is (vacuously) branch-connected. *)
Lemma mg_branch_connected_set0 (G : mgraph) : mg_branch_connected (G:=G) set0.
Proof. by move=> x y; rewrite in_set0. Qed.

(** ================================================================= *)
(** ** Unit-vector (S^2) flows *)

(** Witness: the first standard basis vector lies on the sphere. *)
Lemma sphere_vec_e0 (R : rcfType) :
  sphere_vec (\row_(j < 3) (j == ord0)%:R : 'rV[R]_3).
Proof.
rewrite /sphere_vec !big_ord_recl big_ord0 /= !mxE.
by rewrite !lift_eqF expr1n !expr0n /= !addr0.
Qed.

(** Identity: a sphere vector is nowhere zero. *)
Lemma sphere_vec_neq0 (R : rcfType) (x : 'rV[R]_3) : sphere_vec x -> x != 0.
Proof.
move=> H; apply/eqP => x0; move: H; rewrite x0 /sphere_vec.
rewrite (eq_bigr (fun=> 0)); last by move=> i _; rewrite mxE expr0n.
by rewrite big1 // eq_sym oner_eq0.
Qed.

(** Identity: the zero vector flow is conservative on any graph. *)
Lemma vconservative_const0 (R : rcfType) (G : mgraph) :
  vconservative (fun _ : edge G => 0 : 'rV[R]_3).
Proof. by move=> v; rewrite !big1. Qed.

(** ================================================================= *)
(** ** Embedded-graph primitives (rotation system) *)

(** Identity: dart flip is an involution. *)
Lemma dflip_invol (G : mgraph) (d : edge G * bool) : dflip (dflip d) = d.
Proof. by case: d => e b; rewrite /dflip /= negbK. Qed.

(** Identity: the dart sign of the two darts of an edge. *)
Lemma dsign_tf (G : mgraph) (e : edge G) :
  dsign (e, true) = 1 /\ dsign (e, false) = -1.
Proof. by []. Qed.

(** Identity: the empty face has empty boundary. *)
Lemma fbound_set0 (G : mgraph) : fbound (set0 : {set edge G * bool}) = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

(** Identities: GF(2) symmetric difference unit and self-cancellation. *)
Lemma symd_set0 (G : mgraph) (A : {set edge G}) : symd A set0 = A.
Proof. by rewrite /symd setU0 setI0 setD0. Qed.

Lemma symd_self (G : mgraph) (A : {set edge G}) : symd A A = set0.
Proof. by rewrite /symd setUid setIid setDv. Qed.

(** Witness: the empty cycle is contractible (empty sum of face boundaries). *)
Lemma contractible_set0 (G : mgraph) (sigma : {perm (edge G * bool)}) :
  contractible sigma set0.
Proof.
exists (fun _ => false).
by rewrite big_pred0 // => O; rewrite andbF.
Qed.

(** Witness: edge-width is always [>= 0]. *)
Lemma edge_width_geq0 (G : mgraph) (sigma : {perm (edge G * bool)}) :
  edge_width_geq sigma 0.
Proof. by move=> C _ _. Qed.

(** Identity: a local tension is nowhere zero. *)
Lemma local_tension_neq0 (G : mgraph) (sigma : {perm (edge G * bool)})
    (k : nat) (t : edge G -> int) :
  local_tension sigma k t -> forall e, t e != 0.
Proof.
move=> [Hb _] e; have [H1 _] := Hb e.
by apply/negP => /eqP e0; rewrite e0 normr0 in H1.
Qed.

(** ================================================================= *)
(** ** Orientations and imbalance (Jaeger) *)

(** Identity: tail/head of a kept edge are its source/target. *)
Lemma otail_ohead (G : mgraph) (o : edge G -> bool) (e : edge G) :
  o e = true -> otail o e = source e /\ ohead o e = target e.
Proof. by rewrite /otail /ohead => ->. Qed.

(** Identity: the edge-less graph is balanced under every orientation. *)
Lemma imbalance_U (o : edge U -> bool) (v : U) : imbalance o v = 0.
Proof. by rewrite /imbalance !card_edgeU subrr. Qed.

(** ================================================================= *)
(** ** Flow polynomial *)

(** Identity: the component relation is symmetric. *)
Lemma erel_sym (G : mgraph) (S : {set edge G}) (x y : G) :
  erel S x y = erel S y x.
Proof. by rewrite /erel; apply: eq_existsb => e; rewrite orbC. Qed.

(** Identity: the empty graph has no components. *)
Lemma ncomp_void : ncomp (G:=V) set0 = 0.
Proof. by rewrite /ncomp; apply: preliminaries.n_comp0 => -[]. Qed.

(** Identity: the empty graph has nullity 0. *)
Lemma nullity_void : nullity (G:=V) set0 = 0.
Proof. by rewrite /nullity ncomp_void cards0 add0n sub0n. Qed.

(** Textbook base case: the empty graph's flow polynomial evaluates to 1. *)
Lemma flow_poly_eval_void (x : rat) : flow_poly_eval V x = 1.
Proof.
have He : #|edge V| = 0 by rewrite card_void.
rewrite /flow_poly_eval.
rewrite (eq_bigl (pred1 set0)); last by move=> S; apply/esym/eqP/setP => -[].
rewrite big_pred1_eq /nullity ncomp_void cards0 add0n sub0n He subn0.
by rewrite !expr0 mul1r.
Qed.

(** Textbook base case: the empty graph's flow polynomial is the constant 1. *)
Lemma flow_poly_void : flow_poly V = 1.
Proof.
have He : #|edge V| = 0 by rewrite card_void.
rewrite /flow_poly.
rewrite (eq_bigl (pred1 set0)); last by move=> S; apply/esym/eqP/setP => -[].
rewrite big_pred1_eq /nullity ncomp_void cards0 add0n sub0n He subn0.
by rewrite !expr0 scale1r.
Qed.

(** ================================================================= *)
(** ** Group / B-flows *)

(** Witness (vacuous): the edge-less graph has a [B]-flow in any group. *)
Lemma Bflow_U (M : finGroupType) (B : {set M}) :
  exists phi : edge U -> M, Bflow B phi.
Proof.
by exists (fun=> 1%g); split; [case | move=> v; rewrite !big1 // => -[]].
Qed.

(** Identity: a [B]-flow has all edge weights in [B]. *)
Lemma Bflow_mem (M : finGroupType) (G : mgraph) (B : {set M})
    (phi : edge G -> M) : Bflow B phi -> forall e, phi e \in B.
Proof. by case. Qed.

(** ================================================================= *)
(** ** Edge-disjoint paths / fractional multiflow / treewidth *)

(** Witness: the trivial [s]-[s] routing. *)
Lemma routes_refl (G : mgraph) (P : {set edge G}) (x : G) : routes P x x.
Proof. by exists [::]; split=> //=. Qed.

(** Witness: the empty integral routing is feasible. *)
Lemma edp_feasible_nil (G : mgraph) (dem : seq (G * G)) : edp_feasible dem [::].
Proof. by split; [|split]. Qed.

(** Witness: the empty fractional multiflow is feasible. *)
Lemma frac_feasible_nil (G : mgraph) (dem : seq (G * G)) : frac_feasible dem [::].
Proof. by split; [|move=> e; rewrite big_nil]. Qed.

(** Identity: the empty multiflow has value 0. *)
Lemma frac_value_nil (G : mgraph) : frac_value (G:=G) [::] = 0.
Proof. by rewrite /frac_value big_nil. Qed.

(** Identity: bounded treewidth is upward closed in the width bound. *)
Lemma mtreewidth_le_mono (G : mgraph) (w w' : nat) :
  mtreewidth_le G w -> (w <= w')%N -> mtreewidth_le G w'.
Proof.
by move=> [T [D [Hdec Hw]]] ww'; exists T, D; split=> //; apply: leq_trans Hw ww'.
Qed.

(** Small instance at the 3-flow modulus: the single loop [Lp] carries a
    genuine nowhere-zero 3-flow ([phi == 1], with [1 <= |1| <= 3-1 = 2]) —
    grounds [has_nz_kflow] at the exact modulus [k=3] of the 3-flow conjecture
    on a graph that really has an edge (not the vacuous edge-less witness). *)
Lemma has_nz_kflow_Lp3 : has_nz_kflow Lp 3.
Proof.
exists (fun _ => 1); split; first exact: iconservative_Lp1.
move=> e; rewrite normr1; split; first by [].
by rewrite ler1n.
Qed.
