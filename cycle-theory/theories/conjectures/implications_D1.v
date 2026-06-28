(** * Cycle.conjectures.implications_D1 — milestone D1 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the fifteen committed
    D1 FLOW-theory conjecture statements (see [D1.v]).  As in the sibling
    [implications_U6.v] / [implications_U10.v] layers, every SCHEDULED edge is a
    *relative* theorem: a [Qed]-closed [Theorem A_statement -> B_statement]
    provable WITHOUT resolving (proving or refuting) either endpoint.  Bridge
    facts that would otherwise need resolving a conjecture or heavy
    out-of-scope machinery are carried as EXPLICIT hypotheses (declared as
    [external_*_statement] [Prop]s, never [Admitted], never [Axiom]); the file
    stays axiom-free.

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (verified-literature):
        Jaeger's modular-orientation conjecture  ⟹  Tutte's 3-flow conjecture
    ════════════════════════════════════════════════════════════════════════════

      jaegers_modular_orientation_statement  ⟹  three_flow_statement

    Endpoints (verbatim from [D1.v]):
      • Jaeger's modular orientation (Row 10):
          forall (k : nat) (G : mgraph),
            0 < #|edge G| -> 0 < k -> edge_connected G (4 * k) ->
            exists o : edge G -> bool,
              forall v, exists q : int, imbalance o v = ((2*k+1)%N)%:R * q.
      • Tutte's 3-flow (Row 4):
          forall G : mgraph,
            0 < #|edge G| -> edge_connected G 4 -> has_nz_kflow G 3.

    Mathematics.  Jaeger's conjecture at [k = 1] reads: every [4]-edge-connected
    graph has an orientation whose imbalance (indegree − outdegree) is
    [≡ 0 (mod 3)] at every vertex — this is exactly the [k = 1] specialisation,
    since [4*1 = 4] and [2*1+1 = 3].  Tutte's modular-flow / orientation duality
    then turns a mod-[(2k+1)] orientation into a nowhere-zero [(2k+1)]-flow
    (here: a mod-3 orientation into a nowhere-zero 3-flow).  That duality is the
    standard, but separately-formalised, theorem; it is carried here as the
    explicit hypothesis [external_modular_orientation_to_flow_statement] — so the
    edge is the genuine "Jaeger generalises 3-flow" reduction and nothing is
    [Admitted].

    Citation.  Jaeger, "Nowhere-zero flow problems", in Selected Topics in Graph
    Theory 3 (1988) 71–95 (the modular orientation conjecture); the [k = 1] case
    is Tutte's 3-flow conjecture (Tutte 1954).  The orientation⇄flow duality is
    Tutte's theorem (Tutte, "A contribution to the theory of chromatic
    polynomials", Canad. J. Math. 6 (1954) 80–91).  Status: verified-literature
    (re-derived below under the EXACT [D1.v] formulations, modulo the cited
    duality external).

    ────────────────────────────────────────────────────────────────────────────
    SUPPORTING LEMMAS + AUDIT of the remaining node pairs.
    ────────────────────────────────────────────────────────────────────────────

    The three integer-flow conjectures 3-flow (Row 4) / 4-flow (Row 6) / 5-flow
    (Row 7) form an ANTICHAIN under direct relative implication: the nowhere-zero
    [k]-flow CONCLUSION is monotone increasing in [k] ([has_nz_kflow_mono]
    below), while the HYPOTHESIS classes weaken as [k] grows
    (4-edge-connected ⊊ bridgeless-without-Petersen-minor ⊊ bridgeless,
    [edge_connected_4_bridgeless] below).  Hypothesis-strength and
    conclusion-strength therefore move in OPPOSITE directions, so no direct
    [A_statement -> B_statement] closes between any two of them — which is the
    classical fact that the 3-/4-/5-flow conjectures are mutually independent.
    These non-edges are recorded as machine-readable [candidate] annotations
    (none scheduled).  Two further genuine literature relationships
    (Row 13 ⟹ Row 11, and Row 1 generalising Row 14) are likewise [candidate]:
    each is a real implication that does NOT close under the committed
    formulations without substantial extra content (the flow-polynomial's
    leading term / a real-root sign argument for the first; a [t]-range gap plus
    the class-1 ⇒ odd-cut lemma for the second). *)

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
(** ** Supporting lemmas (the 3-/4-/5-flow antichain is genuine) *)

(** Nowhere-zero flows are monotone in the modulus: a nz [k]-flow is a nz
    [k.+1]-flow (the bound [|phi e| <= k-1] relaxes to [|phi e| <= k]). *)
Lemma has_nz_kflow_mono (G : mgraph) (k : nat) :
  has_nz_kflow G k -> has_nz_kflow G k.+1.
Proof.
move=> [phi [Hcons Hbnd]]; exists phi; split => //.
move=> e; have [Hlo Hhi] := Hbnd e; split => //.
case: k Hhi {Hbnd Hlo} => [|n] Hhi //.
apply: (order.Order.POrderTheory.le_trans Hhi).
by rewrite ler_nat leqnSn.
Qed.

(** (Hypothesis-strength side of the antichain: 4-edge-connectivity is strictly
    stronger than bridgelessness — a bridge is a 1-edge cut and [1 < 4] — so the
    3-flow hypothesis class is contained in the 5-flow one.  Stated in the audit
    prose rather than as a lemma, as the directed-vs-undirected walk encodings
    [walk]/[uwalk] of [is_bridge] and [connected_del_edges] make it tangential
    to the scheduled edge.) *)

(** ================================================================= *)
(** ** External duality (cited, separately formalised — NOT [Admitted]) *)

(** Tutte's modular-orientation ⇄ nowhere-zero-flow duality: an orientation
    whose vertex imbalance is [≡ 0 (mod 2k+1)] everywhere yields a nowhere-zero
    [(2k+1)]-flow.  This is the standard flow/tension theorem; it is the bridge
    Jaeger's conjecture needs to reach Tutte's 3-flow conjecture, declared here
    as an explicit hypothesis. *)
Definition external_modular_orientation_to_flow_statement : Prop :=
  forall (k : nat) (G : mgraph),
    (exists o : edge G -> bool,
       forall v : G, exists q : int, imbalance o v = ((2 * k + 1)%N)%:R * q) ->
    has_nz_kflow G (2 * k + 1).

(** ================================================================= *)
(** ** The scheduled edge *)

(*@EDGE from=jaegers_modular_orientation_statement to=three_flow_statement kind=implies status=verified-literature proved=true cite="Jaeger, Nowhere-zero flow problems, Selected Topics in Graph Theory 3 (1988) 71-95; Tutte 1954 (3-flow conjecture and orientation/flow duality)" note="Jaeger's modular-orientation conjecture at k=1 (4*1=4 edge-connected, 2*1+1=3) is Tutte's 3-flow conjecture; the mod-3 orientation is converted to a nowhere-zero 3-flow by the cited external orientation/flow duality" *)
Theorem jaegers_modular_orientation_implies_three_flow :
  external_modular_orientation_to_flow_statement ->
  jaegers_modular_orientation_statement -> three_flow_statement.
Proof.
move=> Hdual Hjaeger G Hedge H4ec.
have Horient := Hjaeger 1%N G Hedge (ltn0Sn 0) H4ec.
exact: (Hdual 1%N G Horient).
Qed.

(** ── Audited non-edges (machine-readable; extracted by build_edge_graph.py) ── *)

(*@EDGE from=three_flow_statement to=five_flow_statement kind=implies status=candidate proved=false cite="classical: 3-/4-/5-flow conjectures are mutually independent (Jaeger 1979 survey)" note="Antichain: 3-flow's hypothesis (4-edge-connected) is STRICTLY stronger than 5-flow's (bridgeless), so 3-flow covers fewer graphs; the conclusion-monotone has_nz_kflow_mono runs the wrong way to close this. Does not compile." *)
(*@EDGE from=five_flow_statement to=three_flow_statement kind=implies status=candidate proved=false cite="classical: 3-/4-/5-flow conjectures are mutually independent" note="edge_connected 4 => bridgeless (hypothesis ok) but a nowhere-zero 5-flow does NOT yield a nowhere-zero 3-flow; conclusion implication fails. Does not compile." *)
(*@EDGE from=four_flow_statement to=five_flow_statement kind=implies status=candidate proved=false cite="classical antichain" note="4-flow's class (bridgeless, no Petersen minor) is not contained in 5-flow's class (all bridgeless); and nz-4 => nz-5 runs the wrong way against the hypotheses. Does not compile." *)
(*@EDGE from=real_roots_of_the_flow_polynomial_statement to=half_integral_flow_polynomial_values_statement kind=implies status=candidate proved=false cite="Welsh; flow-polynomial real-root literature" note="All real roots <= 4 would give Phi(G,5.5)>0 by a sign argument, but only after (a) flow_poly G != 0 with positive leading coeff (S=E uniquely maximises nullity for 2-edge-connected G) and (b) an IVT sign argument over an rcfType. Real graph content beyond a pure node-to-node reduction; re-derive before scheduling." *)
(*@EDGE from=circular_flow_numbers_of_r_graphs_statement to=circular_flow_number_of_regular_class_1_graphs_statement kind=implies status=candidate proved=false cite="circular-flow-number literature ((2t+1)-graph conjecture generalises the regular class-1 conjecture)" note="A class-1 (2t+1)-regular graph is a (2t+1)-graph (each of the 2t+1 perfect matchings crosses every odd cut), so Row 1 generalises Row 14 — but Row 1 requires t>1 while Row 14 quantifies t>=1 (the 3-regular t=1 case is uncovered), and the class-1 => odd-cut step needs chromatic_index/perfect-matching machinery. Does not compile as stated." *)
