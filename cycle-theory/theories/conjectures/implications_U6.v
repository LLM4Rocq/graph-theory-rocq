(** * Cycle.conjectures.implications_U6 — milestone U6 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the eleven committed
    U6 conjecture statements (see [U6.v]).  As in the digraph-theory
    [implications.v] layer and the sibling chromatic [implications_U1.v] /
    [implications_U5.v], every scheduled edge here is a *relative* theorem: a
    [Qed]-closed [Theorem A_statement -> B_statement] provable WITHOUT resolving
    (proving or refuting) either endpoint.  Bridge facts that would otherwise
    need resolving a conjecture or heavy out-of-scope machinery are carried as
    EXPLICIT hypotheses (never [Admitted], never [Axiom]); the file stays
    axiom-free.

    ════════════════════════════════════════════════════════════════════════════
    SCHEDULED EDGE (verified-literature):  Faithful cycle covers ⟹ CDC
    ════════════════════════════════════════════════════════════════════════════

      faithful_cycle_covers_statement  ⟹  cycle_double_cover_statement

    Endpoints (verbatim from [U6.v]):
      • Faithful cycle covers (Row 9):
          forall (G : mgraph) (p : edge G -> nat),
            0 < #|G| -> 0 < #|edge G| -> admissible p ->
            (forall e, ~~ odd (p e)) -> exists L, faithful_cover p L.
      • Cycle double cover (Row 11):
          forall G : mgraph,
            0 < #|G| -> 0 < #|edge G| -> bridgeless G -> exists L, cdc L.

    Mathematics.  Take the constant weighting [p ≡ 2].  Then
      (i)  [p] is EVEN everywhere ([~~ odd 2]);
      (ii) [p] is ADMISSIBLE: across every cut [δ(S)] the total is
             [\sum_(f in δS) 2 = 2·|δS|], which is even, and for each
             [e ∈ δS] one needs [2·p(e) = 4 ≤ 2·|δS|], i.e. [|δS| ≥ 2].
           A cut of size 1 around [e] would mean every (directed) walk between
           the endpoints of [e] crosses [δS] only through [e] — i.e. [e] is a
           bridge ([eseparates]).  Since [G] is bridgeless, no cut containing an
           edge is a singleton, so [|δS| ≥ 2] ([bridgeless_cut2] below, via the
           combinatorial [walk_crosses]: a walk whose endpoints straddle [S]
           must use a [δS]-edge).
    A faithful cover for [p ≡ 2] is, by definition, a list of circuits covering
    each edge exactly [p(e) = 2] times — that is exactly a cycle double cover.

    Citation.  The Faithful Cover Conjecture (Seymour; Alspach–Goddyn–Zhang,
    "Graphs with the circuit cover property", Trans. AMS 344 (1994) 131–154)
    specialises at [p ≡ 2] to the Cycle Double Cover Conjecture (Seymour 1979;
    Szekeres 1973).  Status: verified-literature (re-derived in full below; the
    [Qed] gate confirms it under the EXACT [U6.v] formulations).

    ────────────────────────────────────────────────────────────────────────────
    AUDIT of the other node pairs (no further verified-literature U6-internal
    edge compiles under the committed formulations).
    ────────────────────────────────────────────────────────────────────────────

    The §6 verified-literature table lists, for the cycle area:
      Petersen-colouring ⟹ Berge–Fulkerson / ⟹ CDC, Berge–Fulkerson ⟹ CDC
      (all U10 endpoints — CROSS-milestone), strong-k-CDC ⟹ CDC,
      circular/strong-embedding ⟹ CDC (no embedding node in U6), and the
      D1 4-flow ⟺ 3-edge-colouring.  Only strong-5-CDC ⟹ CDC is U6-internal
      (Row 10 ⟹ Row 11), but it does NOT compile under the committed
      formulations: Row 10 [strong_5_cycle_double_cover_statement] is restricted
      to CUBIC graphs and produces EVEN-SUBGRAPH cover members, whereas Row 11
      [cdc] quantifies over ALL bridgeless graphs and demands single-CIRCUIT
      members — so the universally-quantified Row-10 hypothesis cannot be applied
      to an arbitrary (non-cubic) bridgeless graph, and the member shapes differ.
      Forcing that edge would mis-state it; recorded below as a candidate, not
      scheduled.  Likewise the (5,2)-cover (Row 7) and CDC (Row 11) differ in
      member shape (even subgraph vs circuit) and in the fixed size-5 budget, so
      neither implies the other.  Hence exactly ONE verified-literature edge is
      internal to U6, and it is scheduled above. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** A directed walk straddling [S] must cross the cut [δS] *)

(** If [walk x y w] and [x], [y] lie on opposite sides of [S], then some edge of
    [w] has exactly one endpoint in [S], i.e. lies in [cut S]. *)
Lemma walk_crosses (G : mgraph) (S : {set G}) (w : seq (edge G)) (x y : G) :
  walk x y w -> (x \in S) != (y \in S) ->
  exists2 f, f \in w & f \in cut S.
Proof.
elim: w x y => [|e w IH] x y /=.
- by move=> /eqP <-; rewrite eqxx.
- move=> /andP[/eqP Hsx Hw] Hne.
  case Hcmp: ((target e \in S) == (x \in S)).
  + have Hne' : (target e \in S) != (y \in S) by rewrite (eqP Hcmp).
    have [f Hfw Hfc] := IH (target e) y Hw Hne'.
    by exists f => //; rewrite inE Hfw orbT.
  + exists e; first by rewrite inE eqxx.
    rewrite /cut inE Hsx.
    by move/negbT: Hcmp; case: (x \in S); case: (target e \in S).
Qed.

(** ** Bridgeless ⟹ every cut around an edge has size ≥ 2 *)

Lemma bridgeless_cut2 (G : mgraph) (S : {set G}) (e : edge G) :
  bridgeless G -> e \in cut S -> 2 <= #|cut S|.
Proof.
move=> Hbl Hin.
rewrite leqNgt; apply/negP => Hlt.
have Hge1 : 0 < #|cut S| by apply/card_gt0P; exists e.
have Hc1 : #|cut S| = 1.
  by apply/eqP; rewrite eqn_leq Hge1 andbT -ltnS.
have Heq : cut S = [set e].
  by apply/eqP; rewrite eq_sym eqEcard sub1set Hin cards1 Hc1.
apply: (Hbl e); rewrite /is_bridge => w Hw.
have Hxy : (source e \in S) != (target e \in S).
  by move: Hin; rewrite inE; case: (source e \in S); case: (target e \in S).
have [f Hfw Hfc] := walk_crosses Hw Hxy.
by exists f; [rewrite -Heq | exact: Hfw].
Qed.

(** ** Bridgeless ⟹ the constant weighting [p ≡ 2] is admissible *)

Lemma bridgeless_admissible2 (G : mgraph) :
  bridgeless G -> admissible (fun _ : edge G => 2).
Proof.
move=> Hbl S e Hin.
have H2 := bridgeless_cut2 Hbl Hin.
rewrite sum_nat_const; split.
- by rewrite leq_mul2r /=.
- by rewrite oddM andbF.
Qed.

(** ** The scheduled edge *)

(*@EDGE from=faithful_cycle_covers_statement to=cycle_double_cover_statement kind=implies status=verified-literature proved=true cite="Seymour 1979; Alspach-Goddyn-Zhang, Graphs with the circuit cover property, Trans. AMS 344 (1994) 131-154; Szekeres 1973" note="Faithful Cover Conjecture at the even weighting p==2 is exactly the Cycle Double Cover Conjecture; bridgeless => p==2 admissible via the walk/cut crossing lemma" *)
Theorem faithful_cycle_covers_implies_cycle_double_cover :
  faithful_cycle_covers_statement -> cycle_double_cover_statement.
Proof.
move=> Hf G Hn He Hbl.
have Hadm := bridgeless_admissible2 Hbl.
have Heven : forall e : edge G, ~~ odd ((fun _ : edge G => 2) e) by [].
have [L HL] := Hf G (fun _ : edge G => 2) Hn He Hadm Heven.
by exists L; exact: HL.
Qed.

(** ── Audited non-edges (machine-readable; extracted by build_edge_graph.py) ── *)

(*@EDGE from=strong_5_cycle_double_cover_statement to=cycle_double_cover_statement kind=implies status=candidate proved=false cite="OPG_FULL_FORMALIZATION_PLAN §6 (strong-k-CDC => CDC)" note="Does NOT compile under committed formulations: Row 10 is restricted to CUBIC graphs and yields even-subgraph members, Row 11 quantifies over all bridgeless graphs and demands single-circuit members" *)
(*@EDGE from=m_n_cycle_covers_statement to=cycle_double_cover_statement kind=implies status=candidate proved=false cite="OPG cycle-cover literature" note="member-shape mismatch: (5,2)-cover yields even subgraphs of fixed size 5, cdc demands single circuits" *)
