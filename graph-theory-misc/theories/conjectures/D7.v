(** * GTMisc.conjectures.D7 — milestone D7 (namespace GTMisc, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of five OPEN/SOLVED ALGORITHMIC & COMPLEXITY problems from the
    "miscellaneous graph theory" bucket.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph]):
      - Row 1 (homomorphism algorithm): a PAIR of undirected graphs
        [sgraph * sgraph];
      - Row 2 (MaxEDP approximation): a planar [sgraph] with a demand list,
        bundled as [edp_input := {G : sgraph & seq (G*G)}];
      - Row 3 (H-factor NP-hardness): the abstract decision [problem] whose
        instances are min-degree-[cn] graphs ([sgraph]);
      - Row 4 (PTAS feedback-arc-set, SOLVED): a tournament, modelled directly as
        a [finType] with a [rel] ([t_input := {T : finType & rel T}]);
      - Row 5 (k-edge-outerplanar embeddings): an undirected [sgraph].

    ALGORITHM / COST MODEL — TWO TRACKS (post-audit).

    POSITIVE rows (1, 2, 4, 5: "an efficient algorithm EXISTS") use the
    cost-coupled computation model of [GTMisc.foundations.complexity]: an
    algorithm is a [prog] — syntax in a fixed total combinator language — and
    BOTH its output ([prun]) and its step count ([pcost]) are computed by the
    ONE fixed interpreter, so the cost is FORCED by the very object that
    produces the answers ([pcost_pos] / [no_zero_cost_program]: the decoupled
    [alg := exact-answer, cost := 0] vacuity is impossible by construction).
    Each positive row therefore asserts, of a SINGLE program [p] over an
    EXPLICIT per-row instance encoding into [data]:
      - CORRECTNESS: a [decides_on] / [realizes_on] clause constraining
        [prun p] on EVERY encoded instance (universal — never an existential
        choice of outputs), and
      - EFFICIENCY: a [poly_cost_on] / explicit [pcost] bound on the SAME [p].
    Per-row encodings: [enc_hom] (Row 1: [Dpair] of the two adjacency
    matrices), [enc_edp] (Row 2: adjacency matrix paired with the demand list
    as [enum_rank] vertex indices), [enc_tournament] (Row 4: the arc matrix),
    [enc_graph] (Row 5; from complexity.v).  Sizes are unary and [dsize] of
    each encoding is polynomially equivalent to the natural instance size
    (vertices [+ demands]), so poly-in-[dsize] = poly-in-instance-size — see
    the faithfulness meta-note in complexity.v.

    HARDNESS row (3 — a UNIVERSAL claim, hence already non-vacuous in the
    abstract reading) stays in the machine-free RELATIONAL layer kept below:
    [decides] / [runs_in_time] / [poly_bounded] as vocabulary, and the
    [problem] / [poly_reduces] / [in_NP] / [NP_hard] complexity layer.
    "Polynomial" is encoded concretely as a bound [n |-> a*n^d + b] (the
    repo-wide convention, cf. digraph-theory unvd.prob_6).

    REUSE FROM graph-theory-base (GTBase.base): [homs_to]/[is_hom] (Rows 1,3),
    [wagner_planar] (combinatorial Wagner planarity, the available planarity
    proxy — the embedding/face API arrives with gate G2; Rows 2,5).  REUSE FROM
    GTMisc.foundations.complexity (Track-B model): [prog]/[prun]/[pcost],
    [decides_on]/[realizes_on]/[poly_cost_on], [enc_graph]/[enc_list]/
    [enc_nat]/[enc_bool].  Every other notion is AREA-SPECIFIC and defined
    locally. *)

From GraphTheory Require Import minor.
From GTBase Require Export base.
From GTMisc.foundations Require Export complexity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Abstract cost / algorithm vocabulary (area-local, HARDNESS row only)

    [decides verdict P]   — the boolean algorithm [verdict] decides predicate [P];
    [runs_in_time c bnd]  — abstract cost [c] is pointwise bounded by [bnd];
    [poly_bounded sz c]   — [c] is bounded by a polynomial [a*sz^d + b] in the
                            instance size [sz].  All three are relational Props;
    none commits to a computation model.  They remain the vocabulary of the
    Row-3 NP-hardness layer (universal hardness claims are non-vacuous as-is);
    the POSITIVE rows below instead use the coupled [prog] model of
    [GTMisc.foundations.complexity]. *)
Definition decides {I : Type} (verdict : I -> bool) (P : I -> Prop) : Prop :=
  forall x : I, verdict x <-> P x.

Definition runs_in_time {I : Type} (cost bound : I -> nat) : Prop :=
  forall x : I, cost x <= bound x.

Definition poly_bounded {I : Type} (size cost : I -> nat) : Prop :=
  exists a d b : nat, forall x : I, cost x <= a * (size x) ^ d + b.

(** Output decoder for value-computing programs: a [Dnat] output reads back as
    its value; junk (non-[Dnat]) outputs read as [0], so a program meeting a
    positive value specification is FORCED to produce a genuine [Dnat]. *)
Definition dnat_val (d : data) : nat := if d is Dnat n then n else 0.

(** ================================================================= *)
(** ** Row 1 — An algorithm for graph homomorphisms  (OPEN)

    Source: "Question Is there an algorithm that decides, for input graphs G and
    H, whether there exists a homomorphism from G to H in time
    O(c^(|V(G)|+|V(H)|)) for some constant c?"

    Carrier: a pair [sgraph * sgraph], encoded ([enc_hom]) as the [Dpair] of
    the two adjacency matrices.  The decision predicate is base's
    [homs_to G H] (existence of an adjacency-preserving map).  The algorithm
    is ONE [prog] [p] that (i) decides the predicate on every encoded instance
    ([decides_on]) and (ii) whose OWN step count [pcost p] on those SAME
    encodings is O(c^(|G|+|H|)) — written with explicit big-O constants
    [a * c ^ (|G|+|H|) + b], the base [c] existentially quantified with guard
    [1 < c] (a genuine exponential; the source's complexity class). *)
Definition enc_hom (GH : sgraph * sgraph) : data :=
  Dpair (enc_graph GH.1) (enc_graph GH.2).

Definition algorithm_for_graph_homomorphisms_statement : Prop :=
  exists (c : nat) (p : prog) (a b : nat),
    [/\ 1 < c,
        decides_on enc_hom (fun GH => homs_to GH.1 GH.2) p &
        forall GH : sgraph * sgraph,
          pcost p (enc_hom GH) <= a * c ^ (#|GH.1| + #|GH.2|) + b ].

(** ================================================================= *)
(** ** Row 2 — Approximation ratio for Maximum Edge-Disjoint Paths  (OPEN)

    Source: "Conjecture Can the approximation ratio O(sqrt(n)) be improved for
    the Maximum Edge Disjoint Paths problem (MaxEDP) in planar graphs or can an
    inapproximability result stronger than APX-hardness?"

    Carrier: [edp_input := {G : sgraph & seq (G*G)}] (a graph with a list of
    terminal demands), restricted to planar [G] via base's [wagner_planar];
    encoded ([enc_edp]) as the adjacency matrix paired with the demand list as
    [enum_rank] vertex-index pairs ([dsize (enc_edp x)] is polynomial in
    [edp_vsize x = #|G| + size demands], and conversely).
    AREA primitives:
      - [walkb s t p] / [walk_uses s p u v] (walk / edge-usage): [p] is a walk
        from [s] to [t]; it uses undirected edge [{u,v}] iff [(u,v)] is a
        consecutive pair of [s::p] (via [zip (s::p) p]);
      - [edp_feasible S route] (edge-disjoint routing): the demands indexed by
        [S] are routed by pairwise EDGE-DISJOINT walks [route];
      - [edp_opt D k] (MaxEDP optimum): [k] is the maximum number of
        simultaneously routable demands;
      - [edp_ratio_spec rho] (per-instance correctness): on a planar instance
        with optimum [k], the program's output VALUE ([dnat_val]) is feasible
        ([<= OPT]) and within ratio [rho(|V|)] of the optimum
        ([OPT <= rho(n)*value]);
      - [maxedp_approx p rho] (approximation-ratio, COUPLED): the single
        program [p] realizes [edp_ratio_spec rho] on every encoded instance
        AND has polynomially bounded step count ([poly_cost_on enc_edp p]);
      - [little_o_sqrt rho] : [rho(n) = o(sqrt n)]  (for all [c], eventually
        [c*rho(n)^2 <= n]) — the existing eps–N nat style.
    The disjunctive question is stated faithfully: EITHER the ratio can be
    pushed below sqrt(n) (a poly-cost [prog] realizing an [o(sqrt n)]
    approximation exists), OR a stronger-than-APX inapproximability holds (NO
    [prog] is a poly-cost CONSTANT-factor approximation). *)
(* Reuse base's [pathp] (= [path (--) s p && (last s p == t)], from
   GraphTheory.core.digraph, re-exported by base); the only NEW content is the
   non-emptiness guard. *)
Definition walkb {G : sgraph} (s t : G) (p : seq G) : bool :=
  (p != [::]) && pathp s t p.

Definition walk_uses {G : sgraph} (s : G) (p : seq G) (u v : G) : bool :=
  ((u, v) \in zip (s :: p) p) || ((v, u) \in zip (s :: p) p).

Definition edp_feasible {G : sgraph} {D : seq (G * G)}
  (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G) : Prop :=
  (forall i : 'I_(size D), i \in S ->
     walkb (tnth (in_tuple D) i).1 (tnth (in_tuple D) i).2 (route i)) /\
  (forall (i j : 'I_(size D)) (u v : G),
     i \in S -> j \in S -> i != j ->
     walk_uses (tnth (in_tuple D) i).1 (route i) u v ->
     ~~ walk_uses (tnth (in_tuple D) j).1 (route j) u v).

Definition edp_opt {G : sgraph} (D : seq (G * G)) (k : nat) : Prop :=
  (exists (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G),
      edp_feasible S route /\ #|S| = k) /\
  (forall (S : {set 'I_(size D)}) (route : 'I_(size D) -> seq G),
      edp_feasible S route -> #|S| <= k).

Definition edp_input : Type := {G : sgraph & seq (G * G)}.
Definition edp_vsize (x : edp_input) : nat := #|projT1 x| + size (projT2 x).

Definition enc_edp (x : edp_input) : data :=
  Dpair (enc_graph (projT1 x))
        (enc_list [seq Dpair (enc_nat (enum_rank d.1)) (enc_nat (enum_rank d.2))
                  | d <- projT2 x]).

Definition edp_ratio_spec (rho : nat -> nat) (x : edp_input) (out : data) : Prop :=
  forall k : nat,
    wagner_planar (projT1 x) -> edp_opt (projT2 x) k ->
    dnat_val out <= k /\ k <= rho #|projT1 x| * dnat_val out.

Definition maxedp_approx (p : prog) (rho : nat -> nat) : Prop :=
  realizes_on enc_edp (edp_ratio_spec rho) p /\ poly_cost_on enc_edp p.

Definition little_o_sqrt (rho : nat -> nat) : Prop :=
  forall c : nat, exists N : nat, forall n : nat, N <= n -> c * (rho n) ^ 2 <= n.

(** DISJUNCTION FIX (Track-B skeptic, machine-checked): the source poses a
    disjunctive research QUESTION — "improve the O(√n) ratio, or show a
    constant ratio is impossible".  Encoding it as [LEFT \/ RIGHT] is a
    CLASSICAL TAUTOLOGY: the right branch's ratio family (positive constants)
    is a SUBSET of the left branch's family (o(√n) functions — constants ARE
    o(√n)), so excluded middle alone decides the disjunction with zero MaxEDP
    content (a Qed'd probe derives it from [forall P, P \/ ~P]).  No two-branch
    rendering survives when the hardness branch is the complement of a
    subfamily of the algorithm branch.  SELECTED PROPOSITION (the open
    algorithmic content): the IMPROVEMENT branch — a poly-cost program
    approximating MaxEDP within a ratio that is o(√n).  This Prop is genuinely
    open (best known ratio is O(√n), Chekuri–Khanna–Shepherd; no o(√n)
    algorithm and no matching lower bound are known).  Fidelity note: the spec
    is the VALUE-ESTIMATION form (output approximates the optimum value; it
    does not demand a routing witness) — documented, weaker than
    solution-producing approximation, still open. *)
Definition approximation_ratio_for_maximum_edge_disjoint_paths_statement : Prop :=
  exists (p : prog) (rho : nat -> nat),
    maxedp_approx p rho /\ little_o_sqrt rho.

(** ================================================================= *)
(** ** Row 3 — Complexity of the H-factor problem  (OPEN)

    Source: "An H-factor in a graph G is a set of vertex-disjoint copies of H
    covering all vertices of G.  Problem Let c be a fixed positive real number
    and H a fixed graph.  Is it NP-hard to determine whether a graph G on n
    vertices and minimum degree cn contains an H-factor?"

    Carrier: the abstract decision [problem] whose instances are graphs of
    minimum degree [>= cn].  AREA primitives:
      - [is_copy f] / [h_factor H G] (H-factor): a copy of [H] in [G] is an
        injective homomorphism [H -> G]; an H-factor is a family of
        vertex-disjoint copies whose images PARTITION [V(G)];
      - [mindeg_cn G a b] (min-degree cn): the positive real [c] is the rational
        [a/b] ([0 < a <= b]); "min degree >= c*n" is the fraction-free
        [a*|G| <= b*deg(v)] for every [v];
      - the abstract-but-relational complexity layer [problem] / [poly_reduces]
        / [in_NP] / [NP_hard] (NP-hardness): a [problem] is a typed instance
        family with a size measure and a YES-predicate; [poly_reduces A B] is a
        poly-time, poly-size-blowup many-one reduction; [in_NP A] is a poly-size
        certificate + poly-time boolean verifier; [NP_hard B] is: every NP
        problem poly-reduces to [B].  No machine model: "computed in poly time"
        is the abstract cost bound — a UNIVERSAL hardness claim is non-vacuous
        in this reading (the coupled [prog] model is NOT needed here).
    The statement asserts NP-hardness of the (fixed-[H], fixed-[c]) H-factor
    problem; its truth value is the OPEN question. *)
(* [@MOVE-to-base]: [is_copy]/[h_factor] are cross-area (subgraph-copy /
   vertex-disjoint-cover) notions with no base counterpart yet; they migrate to
   base when a 2nd area needs them. *)
Definition is_copy (H G : sgraph) (f : H -> G) : Prop := injective f /\ is_hom f.

Definition h_factor (H G : sgraph) : Prop :=
  exists (m : nat) (blk : 'I_m -> {set G}) (emb : 'I_m -> (H -> G)),
    [/\ (forall v : G, exists i : 'I_m, v \in blk i),
        (forall (i j : 'I_m) (v : G), v \in blk i -> v \in blk j -> i = j),
        (forall i : 'I_m, is_copy (emb i)) &
        (forall i : 'I_m, blk i = [set emb i x | x in [set: H]]) ].

Definition mindeg_cn (G : sgraph) (a b : nat) : Prop :=
  forall v : G, a * #|G| <= b * #|N(v)|.

Record problem := Problem {
  pinput : Type;
  psize  : pinput -> nat;
  pmem   : pinput -> Prop }.

Definition poly_reduces (A B : problem) : Prop :=
  exists (f : pinput A -> pinput B) (cost : pinput A -> nat) (a d b : nat),
    [/\ (forall x, @pmem A x <-> @pmem B (f x)),
        (forall x, cost x <= a * (@psize A x) ^ d + b) &
        (forall x, @psize B (f x) <= a * (@psize A x) ^ d + b) ].

Definition in_NP (A : problem) : Prop :=
  exists (verify : pinput A -> seq bool -> bool)
         (vcost : pinput A -> seq bool -> nat) (a d b : nat),
    (forall x, @pmem A x <-> exists cert : seq bool,
        size cert <= a * (@psize A x) ^ d + b /\ verify x cert) /\
    (forall x cert, vcost x cert <= a * (@psize A x + size cert) ^ d + b).

Definition NP_hard (B : problem) : Prop :=
  forall A : problem, in_NP A -> poly_reduces A B.

Definition hfactor_problem (H : sgraph) (a b : nat) : problem :=
  {| pinput := {G : sgraph | mindeg_cn G a b};
     psize  := fun GH => #| sval GH |;
     pmem   := fun GH => h_factor H (sval GH) |}.

(* Non-triviality guard on [H] (faithfulness): with only [0 < #|H|] the claim is
   refutable — H = K1 makes every graph a YES-instance (in P) and H = K2 is a
   perfect matching (Edmonds, in P), so [NP_hard] would be FALSE rather than
   open.  We restrict to the regime the source intends ("a fixed graph H"): H
   CONNECTED on at least 3 vertices (the Hell–Kirkpatrick threshold of a
   component of order >= 3), where NP-hardness is the genuine OPEN question. *)
(** GUARD FIX (Track-B skeptic): the density ratio c = a/b must be STRICTLY
    below 1 — at a = b (c = 1) [mindeg_cn G a a] demands deg(v) >= #|G|, which
    is impossible on an irreflexive graph, so the instance class is empty and
    [NP_hard] is FALSE there, making the former [a <= b] form refutable
    axiom-free.  The source's "fixed positive real c" means 0 < c < 1. *)
Definition complexity_of_the_h_factor_statement : Prop :=
  forall (H : sgraph) (a b : nat),
    0 < a -> a < b -> 2 < #|H| -> connected [set: H] ->
    NP_hard (hfactor_problem H a b).

(** ================================================================= *)
(** ** Row 4 — PTAS for feedback arc set in tournaments  (SOLVED, statement-only)

    Source: "Question Is there a polynomial time approximation scheme for the
    feedback arc set problem for the class of tournaments?"
    Status: SOLVED (Kenyon-Mathieu-Schudy PTAS, 2007); we state only the math
    predicate "a PTAS exists", now in the coupled [prog] model — no proof of
    the PTAS is attempted here.

    Carrier: [t_input := {T : finType & rel T}] (a tournament given by its arc
    relation), encoded ([enc_tournament]) as the arc matrix over [enum T].
    AREA primitives:
      - [is_tournament T r] (tournament): irreflexive + for distinct [x,y]
        exactly one of [r x y], [r y x] (asymmetric & complete);
      - [back_arcs r pos] (feedback arc set, ordering form): the number of arcs
        pointing BACKWARD under the linear order [pos : T -> nat]; for a
        tournament the minimum feedback arc set equals the minimum over orders;
      - [fas_opt r k] : [k] is that minimum;
      - [fas_ptas_spec num den] (per-instance correctness): on a tournament
        with optimum [k], the program's output VALUE ([dnat_val]) is
        achievable ([OPT <= value]) and within [(1 + num/den)] of the optimum,
        fraction-free: [den * value <= (den + num) * k].
    The PTAS predicate (ptas / polytime-algorithm), COUPLED: for every rational
    [eps = p/q > 0] (a positive nat pair) there EXISTS one [prog] realizing
    [fas_ptas_spec p q] on every encoded tournament, with polynomially bounded
    step count [poly_cost_on enc_tournament].  The program — hence its
    polynomial cost bound — is chosen AFTER [eps], so the polynomial may depend
    on [eps]: that dependence is exactly what "PTAS" means (as opposed to the
    stronger uniform/FPTAS reading). *)
Definition is_tournament (T : finType) (r : rel T) : Prop :=
  (forall x : T, ~~ r x x) /\ (forall x y : T, x != y -> r x y (+) r y x).

Definition back_arcs {T : finType} (r : rel T) (pos : T -> nat) : nat :=
  #|[set p : T * T | r p.1 p.2 && (pos p.2 < pos p.1)]|.

Definition fas_opt {T : finType} (r : rel T) (k : nat) : Prop :=
  (exists pos : T -> nat, injective pos /\ back_arcs r pos = k) /\
  (forall pos : T -> nat, injective pos -> k <= back_arcs r pos).

Definition t_input : Type := {T : finType & rel T}.
Definition t_vsize (x : t_input) : nat := #|projT1 x|.

Definition enc_tournament (x : t_input) : data :=
  enc_list [seq enc_list [seq enc_bool (projT2 x i j) | j <- enum (projT1 x)]
           | i <- enum (projT1 x)].

Definition fas_ptas_spec (num den : nat) (x : t_input) (out : data) : Prop :=
  forall k : nat,
    is_tournament (projT2 x) -> fas_opt (projT2 x) k ->
    k <= dnat_val out /\ den * dnat_val out <= (den + num) * k.

Definition ptas_for_feedback_arc_set_in_tournaments_statement : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    exists alg : prog,
      realizes_on enc_tournament (fas_ptas_spec p q) alg /\
      poly_cost_on enc_tournament alg.

(** ================================================================= *)
(** ** Row 5 — Finding k-edge-outerplanar graph embeddings  (OPEN)

    Source: "Conjecture It has been shown that a k-outerplanar embedding for
    which k is minimal can be found in polynomial time.  Does a similar result
    hold for k-edge-outerplanar graphs?"

    Carrier: [G : sgraph], encoded as its adjacency matrix ([enc_graph], from
    complexity.v; [dsize (enc_graph G)] is Theta(#|G|^2), so poly-in-[dsize] =
    poly-in-vertices).  AREA primitive [edge_outerplanar] /
    [min_edge_outerplanar] (outerplanar-layering): a PROXY for
    k-edge-outerplanarity — a planar graph ([wagner_planar]) with a symmetric
    edge-layering [elev : G -> G -> nat] of depth [k] in which edges sharing a
    vertex lie in adjacent layers and the outer (zero) layer is realised.
    [The faithful faces/outer-boundary definition needs the embedding API of
    the planarity package, gate G2; this layering is the available
    combinatorial skeleton.]  [min_edge_outerplanar G k] fixes [k] as the
    minimum depth.  The statement asserts the EXISTENCE of ONE [prog] whose
    output VALUE ([dnat_val], via [min_eop_spec]) is that minimal [k] on EVERY
    (nonempty, planar, edged) instance — the witness layering lives inside
    [edge_outerplanar] — and whose step count on the SAME encodings is
    polynomial ([poly_cost_on enc_graph]). *)
(** PROXY REPAIR (Track-B skeptic, machine-checked): the former layering
    proxy admitted the all-zero level function, making the minimum depth 1 on
    EVERY planar edged instance — so the constant program [Pconst (Dnat 1)]
    PROVED the "open" statement outright (the oracle attack in coupled
    clothing: the spec, not the cost, was degenerate).  The repaired proxy has
    a genuine LEVEL-FORCING clause: each level's edge-subgraph must be
    OUTERPLANAR in the Chartrand–Harary minor sense (no K4 and no K2,3 minor).
    Now minima differ across instances ('K_2 has depth 1; 'K_4 is planar but
    not outerplanar, so it needs >= 2 levels), which kills every
    constant-output program.  Still a documented PROXY for true
    k-edge-outerplanarity (the faces/outer-boundary definition — now
    expressible in principle via the Track-A embedding layer — remains
    follow-up work): genuine k-edge-outerplanar graphs peel into k outerplanar
    edge-layers, so the proxy is implied by the true notion. *)
Definition outerplanar_w (G : sgraph) : Prop :=
  ~ minor G 'K_4 /\ ~ minor G (KB 2 3).

(** The subgraph of [G] carrying exactly the level-[j] edges of [lev]
    (symmetrised; irreflexivity inherited from [G]). *)
Definition level_rel (G : sgraph) (lev : G -> G -> nat) (j : nat) : rel G :=
  fun x y => [&& x -- y, lev x y == j & lev y x == j].
Lemma level_rel_sym (G : sgraph) (lev : G -> G -> nat) (j : nat) :
  symmetric (level_rel lev j).
Proof. by move=> x y; rewrite /level_rel sg_sym [X in _ && X]andbC. Qed.
Lemma level_rel_irr (G : sgraph) (lev : G -> G -> nat) (j : nat) :
  irreflexive (level_rel lev j).
Proof. by move=> x; rewrite /level_rel sg_irrefl. Qed.
Definition level_graph (G : sgraph) (lev : G -> G -> nat) (j : nat) : sgraph :=
  SGraph (@level_rel_sym G lev j) (@level_rel_irr G lev j).

Definition edge_outerplanar (G : sgraph) (k : nat) : Prop :=
  wagner_planar G /\
  exists lev : G -> G -> nat,
    (forall x y : G, x -- y -> lev x y < k) /\
    (forall j : nat, j < k -> outerplanar_w (level_graph lev j)).

Definition min_edge_outerplanar (G : sgraph) (k : nat) : Prop :=
  edge_outerplanar G k /\ (forall m : nat, edge_outerplanar G m -> k <= m).

Definition min_eop_spec (G : sgraph) (out : data) : Prop :=
  0 < #|G| -> wagner_planar G -> (exists x y : G, x -- y) ->
  min_edge_outerplanar G (dnat_val out).

Definition finding_k_edge_outerplanar_graph_embeddings_statement : Prop :=
  exists p : prog,
    realizes_on enc_graph min_eop_spec p /\ poly_cost_on enc_graph p.

(** ================================================================= *)
(** ** Non-triviality / sanity guards (all statements are well-typed Props) *)
Check algorithm_for_graph_homomorphisms_statement : Prop.
Check approximation_ratio_for_maximum_edge_disjoint_paths_statement : Prop.
Check complexity_of_the_h_factor_statement : Prop.
Check ptas_for_feedback_arc_set_in_tournaments_statement : Prop.
Check finding_k_edge_outerplanar_graph_embeddings_statement : Prop.
