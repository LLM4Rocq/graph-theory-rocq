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

    ABSTRACT COST / ALGORITHM LAYER (shared by every row, plan §"algorithmic
    rows").  We DELIBERATELY keep "algorithm", "running time", "polynomial time",
    "approximation ratio", "PTAS" and "NP-hard" RELATIONAL and machine-free: an
    algorithm is an abstract function plus an abstract cost function [I -> nat],
    and the cost bounds are Props ([runs_in_time], [poly_bounded]) — NO Turing /
    RAM model is built.  "Polynomial" is encoded concretely as a bound
    [n |-> a*n^d + b] (the repo-wide convention, cf. digraph-theory unvd.prob_6).
    These cross-row helpers are AREA-LOCAL to graph-theory-misc; a second area
    needing them would trigger a [@MOVE-to-base] into a foundations module
    [foundations/complexity.v].

    REUSE FROM graph-theory-base (GTBase.base): [homs_to]/[is_hom] (Rows 1,3),
    [wagner_planar] (combinatorial Wagner planarity, the available planarity
    proxy — the embedding/face API arrives with gate G2; Rows 2,5).  Every other
    notion is AREA-SPECIFIC and defined locally. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared abstract cost / algorithm vocabulary (area-local)

    [decides verdict P]   — the boolean algorithm [verdict] decides predicate [P];
    [runs_in_time c bnd]  — abstract cost [c] is pointwise bounded by [bnd];
    [poly_bounded sz c]   — [c] is bounded by a polynomial [a*sz^d + b] in the
                            instance size [sz].  All three are relational Props;
    none commits to a computation model. *)
Definition decides {I : Type} (verdict : I -> bool) (P : I -> Prop) : Prop :=
  forall x : I, verdict x <-> P x.

Definition runs_in_time {I : Type} (cost bound : I -> nat) : Prop :=
  forall x : I, cost x <= bound x.

Definition poly_bounded {I : Type} (size cost : I -> nat) : Prop :=
  exists a d b : nat, forall x : I, cost x <= a * (size x) ^ d + b.

(** ================================================================= *)
(** ** Row 1 — An algorithm for graph homomorphisms  (OPEN)

    Source: "Question Is there an algorithm that decides, for input graphs G and
    H, whether there exists a homomorphism from G to H in time
    O(c^(|V(G)|+|V(H)|)) for some constant c?"

    Carrier: a pair [sgraph * sgraph].  The decision predicate is base's
    [homs_to G H] (existence of an adjacency-preserving map).  "in time
    O(c^(|G|+|H|)) for some constant c" is [runs_in_time cost (c^(|G|+|H|))] for
    an existentially-quantified base [c] (guard [1 < c]: a genuine exponential
    base).  The whole question is the EXISTENCE of such a [(decide, cost)]. *)
Definition algorithm_for_graph_homomorphisms_statement : Prop :=
  exists (c : nat) (decide : sgraph * sgraph -> bool)
         (cost : sgraph * sgraph -> nat),
    [/\ 1 < c,
        decides decide (fun GH => homs_to GH.1 GH.2) &
        runs_in_time cost (fun GH => c ^ (#|GH.1| + #|GH.2|)) ].

(** ================================================================= *)
(** ** Row 2 — Approximation ratio for Maximum Edge-Disjoint Paths  (OPEN)

    Source: "Conjecture Can the approximation ratio O(sqrt(n)) be improved for
    the Maximum Edge Disjoint Paths problem (MaxEDP) in planar graphs or can an
    inapproximability result stronger than APX-hardness?"

    Carrier: [edp_input := {G : sgraph & seq (G*G)}] (a graph with a list of
    terminal demands), restricted to planar [G] via base's [wagner_planar].
    AREA primitives:
      - [walkb s t p] / [walk_uses s p u v] (walk / edge-usage): [p] is a walk
        from [s] to [t]; it uses undirected edge [{u,v}] iff [(u,v)] is a
        consecutive pair of [s::p] (via [zip (s::p) p]);
      - [edp_feasible S route] (edge-disjoint routing): the demands indexed by
        [S] are routed by pairwise EDGE-DISJOINT walks [route];
      - [edp_opt D k] (MaxEDP optimum): [k] is the maximum number of
        simultaneously routable demands;
      - [maxedp_approx alg cost rho] (approximation-ratio): a poly-time
        algorithm whose output value [alg] is feasible ([<= OPT]) and within
        ratio [rho(|V|)] of the optimum ([OPT <= rho(n)*alg]);
      - [little_o_sqrt rho] : [rho(n) = o(sqrt n)]  (for all [c], eventually
        [c*rho(n)^2 <= n]).
    The disjunctive question is stated faithfully: EITHER the ratio can be pushed
    below sqrt(n) (a poly-time [o(sqrt n)]-approximation exists), OR a
    stronger-than-APX inapproximability holds (NO poly-time CONSTANT-factor
    approximation exists). *)
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

Definition maxedp_approx (alg cost : edp_input -> nat) (rho : nat -> nat) : Prop :=
  poly_bounded edp_vsize cost /\
  forall (x : edp_input) (k : nat),
    wagner_planar (projT1 x) -> edp_opt (projT2 x) k ->
    alg x <= k /\ k <= rho #|projT1 x| * alg x.

Definition little_o_sqrt (rho : nat -> nat) : Prop :=
  forall c : nat, exists N : nat, forall n : nat, N <= n -> c * (rho n) ^ 2 <= n.

Definition approximation_ratio_for_maximum_edge_disjoint_paths_statement : Prop :=
  (exists (alg cost : edp_input -> nat) (rho : nat -> nat),
      maxedp_approx alg cost rho /\ little_o_sqrt rho)
  \/
  (forall (alg cost : edp_input -> nat) (rho0 : nat),
      0 < rho0 -> ~ maxedp_approx alg cost (fun _ => rho0)).

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
        is the abstract cost bound.
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
Definition complexity_of_the_h_factor_statement : Prop :=
  forall (H : sgraph) (a b : nat),
    0 < a -> a <= b -> 2 < #|H| -> connected [set: H] ->
    NP_hard (hfactor_problem H a b).

(** ================================================================= *)
(** ** Row 4 — PTAS for feedback arc set in tournaments  (SOLVED, statement-only)

    Source: "Question Is there a polynomial time approximation scheme for the
    feedback arc set problem for the class of tournaments?"
    Status: SOLVED (Kenyon-Mathieu-Schudy PTAS, 2007); we state only the math
    predicate "a PTAS exists" — the algorithm/cost model is out of scope.

    Carrier: [t_input := {T : finType & rel T}] (a tournament given by its arc
    relation).  AREA primitives:
      - [is_tournament T r] (tournament): irreflexive + for distinct [x,y]
        exactly one of [r x y], [r y x] (asymmetric & complete);
      - [back_arcs r pos] (feedback arc set, ordering form): the number of arcs
        pointing BACKWARD under the linear order [pos : T -> nat]; for a
        tournament the minimum feedback arc set equals the minimum over orders;
      - [fas_opt r k] : [k] is that minimum;
      - the PTAS predicate (ptas / polytime-algorithm): for every rational
        [eps = p/q > 0] there is a poly-time algorithm whose value [alg] is
        achievable ([OPT <= alg]) and within [(1+eps)] of the optimum, written
        fraction-free as [q*alg <= (q+p)*OPT]. *)
Definition is_tournament (T : finType) (r : rel T) : Prop :=
  (forall x : T, ~~ r x x) /\ (forall x y : T, x != y -> r x y (+) r y x).

Definition back_arcs {T : finType} (r : rel T) (pos : T -> nat) : nat :=
  #|[set p : T * T | r p.1 p.2 && (pos p.2 < pos p.1)]|.

Definition fas_opt {T : finType} (r : rel T) (k : nat) : Prop :=
  (exists pos : T -> nat, injective pos /\ back_arcs r pos = k) /\
  (forall pos : T -> nat, injective pos -> k <= back_arcs r pos).

Definition t_input : Type := {T : finType & rel T}.
Definition t_vsize (x : t_input) : nat := #|projT1 x|.

Definition ptas_for_feedback_arc_set_in_tournaments_statement : Prop :=
  forall p q : nat, 0 < p -> 0 < q ->
    exists (alg cost : t_input -> nat) (a d b : nat),
      (forall x : t_input, cost x <= a * (t_vsize x) ^ d + b) /\
      forall (x : t_input) (k : nat),
        is_tournament (projT2 x) ->
        fas_opt (projT2 x) k ->
        k <= alg x /\ q * alg x <= (q + p) * k.

(** ================================================================= *)
(** ** Row 5 — Finding k-edge-outerplanar graph embeddings  (OPEN)

    Source: "Conjecture It has been shown that a k-outerplanar embedding for
    which k is minimal can be found in polynomial time.  Does a similar result
    hold for k-edge-outerplanar graphs?"

    Carrier: [G : sgraph].  AREA primitive [edge_outerplanar] / [min_edge_outerplanar]
    (outerplanar-layering): a PROXY for k-edge-outerplanarity — a planar graph
    ([wagner_planar]) with a symmetric edge-layering [elev : G -> G -> nat] of
    depth [k] in which edges sharing a vertex lie in adjacent layers and the
    outer (zero) layer is realised.  [The faithful faces/outer-boundary
    definition needs the embedding API of the planarity package, gate G2; this
    layering is the available combinatorial skeleton.]  [min_edge_outerplanar G k]
    fixes [k] as the minimum depth.  The statement asserts the EXISTENCE of a
    poly-time algorithm [alg] computing that minimal [k] together with a witness
    embedding (the layering inside [edge_outerplanar]). *)
Definition edge_outerplanar (G : sgraph) (k : nat) : Prop :=
  wagner_planar G /\
  exists elev : G -> G -> nat,
    [/\ (forall x y : G, elev x y = elev y x),
        (forall x y : G, x -- y -> elev x y < k),
        (forall x y z : G, x -- y -> x -- z -> elev x y <= (elev x z).+1) &
        (exists x y : G, (x -- y) /\ elev x y = 0) ].

Definition min_edge_outerplanar (G : sgraph) (k : nat) : Prop :=
  edge_outerplanar G k /\ (forall m : nat, edge_outerplanar G m -> k <= m).

Definition finding_k_edge_outerplanar_graph_embeddings_statement : Prop :=
  exists (alg cost : sgraph -> nat),
    poly_bounded (fun G : sgraph => #|G|) cost /\
    forall G : sgraph,
      0 < #|G| -> wagner_planar G -> (exists x y : G, x -- y) ->
      min_edge_outerplanar G (alg G).

(** ================================================================= *)
(** ** Non-triviality / sanity guards (all statements are well-typed Props) *)
Check algorithm_for_graph_homomorphisms_statement : Prop.
Check approximation_ratio_for_maximum_edge_disjoint_paths_statement : Prop.
Check complexity_of_the_h_factor_statement : Prop.
Check ptas_for_feedback_arc_set_in_tournaments_statement : Prop.
Check finding_k_edge_outerplanar_graph_embeddings_statement : Prop.
