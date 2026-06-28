(** * Minor.conjectures.U7 — milestone U7 (namespace Minor, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of six open problems on graph minors and immersions.

    CORE API used (verified to load on switch `digraph`, Rocq 9.1.1 +
    coq-graph-theory + graph-theory-base):
      - [G : sgraph]; [x -- y] adjacency = [sedge x y]; [N(x)] open
        neighbourhood ({set G}); [#|N(v)|] = degree of [v];
      - [minor G H : Prop] — note the LIBRARY ORDER: [minor G H] means "G
        CONTAINS H as a minor" ([exists phi, minor_map phi]).  So "G has a K6
        minor" is [minor G 'K_6], NOT [minor 'K_6 G];
      - ['K_n] = [complete n : sgraph] : the complete graph on [n] vertices —
        the manifest's "complete-graph" primitive ALREADY exists as ['K_n], so
        no new primitive is introduced for it;
      - [k.-connected G] = [kconnected k G : Prop] (connectivity.v);
      - [α(G)] = independence number (whole graph); [α(G) <= 2] ⟺ no
        independent set of size 3;
      - [χ([set: G])] = chromatic number of the whole graph (coloring.v);
      - [induced (~: S)] : the subgraph of [G] obtained by DELETING the vertex
        set [S] (induced on the complement);
      - [regular G d] (base) : every vertex of [G] has degree exactly [d];
      - [ceil_div a b] (base) : ⌈a/b⌉.

    PLANARITY GATE (plan G2).  coq-graph-theory-planar / coq-fourcolor are NOT
    installed.  The two rows whose statement needs planarity
    ([high_connectivity_no_k_n_statement], [jorgensens_statement]) take an
    ABSTRACT planarity predicate [is_planar : sgraph -> Prop] as a universally
    quantified hypothesis discharged INTO the statement — never a top-level
    Parameter/Axiom (that would contaminate Print Assumptions).  These two rows
    are therefore axiom-free and type-check, but are flagged compile_blocked:
    they are NOT a faithful planarity statement until a real [planar] predicate
    is available (G2).  The other five rows are unconditional. *)

From GraphTheory Require Import minor connectivity coloring.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** New AREA primitives *)

(** [path_edges s] : the set of (undirected) edges traversed by the vertex
    sequence [s], i.e. the 2-element sets of consecutive entries.  Helper for
    [immersion] below.  [@MOVE-to-base] candidate (walk/edge bookkeeping). *)
Definition path_edges (G : sgraph) (s : seq G) : {set {set G}} :=
  [set e in [seq [set p.1; p.2] | p <- zip s (behead s)]].

(** [immersion G H] : "G immerses H" (G contains an immersion of H).  There is
    an injection [f] of [V(H)] into [V(G)] and, for every edge [u -- v] of [H],
    a walk [f u :: P u v] in [G] from [f u] to [f v]; these walks are pairwise
    EDGE-DISJOINT (the defining feature of an immersion, as opposed to a
    topological minor where the branch paths must also be internally
    vertex-disjoint).  Cross-area primitive (used by the colouring conjecture
    below); not present in base — defined here and tagged [@MOVE-to-base]. *)
Definition immersion (G H : sgraph) : Prop :=
  exists (f : H -> G) (P : H -> H -> seq G),
    injective f /\
    (forall u v : H, u -- v ->
        path sedge (f u) (P u v) /\ last (f u) (P u v) = f v) /\
    (forall u1 v1 u2 v2 : H, u1 -- v1 -> u2 -- v2 ->
        [set u1; v1] != [set u2; v2] ->
        [disjoint path_edges (f u1 :: P u1 v1)
                & path_edges (f u2 :: P u2 v2)]).

(** [average_degree_geq G a b] : the average degree of [G] is at least the
    rational [a/b], stated cross-multiplied to stay in [nat].  Average degree
    = (∑ deg)/|G|, so "≥ a/b" ⟺ [a * #|G| <= b * (∑ deg)].  Cross-area
    (extremal) primitive, not in base — [@MOVE-to-base]. *)
(* [average_degree_geq] now from graph-theory-base (identical). *)

(** [planar_after_deleting is_planar G k] : there is a set of [k] vertices
    whose deletion leaves a planar graph (the "apex-bounded-deletion" notion).
    AREA primitive, parametrised by an abstract planarity predicate (G2 gate).
    Intentionally NOT tagged [@MOVE-to-base]: unlike the three cross-area
    helpers above, this and [apex] depend on the abstract [is_planar] and
    cannot migrate to base until a real [planar] predicate lands (G2). *)
Definition planar_after_deleting
    (is_planar : sgraph -> Prop) (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, #|S| = k /\ is_planar (induced (~: S)).

(** [apex is_planar G] : [G] is apex — deleting a single vertex makes it
    planar ("planar plus one vertex").  AREA primitive (G2 gate). *)
Definition apex (is_planar : sgraph -> Prop) (G : sgraph) : Prop :=
  exists v : G, is_planar (induced (~: [set v])).

(** ** Row 1 — Forcing a K6 minor
    OPEN.  Source (two conjectures, conjoined as the primary statement):
      "Every graph with minimum degree at least 7 contains a K6-minor."
      "Every 7-connected graph contains a K6-minor."
    Minimum degree ≥ 7 is [forall v, 7 <= #|N(v)|]; "contains a K6-minor" is
    [minor G 'K_6] (library order: G first). *)
Definition forcing_a_k_6_minor_statement : Prop :=
  (forall G : sgraph, 0 < #|G| ->
      (forall v : G, 7 <= #|N(v)|) -> minor G 'K_6)
  /\
  (forall G : sgraph, 0 < #|G| ->
      7.-connected G -> minor G 'K_6).

(** ** Row 2 — Seagull problem
    OPEN.  Source: "Every n-vertex graph with no independent set of size 3 has
    a complete graph on ≥ n/2 vertices as a minor."  No independent set of
    size 3 ⟺ [α(G) <= 2]; "K on ≥ n/2 vertices as a minor" is witnessed by the
    ceiling [⌈n/2⌉], i.e. [minor G 'K_(⌈#|G|/2⌉)]. *)
Definition seagull_statement : Prop :=
  forall G : sgraph, 0 < #|G| ->
    α(G) <= 2 -> minor G 'K_(ceil_div #|G| 2).

(** ** Row 3 — Colouring and immersion
    OPEN.  Source: "For every positive integer t, every (loopless) graph G with
    χ(G) ≥ t immerses K_t."  [sgraph] is loopless by construction (irreflexive
    adjacency), so no separate loopless hypothesis is needed. *)
Definition coloring_and_immersion_statement : Prop :=
  forall (t : nat) (G : sgraph),
    0 < t -> t <= χ([set: G]) -> immersion G 'K_t.

(** ** Row 4 — High connectivity, no K_n minor  [PLANARITY-GATED, compile_blocked]
    OPEN (Problem).  Source: "Is it true for all n ≥ 0 that every sufficiently
    large n-connected graph without a K_n minor has a set of n-5 vertices whose
    deletion results in a planar graph?"  Planarity abstracted as [is_planar].
    "Sufficiently large" is [exists N, forall G, N <= #|G| -> ...]. *)
Definition high_connectivity_no_k_n_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (n : nat),
    exists N : nat,
      forall G : sgraph,
        N <= #|G| -> n.-connected G -> ~ minor G 'K_n ->
        planar_after_deleting is_planar G (n - 5).

(** ** Row 5 — Jørgensen's conjecture  [PLANARITY-GATED, compile_blocked]
    OPEN.  Source: "Every 6-connected graph without a K6 minor is apex (planar
    plus one vertex)."  Planarity abstracted as [is_planar]. *)
Definition jorgensens_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    6.-connected G -> ~ minor G 'K_6 -> apex is_planar G.

(** ** Row 6 — Forcing a 2-regular minor
    OPEN.  Source: "Every graph with average degree at least (4/3)t - 2
    contains every 2-regular graph on t vertices as a minor."  Here
    (4/3)t - 2 = (4t-6)/3, so the degree bound is [average_degree_geq G (4*t-6) 3]
    (for [t >= 3] the numerator [4t-6] is positive, avoiding nat truncation; a
    2-regular graph needs at least 3 vertices, so [3 <= t] is the natural
    non-triviality guard).  The [0 < #|G|] guard is REQUIRED for soundness:
    without it the empty graph satisfies [average_degree_geq G _ 3] vacuously
    ([_ * 0 <= 3 * 0]) yet has no nonempty minor, refuting the statement.  It
    matches the [0 < #|G|] convention of Rows 1–2. *)
Definition forcing_a_2_regular_minor_statement : Prop :=
  forall (t : nat) (G H : sgraph),
    3 <= t ->
    0 < #|G| ->
    average_degree_geq G (4 * t - 6) 3 ->
    regular H 2 -> #|H| = t ->
    minor G H.
