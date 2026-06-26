(** * Hypergraph.conjectures.U12 — milestone U12 (namespace Hypergraph, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four OPEN problems on finite hypergraphs.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph]).  Every row is about
    finite hypergraphs, modelled — following each row's [rocq_idiom] — as a
    finite vertex type [T : finType] together with a family of hyperedges
    [E : {set {set T}}] (each hyperedge a vertex set).  Frankl's row (Row 1)
    operates directly on the set family [F : {set {set T}}], exactly as in the
    union-closed-sets formulation.

      - Row 1 (Frankl's union-closed sets): family [F : {set {set T}}],
        carrier [{set {set T}}];
      - Row 2 (Turán for 3-uniform hypergraphs): vertices [T : finType],
        hyperedges [E : {set {set T}}];
      - Row 3 (critical k-forests): vertices [T], hyperedges [E];
      - Row 4 (Ryser): vertices [T] with an r-part assignment [part : T -> 'I_r],
        hyperedges [E].

    No multigraph [edge]/[source]/[target] API is needed (object level is vertex
    SUBSETS), so we do not import coq-graph-theory's [mgraph]; [base] (which
    re-exports all_boot + the undirected vocabulary, [finset], [tuple], …) is the
    sole import.  No base primitive matches these hypergraph notions, so every
    primitive below is AREA-SPECIFIC (none is a cross-area [@MOVE-to-base]
    candidate at this point — they are hypergraph-only).

    AREA primitives introduced here (all hypergraph-specific): [union_closed]
    (union-closed-family, Row 1); [k_uniform] (uniform-hypergraph, Rows 2,3),
    [complete_sub] / [contains_complete] (complete-hypergraph K_m^{(k)} subobject,
    Row 2) — [#|E|] is the hyperedge-count directly; [berge_cycle] / [berge_acyclic]
    / [hg_connected] / [k_forest] / [k_tree] / [critical_k_forest] (k-forest,
    k-tree and forest-maximality "criticality", Row 3); [r_partite_uniform]
    (r-partite-uniform), [hg_matching] / [is_matching_number] (ν, matching-number),
    [hg_cover] / [is_cover_number] (τ, cover-number) (Row 4).

    NAMING: predicates carrying an existence/uniqueness extremal flavour use the
    [is_] prefix ([is_matching_number], [is_cover_number]); the [hg_] prefix on
    [hg_matching] / [hg_cover] / [hg_connected] dodges any clash with generic
    mathcomp vocabulary. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared hypergraph primitives *)

(** A [k]-uniform hyperedge family: every hyperedge has exactly [k] vertices. *)
Definition k_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = k.

(** ================================================================= *)
(** ** Row 1 — Frankl's union-closed sets conjecture  (OPEN)

    Source: "Conjecture Let F be a finite family of finite sets, not all empty,
    that is closed under taking unions.  Then there exists x such that x is an
    element of at least half the members of F."

    Carrier: the set family [F : {set {set T}}] over a finite vertex type [T]
    (finite sets ↦ finite [T]).  "Closed under taking unions" = [union_closed].
    "Not all empty" is the faithful non-triviality guard [exists2 A, A \in F &
    A != set0] (some member is nonempty; this also forces [F != set0]).  "x in at
    least half the members" = [#|F| <= 2 * #|members of F containing x|]
    (fraction-free). *)

(** A family closed under taking (pairwise, hence finite) unions. *)
Definition union_closed (T : finType) (F : {set {set T}}) : Prop :=
  forall A B : {set T}, A \in F -> B \in F -> (A :|: B) \in F.

Definition frankls_union_closed_sets_statement : Prop :=
  forall (T : finType) (F : {set {set T}}),
    union_closed F ->
    (exists2 A : {set T}, A \in F & A != set0) ->
    exists x : T, #|F| <= 2 * #|[set A in F | x \in A]|.

(** ================================================================= *)
(** ** Row 2 — Turán's problem for 3-uniform hypergraphs  (OPEN)

    Source (primary, K_4^{(3)}-free leg): "Conjecture Every simple 3-uniform
    hypergraph on 3n vertices which contains no complete 3-uniform hypergraph on
    four vertices has at most ½ n²(5n-3) hyperedges."

    Carrier: vertices [T : finType], hyperedges [E : {set {set T}}].  simple +
    3-uniform = [k_uniform E 3] (a [{set {set T}}] family is automatically simple:
    no repeated hyperedges).  "On 3n vertices" = [#|T| = 3 * n].  "Contains no
    complete 3-uniform hypergraph on four vertices" = no 4-set all of whose
    3-subsets are hyperedges = [~ contains_complete E 4 3].  Hyperedge count =
    [#|E|].  The bound ½ n²(5n-3) is stated fraction-free as
    [2 * #|E| <= n^2 * (5*n - 3)].  Guard [0 < n]. *)

(** [S] spans a complete [k]-uniform hypergraph: every [k]-subset of [S] is a
    hyperedge. *)
Definition complete_sub (T : finType) (E : {set {set T}}) (S : {set T}) (k : nat)
  : Prop :=
  forall e : {set T}, e \subset S -> #|e| = k -> e \in E.

(** [E] contains a complete [k]-uniform hypergraph on [m] vertices
    (a copy of K_m^{(k)}). *)
Definition contains_complete (T : finType) (E : {set {set T}}) (m k : nat) : Prop :=
  exists S : {set T}, #|S| = m /\ complete_sub E S k.

Definition turans_problem_for_hypergraphs_statement : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    0 < n ->
    k_uniform E 3 ->
    #|T| = 3 * n ->
    ~ contains_complete E 4 3 ->
    2 * #|E| <= n ^ 2 * (5 * n - 3).

(** ================================================================= *)
(** ** Row 3 — Are critical k-forests tight?  (OPEN)

    Source: "Conjecture Let H be a k-uniform hypergraph.  If H is a critical
    k-forest, then it is a k-tree."

    Carrier: vertices [T : finType], hyperedges [E : {set {set T}}], with [E]
    [k]-uniform.  Hypergraph acyclicity is Berge-acyclicity ([berge_acyclic]):
    no Berge cycle (distinct vertices [v_i] and distinct hyperedges [e_i],
    [t >= 2], with [v_i ∈ e_i ∩ e_{i+1}] cyclically).  A [k]-forest is a
    [k]-uniform Berge-acyclic family; a [k]-tree is a connected [k]-forest
    ([hg_connected]: every two hyperedges are joined by an intersection-path of
    hyperedges).  "Critical" is read as forest-maximality: no new [k]-hyperedge
    can be added while staying Berge-acyclic.  The conjecture then asks whether a
    maximal [k]-forest is forced to be connected (a single [k]-tree).  Guards
    [0 < k] and the non-triviality requirement [E != set0] (the forest has at
    least one hyperedge — without it the empty family [E = set0] over a carrier
    with [#|T| < k] vacuously satisfies [critical_k_forest] yet fails [k_tree],
    refuting the statement; [E != set0] together with [k]-uniformity also forces
    [k <= #|T|]). *)

(** A Berge cycle of [E]: distinct vertices [vs] and distinct hyperedges [es]
    of common length [t >= 2], with [v_i ∈ e_i] and [v_i ∈ e_{i+1}] (cyclically,
    via [rot 1 es]) — each [v_i] links two consecutive hyperedges. *)
Definition berge_cycle (T : finType) (E : {set {set T}}) : Prop :=
  exists (vs : seq T) (es : seq {set T}),
    [/\ 2 <= size es,
        size vs = size es,
        uniq vs && uniq es,
        (forall e : {set T}, e \in es -> e \in E)
      & all (fun t : T * ({set T} * {set T}) =>
               let: (v, ef) := t in (v \in ef.1) && (v \in ef.2))
            (zip vs (zip es (rot 1 es)))].

(** Berge-acyclic = no Berge cycle. *)
Definition berge_acyclic (T : finType) (E : {set {set T}}) : Prop :=
  ~ berge_cycle E.

(** Connected hypergraph: nonempty, and any two hyperedges are joined by a path
    of hyperedges with consecutive members intersecting (Berge-connectivity). *)
Definition hg_connected (T : finType) (E : {set {set T}}) : Prop :=
  E != set0 /\
  forall e f : {set T}, e \in E -> f \in E ->
    exists p : seq {set T},
      [/\ path (fun a b => a :&: b != set0) e p,
          last e p = f
        & all (fun a => a \in E) p].

(** A [k]-forest: a [k]-uniform Berge-acyclic hyperedge family. *)
Definition k_forest (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  k_uniform E k /\ berge_acyclic E.

(** A [k]-tree: a connected [k]-forest. *)
Definition k_tree (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  k_forest E k /\ hg_connected E.

(** A critical [k]-forest: a [k]-forest that is maximal Berge-acyclic — adjoining
    any further [k]-hyperedge creates a Berge cycle. *)
Definition critical_k_forest (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  k_forest E k /\
  (forall e : {set T}, #|e| = k -> e \notin E -> berge_cycle (e |: E)).

Definition are_critical_k_forests_tight_statement : Prop :=
  forall (k : nat) (T : finType) (E : {set {set T}}),
    0 < k ->
    E != set0 ->
    critical_k_forest E k ->
    k_tree E k.

(** ================================================================= *)
(** ** Row 4 — Ryser's conjecture  (OPEN)

    Source: "Conjecture Let H be an r-uniform r-partite hypergraph.  If ν is the
    maximum number of pairwise disjoint edges in H, and τ is the size of the
    smallest set of vertices which meets every edge, then τ ≤ (r-1)ν."

    Carrier: vertices [T : finType] with an r-part assignment [part : T -> 'I_r]
    (the r colour classes), hyperedges [E : {set {set T}}].  r-uniform r-partite =
    [r_partite_uniform part E r]: every hyperedge meets each of the [r] parts in
    exactly one vertex (so [|e| = r], one vertex per part).  ν (matching-number) =
    [is_matching_number E ν]: max size of a family of pairwise-disjoint hyperedges.
    τ (cover-number) = [is_cover_number E τ]: min size of a vertex set meeting
    every hyperedge.  Guard [1 < r] (i.e. [2 <= r]): this is the faithful domain
    of Ryser's conjecture.  At [r = 1] the bound degenerates to [τ <= 0] while
    [τ = ν > 0] whenever an edge exists, so [r = 1] would make the statement
    refutable rather than open; [r = 2] is König's theorem, [r = 3] is Aharoni's
    theorem, and the problem is open for [r >= 4].  ([1 < r] also keeps ['I_r]
    inhabited and makes [r - 1] the intended predecessor.) *)

(** r-uniform r-partite: every hyperedge has exactly one vertex in each part [j]. *)
Definition r_partite_uniform (T : finType) (r : nat) (part : T -> 'I_r)
  (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E ->
    forall j : 'I_r, #|[set v in e | part v == j]| = 1.

(** A matching: a subfamily of pairwise-disjoint hyperedges. *)
Definition hg_matching (T : finType) (M E : {set {set T}}) : Prop :=
  M \subset E /\
  {in M &, forall e f : {set T}, e != f -> [disjoint e & f]}.

(** [nu] is the matching number ν(H): the maximum size of a matching. *)
Definition is_matching_number (T : finType) (E : {set {set T}}) (nu : nat) : Prop :=
  (exists M : {set {set T}}, hg_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, hg_matching M E -> #|M| <= nu).

(** A vertex cover: a vertex set meeting every hyperedge. *)
Definition hg_cover (T : finType) (X : {set T}) (E : {set {set T}}) : Prop :=
  forall e : {set T}, e \in E -> X :&: e != set0.

(** [tau] is the cover number τ(H): the minimum size of a vertex cover. *)
Definition is_cover_number (T : finType) (E : {set {set T}}) (tau : nat) : Prop :=
  (exists X : {set T}, hg_cover X E /\ #|X| = tau) /\
  (forall X : {set T}, hg_cover X E -> tau <= #|X|).

Definition rysers_statement : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}})
         (nu tau : nat),
    1 < r ->
    r_partite_uniform part E ->
    is_matching_number E nu ->
    is_cover_number E tau ->
    tau <= (r - 1) * nu.
