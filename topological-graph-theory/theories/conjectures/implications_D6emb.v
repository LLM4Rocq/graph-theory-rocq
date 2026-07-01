(** * Topological.conjectures.implications_D6emb — milestone D6emb edges

    Implication / refutation EDGES among the three D6emb embedding / surface
    nodes, as Qed-closed RELATIVE theorems where one exists:

      - [grunbaums_statement]
          — the dual of a triangulation of an orientable surface is
            3-edge-colourable (a COLOURING-EXISTENCE claim; hypothesis:
            [triangulation E]);
      - [the_circular_embedding_statement]
          — every 2-connected graph has SOME embedding all of whose face
            boundaries are cycles (an EMBEDDING-EXISTENCE claim; hypothesis:
            [k_connected G 2]);
      - [what_is_the_largest_graph_of_positive_curvature_statement]
          — a uniform vertex bound [Nmax] over all connected, min-degree-3,
            everywhere-positive-curvature planar graphs that are neither a prism
            nor an antiprism (a FINITENESS claim).

    OUTCOME (honest).  The three D6emb rows are three MUTUALLY-INDEPENDENT famous
    open problems, grouped only by topic (surface embeddings / faces /
    curvature).  The verified-literature edge table of
    OPG_FULL_FORMALIZATION_PLAN.md §6 lists exactly ONE edge in this area —
    "circular/strong-embedding ⟹ CDC" (folklore: the face boundaries of a strong
    embedding form a cycle double cover) — but its TARGET, the Cycle Double Cover
    conjecture, is NOT a D6emb node (CDC lives in the cycle / double-cover
    milestone).  Hence that verified edge is cross-milestone and out of scope
    here.  Restricted to the THREE nodes above, §6 lists no "A ⟹ B".
    Consequently this milestone schedules ZERO verified edges — there is no real
    [Theorem A_implies_B. Qed] to add, because forcing one would either fail to
    compile or misstate the mathematics.  Per the edge policy a false / unclosing
    edge must NOT be forced.

    WHY THE STATEMENTS DO NOT LINK FORMALLY (pairwise).

    (1) [grunbaums_statement] vs [the_circular_embedding_statement].  A
    triangulation IS a circular (strong) embedding — every face is a triangle
    and a triangle boundary is a 3-cycle — so Grünbaum's HYPOTHESIS is a special
    case of the embeddings the circular-embedding conjecture produces.  But this
    is a relation between the two HYPOTHESES, not an implication between the two
    CONCLUSIONS, and the conclusions are of incomparable kind: Grünbaum asserts a
    3-edge-COLOURING of the dual of a given triangulation, whereas the
    circular-embedding conjecture asserts the EXISTENCE of a circular EMBEDDING
    for an arbitrary 2-connected graph.  Neither direction closes:
      • [the_circular_embedding_statement -> grunbaums_statement] would have to
        manufacture a dual 3-edge-colouring of an already-given triangulation out
        of an embedding-existence guarantee for arbitrary 2-connected graphs — it
        supplies an embedding, never a colouring, and for the wrong graph class;
      • [grunbaums_statement -> the_circular_embedding_statement] would have to
        manufacture a circular embedding of an arbitrary 2-connected graph out of
        a colouring guarantee that only speaks about graphs that ALREADY carry a
        triangulation embedding.
    So there is no logical implication in either direction; the shared "orientable
    triangulation / strong embedding" vocabulary is a hypothesis coincidence, not
    an edge.  (Both conjectures are, separately, known to IMPLY the Cycle Double
    Cover conjecture — Grünbaum via the CDC in the cubic-dual setting, circular
    embedding via §6's folklore edge — but converging on a THIRD, out-of-milestone
    target is not an edge between them.)

    (2) [what_is_the_largest_graph_of_positive_curvature_statement] vs the other
    two.  The finiteness node is a quantitative bound over a specific graph class
    (connected, planar, min-degree ≥ 3, everywhere-positive combinatorial
    curvature, prism/antiprism-excluded).  It yields no colouring and no
    embedding-existence guarantee, so it cannot deliver Grünbaum or the circular
    embedding; conversely neither a dual-3-edge-colouring guarantee nor a
    circular-embedding-existence guarantee bounds the ORDER of positive-curvature
    graphs (a triangulation or a circularly-embeddable graph can be arbitrarily
    large and can have curvature of either sign at a vertex — positive curvature
    forces the local face/degree pattern that the other two do not constrain).
    The node is mutually independent of the other two.

    No pair even exhibits the "looks-like-an-edge but the constant / transfer step
    is the whole conjecture" pattern of the §6 withdrawn edges — here the
    conclusions are of genuinely incomparable KIND (colouring vs embedding vs
    order bound), so not a single literature-motivated CANDIDATE direction is
    defensible either.  The edge set is therefore EMPTY.

    The file imports the three node Definitions verbatim from
    [Topological.conjectures.D6emb] (so any endpoint reference would be the EXACT
    [_statement] name) and is axiom-free: no Conjecture/Axiom/Parameter/
    Admitted, and no [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.foundations Require Import embedding.
From Topological Require Import conjectures.D6emb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Edges

    No verified-literature edge exists among the three nodes restricted to this
    milestone (§6's one surface edge, circular/strong-embedding ⟹ CDC, targets
    the out-of-milestone CDC node).  The three conclusions are of incomparable
    kind (dual 3-edge-colouring vs circular-embedding existence vs order bound),
    so not even a literature-motivated CANDIDATE direction is defensible: the
    edge set is empty.  Consequently there are NO [Theorem … Qed] here and NO
    [(*@EDGE …*)] annotation lines — forcing any would assert an implication that
    does not logically close.

    (Sanity: the three endpoint names below are the exact node Definitions, kept
    referenced so the file breaks loudly if a node is renamed.) *)

Definition _d6emb_edge_endpoints_exist : Prop :=
  grunbaums_statement
  /\ the_circular_embedding_statement
  /\ what_is_the_largest_graph_of_positive_curvature_statement.
