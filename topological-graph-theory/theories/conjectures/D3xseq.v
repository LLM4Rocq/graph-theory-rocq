(** * D3 crossing-sequences row via the genus crossing-number layer. *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding crossing crossing_genus.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Crossing sequences  (Conjecture, OPEN)

    Source (Conjecture): "Let (a₀,a₁,a₂,…,0) be a sequence of nonnegative
    integers which strictly decreases until 0.  Then there exists a graph that
    can be drawn on a surface of orientable (nonorientable, resp.) genus i with
    aᵢ crossings, but not with fewer crossings."

    Encoding (ORIENTABLE primary; genus crossing-number layer
    [Topological.foundations.crossing_genus]).  A finite sequence is [a : seq
    nat]; "strictly decreases until 0" = nonempty, consecutive strict decrease,
    last term 0.  "drawn on the genus-i surface with aᵢ crossings but not fewer"
    = [is_crossing_genus G i (nth 0 a i)] (cr_i(G) = aᵢ: aᵢ crossing-resolutions
    land G in orientable genus i, and no fewer do — [crossing_genus.v]).  The
    claim: every such sequence is REALIZED by some graph's crossing sequence.
    The non-increasing shape the conjecture presupposes is here a THEOREM, not an
    assumption ([is_crossing_genus_nonincreasing]).

    EXACTLY FAITHFUL (why the witness is [connected]).  [is_crossing_genus] rests
    on [embeds_in_genus]/[euler_genus], which is the connected-map Euler relation
    — EXACT on connected maps, but understating on disconnected ones.  [xsplit]
    PRESERVES connectivity ([crossing_genus.xsplit_connected], machine-checked:
    the new vertex reroutes each deleted edge), so for a CONNECTED witness every
    planarization stays connected and [euler_genus] is exact throughout; hence
    [is_crossing_genus] is EXACTLY the topological genus crossing number and the
    encoding is faithful (not a proxy).  Restricting to a connected witness is
    faithful to the source: a crossing-sequence realizer can always be taken
    connected (a bridge added in a common face joins components without changing
    any cr_i or genus), so connected-realizability ⇔ realizability.

    SCOPE.  Only the ORIENTABLE variant is formalized; the conjecture's
    NONORIENTABLE "(resp.)" twin is the analogous separate statement over the
    signed layer [signed_embedding.semb_in_genus], not built here. *)
Definition crossing_sequences_statement : Prop :=
  forall a : seq nat,
    0 < size a ->
    (forall j : nat, j.+1 < size a -> nth 0 a j.+1 < nth 0 a j) ->
    nth 0 a (size a).-1 = 0 ->
    exists G : sgraph,
      connected [set: G] /\
      forall i : nat, i < size a -> is_crossing_genus G i (nth 0 a i).
