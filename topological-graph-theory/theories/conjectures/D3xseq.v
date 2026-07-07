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

    PARTIAL / PROXY STATUS (why the witness is [connected]).  [is_crossing_genus]
    rests on [embeds_in_genus]/[euler_genus], which is the connected-map Euler
    relation — exact on connected maps, but understating on disconnected ones.
    [xsplit] preserves connectivity ([crossing_genus.xsplit_connected],
    machine-checked), so for a connected witness every split target stays
    connected and the Euler-genus side is exact.  This does not by itself validate
    equality with the usual drawing genus-crossing number, because the inherited
    [xsplit] model lacks local rotation/alternation data at crossing vertices.
    Restricting to a connected witness is still the intended faithful side of the
    source, but the row remains partial until the drawing/rotation equivalence is
    built.

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
