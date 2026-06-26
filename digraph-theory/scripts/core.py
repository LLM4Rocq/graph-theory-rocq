"""Core EXACT oracle for the clique number of a tournament (arXiv:2310.04265).

Definitions (Aboulker, Aubian, Charbit, ... "Clique number of tournaments"):
  * A *tournament* T on V = {0..n-1}: for every unordered pair {u,v}, exactly one
    of the arcs u->v, v->u is present.  Represented as (n, arcs), arcs a list of
    (u,v) ordered pairs, |arcs| = C(n,2).
  * Given a total order  prec  on V(T), the *backedge graph*  T^prec  is the
    UNDIRECTED graph with vertex set V(T) and an edge uv iff  u prec v  and the
    arc  v->u  is in A(T)  (i.e. v->u is a BACKWARD arc w.r.t. prec).
  * omega_vec(T)  =  min over all total orders prec of  omega(T^prec),
    where omega(.) is the ordinary undirected clique number.
    [Eq. after "clique number of a digraph", Section 2 of the paper.]

Everything here is EXACT (no heuristics).  omega_vec is computed by enumerating
total orders (n! of them) and taking the minimum clique number of the backedge
graph -- this is the sound ground truth.  An exact branch-and-bound variant
(`omega_vec_bb`) prunes equivalent orders for larger n but returns the IDENTICAL
value; `omega_vec` dispatches to it and both are cross-checked in the tests.

A tournament is stored as (n, arcs).  We also keep an n x n boolean adjacency
`beats[u][v]  ==  (u->v) in A(T)` for O(1) arc queries.
"""
from __future__ import annotations

import itertools
from functools import lru_cache

import networkx as nx


# --------------------------------------------------------------------------- #
#  Structure
# --------------------------------------------------------------------------- #

def is_tournament(n, arcs):
    """True iff (n, arcs) is a tournament: exactly one arc per unordered pair,
    no loops, no repeated/2-cycle arcs."""
    s = set()
    for (u, v) in arcs:
        if u == v:
            return False
        if (u, v) in s or (v, u) in s:
            return False
        s.add((u, v))
    return len(s) == n * (n - 1) // 2


def beats_matrix(n, arcs):
    """beats[u][v] is True iff u->v in A(T)."""
    beats = [[False] * n for _ in range(n)]
    for (u, v) in arcs:
        beats[u][v] = True
    return beats


# --------------------------------------------------------------------------- #
#  Backedge graph and its clique number
# --------------------------------------------------------------------------- #

def backedge_graph(n, arcs, order):
    """The backedge graph T^prec for the total order `order` (a permutation of
    range(n), order[0] is the prec-smallest).  Returns a networkx.Graph.

    Edge uv iff  u prec v  and  v->u in A(T).  Equivalently, for positions
    i<j with a=order[i], b=order[j] (a prec b): edge iff arc b->a present.
    """
    beats = beats_matrix(n, arcs)
    g = nx.Graph()
    g.add_nodes_from(range(n))
    for i in range(n):
        a = order[i]
        for j in range(i + 1, n):
            b = order[j]            # a prec b
            if beats[b][a]:         # backward arc b->a  =>  edge a-b
                g.add_edge(a, b)
    return g


def clique_number(g):
    """Exact ordinary clique number of an undirected networkx graph."""
    if g.number_of_nodes() == 0:
        return 0
    # networkx exact max clique (Bron-Kerbosch based)
    return max((len(c) for c in nx.find_cliques(g)), default=1)


def omega_of_order(n, arcs, order):
    """omega(T^prec) for one explicit order."""
    return clique_number(backedge_graph(n, arcs, order))


# --------------------------------------------------------------------------- #
#  EXACT omega_vec(T)  =  min over all n! orders of omega(T^prec)
# --------------------------------------------------------------------------- #

def omega_vec_bruteforce(n, arcs):
    """Sound exact value by enumerating ALL n! total orders.  The reference
    implementation; feasible to ~ n <= 9 (9! = 362880)."""
    if n == 0:
        return 0
    beats = beats_matrix(n, arcs)
    best = n
    for order in itertools.permutations(range(n)):
        # build backedge graph as adjacency and take clique number
        g = nx.Graph()
        g.add_nodes_from(range(n))
        for i in range(n):
            a = order[i]
            for j in range(i + 1, n):
                b = order[j]
                if beats[b][a]:
                    g.add_edge(a, b)
        w = clique_number(g)
        if w < best:
            best = w
            if best <= 1:
                return best   # cannot go below 1 for n>=1
    return best


def omega_vec_bb(n, arcs, ub=None):
    """EXACT omega_vec via branch-and-bound over prefixes of the order.

    We build the order position by position (prec-smallest first).  At each
    step we choose the next vertex among the remaining ones.  The backedge
    graph restricted to already-placed vertices only gains edges from future
    placements onto the *already placed* set? No: a future vertex b placed
    later than already-placed a contributes edge a-b iff b->a.  So edges among
    *placed* vertices are FINAL once both endpoints are placed.  Hence the
    clique number of the placed sub-backedge-graph is monotone non-decreasing
    as we extend the prefix -> a sound lower-bound prune against `ub`.

    Returns the exact omega_vec (identical to brute force).
    """
    if n == 0:
        return 0
    beats = beats_matrix(n, arcs)
    if ub is None:
        ub = n
    best = [ub]

    # adjacency in the backedge graph among PLACED vertices is determined by
    # placement order: for placed a (earlier) and b (later), edge iff beats[b][a].
    placed = []                     # order prefix (prec increasing)
    placed_adj = {}                 # v -> set of placed neighbours in backedge graph

    def cur_clique_number():
        g = nx.Graph()
        g.add_nodes_from(placed)
        for v in placed:
            for u in placed_adj[v]:
                g.add_edge(u, v)
        return clique_number(g)

    def recurse(remaining):
        if not remaining:
            w = cur_clique_number()
            if w < best[0]:
                best[0] = w
            return
        # prune: current placed-clique already >= best -> no improvement possible
        cur = cur_clique_number()
        if cur >= best[0]:
            return
        for b in list(remaining):
            # placing b after all current `placed`: edges b-a for placed a with beats[b][a]
            nb = {a for a in placed if beats[b][a]}
            placed.append(b)
            placed_adj[b] = nb
            for a in nb:
                placed_adj[a].add(b)
            remaining2 = remaining - {b}
            recurse(remaining2)
            # undo
            placed.pop()
            for a in nb:
                placed_adj[a].discard(b)
            del placed_adj[b]

    recurse(frozenset(range(n)))
    return best[0]


def omega_vec(n, arcs, method="auto"):
    """EXACT omega_vec(T).  `method` in {auto, bruteforce, bb}.

    auto: brute force for n<=7 (fast, trivially sound), branch-and-bound above.
    """
    if not is_tournament(n, arcs):
        raise ValueError("omega_vec is defined on tournaments only")
    if n == 0:
        return 0
    if method == "bruteforce":
        return omega_vec_bruteforce(n, arcs)
    if method == "bb":
        return omega_vec_bb(n, arcs)
    # auto
    if n <= 7:
        return omega_vec_bruteforce(n, arcs)
    return omega_vec_bb(n, arcs)


# --------------------------------------------------------------------------- #
#  Subtournaments / criticality
# --------------------------------------------------------------------------- #

def subtournament(n, arcs, keep):
    """Induced subtournament on the vertex subset `keep` (iterable), relabelled
    to 0..len(keep)-1.  Returns (n', arcs')."""
    keep = list(keep)
    relabel = {v: i for i, v in enumerate(keep)}
    ks = set(keep)
    sub = [(relabel[u], relabel[v]) for (u, v) in arcs if u in ks and v in ks]
    return len(keep), sub


def is_k_omega_vec_critical(n, arcs, k):
    """True iff omega_vec(T) == k and for every vertex v, omega_vec(T - v) == k-1.

    (Definition just before Conjecture 5.10 / conj:critique in the paper.)
    """
    if omega_vec(n, arcs) != k:
        return False
    for v in range(n):
        nn, sub = subtournament(n, arcs, [w for w in range(n) if w != v])
        if omega_vec(nn, sub) != k - 1:
            return False
    return True


def min_subtournament_order_for_k(n, arcs, k, max_order=None):
    """Smallest order |X| of a subtournament X of T with omega_vec(X) >= k.
    Returns (size, vertex_set) or (None, None) if none up to max_order.

    This is the finite handle for Question 5.9 / Conjecture 5.8: if omega_vec(T)
    >= k, is there always a SMALL certifying subtournament?
    """
    if omega_vec(n, arcs) < k:
        return None, None
    top = max_order if max_order is not None else n
    for size in range(1, top + 1):
        for keep in itertools.combinations(range(n), size):
            nn, sub = subtournament(n, arcs, keep)
            if omega_vec(nn, sub) >= k:
                return size, keep
    return None, None
