"""Explicit tournament families for arXiv:2310.04265 (clique number of tournaments).

Each builder returns (n, arcs), arcs the FULL arc set of a tournament (one arc
per unordered pair).  The anchors are:
  * transitive_tournament(k) = TT_k  -- omega_vec = 1 (paper: omega_vec(TT_n)=1).
  * directed_C3 = Delta(1,1,1)       -- the unique 2-omega_vec-critical tournament,
    omega_vec = 2 (stated just after Question 5.9 / conj:critique).
  * S_tilde(n) -- S~_1 = TT_1, S~_n = Delta(S~_{n-1}, S~_{n-1}, S~_{n-1});
    Lemma 3.8 (lem:Stilde_omega): omega_vec(S~_n) >= n.  On 3^{n-1} vertices.
The Delta(.,.,.) substitution operator is the load-bearing primitive
(Delta(T1,T2,T3): T1=>T2, T2=>T3, T3=>T1 between the three disjoint blocks).
"""
from __future__ import annotations

import random


def transitive_tournament(k):
    """TT_k: arc i->j for i<j.  omega_vec = 1 (paper anchor)."""
    return k, [(i, j) for i in range(k) for j in range(i + 1, k)]


def directed_C3():
    """The directed triangle = Delta(1,1,1) = C_3.  omega_vec = 2,
    the unique 2-omega_vec-critical tournament."""
    return 3, [(0, 1), (1, 2), (2, 0)]


def directed_cycle_tournament_skeleton(*args, **kwargs):  # pragma: no cover
    raise NotImplementedError("not a tournament; use directed_C3 or random_tournament")


def delta(T1, T2, T3):
    """Delta(T1,T2,T3): from disjoint copies of the three tournaments (each given
    as (n, arcs)), add ALL arcs so that block1 => block2, block2 => block3,
    block3 => block1.  Returns (n, arcs) on n1+n2+n3 vertices.

    (Paper, Section 2: 'T1 => T2' means every vertex of T1 beats every vertex of
    T2.)  Vertices: block1 = [0,n1), block2 = [n1,n1+n2), block3 = [n1+n2, n).
    """
    (n1, a1), (n2, a2), (n3, a3) = T1, T2, T3
    off1, off2, off3 = 0, n1, n1 + n2
    n = n1 + n2 + n3
    arcs = []
    for (u, v) in a1:
        arcs.append((u + off1, v + off1))
    for (u, v) in a2:
        arcs.append((u + off2, v + off2))
    for (u, v) in a3:
        arcs.append((u + off3, v + off3))
    b1 = range(off1, off1 + n1)
    b2 = range(off2, off2 + n2)
    b3 = range(off3, off3 + n3)
    for u in b1:                 # T1 => T2
        for v in b2:
            arcs.append((u, v))
    for u in b2:                 # T2 => T3
        for v in b3:
            arcs.append((u, v))
    for u in b3:                 # T3 => T1
        for v in b1:
            arcs.append((u, v))
    return n, arcs


def S_tilde(n):
    """S~_n: S~_1 = TT_1, S~_n = Delta(S~_{n-1}, S~_{n-1}, S~_{n-1}).
    On 3^{n-1} vertices.  Lemma 3.8: omega_vec(S~_n) >= n."""
    if n <= 1:
        return 1, []                       # TT_1: single vertex, no arcs
    prev = S_tilde(n - 1)
    return delta(prev, prev, prev)


def random_tournament(n, seed=0):
    """A uniformly random tournament on n vertices (orient each pair by coin)."""
    rng = random.Random(seed)
    arcs = []
    for i in range(n):
        for j in range(i + 1, n):
            arcs.append((i, j) if rng.random() < 0.5 else (j, i))
    return n, arcs


def all_tournaments(n):
    """Yield every tournament (n, arcs) by orienting each of the C(n,2) pairs
    both ways.  2^{C(n,2)} of them (NOT iso-reduced) -- small n only.
    For n=4: 2^6=64; n=5: 2^10=1024; n=6: 2^15=32768; n=7: 2^21=2.1M."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    m = len(pairs)
    for mask in range(1 << m):
        arcs = [(i, j) if (mask >> k) & 1 else (j, i)
                for k, (i, j) in enumerate(pairs)]
        yield n, arcs
