"""Oracle for the k = 4 formalization (docs/k34_dossier.md §6).

AC_n[C3] construction + per-item checks of the value casework (V-items,
merged order) and the deletion casework (D-items, d_then_c order).
Vertices of AC_n[C3] are encoded as 3*t + h (t in Z_n, h in {0,1,2}).

Bounds strategy (mirrors the formal proof; exact omega_vec on 3n >= 21
vertices is infeasible — the source project's verify_4critical_n21.py
also used explicit orders + SAT, never exact min-over-orders):
  * upper bounds: explicit witness orders kv / kd via omega_of_order;
  * lower bounds: SAT — "no backedge K_k clique" CNF UNSAT means every
    order has a K_k, i.e. omega_vec >= k (encoding lifted from the
    red-team-passed verify_4critical_n21.py);
  * exact omega_vec only on the small factors (AC_n for n in {7,9}, C3).
CRT crosscheck: AC_7[C3] is isomorphic to the circulant (21, g21) that
verify_4critical_n21.py independently certified 4-critical.
"""

import itertools

from core import (omega_vec, omega_of_order, is_tournament, subtournament,
                  beats_matrix)


def g_set(m):
    """g = [1, m-1] union {m+1} in Z_n, n = 2m+1."""
    return set(range(1, m)) | {m + 1}


def ac_arcs(m):
    n = 2 * m + 1
    g = g_set(m)
    return {(i, j) for i in range(n) for j in range(n)
            if (j - i) % n in g}


def c3_arcs():
    return {(0, 1), (1, 2), (2, 0)}


def lex_arcs(n1, arcs1, n2, arcs2):
    """Lexicographic substitution T1[T2]; vertex (t,h) -> n2*t + h."""
    arcs = set()
    for t in range(n1):
        for tp in range(n1):
            for h in range(n2):
                for hp in range(n2):
                    if t != tp:
                        if (t, tp) in arcs1:
                            arcs.add((n2 * t + h, n2 * tp + hp))
                    elif (h, hp) in arcs2:
                        arcs.add((n2 * t + h, n2 * t + hp))
    return arcs


def t4(m):
    """AC_n[C3] on 3n vertices."""
    n = 2 * m + 1
    return 3 * n, lex_arcs(n, ac_arcs(m), 3, c3_arcs())


# ---------- bands / classes ----------

def band(m, t):
    return 3 if t == 0 else (2 if t <= m else 1)


def dband(h):
    return 2 if h == 0 else 1


def kappa(m, t, h):
    return band(m, t) + dband(h)


def kv_key(m, t, h):
    n = 2 * m + 1
    return (kappa(m, t, h) * n + t) * 3 + h


def kd_key(m, t, h):
    n = 2 * m + 1
    return ((dband(h) * 4 + band(m, t)) * n + t) * 3 + h


def arc_ac(m, a, b):
    return (b - a) % (2 * m + 1) in g_set(m)


def arc_t4(m, t, h, tp, hp):
    if t != tp:
        return arc_ac(m, t, tp)
    return (h, hp) in c3_arcs()


def backedge_pair(m, key, u, v):
    """u, v as (t,h); True iff {u,v} is a backedge under the key order:
    the key-later vertex has an arc to the key-earlier one."""
    (t, h), (tp, hp) = u, v
    if key(m, *u) > key(m, *v):
        u, v = v, u
        (t, h), (tp, hp) = u, v
    return arc_t4(m, tp, hp, t, h)


# ---------- SAT lower bound (encoding from verify_4critical_n21.py) ----------

def transitive_ksubsets_order(n, beats, K):
    """K-subsets inducing a transitive subtournament, in dominance order
    (= the only pattern a backedge K-clique can realize, reversed)."""
    for S in itertools.combinations(range(n), K):
        outdeg = {x: sum(1 for y in S if y != x and beats[x][y]) for x in S}
        if sorted(outdeg.values()) != list(range(K)):
            continue
        order = sorted(S, key=lambda x: -outdeg[x])
        if all(beats[order[a]][order[b]]
               for a in range(K) for b in range(a + 1, K)):
            yield order


def build_cnf_no_kclique(n, arcs, K):
    """CNF satisfiable iff some total order has no backedge K-clique.
    Var lit(u,v) = 'u precedes v'; transitivity clauses; for each
    transitive K-subset (dominance order d0 > d1 > ...), a backedge
    K-clique appears iff the order is d_{K-1} prec ... prec d0 — forbid it."""
    from pysat.formula import CNF
    beats = beats_matrix(n, arcs)
    idx = {}
    nv = 0

    def lit(u, v):
        nonlocal nv
        if (u, v) in idx:
            return idx[(u, v)]
        if (v, u) in idx:
            return -idx[(v, u)]
        nv += 1
        idx[(u, v)] = nv
        return nv

    cnf = CNF()
    for u in range(n):
        for v in range(u + 1, n):
            lit(u, v)
    for u in range(n):
        for v in range(n):
            if v == u:
                continue
            for w in range(n):
                if w in (u, v):
                    continue
                cnf.append([-lit(u, v), -lit(v, w), lit(u, w)])
    for order in transitive_ksubsets_order(n, beats, K):
        cnf.append([lit(order[a], order[b])
                    for a in range(K) for b in range(a + 1, K)])
    return cnf


def sat_omega_lb(n, arcs, k):
    """True iff omega_vec >= k, certified by no-K_k CNF UNSAT under two
    independent solvers."""
    from pysat.solvers import Cadical153, Minisat22
    cnf = build_cnf_no_kclique(n, arcs, k)
    res = []
    for solver_cls in (Cadical153, Minisat22):
        with solver_cls(bootstrap_with=cnf.clauses) as s:
            res.append(s.solve())
    assert res[0] == res[1], "solver disagreement"
    return not res[0]


# ---------- checks ----------

def check_factors_exact(m):
    """Exact small-factor values feeding the substitution lower bound:
    omega_vec(AC_n) = 3, omega_vec(AC_n - 0) = 2, omega_vec(C3) = 2."""
    n = 2 * m + 1
    arcs = ac_arcs(m)
    assert is_tournament(n, arcs)
    assert omega_vec(n, arcs) == 3
    nd, darcs = subtournament(n, arcs, list(range(1, n)))
    assert omega_vec(nd, darcs) == 2
    assert omega_vec(3, c3_arcs()) == 2
    return True


def check_t4_value(m):
    """omega_vec(T4) = 4: kv order gives <= 4, SAT no-K4 UNSAT gives >= 4."""
    nv, arcs = t4(m)
    assert is_tournament(nv, arcs)
    assert check_value_order_clique4(m)
    assert sat_omega_lb(nv, arcs, 4)
    return True


def check_t4_deletion(m):
    """omega_vec(T4 - (0,0)) = 3: kd order <= 3, SAT no-K3 UNSAT >= 3."""
    nv, arcs = t4(m)
    keep = [v for v in range(nv) if v != 0]      # delete (0,0)
    nd, darcs = subtournament(nv, arcs, keep)
    assert sat_omega_lb(nd, darcs, 3)
    assert check_deletion_order_clique3(m)
    return True


def check_t4_vertex_transitive(m):
    """(t,h) -> (t+1,h) and (t,h) -> (t,h+1) are automorphisms; together
    they act transitively (so one deletion settles all)."""
    n = 2 * m + 1

    def shift_t(v):
        return 3 * ((v // 3 + 1) % n) + v % 3

    def shift_h(v):
        return 3 * (v // 3) + (v % 3 + 1) % 3

    nv, arcs = t4(m)
    for f in (shift_t, shift_h):
        assert {(f(u), f(v)) for (u, v) in arcs} == arcs
    return True


G21 = {1, 2, 4, 7, 8, 9, 11, 15, 16, 18}


def check_crt_iso_m3():
    """AC_7[C3] = circulant(21, G21) under CRT (x mod 7, x mod 3) — the
    tournament independently certified 4-critical by the source project's
    verify_4critical_n21.py."""
    nv, arcs = t4(3)
    iso = {3 * (x % 7) + (x % 3): x for x in range(21)}   # (t,h)-code -> x
    circ = {(u, v) for u in range(21) for v in range(21)
            if (v - u) % 21 in G21}
    assert {(iso[u], iso[v]) for (u, v) in arcs} == circ
    return True


def check_value_order_clique4(m):
    """Under the merged order, the backedge clique number is exactly 4."""
    nv, arcs = t4(m)
    order = sorted(range(nv), key=lambda v: kv_key(m, v // 3, v % 3))
    return omega_of_order(nv, arcs, order) == 4


def check_deletion_order_clique3(m):
    """Under d_then_c on the survivors, backedge clique number is 3."""
    nv, arcs = t4(m)
    keep = [v for v in range(nv) if v != 0]
    keep.sort(key=lambda v: kd_key(m, v // 3, v % 3))
    nd, darcs = subtournament(nv, arcs, keep)
    return omega_of_order(nd, darcs, list(range(nd))) == 3


def classes(m):
    """kappa-classes as dict K -> list of (t,h)."""
    n = 2 * m + 1
    out = {2: [], 3: [], 4: [], 5: []}
    for t in range(n):
        for h in range(3):
            out[kappa(m, t, h)].append((t, h))
    return out


def check_class_caps(m):
    """V1-V4: within-class backedges are exactly the listed ones."""
    cl = classes(m)
    assert cl[5] == [(0, 0)]
    for K, members in cl.items():
        for i, u in enumerate(members):
            for v in members[i + 1:]:
                be = backedge_pair(m, kv_key, u, v)
                if K in (2, 5):
                    assert not be, (K, u, v)
                elif K == 4:
                    ok = {u, v} in ({(m, 0), (0, 1)}, {(m, 0), (0, 2)})
                    assert be == ok, (K, u, v)
                else:                                   # K == 3
                    low = u if u[0] <= m else v
                    high = v if u[0] <= m else u
                    ok = (low[0] <= m and high[0] > m and high[1] == 0
                          and (high[0] - low[0]) in
                          ({m} | set(range(m + 2, 2 * m + 1))))
                    assert be == ok, (K, u, v)
    return True


def check_bands_D1(m):
    """D1: no within-band backedge under kd (survivors)."""
    n = 2 * m + 1
    bands = {}
    for t in range(n):
        for h in range(3):
            if (t, h) == (0, 0):
                continue
            bands.setdefault((dband(h), band(m, t)), []).append((t, h))
    for members in bands.values():
        for i, u in enumerate(members):
            for v in members[i + 1:]:
                assert not backedge_pair(m, kd_key, u, v), (u, v)
    return True


def check_31_exclusion(m):
    """D2: no (s,0) dominates blocks {0, t2, m+1} for t2 in [2, m-1]."""
    for t2 in range(2, m):
        for s in range(1, 2 * m + 1):
            doms = []
            for blockv, hh in ((0, 1), (t2, 1), (m + 1, 1)):
                if s == blockv:
                    doms.append(hh == 1)       # internal (s,0)->(s,1) only
                else:
                    doms.append(arc_ac(m, s, blockv))
            assert not all(doms), (s, t2)
    return True


def check_22_core(m):
    """Core incompatibility: no delta in g with 1+delta and m+1+delta in g."""
    n = 2 * m + 1
    g = g_set(m)
    for d in g:
        assert not ((1 + d) % n in g and (m + 1 + d) % n in g), d
    return True


def check_22_lemma(m):
    """D3: X is backedge-independent for every B4/B5 pair."""
    n = 2 * m + 1
    for s in range(m + 1, 2 * m + 1):
        for sp in range(1, m + 1):
            if (s - sp) % n not in g_set(m):
                continue
            X = []
            for t in range(n):
                for h in (1, 2):
                    if (t, h) == (0, 0):
                        continue
                    dom_s = (h == 1) if t == s else arc_ac(m, s, t)
                    dom_sp = (h == 1) if t == sp else arc_ac(m, sp, t)
                    if dom_s and dom_sp:
                        X.append((t, h))
            for i, u in enumerate(X):
                for v in X[i + 1:]:
                    assert not backedge_pair(m, kd_key, u, v), (s, sp, u, v)
    return True
