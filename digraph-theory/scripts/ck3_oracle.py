"""Exact oracle for the CK3 development (docs/ck3_dossier.md §6).

Digraphs are (n, adj) with adj a list of sets of out-neighbours over
vertices 0..n-1. Pure python, no dependencies. Each checker mirrors a
dossier item (O1, O2/R, M-ell, K-A, K-D, K-a1, K-10, K-11, K-12, K-AB,
K-count, MAIN) and returns True / raises AssertionError with context.
"""

from itertools import combinations
import random

# ---------- basic structure ----------

def is_oriented(adj):
    for u, outs in enumerate(adj):
        if u in outs:
            return False
        for v in outs:
            if u in adj[v]:
                return False
    return True

def outdegs(adj):
    return [len(s) for s in adj]

def arcs(adj):
    return [(u, v) for u, outs in enumerate(adj) for v in outs]

def reachable(adj, x):
    seen, stack = {x}, [x]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return seen

def is_strong(adj):
    n = len(adj)
    return n == 0 or all(len(reachable(adj, x)) == n for x in range(n))

def induced(adj, A):
    """Relabelled induced subgraph; returns (sorted vertex list, adj')."""
    order = sorted(A)
    idx = {v: i for i, v in enumerate(order)}
    return order, [set(idx[w] for w in adj[v] if w in A) for v in order]

# ---------- paths and ell ----------

def all_simple_paths(adj):
    """Yield every simple path (as a vertex tuple). Exponential: only
    call on graphs with small out-degree and small ell."""
    n = len(adj)
    def extend(path, used):
        yield tuple(path)
        for w in adj[path[-1]]:
            if w not in used:
                path.append(w); used.add(w)
                yield from extend(path, used)
                path.pop(); used.discard(w)
    for x in range(n):
        yield from extend([x], {x})

def ell(adj):
    """Exact longest-path arc count (full enumeration)."""
    return max((len(p) - 1 for p in all_simple_paths(adj)), default=0)

def max_paths(adj):
    best, out = -1, []
    for p in all_simple_paths(adj):
        l = len(p) - 1
        if l > best:
            best, out = l, [p]
        elif l == best:
            out.append(p)
    return best, out

def exists_path_len(adj, target):
    """Early-exit DFS: is there a simple path with >= target arcs?"""
    n = len(adj)
    def extend(v, used, length):
        if length >= target:
            return True
        return any(w not in used and extend(w, used | {w}, length + 1)
                   for w in adj[v])
    return target <= 0 and n > 0 or any(extend(x, {x}, 0) for x in range(n))

# ---------- cycles ----------

def simple_cycles_upto(adj, maxlen):
    """All simple cycles of length <= maxlen, as tuples starting at
    their minimum vertex (each cycle once)."""
    n, out = len(adj), []
    def extend(path, used, root):
        v = path[-1]
        for w in adj[v]:
            if w == root and len(path) >= 2:
                out.append(tuple(path))
            elif w > root and w not in used and len(path) < maxlen:
                path.append(w); used.add(w)
                extend(path, used, root)
                path.pop(); used.discard(w)
    for root in range(n):
        extend([root], {root}, root)
    return out

# ---------- generators ----------

def random_oriented(n, p, rng):
    """Random orientation of G(n, p): each present edge gets one
    direction, so the result is oriented by construction."""
    adj = [set() for _ in range(n)]
    for u, v in combinations(range(n), 2):
        if rng.random() < p:
            if rng.random() < 0.5:
                adj[u].add(v)
            else:
                adj[v].add(u)
    return adj

def random_oriented_mindeg(n, k, p, rng, tries=200):
    for _ in range(tries):
        adj = random_oriented(n, p, rng)
        if min(outdegs(adj)) >= k:
            return adj
    raise RuntimeError("no sample with min outdegree >= %d" % k)

def rotational_tournament(n):
    """R_n, n odd: i -> i+1, ..., i+(n-1)/2 (mod n). delta = (n-1)/2,
    strong, ell = n-1 = 2*delta (Hamilton path)."""
    k = (n - 1) // 2
    return [set((i + j) % n for j in range(1, k + 1)) for i in range(n)]

def lift_D12(delta):
    """Cheng-Keevash D_{1,2}: 1-lift one vertex, 2-lift the others, of
    the complete digraph on delta+1 vertices. delta-outregular, oriented,
    strong, girth 3. NOTE: paper Claim 6 asserts ell = delta*b + a - 1 =
    2*delta, but the true value is 2*delta + 1 = (delta+1)*b - 1 (e.g.
    delta = 2: the path 3 2 5 1 4 0 has 5 arcs); Claim 6's segment count
    silently assumes a segment starting at v_1. Unused in our proof
    chain - see dossier section 4, landmine 5."""
    base = delta + 1
    n = base + delta * delta          # delta new vertices per lifted vertex
    adj = [set() for _ in range(n)]
    adj[0] = set(range(1, base))                       # v1 keeps its arcs
    for i in range(1, base):                           # 2-lift v_{i+1}
        U = set(range(base + (i - 1) * delta, base + i * delta))
        adj[i] = set(U)
        orig_out = set(range(base)) - {i}              # N+(v_i) in K
        for u in U:
            adj[u] = set(orig_out)
    return adj

# ---------- reduction (dossier R = O2 + S1) ----------

def out_select(adj, k, rng):
    return [set(rng.sample(sorted(outs), k)) for outs in adj]

def sink_component(adj):
    n = len(adj)
    best = min(range(n), key=lambda x: len(reachable(adj, x)))
    return reachable(adj, best)

def reduce_R(adj, k, rng):
    """Dossier item R: returns (W, adjH) with H = sink SCC of a random
    k-out-selection, relabelled."""
    h1 = out_select(adj, k, rng)
    W = sink_component(h1)
    order, adjH = induced(h1, W)
    return order, adjH

# ---------- checkers (dossier IDs) ----------

def check_O1(adj, A):
    assert is_oriented(adj) and A
    order, adjA = induced(adj, A)
    m = len(A)
    assert sum(len(s) for s in adjA) <= m * (m - 1) // 2
    assert min(len(s) for s in adjA) <= (m - 1) // 2
    return True

def check_R(adj, k, rng):
    assert is_oriented(adj) and min(outdegs(adj)) >= k
    order, adjH = reduce_R(adj, k, rng)
    assert is_oriented(adjH), "R: oriented"
    assert is_strong(adjH), "R: strong"
    assert all(d == k for d in outdegs(adjH)), "R: k-outregular"
    assert len(adjH) >= 2 * k + 1, "R: order >= 2k+1"
    return order, adjH

def check_M_ell(adj, adjH_order, adjH):
    # every H-path maps to a D-path; spot-check via ell on small H
    lh = ell(adjH)
    assert exists_path_len(adj, lh), "M-ell: ell(H) <= ell(D)"
    return True

def check_K_A(adj):
    """Every maximum path: endpoint out-neighbours lie on it."""
    _, mps = max_paths(adj)
    for p in mps:
        assert adj[p[-1]] <= set(p), ("K-A", p)
    return True

def check_K_D(adj):
    """Suffix cycle: length = ell - a + 1 >= d+(end) + 1 (irreflexive)."""
    L, mps = max_paths(adj)
    for p in mps:
        outs = adj[p[-1]]
        if not outs:
            continue
        I = [i for i, v in enumerate(p) if v in outs]
        assert len(I) == len(outs), "K-D: K-A prerequisite"
        a = min(I)
        assert a <= L - len(outs), ("K-D: a <= L - d+", p, a)
        # the suffix really is a cycle
        cyc = p[a:]
        assert all(cyc[i + 1] in adj[cyc[i]] for i in range(len(cyc) - 1))
        assert cyc[0] in adj[cyc[-1]]
    return True

def check_K_a1(adj):
    """a >= 1 on strong graphs with n >= ell + 2."""
    n = len(adj)
    L, mps = max_paths(adj)
    if not (is_strong(adj) and n >= L + 2):
        return None
    for p in mps:
        outs = adj[p[-1]]
        if outs:
            a = min(i for i, v in enumerate(p) if v in outs)
            assert a >= 1, ("K-a1", p)
    return True

def check_K10(adj, maxlen=8, maxpairs=2000):
    """Disjoint cycle pairs: ell >= |C1| + |C2| - 1 (strong graphs)."""
    if not is_strong(adj):
        return None
    cycles = simple_cycles_upto(adj, maxlen)
    L = ell(adj)
    checked = 0
    for i in range(len(cycles)):
        for j in range(i + 1, len(cycles)):
            c1, c2 = cycles[i], cycles[j]
            if set(c1) & set(c2):
                continue
            assert L >= len(c1) + len(c2) - 1, ("K-10", c1, c2, L)
            checked += 1
            if checked >= maxpairs:
                return True
    return True

def kernel_check(adj, delta):
    """Full kernel claim suite (K-11, K-AB, K-B-, K-12, K-count) on a
    strong delta-outregular oriented graph with ell <= 2*delta and
    n >= ell + 2 (so that a >= 1, dossier K-a1). Checks EVERY maximum
    path of maximum cycle bound. Returns the number of witnesses checked
    (0 if not a KS instance). Empirically no KS instance is reachable -
    that emptiness IS the theorem; see test_no_KS_instances."""
    assert is_oriented(adj) and is_strong(adj)
    assert all(d == delta for d in outdegs(adj))
    n = len(adj)
    assert n >= 2 * delta + 1
    L, mps = max_paths(adj)
    if L > 2 * delta or n < L + 2:
        return 0
    # cycle bound of each maximum path
    def cb(p):
        a = min(i for i, v in enumerate(p) if v in adj[p[-1]])
        return L - a + 1
    for p in mps:                       # K-A holds on all of them
        assert adj[p[-1]] <= set(p), "K-A"
    best = max(cb(p) for p in mps)
    checked = 0
    for p in (q for q in mps if cb(q) == best):
        a = min(i for i, v in enumerate(p) if v in adj[p[-1]])
        assert a >= 1, "K-a1'"
        C = p[a:]
        prefix = set(p[:a])
        # K-11
        assert adj[p[a - 1]] <= set(p), ("K-11", p)
        # K-AB
        A = adj[p[a - 1]] & prefix
        B = adj[p[a - 1]] & set(C)
        assert len(A) + len(B) == delta and p[a] in B
        assert len(A) <= a - 1
        # K-B^-
        pred = {C[(i + 1) % len(C)]: C[i] for i in range(len(C))}
        Bm = set(pred[b] for b in B)
        assert len(Bm) == len(B) and pred[p[a]] == p[-1]
        # K-12
        for b in Bm:
            assert adj[b] <= set(C), ("K-12", p, b)
        # K-count
        _, adjS = induced(adj, Bm)
        s = min(len(t) for t in adjS)
        assert len(C) >= len(Bm) + delta - s, ("K-count a", p)
        assert L >= 2 * delta - s, ("K-count b", p)
        checked += 1
    return checked

def random_digraph(n, p, rng):
    """Arbitrary digraph: each ordered pair (u, v), u != v, is an arc
    independently with probability p (loops excluded). NOT oriented in
    general - used to test the fully general K-12."""
    return [set(v for v in range(n) if v != u and rng.random() < p)
            for u in range(n)]

def check_K12_general(adj):
    """Dossier K-12 in its full generality: in ANY digraph, for any
    maximum path of maximum cycle bound with a >= 1, every out-neighbour
    of every vertex of B^- lies on the endpoint cycle C. Returns the
    number of (path, b) pairs checked."""
    L, mps = max_paths(adj)
    def back(p):
        outs = adj[p[-1]] & set(p)      # K-A: all on P for max paths,
        outs.discard(p[-1])             # but intersect defensively
        return min((i for i, v in enumerate(p) if v in outs), default=None)
    cbs = [(p, back(p)) for p in mps]
    cbs = [(p, a) for p, a in cbs if a is not None]
    if not cbs:
        return 0
    best = max(L - a + 1 for _, a in cbs)
    checked = 0
    for p, a in cbs:
        if L - a + 1 != best or a == 0:
            continue
        C = p[a:]
        pred = {C[(i + 1) % len(C)]: C[i] for i in range(len(C))}
        B = adj[p[a - 1]] & set(C)
        for b in (pred[x] for x in B):
            assert adj[b] <= set(C), ("K-12 general", p, b)
            checked += 1
    return checked

def check_MAIN(adj, k, bound):
    """delta+ >= k  ==>  ell >= bound (early-exit search)."""
    assert is_oriented(adj) and len(adj) > 0
    assert min(outdegs(adj)) >= k
    assert exists_path_len(adj, bound), ("MAIN", k, bound)
    return True
