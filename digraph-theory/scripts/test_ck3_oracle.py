"""Oracle test suite for the CK3 dossier (docs/ck3_dossier.md §6).

Run:  uv run --with pytest python3 -m pytest scripts/test_ck3_oracle.py -q
"""

import random
import pytest

from ck3_oracle import (
    is_oriented, is_strong, outdegs, ell, exists_path_len,
    random_oriented, random_oriented_mindeg, random_digraph,
    rotational_tournament, lift_D12, reduce_R, check_O1, check_R,
    check_M_ell, check_K_A, check_K_D, check_K_a1, check_K10,
    kernel_check, check_K12_general, check_MAIN,
)

SEEDS = [11, 23, 37, 41]

# ---------- seed instances ----------

def test_R5_is_tight():
    """R5: 2-outregular tournament, ell = 4 = 2*delta."""
    adj = rotational_tournament(5)
    assert is_oriented(adj) and is_strong(adj)
    assert outdegs(adj) == [2] * 5 and ell(adj) == 4

def test_R7_is_tight():
    """R7: 3-outregular tournament, ell = 6 = 2*delta."""
    adj = rotational_tournament(7)
    assert is_oriented(adj) and is_strong(adj)
    assert outdegs(adj) == [3] * 7 and ell(adj) == 6

@pytest.mark.parametrize("delta", [2, 3])
def test_D12_structure(delta):
    """D_{1,2}: delta-outregular, oriented, strong — and ell is
    2*delta + 1, NOT the 2*delta of paper Claim 6 (dossier landmine 5:
    Claim 6's segment count silently assumes a segment starting at v_1;
    unused in our proof chain)."""
    adj = lift_D12(delta)
    assert len(adj) == (delta + 1) + delta * delta
    assert is_oriented(adj) and is_strong(adj)
    assert all(d == delta for d in outdegs(adj))
    assert ell(adj) == 2 * delta + 1

# ---------- O1 ----------

@pytest.mark.parametrize("seed", SEEDS)
def test_O1_random_subsets(seed):
    rng = random.Random(seed)
    adj = random_oriented(10, 0.6, rng)
    for _ in range(20):
        m = rng.randint(1, 10)
        A = set(rng.sample(range(10), m))
        check_O1(adj, A)

# ---------- O2 + S1 = R, M-ell ----------

@pytest.mark.parametrize("seed", SEEDS)
def test_reduction_and_monotonicity(seed):
    rng = random.Random(seed)
    adj = random_oriented_mindeg(11, 3, 0.75, rng)
    order, adjH = check_R(adj, 3, rng)
    check_M_ell(adj, order, adjH)

# ---------- K-A, K-D, K-a1 on sparse instances ----------

@pytest.mark.parametrize("name,adj", [
    ("R5", rotational_tournament(5)),
    ("R7", rotational_tournament(7)),
    ("D12_2", lift_D12(2)),
    ("D12_3", lift_D12(3)),
])
def test_KA_KD_Ka1_on_seeds(name, adj):
    assert check_K_A(adj)
    assert check_K_D(adj)
    res = check_K_a1(adj)
    if name.startswith("D12"):
        assert res is True          # n >= ell + 2 holds for the lifts

@pytest.mark.parametrize("seed", SEEDS)
def test_KA_KD_on_reductions(seed):
    rng = random.Random(seed)
    adj = random_oriented_mindeg(10, 2, 0.7, rng)
    _, adjH = reduce_R(adj, 2, rng)
    assert check_K_A(adjH)
    assert check_K_D(adjH)
    check_K_a1(adjH)

# ---------- K-10 ----------

@pytest.mark.parametrize("name,adj", [
    ("R5", rotational_tournament(5)),
    ("R7", rotational_tournament(7)),
    ("D12_2", lift_D12(2)),
])
def test_K10_on_seeds(name, adj):
    assert check_K10(adj) in (True, None)

@pytest.mark.parametrize("seed", SEEDS)
def test_K10_on_reductions(seed):
    rng = random.Random(seed)
    adj = random_oriented_mindeg(9, 2, 0.7, rng)
    _, adjH = reduce_R(adj, 2, rng)
    check_K10(adjH, maxlen=6)

# ---------- the kernel ----------
#
# Genuine KS instances (strong, delta-outregular, oriented, ell <= 2*delta,
# n >= ell + 2) appear to be unreachable: their emptiness for delta <= 3 IS
# the theorem being formalized. Coverage strategy (dossier section 6):
# (i) kernel_check degrades gracefully (returns 0) on the near-miss seeds;
# (ii) a vacuity scan documents that random reductions never produce a KS
#     instance, and would run the full suite if one ever appeared;
# (iii) K-12 — true in ANY digraph (dossier generality note) — is checked
#     directly on random digraphs and all seeds.

@pytest.mark.parametrize("name,adj,delta", [
    ("R5", rotational_tournament(5), 2),      # ell = 2d but n = ell + 1
    ("R7", rotational_tournament(7), 3),
    ("D12_2", lift_D12(2), 2),                # n big but ell = 2d + 1
    ("D12_3", lift_D12(3), 3),
])
def test_kernel_check_on_near_misses(name, adj, delta):
    assert kernel_check(adj, delta) == 0      # not KS instances

@pytest.mark.parametrize("seed", SEEDS)
def test_no_KS_instances_delta2(seed):
    """Vacuity scan: reductions at k = 2 with n >= 6 always have
    ell >= 5 = 2*delta + 1 (a KS instance would refute the delta = 2
    theorem); kernel_check would fully verify one if it appeared."""
    rng = random.Random(seed)
    for _ in range(15):
        adj = random_oriented_mindeg(8, 2, 0.85, rng, tries=500)
        _, adjH = reduce_R(adj, 2, rng)
        checked = kernel_check(adjH, 2)
        if len(adjH) >= 6:
            assert ell(adjH) >= 5 or checked > 0

@pytest.mark.parametrize("seed", SEEDS)
def test_K12_general_random_digraphs(seed):
    """K-12 in full generality on arbitrary (non-oriented) digraphs."""
    rng = random.Random(seed)
    total = 0
    for _ in range(25):
        n = rng.randint(5, 8)
        adj = random_digraph(n, 0.25, rng)
        total += check_K12_general(adj)
    assert total >= 10                        # the check actually fires

@pytest.mark.parametrize("name,adj", [
    ("R5", rotational_tournament(5)),
    ("R7", rotational_tournament(7)),
    ("D12_2", lift_D12(2)),
    ("D12_3", lift_D12(3)),
])
def test_K12_general_on_seeds(name, adj):
    check_K12_general(adj)                    # no assertion failure

# ---------- MAIN (and the delta = 2 corollary) ----------

@pytest.mark.parametrize("seed", SEEDS)
def test_MAIN_delta3(seed):
    rng = random.Random(seed)
    for n in (10, 12):
        adj = random_oriented_mindeg(n, 3, 0.92, rng, tries=500)
        check_MAIN(adj, 3, 6)

@pytest.mark.parametrize("seed", SEEDS)
def test_MAIN_delta2(seed):
    rng = random.Random(seed)
    for n in (8, 10):
        adj = random_oriented_mindeg(n, 2, 0.85, rng, tries=500)
        check_MAIN(adj, 2, 4)

def test_MAIN_on_tight_seeds():
    check_MAIN(rotational_tournament(7), 3, 6)
    check_MAIN(lift_D12(3), 3, 6)
    check_MAIN(lift_D12(2), 2, 4)
