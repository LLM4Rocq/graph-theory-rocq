"""Regression suite pinning the omega_vec oracle to arXiv:2310.04265's known
values.  These are the soundness guards: if a future edit breaks any of these,
the ground truth is no longer trustworthy.

Run:  python3 -m pytest scripts/ -q     (needs: networkx, pytest)
"""
import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

import core                       # noqa: E402
import constructions as C        # noqa: E402
import oracle                    # noqa: E402


# ---- structure -------------------------------------------------------------

def test_is_tournament():
    n, a = C.directed_C3()
    assert core.is_tournament(n, a)
    n5, a5 = C.transitive_tournament(5)
    assert core.is_tournament(n5, a5)
    n9, a9 = C.S_tilde(3)
    assert n9 == 9 and core.is_tournament(n9, a9)
    # not a tournament: missing a pair
    assert not core.is_tournament(3, [(0, 1), (1, 2)])
    # not a tournament: a 2-cycle / duplicated pair
    assert not core.is_tournament(3, [(0, 1), (1, 0), (1, 2)])


# ---- omega_vec anchors from the paper --------------------------------------

def test_directed_C3_omega_vec():
    n, a = C.directed_C3()
    assert core.omega_vec(n, a) == 2           # stated just after Question 5.9


def test_transitive_omega_vec_is_one():
    for k in (1, 2, 3, 4, 5, 6):
        n, a = C.transitive_tournament(k)
        assert core.omega_vec(n, a) == 1       # omega_vec(TT_k)=1


@pytest.mark.parametrize("nn,n_vtx,expected", [
    (1, 1, 1),
    (2, 3, 2),
    (3, 9, 3),                                  # Lemma 3.8: omega_vec(S~_n) >= n; =n here
])
def test_stilde_omega_vec(nn, n_vtx, expected):
    n, a = C.S_tilde(nn)
    assert n == n_vtx
    assert core.omega_vec(n, a) == expected
    assert core.omega_vec(n, a) >= nn          # the Lemma 3.8 lower bound itself


# ---- branch-and-bound == brute force (the exactness cross-check) -----------

def test_bb_equals_bruteforce():
    for builder in (lambda: C.directed_C3(),
                    lambda: C.transitive_tournament(4),
                    lambda: C.S_tilde(2),
                    lambda: C.random_tournament(6, seed=1),
                    lambda: C.random_tournament(7, seed=2)):
        n, a = builder()
        assert core.omega_vec_bb(n, a) == core.omega_vec_bruteforce(n, a)


def test_bb_equals_bruteforce_stilde3():
    n, a = C.S_tilde(3)                         # n=9, 9! brute force ~10s
    assert core.omega_vec_bb(n, a) == core.omega_vec_bruteforce(n, a) == 3


# ---- criticality -----------------------------------------------------------

def test_C3_is_unique_2_critical():
    n, a = C.directed_C3()
    assert core.is_k_omega_vec_critical(n, a, 2)
    # the single-vertex tournament is the unique 1-critical
    n1, a1 = C.transitive_tournament(1)
    assert core.is_k_omega_vec_critical(n1, a1, 1)


def test_scan_critical_n3():
    """At n=3 the only omega_vec=2 tournaments are the two labellings of C3,
    both 2-critical (paper: C3 is THE unique 2-omega_vec-critical tournament)."""
    res = oracle.scan_critical(3, 2)
    assert res["omega_vec_histogram"] == {"1": 6, "2": 2}
    assert res["num_k_critical"] == 2          # two labelled copies of C3
    assert res["distinct_critical_score_seqs"] == 1   # one iso class


def test_no_omega3_below_6():
    """No tournament on <=5 vertices has omega_vec=3 (so no 3-critical there)."""
    for n in (4, 5):
        res = oracle.scan_critical(n, 3)
        assert "3" not in res["omega_vec_histogram"]
        assert res["num_k_critical"] == 0


# ---- finite cluster handle (Question 5.9) ----------------------------------

def test_min_cert_order():
    n, a = C.S_tilde(2)
    sz, vs = core.min_subtournament_order_for_k(n, a, 2)
    assert sz == 3 and set(vs) == {0, 1, 2}    # the C3 itself certifies omega_vec>=2
