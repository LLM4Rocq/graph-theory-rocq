"""Oracle test suite for the k4 dossier (docs/k34_dossier.md §6).

Run:  uv run --with pytest --with networkx --with python-sat \
        python3 -m pytest scripts/test_k4_oracle.py -q
"""

import pytest

from core import is_tournament
from k4_oracle import (
    t4, kv_key, kd_key, classes,
    check_factors_exact, check_t4_value, check_t4_deletion,
    check_t4_vertex_transitive, check_crt_iso_m3,
    check_value_order_clique4, check_deletion_order_clique3,
    check_class_caps, check_bands_D1, check_31_exclusion,
    check_22_core, check_22_lemma,
)

SMALL = [3, 4]          # m values where exact omega_vec is affordable (n = 7, 9)
RANGE = list(range(3, 13))   # m values for the uniform-in-m arithmetic items

# ---------- construction sanity ----------

@pytest.mark.parametrize("m", SMALL)
def test_t4_is_tournament(m):
    nv, arcs = t4(m)
    assert nv == 3 * (2 * m + 1)
    assert is_tournament(nv, arcs)

@pytest.mark.parametrize("m", SMALL)
def test_keys_injective(m):
    n = 2 * m + 1
    kv = {kv_key(m, t, h) for t in range(n) for h in range(3)}
    kd = {kd_key(m, t, h) for t in range(n) for h in range(3)}
    assert len(kv) == 3 * n and len(kd) == 3 * n

@pytest.mark.parametrize("m", RANGE)
def test_class_sizes(m):
    """K5 = {(0,0)}, K4 = {(0,1),(0,2)} ∪ {(t,0) : 1≤t≤m}."""
    cl = classes(m)
    assert cl[5] == [(0, 0)]
    assert len(cl[4]) == m + 2 and len(cl[3]) == 3 * m and len(cl[2]) == 2 * m

# ---------- headline values ----------

@pytest.mark.parametrize("m", SMALL)
def test_factor_values_exact(m):
    """omega(AC_n) = 3, omega(AC_n - v) = 2, omega(C3) = 2 (exact)."""
    assert check_factors_exact(m)

@pytest.mark.parametrize("m", SMALL)
def test_omegabar_T4_is_4(m):
    """kv order <= 4; SAT no-K4 UNSAT >= 4."""
    assert check_t4_value(m)

@pytest.mark.parametrize("m", SMALL)
def test_omegabar_T4_deletion_is_3(m):
    """kd order <= 3 on T4 - (0,0); SAT no-K3 UNSAT >= 3."""
    assert check_t4_deletion(m)

@pytest.mark.parametrize("m", RANGE)
def test_T4_vertex_transitive(m):
    assert check_t4_vertex_transitive(m)

def test_crt_iso_m3():
    """AC_7[C3] = the independently certified circulant(21, g21)."""
    assert check_crt_iso_m3()

# ---------- the two witnessing orders (V-items / D-items) ----------

@pytest.mark.parametrize("m", SMALL + [5])
def test_merged_order_gives_4(m):
    assert check_value_order_clique4(m)

@pytest.mark.parametrize("m", SMALL + [5])
def test_d_then_c_order_gives_3(m):
    assert check_deletion_order_clique3(m)

# ---------- V-items: within-class caps (V1-V4), uniform in m ----------

@pytest.mark.parametrize("m", RANGE)
def test_class_caps(m):
    assert check_class_caps(m)

# ---------- D-items ----------

@pytest.mark.parametrize("m", RANGE)
def test_D1_no_within_band_backedge(m):
    assert check_bands_D1(m)

@pytest.mark.parametrize("m", RANGE)
def test_D2_31_exclusion(m):
    assert check_31_exclusion(m)

@pytest.mark.parametrize("m", list(range(3, 40)))
def test_D3_core_incompatibility(m):
    assert check_22_core(m)

@pytest.mark.parametrize("m", RANGE)
def test_D3_22_lemma(m):
    assert check_22_lemma(m)
