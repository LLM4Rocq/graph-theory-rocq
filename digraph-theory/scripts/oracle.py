"""Oracle CLI + benchmark for arXiv:2310.04265 (clique number of tournaments).

Central object: omega_vec(T), the EXACT clique number of a tournament T --
  omega_vec(T) = min over all total orders prec of omega(T^prec),
where T^prec is the (undirected) backedge graph (edge uv iff u prec v and the
arc v->u is backward).  Computed EXACTLY (no heuristics) by enumerating orders
(brute force) or by an exact branch-and-bound that returns the identical value.

This is the engine's anti-hallucination spine for Question 5.9 (the f=identity
"super omega_vec-cluster" form of Conjecture 5.8) and its NEGATION Conjecture
5.10 ("for every k>=3 there are infinitely many k-omega_vec-critical
tournaments").  The oracle:
  * check_construction(n, arcs): verify a tournament, report omega_vec and,
    optionally, its minimal certifying subtournament order.
  * is_k_omega_vec_critical(n, arcs, k): exact criticality test.
  * scan_critical(n, k): enumerate tournaments on n vertices (geng/orientation
    free brute force over the 2^C(n,2) orientations) and report all
    k-omega_vec-critical ones -- bounded sizes support Question 5.9, growth of
    the max order of a 3-critical tournament supports Conjecture 5.10.

Benchmark / ground truth (verified by this oracle, see ground_truth_landmarks
in ledger.json):
  omega_vec(directed C3) = 2  (unique 2-omega_vec-critical tournament)
  omega_vec(TT_k)        = 1  for every transitive tournament
  omega_vec(S~_n)       >= n  (Lemma 3.8); = n verified for n=2 (3 vtx) and
                              n=3 (9 vtx).
"""
from __future__ import annotations

import argparse
import json

import core
import constructions as C


# --------------------------------------------------------------------------- #
#  Grounding a proposed tournament
# --------------------------------------------------------------------------- #

def check_construction(n, arcs, name="construction", with_cert=False,
                       method="auto"):
    """Exactly verify and measure an explicit tournament."""
    is_t = core.is_tournament(n, arcs)
    out = {"name": name, "n": n, "m_arcs": len(arcs), "is_tournament": is_t}
    if not is_t:
        out["error"] = "not a tournament (need exactly one arc per pair)"
        return out
    w = core.omega_vec(n, arcs, method=method)
    out["omega_vec"] = w
    if with_cert and w >= 1:
        sz, vs = core.min_subtournament_order_for_k(n, arcs, w)
        out["min_cert_order_for_omega_vec"] = sz
        out["min_cert_vertices"] = list(vs) if vs is not None else None
    return out


# --------------------------------------------------------------------------- #
#  Criticality scan  (probing Question 5.9 vs Conjecture 5.10)
# --------------------------------------------------------------------------- #

def _canonical_key(n, arcs):
    """A cheap iso-invariant signature (sorted score sequence) to dedupe
    reporting -- NOT a full iso test, only used to limit witness spam."""
    out_deg = [0] * n
    for (u, v) in arcs:
        out_deg[u] += 1
    return tuple(sorted(out_deg))


def scan_critical(n, k, max_witnesses=20):
    """Enumerate ALL tournaments on n vertices (2^C(n,2) orientations of K_n,
    not iso-reduced) and return the k-omega_vec-critical ones.

    Reports count, up to `max_witnesses` example arc-sets, and the distribution
    of omega_vec over all tournaments on n vertices.  Feasible for n<=6
    (2^15=32768); n=7 is 2.1M and slow.
    """
    crit = []
    omega_hist = {}
    seen_sig = set()
    total = 0
    num_crit = 0
    for (nn, arcs) in C.all_tournaments(n):
        total += 1
        w = core.omega_vec(nn, arcs)
        omega_hist[w] = omega_hist.get(w, 0) + 1
        if w == k and core.is_k_omega_vec_critical(nn, arcs, k):
            num_crit += 1
            sig = _canonical_key(nn, arcs)
            if len(crit) < max_witnesses:
                crit.append({"arcs": list(arcs), "score_seq": list(sig)})
            seen_sig.add(sig)
    return {
        "n": n, "k": k,
        "n_tournaments_enumerated": total,
        "omega_vec_histogram": {str(kk): vv for kk, vv in sorted(omega_hist.items())},
        "num_k_critical": num_crit,
        "distinct_critical_score_seqs": len(seen_sig),
        "critical_witnesses": crit,
    }


# --------------------------------------------------------------------------- #
#  Named built-ins  (the landmark check)
# --------------------------------------------------------------------------- #

_BUILDERS = {
    "c3": lambda: C.directed_C3(),
    "tt1": lambda: C.transitive_tournament(1),
    "tt3": lambda: C.transitive_tournament(3),
    "tt5": lambda: C.transitive_tournament(5),
    "s2": lambda: C.S_tilde(2),
    "s3": lambda: C.S_tilde(3),
    "s4": lambda: C.S_tilde(4),
}


def landmarks():
    """Run and return the paper's anchor values (the verification table)."""
    res = {}
    n, a = C.directed_C3()
    res["omega_vec(C3)"] = core.omega_vec(n, a)
    res["C3_is_2_critical"] = core.is_k_omega_vec_critical(n, a, 2)
    for k in (1, 3, 5):
        n, a = C.transitive_tournament(k)
        res[f"omega_vec(TT_{k})"] = core.omega_vec(n, a)
    for nn in (1, 2, 3):
        n, a = C.S_tilde(nn)
        res[f"omega_vec(S~_{nn})[n={n}]"] = core.omega_vec(n, a)
    return res


# --------------------------------------------------------------------------- #
#  CLI
# --------------------------------------------------------------------------- #

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_chk = sub.add_parser("check", help="check a named built-in tournament")
    p_chk.add_argument("name", choices=sorted(_BUILDERS))
    p_chk.add_argument("--cert", action="store_true",
                       help="also report minimal certifying subtournament order")

    p_lm = sub.add_parser("landmarks", help="run the paper's anchor table")

    p_sc = sub.add_parser("scan-critical",
                          help="enumerate all tournaments on n vtx, find k-omega_vec-critical ones")
    p_sc.add_argument("n", type=int)
    p_sc.add_argument("k", type=int)
    p_sc.add_argument("--max-witnesses", type=int, default=20)

    p_om = sub.add_parser("stilde", help="omega_vec(S~_n) (Lemma 3.8 anchor)")
    p_om.add_argument("n", type=int)

    args = ap.parse_args()
    if args.cmd == "check":
        n, arcs = _BUILDERS[args.name]()
        res = check_construction(n, arcs, name=args.name, with_cert=args.cert)
    elif args.cmd == "landmarks":
        res = landmarks()
    elif args.cmd == "scan-critical":
        res = scan_critical(args.n, args.k, max_witnesses=args.max_witnesses)
    elif args.cmd == "stilde":
        n, arcs = C.S_tilde(args.n)
        res = check_construction(n, arcs, name=f"S~_{args.n}")
        res["lemma_3.8_lower_bound"] = args.n

    print(json.dumps(res, indent=2, default=str))


if __name__ == "__main__":
    main()
