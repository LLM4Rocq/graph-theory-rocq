#!/usr/bin/env python3
"""Acceptance gate for a landed milestone:  python3 meta/check_milestone.py <phase> <package>

Verifies, against the live opam switch `digraph`:
  1. every expected formal_name (from milestone_rows.py) is Defined in theories/conjectures/<phase>.v;
  2. the milestone .v files are listed in the package _CoqProject;
  3. the package compiles (coq_makefile + make);
  4. Print Assumptions is clean (Closed under the global context) for every statement node;
  5. no top-level Axiom / Parameter / Admitted / Conjecture / Hypothesis (outside comments);
  6. each non-todo leg in meta/opg_legs_state.json is justified by an artifact + carries provenance.
Exit 0 iff all pass. Run only inside (or with) the `digraph` switch on PATH.
"""
import json, os, re, sys, subprocess, glob

META = os.path.dirname(os.path.abspath(__file__))
MONO = os.path.dirname(META)
NS = {'chromatic-theory': 'Chromatic', 'hamiltonicity-theory': 'Hamilton', 'homomorphism-theory': 'Hom',
      'cycle-theory': 'Cycle', 'minor-theory': 'Minor', 'packing-theory': 'Packing',
      'reconstruction-theory': 'Reconstruction', 'hypergraph-theory': 'Hypergraph',
      'topological-graph-theory': 'Topological', 'graph-theory-misc': 'GTMisc', 'digraph-theory': 'Digraph',
      'extremal-graph-theory': 'Extremal', 'infinite-graph-theory': 'Infinite', 'spectral-graph-theory': 'Spectral'}

if len(sys.argv) < 3:
    sys.exit("usage: check_milestone.py <phase> <package>")
phase, package = sys.argv[1], sys.argv[2]
pkg = os.path.join(MONO, package)
ns = NS.get(package)
results = []  # (ok, label, detail)
def chk(ok, label, detail=""): results.append((bool(ok), label, detail))

# switch resolution: prefer PATH, else the known global switch bin
SW = os.path.expanduser("~/.opam/digraph/bin")
env = dict(os.environ)
if os.path.isdir(SW):
    env["PATH"] = SW + os.pathsep + env.get("PATH", "")
    env.setdefault("OPAM_SWITCH_PREFIX", os.path.expanduser("~/.opam/digraph"))
def run(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd or pkg, env=env, capture_output=True, text=True)

# expected formal_names from the deterministic loader
proc = subprocess.run([sys.executable, os.path.join(META, "milestone_rows.py"), phase, package],
                      capture_output=True, text=True)
if proc.returncode != 0:
    sys.exit(f"milestone_rows.py failed:\n{proc.stderr}")
rows = json.loads(proc.stdout)
expected = [r["formal_name"] for r in rows]
slugs = [r["slug"] for r in rows]

stmt = os.path.join(pkg, "theories", "conjectures", f"{phase}.v")
grounding = os.path.join(pkg, "theories", "conjectures", f"grounding_{phase}.v")
implications = os.path.join(pkg, "theories", "conjectures", f"implications_{phase}.v")
chk(ns, "package known", package if ns else f"unknown package {package}")
chk(os.path.exists(stmt), "statement file exists", stmt)

# 1) every expected formal_name is Defined — search ALL conjecture files, not just
#    <phase>.v: some milestones (e.g. the absorbed Digraph P9) define "already-formalized"
#    rows in sibling files (classic_core.v / packing.v / sad.v) re-exported by <phase>.v.
conj_dir = os.path.join(pkg, "theories", "conjectures")
def_re = re.compile(r"^\s*Definition\s+([A-Za-z0-9_']+)", re.M)
defined_in = {}  # formal_name -> module basename (no .v) that defines it
for vf in sorted(glob.glob(os.path.join(conj_dir, "*.v"))):
    base = os.path.basename(vf)[:-2]
    try:
        for n in def_re.findall(open(vf).read()):
            defined_in.setdefault(n, base)
    except OSError:
        pass
defined = set(defined_in)
missing = [n for n in expected if n not in defined]
chk(not missing, f"all {len(expected)} formal_names Defined", f"missing: {missing}" if missing else "")

# 2) milestone .v files in _CoqProject
cqp = os.path.join(pkg, "_CoqProject")
cqp_txt = open(cqp).read() if os.path.exists(cqp) else ""
need_files = [f"theories/conjectures/{phase}.v"] + \
             [f"theories/conjectures/{os.path.basename(p)}" for p in (grounding, implications) if os.path.exists(p)]
notlisted = [f for f in need_files if f not in cqp_txt]
chk(os.path.exists(cqp) and not notlisted, "files in _CoqProject", f"not listed: {notlisted}" if notlisted else "")

# 3) build sibling dependencies referenced in _CoqProject (e.g. -Q ../base/theories GTBase), then compile
deps = re.findall(r"-[QR]\s+\.\./([\w.-]+)/theories\s+\S+", cqp_txt)
dep_fail = []
for dep in deps:
    dpath = os.path.join(MONO, dep)
    if os.path.isfile(os.path.join(dpath, "_CoqProject")):
        dm = run(["bash", "-c", "rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq"], cwd=dpath)
        if dm.returncode != 0:
            dep_fail.append(dep)
chk(not dep_fail, f"dependencies build ({', '.join(deps) or 'none'})", f"failed: {dep_fail}" if dep_fail else "")
mk = run(["bash", "-c", "rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq"])
compiles = mk.returncode == 0
chk(compiles, "package compiles", "" if compiles else (mk.stdout + mk.stderr)[-500:])

# 5) no top-level axioms/admits (outside comments) — strip block comments first
def strip_comments(t):
    return re.sub(r"\(\*.*?\*\)", "", t, flags=re.S)
axiom_re = re.compile(r"^\s*(Axiom|Parameter|Admitted|Conjecture|Hypothesis|admit)\b", re.M)
ax_hits = []
for p in (stmt, grounding, implications):
    if os.path.exists(p):
        for m in axiom_re.finditer(strip_comments(open(p).read())):
            ax_hits.append(f"{os.path.basename(p)}:{m.group(1)}")
chk(not ax_hits, "no top-level Axiom/Parameter/Admitted", f"found: {ax_hits}" if ax_hits else "")

# 4) Print Assumptions clean for every statement node (probe compiled against the built .vo)
assum_ok, assum_detail = False, "skipped (compile failed)"
if compiles and ns:
    probe = os.path.join(pkg, "theories", "conjectures", f"_assum_{phase}.v")
    # import EVERY conjecture module that defines an expected name (not just <phase>.v):
    # milestones like Digraph P9 spread "already-formalized" rows across sibling files.
    mods = sorted({defined_in[n] for n in expected if n in defined_in} | {phase})
    body = f"From {ns}.conjectures Require Import {' '.join(mods)}.\n" + \
           "".join(f"Print Assumptions {n}.\n" for n in expected)
    open(probe, "w").write(body)
    # build coqc include flags as an argv LIST (no shell string interpolation of _CoqProject paths)
    incl_flags = []
    for m in re.findall(r"-[QR]\s+\S+\s+\S+", cqp_txt):
        incl_flags += m.split()
    if not incl_flags:
        incl_flags = ["-R", "theories", ns]
    pr = run(["coqc"] + incl_flags + [f"theories/conjectures/_assum_{phase}.v"])
    out = pr.stdout + pr.stderr
    closed = out.count("Closed under the global context")
    has_axioms = "Axioms:" in out
    assum_ok = (pr.returncode == 0) and (not has_axioms) and (closed == len(expected))
    assum_detail = "" if assum_ok else f"closed={closed}/{len(expected)} has_axioms={has_axioms}; {out[-300:]}"
    for f in glob.glob(os.path.join(pkg, "theories", "conjectures", f"_assum_{phase}*")) + \
             glob.glob(os.path.join(pkg, "theories", "conjectures", f"._assum_{phase}*")):
        os.remove(f)
n_axfree = closed if (compiles and ns) else 0
chk(assum_ok, f"Print Assumptions clean ({n_axfree}/{len(expected)} statements)", assum_detail)

# 6) overlay legs justified by artifacts + provenance
legs_path = os.path.join(META, "opg_legs_state.json")
overlay = json.load(open(legs_path)).get("entries", {}) if os.path.exists(legs_path) else {}
unjust = []
for s in slugs:
    e = overlay.get(s)
    if not e:
        unjust.append(f"{s}: no overlay entry (every milestone row needs overlay leg-state + provenance)")
        continue
    if e.get("statement") == "done" and not (compiles and not missing):
        unjust.append(f"{s}: statement=done but not (compiles & defined)")
    if e.get("grounding") == "done" and not (compiles and os.path.exists(grounding)):
        unjust.append(f"{s}: grounding=done but grounding file missing/not compiled")
    if e.get("edges") in ("partial", "done") and not os.path.exists(implications):
        unjust.append(f"{s}: edges={e.get('edges')} but no implications file")
    for lg in ("statement", "grounding", "edges"):
        if e.get(lg, "todo") != "todo" and not (e.get("commit") and e.get("package")):
            unjust.append(f"{s}: non-todo {lg} lacks commit+package provenance")
chk(not unjust, "overlay leg-state justified by artifacts", "; ".join(unjust[:6]) if unjust else "")

# ── report ──
print(f"\n=== check_milestone {phase} / {package} ===")
print(f"  {len(expected)} statement nodes: {', '.join(expected)}")
for ok, label, detail in results:
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}" + (f"  — {detail}" if (detail and not ok) else ""))
allok = all(ok for ok, _, _ in results)
n_def = len(expected) - len(missing)
print(f"\n{'ACCEPTED' if allok else 'REJECTED'}: {sum(ok for ok,_,_ in results)}/{len(results)} CHECKS passed | "
      f"statements: {n_def}/{len(expected)} Defined, {n_axfree}/{len(expected)} axiom-free.")
print("  (NB: the X/Y above counts acceptance CHECKS, not statement rows — the row count is the line above.)")
sys.exit(0 if allok else 1)
