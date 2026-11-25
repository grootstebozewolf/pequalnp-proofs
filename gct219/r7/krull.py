"""Krull-dim probe mod p for stuck cells: stage A = colex minors + row-rank only; stage Pk = A + P2..Pk coefficients. args: p q d tout listfile"""
import sys, subprocess, json, os, time
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
p, q, d, tout = map(int, sys.argv[1:5]); L = {tuple(x) for x in json.load(open(sys.argv[5]))}
for S, fr, u in sorted([c for c in cells(p, q, d) if tuple(c[0]) in L], key=lambda c: c[2]):
    s, info = G.build(p, q, d, S, fr, 32003, "exp", int(os.environ.get("MDEG", "3")), [], os.environ.get("RR", "1") == "1")
    row = {"S": list(S), "unknowns": u}
    for stage in ["A"] + [f"P{k}" for k in range(2, p + 1)]:
        keep = 1 if stage == "A" else int(stage[1:])
        ss = "\n".join(l for l in s.splitlines() if not (l.startswith("C = coef(f(P") and int(l[len("C = coef(f(P")]) > keep))
        fn = f"cells/kr_{p}{q}{d}_{'-'.join(map(str, S))}_{stage}.sing"; open(fn, "w").write(ss); t0 = time.time()
        try:
            out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
            r = [l.split("unit=")[1] for l in out.splitlines() if l.startswith("RESULT")] or ["OOM" if "memory" in out else "ERR"]
            row[stage] = r[0] + f" ({time.time()-t0:.0f}s)"
        except subprocess.TimeoutExpired:
            subprocess.run(["pkill", "-f", fn]); row[stage] = f"TIMEOUT {tout}s"; os.remove(fn); break
        os.remove(fn)
    print(json.dumps(row), flush=True)
