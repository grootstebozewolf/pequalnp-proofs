"""R7 runner: p q d variant char tout jobs [statusfile].  variant: rr = colex deg3 minors + row-rank minors (λ-free);
rows = rr + FK full-row separators (λ); blk = rows + all FK blocks |R|+|C|=q+1."""
import sys, json, subprocess, os, time
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
p, q, d = map(int, sys.argv[1:4]); var = sys.argv[4]; char, tout, jobs = map(int, sys.argv[5:8])
KINDS = {"rr": [], "rows": [(1, q)], "blk": [(a, q + 1 - a) for a in range(1, p + 1)]}[var.rstrip("0").replace("m3", "rr").replace("m4", "rr").replace("m5", "rr")]
MDEG = 0 if var.endswith("0") else (int(var[1]) if var in ("m4", "m5") else 3)
if os.environ.get("ALLREPS"):
    need = {tuple(o["S"]) for o in json.load(open(f"orbitw_exp_{p}x{q}_d{d}.json")) if not o["killed"]}
elif p == 4 and q == 5 and d == 7:
    T = json.load(open("r6/table6_4x5_d7.json")); need = {tuple(map(int, k.split(","))) for k, (u, st) in T.items() if not st.startswith(("emptyQ", "FK"))}
else:
    W = json.load(open(f"r6/wstatus_{p}x{q}_d{d}.json")); need = {tuple(S) for S, u, st in W if st not in ("emptyQ", "FK")}
if len(sys.argv) > 8: need &= {tuple(x) for x in json.load(open(sys.argv[8]))}
def run(a):
    S, fr, u = a
    s, info = G.build(p, q, d, S, fr, char, "exp", MDEG, KINDS, var not in ("m3", "m4", "m5"))
    fn = f"cells/r7_{p}{q}{d}_" + "-".join(map(str, S)) + f"_{char}_{var}.sing"; open(fn, "w").write(s)
    t0 = time.time()
    try:
        out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
        res = [l for l in out.splitlines() if l.startswith("RESULT")]
        r = res[0] if res and "?" not in out else ("OOM" if "memory" in out else "ERROR " + out[-150:])
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", fn]); r = "TIMEOUT"
    os.remove(fn)
    return {"S": list(S), "unknowns": u, **info, "var": var, "char": char, "res": r, "sec": round(time.time() - t0, 1)}
todo = sorted([(S, fr, u) for S, fr, u in cells(p, q, d) if tuple(S) in need], key=lambda a: a[2])
print("todo", len(todo), flush=True)
from concurrent.futures import ProcessPoolExecutor
with ProcessPoolExecutor(jobs) as ex, open(f"r7/run_{p}x{q}_d{d}_{var}_c{char}.jsonl", "a") as fh:
    for r in ex.map(run, todo):
        fh.write(json.dumps(r) + "\n"); fh.flush(); print(r, flush=True)
