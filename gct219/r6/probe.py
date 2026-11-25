"""Staged Krull-dim probe (mod 32003, exp-weight minors deg<=3), per open cell: A = P2 + minors, B = + P3, C = + P4.
Prints dim after each stage reached before the timeout."""
import sys, json, subprocess, os, time
sys.path.insert(0, ".")
import minorsw as MW
from schubert import cells
from cell_solve import script
tout, jobs = int(sys.argv[1]), int(sys.argv[2])
p, q, d = 4, 5, 7
H, OM = MW.setup(p, q, "exp")
def run(c):
    S, fr, u = c
    ex = MW.extra(S, fr, p, q, H, OM, 3)
    s = script(p, q, d, S, fr, 32003)
    head = s[:s.index("ideal I; matrix C; int i;")]
    avars = s[s.index("ring A = "):].split("(")[1].split(")")[0]
    xs = "*".join(f"x({i+1})" for i in range(d))
    body = "matrix C; int i; ideal I2; ideal I3; ideal I4; ideal MA;\n" + "".join(f"MA = MA + ({e});\n" for e in ex)
    body += f"C = coef(f(P2), {xs}); for (i = 1; i <= ncols(C); i++) {{ I2 = I2 + C[2, i]; }}\n"
    body += f"""ring A = 32003,({avars}),dp; option(redSB);
ideal G = std(imap(R, MA)); print("STAGE M dim=" + string(dim(G)));
G = std(G + imap(R, I2)); print("STAGE A dim=" + string(dim(G)) + " unit=" + string(G[1]==1));
if (G[1] != 1) {{ setring R; C = coef(f(P3), {xs}); for (i = 1; i <= ncols(C); i++) {{ I3 = I3 + C[2, i]; }} setring A;
  G = std(G + imap(R, I3)); print("STAGE B dim=" + string(dim(G)) + " unit=" + string(G[1]==1)); }}
if (G[1] != 1) {{ setring R; C = coef(f(P4), {xs}); for (i = 1; i <= ncols(C); i++) {{ I4 = I4 + C[2, i]; }} setring A;
  G = std(G + imap(R, I4)); print("STAGE C dim=" + string(dim(G)) + " unit=" + string(G[1]==1)); }}
quit;
"""
    fn = f"cells/pr_" + "-".join(map(str, S)) + ".sing"; open(fn, "w").write(head + body)
    t0 = time.time(); proc = subprocess.Popen(["Singular", "-q", fn], stdout=subprocess.PIPE, text=True)
    try:
        out, _ = proc.communicate(timeout=tout); tag = "done"
    except subprocess.TimeoutExpired:
        proc.kill(); out, _ = proc.communicate(); tag = "TIMEOUT"
    os.remove(fn)
    st = [l for l in (out or "").splitlines() if l.startswith("STAGE")]
    if "no more memory" in (out or ""): tag = "OOM"
    return {"S": list(S), "unknowns": u, "minors": len(ex), "stages": st, "end": tag, "sec": round(time.time() - t0, 1)}
T = json.load(open("r6/table6_4x5_d7.json"))
openS = {tuple(map(int, k.split(","))) for k, v in T.items() if v[1] in ("timeout", "timeout/OOM")}
todo = sorted([c for c in cells(p, q, d) if tuple(c[0]) in openS], key=lambda c: c[2])
print("probe", len(todo), flush=True)
from concurrent.futures import ProcessPoolExecutor
with ProcessPoolExecutor(jobs) as ex, open("r6/probe.jsonl", "w") as fh:
    for r in ex.map(run, todo):
        fh.write(json.dumps(r) + "\n"); fh.flush(); print(r, flush=True)
