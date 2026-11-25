"""Case split on one coordinate v (chosen mod p: max #generators that become constant when v=0):
branch 0: J + (v); branch 1: J + (v*yy - 1) (v invertible). Unit in both => cell empty (mod p screen). args: S tout; env PQD"""
import sys, os, subprocess, json, time
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
PP, QQ, DD = map(int, os.environ.get("PQD", "3,5,6").split(","))
S = tuple(map(int, sys.argv[1].split(","))); tout = int(sys.argv[2])
S_, fr, u = next(c for c in cells(PP, QQ, DD) if tuple(c[0]) == S)
s, info = G.build(PP, QQ, DD, S_, fr, 32003, "exp", 3, [], False)
pre = s[:s.index("int t0 = timer;")]
avars = s[s.index("ring A = "):].split("(")[1].split(")")[0]
choose = pre + """J = simplify(J, 2); int i; int j; int c; int best = 0; int bi = 1; poly h;
for (i = 1; i <= nvars(basering); i++) { c = 0; for (j = 1; j <= ncols(J); j++) { h = subst(J[j], var(i), 0); if (deg(h) <= 0) { c++; } } if (c > best) { best = c; bi = i; } }
print("CHOOSE " + varstr(bi) + " " + string(best)); quit;
"""
def run(sc, tag):
    fn = f"cells/split_{tag}.sing"; open(fn, "w").write(sc); t0 = time.time()
    try: out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
    except subprocess.TimeoutExpired: subprocess.run(["pkill", "-f", fn]); out = "TIMEOUT"
    os.remove(fn); return out, round(time.time() - t0)
out, _ = run(choose, "c"); v, cnt = [l.split()[1:] for l in out.splitlines() if l.startswith("CHOOSE")][0]
rec = {"S": list(S), "unknowns": u, "split_var": v, "const_when_0": int(cnt)}
b0 = pre + f'J = J + {v}; option(redSB); ideal Gs = std(J); print("RES unit=" + string(Gs[1]==1) + " dim=" + string(dim(Gs))); quit;\n'
b1 = pre.replace(f"ring A = 32003,({avars}),dp;", f"ring A = 32003,({avars},yy),dp;") + f'J = J + ({v}*yy-1); option(redSB); ideal Gs = std(J); print("RES unit=" + string(Gs[1]==1) + " dim=" + string(dim(Gs))); quit;\n'
for nm, sc in (("v=0", b0), ("v!=0", b1)):
    o, t = run(sc, nm.replace("!", "n").replace("=", "e")); r = [l for l in o.splitlines() if l.startswith("RES")]
    rec[nm] = (r[0][4:] if r else ("TIMEOUT" if o == "TIMEOUT" else "OOM" if "memory" in o else "ERR " + o[-80:])) + f" ({t}s)"
print(json.dumps(rec), flush=True)
