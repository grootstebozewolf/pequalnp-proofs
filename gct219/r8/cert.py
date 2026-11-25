"""R8 bounded-degree certificate search (generators: P_k x-coefficients + colex minors deg<=3; NO FK-λ, NO row rank).
Stage 1 (F_p, Singular): L = std(linear generators) [LP pre-filter]; J2 = NF(J mod L) (index-preserving);
  degree-truncated std (option degBound = B, B = 2,3,...,BMAX) = Macaulay linear algebra up to total degree B; record first B with 1 found;
  then lift(J2, 1) mod p -> support (indices j with nonzero cofactor).
Stage 2 (Q, Singular): lift 1 into K = J[support] + L_orig (original generators only) -> r7/cert_<S>_r8.txt; Stage 3: r7/cert_verify.py (sympy).
args: S  [tout1] [tout2] [BMAX]; env PQD (default 4,5,7)"""
import sys, os, subprocess, time, json, re
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
PP, QQ, DD = map(int, os.environ.get("PQD", "4,5,7").split(","))
S = tuple(map(int, sys.argv[1].split(","))); tag = sys.argv[1].replace(",", "-")
t1 = int(sys.argv[2]) if len(sys.argv) > 2 else 400; t2 = int(sys.argv[3]) if len(sys.argv) > 3 else 400; BMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 6
S_, fr, u = next(c for c in cells(PP, QQ, DD) if tuple(c[0]) == S)
def sing(script, fn, tout):
    open(fn, "w").write(script)
    try:
        out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", fn]); out = "TIMEOUT"
    os.remove(fn); return out
def head(char):
    s, info = G.build(PP, QQ, DD, S_, fr, char, "exp", 3, [], False)
    return s[:s.index("int t0 = timer;")] + """J = simplify(J, 2);
int i; int k; ideal L;
for (i = 1; i <= ncols(J); i++) { if (deg(J[i]) <= 1) { L = L + J[i]; } }
L = simplify(L, 2);
""", info
rec = {"S": list(S), "unknowns": u, "pqd": [PP, QQ, DD]}
h, info = head(32003); rec.update(minors=info["minors"])
s1 = h + f"""ideal Ls = std(L);
print("LIN nlin=" + string(size(L)) + " rank=" + string(size(Ls)) + " unit=" + string(Ls[1]==1) + " ngens=" + string(ncols(J)));
ideal J2 = reduce(J, Ls);
ideal J2s = simplify(J2, 2);
int md = 0; for (i = 1; i <= ncols(J2s); i++) {{ if (deg(J2s[i]) > md) {{ md = deg(J2s[i]); }} }}
print("RED ngens=" + string(ncols(J2s)) + " maxdeg=" + string(md));
int B; ideal Gb;
for (B = 2; B <= {BMAX}; B++) {{ degBound = B; Gb = std(J2s); print("DEG B=" + string(B) + " unit=" + string(Gb[1]==1) + " t=" + string(timer)); if (Gb[1]==1) {{ break; }} }}
degBound = 0;
matrix Ml = lift(J2, ideal(1));
string sup = "";
for (k = 1; k <= nrows(Ml); k++) {{ if (Ml[k,1] != 0) {{ sup = sup + string(k) + ","; }} }}
print("SUP " + sup);
quit;
"""
t0 = time.time(); out = sing(s1, f"cells/r8a_{tag}.sing", t1); rec["t1"] = round(time.time() - t0)
rec["lin"] = [l for l in out.splitlines() if l.startswith(("LIN", "RED"))]
rec["deg"] = [l for l in out.splitlines() if l.startswith("DEG")]
sup = [l[4:] for l in out.splitlines() if l.startswith("SUP")]
rec["stage1"] = "ok" if sup else ("TIMEOUT" if out == "TIMEOUT" else "OOM" if "memory" in out else "ERR " + out[-120:])
if sup:
    idx = [int(x) for x in sup[0].split(",") if x]; rec["support"] = len(idx)
    h0, _ = head(0)
    s2 = h0 + f"""ideal K = L;
intvec sv = {",".join(map(str, idx))};
for (i = 1; i <= size(sv); i++) {{ K = K + J[sv[i]]; }}
K = simplify(K, 2);
matrix Km = matrix(K); matrix Ml = lift(K, ideal(1));
string cf = "r7/cert_{tag}_r8.txt"; write(":w " + cf, "");
int nz = 0; int md = 0;
for (k = 1; k <= nrows(Ml); k++) {{ if (Ml[k,1] != 0) {{ nz++; if (deg(Ml[k,1]) > md) {{ md = deg(Ml[k,1]); }} write(":a " + cf, string(Km[1,k]) + " ; " + string(Ml[k,1])); }} }}
print("QLIFT gens=" + string(ncols(Km)) + " nonzero=" + string(nz) + " maxcofdeg=" + string(md) + " check=" + string((Km*Ml)[1,1]-1 == 0));
quit;
"""
    t0 = time.time(); out2 = sing(s2, f"cells/r8b_{tag}.sing", t2); rec["t2"] = round(time.time() - t0)
    q = [l for l in out2.splitlines() if l.startswith("QLIFT")]
    rec["qlift"] = q[0] if q else ("TIMEOUT" if out2 == "TIMEOUT" else "OOM" if "memory" in out2 else "ERR " + out2[-120:])
    if q and "check=1" in q[0]:
        t0 = time.time()
        v = subprocess.run(["bash", "-c", f"PQD={PP},{QQ},{DD} timeout 900 ../venv/bin/python r7/cert_verify.py {sys.argv[1]} r8"], capture_output=True, text=True).stdout
        rec["verify"] = v.strip().splitlines(); rec["t3"] = round(time.time() - t0)
print(json.dumps(rec), flush=True)
