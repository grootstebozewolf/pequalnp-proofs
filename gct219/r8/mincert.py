"""R8 item 1/2: generator-subset minimisation + Q certificate. Families (colex, no FK-λ, no row rank):
M1,M2,M3 = colex minors of degree 1,2,3; P2..Pp = x-coefficients of P_k. Prefix order M1, P2, M2, P3, M3, P4.
Stage 1 (F_p): report LP reduction (#unknowns left after substituting the std of all linear generators);
  std of growing prefixes until unit; lift(prefix, 1) mod p -> support. Stage 2 (Q): lift 1 into prefix[support];
  write r7/cert_<S>_r8.txt; Stage 3: r7/cert_verify.py (sympy). args: S [tout1] [tout2]; env PQD"""
import sys, os, subprocess, time, json
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G, minorsw as MW
from schubert import cells
PP, QQ, DD = map(int, os.environ.get("PQD", "4,5,7").split(","))
S = tuple(map(int, sys.argv[1].split(","))); tag = sys.argv[1].replace(",", "-")
t1 = int(sys.argv[2]) if len(sys.argv) > 2 else 300; t2 = int(sys.argv[3]) if len(sys.argv) > 3 else 300; BMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 6; MODE = int(os.environ.get('MODE', '1'))
S_, fr, u = next(c for c in cells(PP, QQ, DD) if tuple(c[0]) == S)
H, OM = MW.setup(PP, QQ, "exp")
ex = [MW.extra(S_, fr, PP, QQ, H, OM, m) for m in (1, 2, 3)]
fam = {"M1": ex[0], "M2": ex[1][len(ex[0]):], "M3": ex[2][len(ex[1]):]}
order = ["M1", "P2", "M2", "P3", "M3", "P4"][: 6 if PP >= 4 else 5]
def body(char):
    s, _ = G.build(PP, QQ, DD, S_, fr, char, "exp", 0, [], False)
    pre = s[:s.index("I = simplify(I, 2);")]
    for k in range(2, PP + 1):
        pre = pre.replace(f"C = coef(f(P{k}), ", f"ideal IP{k}; C = coef(f(P{k}), ", 1)
        pre = pre.replace(f"I = I + C[2, i]; }}", f"IP{k} = IP{k} + C[2, i]; }}", 1) if False else pre
    # rewrite the P_k coefficient loops into separate ideals
    lines = []
    for l in pre.splitlines():
        if l.startswith("ideal IP"):
            k = l[len("ideal IP")]; l = l.replace("I = I + C[2, i];", f"IP{k} = IP{k} + C[2, i];")
        lines.append(l)
    pre = "\n".join(lines) + "\n"
    for nm, L in fam.items():
        pre += f"ideal {nm};\n" + "".join(f"{nm} = {nm} + ({e});\n" for e in L)
    pre += s[s.index("ring A = "):s.index("ideal J = imap(R, I);")]
    for nm in list(fam) + [f"IP{k}" for k in range(2, PP + 1)]:
        pre += f"ideal {nm.replace('IP', 'P')} = simplify(imap(R, {nm}), 2);\n"
    return pre
def sing(script, fn, tout):
    open(fn, "w").write(script)
    try: out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
    except subprocess.TimeoutExpired: subprocess.run(["pkill", "-f", fn]); out = "TIMEOUT"
    (os.remove(fn) if not os.environ.get("KEEP") else None); return out
rec = {"S": list(S), "unknowns": u, "pqd": [PP, QQ, DD], "fam": {k: len(v) for k, v in fam.items()}}
LOG = f"r8/log_{tag}.txt"; open(LOG, "w").close()
ALL = os.environ.get("FAMS", "+".join(order))
s1 = body(32003) + f"""int MODE = {MODE}; int i; int k; int j; int B; ideal L; ideal ALL = {ALL}; ALL = simplify(ALL, 2);
string lg = "{LOG}";
for (i = 1; i <= ncols(ALL); i++) {{ if (deg(ALL[i]) <= 1) {{ L = L + ALL[i]; }} }}
ideal Ls = std(L); write(":a " + lg, "LP nlin=" + string(size(simplify(L,2))) + " left=" + string(nvars(basering) - size(Ls)) + " unit=" + string(Ls[1]==1) + " ngens=" + string(ncols(ALL)));
if (MODE == 3) {{ quit; }}
ideal Gt; int found = 0;
for (B = 2; B <= {BMAX}; B++) {{ degBound = B; Gt = std(ALL); degBound = 0; write(":a " + lg, "DEG B=" + string(B) + " unit=" + string(Gt[1]==1) + " t=" + string(timer)); if (Gt[1]==1) {{ found = 1; break; }} }}
if (found == 0 || MODE == 4) {{ quit; }}
int ok;
if (MODE == 2) {{ degBound = B; matrix Tm; ideal Gq = liftstd(ALL, Tm); degBound = 0; ideal Kc; int c0 = 0; for (k = 1; k <= ncols(Gq); k++) {{ if (deg(Gq[k]) == 0 && Gq[k] != 0) {{ c0 = k; break; }} }} write(":a " + lg, "LIFTSTD c0=" + string(c0) + " t=" + string(timer)); if (c0 > 0) {{ for (k = 1; k <= nrows(Tm); k++) {{ if (Tm[k,c0] != 0) {{ Kc = Kc + ALL[k]; }} }} }} Kc = simplify(Kc, 2); write(":a " + lg, "LIFTSUP kept=" + string(ncols(Kc)) + " t=" + string(timer)); }}
else {{ if (MODE == 1 || MODE == 6) {{ if (MODE == 6) {{ degBound = B; }} matrix Ml = lift(ALL, ideal(1)); degBound = 0; ideal Kc; for (k = 1; k <= nrows(Ml); k++) {{ if (Ml[k,1] != 0) {{ Kc = Kc + ALL[k]; }} }} Kc = simplify(Kc, 2); write(":a " + lg, "LIFTSUP kept=" + string(ncols(Kc)) + " t=" + string(timer)); }}
else {{
ideal Kc = ALL; ideal Tr; int n; int bs = ncols(Kc) div 2; int st;
while (bs >= 1) {{
  st = 1;
  while (st <= ncols(Kc)) {{
    n = ncols(Kc); Tr = ideal(0);
    for (i = 1; i <= n; i++) {{ if (i < st || i >= st + bs) {{ Tr = Tr + Kc[i]; }} }}
    Tr = simplify(Tr, 2);
    ok = 0; if (size(Tr) > 0) {{ degBound = B; Gt = std(Tr); degBound = 0; ok = (Gt[1]==1); }}
    if (ok) {{ Kc = Tr; }} else {{ st = st + bs; }}
  }}
  write(":a " + lg, "LEVEL bs=" + string(bs) + " kept=" + string(ncols(Kc)) + " t=" + string(timer));
  if (bs == 1) {{ break; }}
  bs = bs div 2; if (bs > ncols(Kc) div 2) {{ bs = ncols(Kc) div 2; }} if (bs < 1) {{ bs = 1; }}
}}
}}
}}
write(":w r8/K_{tag}.txt", string(Kc));
write(":a " + lg, "DONE kept=" + string(ncols(Kc)));
quit;
"""
t0 = time.time(); out = sing(s1, f"cells/r8m_{tag}.sing", t1); rec["t1"] = round(time.time() - t0)
lg = open(LOG).read().splitlines(); rec["log"] = lg
done = any(l.startswith("DONE") for l in lg)
rec["stage1"] = "ok" if done else ("TIMEOUT" if out == "TIMEOUT" else "OOM" if "memory" in out else "nounit-within-B/ERR " + out[-100:])
if done:
    K = open(f"r8/K_{tag}.txt").read().strip()
    s2 = body(0) + f"""int k; ideal K = {K};
matrix Km = matrix(K); matrix Ml = lift(K, ideal(1));
string cf = "r7/cert_{tag}_r8.txt"; write(":w " + cf, ""); int nz = 0; int md = 0;
for (k = 1; k <= nrows(Ml); k++) {{ if (Ml[k,1] != 0) {{ nz++; if (deg(Ml[k,1]) > md) {{ md = deg(Ml[k,1]); }} write(":a " + cf, string(Km[1,k]) + " ; " + string(Ml[k,1])); }} }}
print("QLIFT gens=" + string(ncols(Km)) + " nonzero=" + string(nz) + " maxcofdeg=" + string(md) + " check=" + string((Km*Ml)[1,1]-1 == 0));
quit;
"""
    t0 = time.time(); out2 = sing(s2, f"cells/r8q_{tag}.sing", t2); rec["t2"] = round(time.time() - t0)
    q = [l for l in out2.splitlines() if l.startswith("QLIFT")]
    rec["qlift"] = q[0] if q else ("TIMEOUT" if out2 == "TIMEOUT" else "OOM" if "memory" in out2 else "ERR " + out2[-150:])
    if q and "check=1" in q[0]:
        v = subprocess.run(["bash", "-c", f"PQD={PP},{QQ},{DD} timeout 900 ../venv/bin/python r7/cert_verify.py {sys.argv[1]} r8"], capture_output=True, text=True).stdout
        rec["verify"] = v.strip().splitlines()
print(json.dumps(rec), flush=True)
