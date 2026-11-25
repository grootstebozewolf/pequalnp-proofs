"""R9 task 1: certificate extraction. (a) delta-debugging (ddmin, complements) for a minimal unit support S of the generators
(P_k x-coefficients + colex minors deg<=3), each membership test = msolve -g 2 mod p (unit iff reduced GB == [1]); a test that
times out/crashes counts as 'not unit' (conservative: we only drop generators when unit is proven mod p).
(b) Singular lift over Q on g_S alone -> r7/cert_<S>_r9.txt; (c) r7/cert_verify.py (sympy exact expansion + independent recomputation).
args: S [test_timeout] ; env PQD, EXTRA/YVAR/TAGX (case-split branch, passed to msolve_bench dump)"""
import sys, os, subprocess, time, json, re
PQD = os.environ.get("PQD", "4,5,7"); S = sys.argv[1]; T = int(sys.argv[2]) if len(sys.argv) > 2 else 30
tag = S.replace(",", "-") + os.environ.get("TAGX", "")
fin = f"r8/ms_{tag}.in"
if not os.path.exists(fin):
    subprocess.run(["bash", "-c", f"PQD={PQD} timeout 300 ../venv/bin/python r8/msolve_bench.py {S} 1"], capture_output=True)
lines = open(fin).read().splitlines(); vars_, char = lines[0], lines[1]
gens = [l.rstrip(",") for l in lines[2:] if l.strip()]
ntest = [0]
def unit(idx, p=char, t=T):
    ntest[0] += 1
    fn = f"r9/t_{tag}.in"; open(fn, "w").write(vars_ + "\n" + p + "\n" + ",\n".join(gens[i] for i in idx) + "\n")
    try:
        subprocess.run(["bash", "-c", f"ulimit -v 4000000; /workspace/msolve-src/inst/bin/msolve -g 2 -t 2 -f {fn} -o {fn}.out"], capture_output=True, timeout=t)
        o = open(fn + ".out").read() if os.path.exists(fn + ".out") else ""
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", fn]); o = ""
    for f in (fn + ".out",):
        if os.path.exists(f): os.remove(f)
    return bool(re.search(r"length of basis:\s+1 element", o)) and bool(re.search(r"\[1\]:\s*$", o))
rec = {"S": S, "tag": tag, "ngens": len(gens)}; t0 = time.time()
def tdeg(g):
    best = 0
    for term in re.split(r"(?<=[^\^*])[+-]", g):
        dsum = 0
        for f in term.split("*"):
            f = f.strip()
            if re.match(r"^[a-z]+\d*_\d+|^yy", f): dsum += int(f.split("^")[1]) if "^" in f else 1
        best = max(best, dsum)
    return best
order = sorted(range(len(gens)), key=lambda i: (tdeg(gens[i]), len(gens[i])))
LOG = open(f"r9/ddlog_{tag}.txt", "w")
lo, hi = 1, len(order)
if not unit(order, t=max(T, 120)):
    rec["res"] = "full set not unit mod p within limit"; print(json.dumps(rec)); sys.exit()
while lo < hi:   # smallest unit prefix of the (degree, length)-sorted generators
    mid = (lo + hi) // 2
    if unit(order[:mid]): hi = mid
    else: lo = mid + 1
    print("prefix", lo, hi, ntest[0], file=LOG, flush=True)
cur = order[:hi]; rec["prefix"] = hi
n = 2
while len(cur) >= 2:
    k = len(cur); size = (k + n - 1) // n; chunks = [cur[i:i + size] for i in range(0, k, size)]; red = False
    for c in chunks:
        comp = [i for i in cur if i not in set(c)]
        if comp and unit(comp):
            cur = comp; n = max(n - 1, 2); red = True; break
    if not red:
        if n >= len(cur): break
        n = min(2 * n, len(cur))
    print('dd', len(cur), n, ntest[0], file=LOG, flush=True)
rec.update(support=len(cur), tests=ntest[0], dd_sec=round(time.time() - t0))
rec["second_prime_unit"] = unit(cur, p="65521", t=120)
sub = [gens[i] for i in cur]
vs = sorted(set(re.findall(r"[a-z]+\d*_\d+|yy", " ".join(sub))))
s2 = f"""ring A = 0,({",".join(vs)}),dp;
ideal K = {",".join(sub)};
matrix Km = matrix(K); matrix Ml = lift(K, ideal(1)); int k;
string cf = "r7/cert_{tag}_r9.txt"; write(":w " + cf, ""); int nz = 0; int md = 0;
for (k = 1; k <= nrows(Ml); k++) {{ if (Ml[k,1] != 0) {{ nz++; if (deg(Ml[k,1]) > md) {{ md = deg(Ml[k,1]); }} write(":a " + cf, string(Km[1,k]) + " ; " + string(Ml[k,1])); }} }}
print("QLIFT gens=" + string(ncols(Km)) + " nonzero=" + string(nz) + " maxcofdeg=" + string(md) + " check=" + string((Km*Ml)[1,1]-1 == 0));
quit;
"""
open(f"r9/q_{tag}.sing", "w").write(s2); t0 = time.time()
try: out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q r9/q_{tag}.sing"], capture_output=True, text=True, timeout=900).stdout
except subprocess.TimeoutExpired: out = "TIMEOUT"
q = [l for l in out.splitlines() if l.startswith("QLIFT")]
rec["qlift"] = q[0] if q else ("TIMEOUT" if out == "TIMEOUT" else "OOM" if "memory" in out else "ERR " + out[-150:]); rec["q_sec"] = round(time.time() - t0)
if q and "check=1" in q[0] and not os.environ.get("TAGX"):
    v = subprocess.run(["bash", "-c", f"PQD={PQD} timeout 1200 ../venv/bin/python r7/cert_verify.py {S} r9"], capture_output=True, text=True).stdout
    rec["verify"] = v.strip().splitlines()
print(json.dumps(rec), flush=True)
