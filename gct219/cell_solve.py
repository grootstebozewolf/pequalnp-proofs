"""Exact solve of Schubert cells for 'd-dim L of p x q matrices with P1..Pp = 0' (see schubert.py).
For each non-empty cell with <= U unknowns: Singular script (char C: 0 = over Q, or a prime) builds the cell
basis, maps P_k (k = 2..p), takes all x-coefficients, eliminates P1 linearly, computes std and dim.
unit=1  => the cell contains no level space (over Q: a certificate; lift() would give the cofactors).
Usage: python cell_solve.py p q d U char timeout jobs"""
import itertools, sys, subprocess, os, json, time
from concurrent.futures import ThreadPoolExecutor
from schubert import cells

def P_string(p, q, k):
    terms = []
    for R in itertools.combinations(range(p), k):
        for f in itertools.permutations(range(q), k):
            terms.append("*".join(f"t({R[a]*q+f[a]+1})" for a in range(k)))
    return "+".join(terms)

def script(p, q, d, S, free, char):
    n = p * q
    # unknown a(b,c) for basis row b, free position c; last free position of each row eliminated by P1
    names, entry = [], {}
    for b, (s, fr) in enumerate(zip(S, free)):
        for c in fr[:-1]:
            nm = f"a{b}_{c}"; names.append(nm); entry[(b, c)] = nm
        entry[(b, fr[-1])] = "(-1" + "".join(f"-{entry[(b, c)]}" for c in fr[:-1]) + ")"
    rows = []
    for b, s in enumerate(S):
        comps = ["0"] * n; comps[s] = "1"
        for c in free[b]: comps[c] = entry[(b, c)]
        rows.append(comps)
    tmap = ",".join("+".join(f"({rows[b][c]})*x({b+1})" for b in range(d) if rows[b][c] != "0") or "0" for c in range(n))
    nv = len(names)
    avars = ",".join(names) if names else "dummy"
    Ps = ";\n".join(f"poly P{k} = {P_string(p, q, k)}" for k in range(2, p + 1))
    xs = "*".join(f"x({i+1})" for i in range(d))
    coefs = "\n".join(f"C = coef(f(P{k}), {xs}); for (i = 1; i <= ncols(C); i++) {{ I = I + C[2, i]; }}" for k in range(2, p + 1))
    return f"""ring T = {char},(t(1..{n})),dp;
{Ps};
ring R = {char},(x(1..{d}),{avars}),dp;
map f = T,{tmap};
ideal I; matrix C; int i;
{coefs}
I = simplify(I, 2);
ring A = {char},({avars}),dp;
ideal J = imap(R, I);
int t0 = timer;
option(redSB);
ideal G = std(J);
print("RESULT unknowns={nv} unit=" + string(G[1]==1) + " dim=" + string(dim(G)));
quit;
"""

def run(args):
    p, q, d, S, free, nv, char, tout = args
    fn = f"cells/{p}x{q}_d{d}_" + "-".join(map(str, S)) + ".sing"
    open(fn, "w").write(script(p, q, d, S, free, char))
    t0 = time.time()
    try:
        out = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True, timeout=tout).stdout
        res = [l for l in out.splitlines() if l.startswith("RESULT")]
        r = res[0] if res and "?" not in out else "ERROR " + out[-300:]
    except subprocess.TimeoutExpired:
        r = "TIMEOUT"
    os.remove(fn)
    return {"S": S, "unknowns": nv, "res": r, "sec": round(time.time() - t0, 1)}

if __name__ == "__main__":
    p, q, d, U, char, tout, jobs = map(int, sys.argv[1:8])
    Umin = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    todo = sorted([(p, q, d, S, fr, u, char, tout) for S, fr, u in cells(p, q, d) if Umin <= u <= U], key=lambda a: a[5])
    stats = {"unit": 0, "nonempty": 0, "timeout": 0, "error": 0}
    with ThreadPoolExecutor(jobs) as ex, open(f"cells_{p}x{q}_d{d}_U{Umin}-{U}_c{char}.jsonl", "w") as fh:
        for r in ex.map(run, todo):
            k = "error" if r["res"].startswith("ERROR") else "unit" if "unit=1" in r["res"] else "nonempty" if "unit=0" in r["res"] else "timeout"
            stats[k] += 1; fh.write(json.dumps(r) + "\n"); fh.flush()
    print(json.dumps({"p": p, "q": q, "d": d, "U": U, "char": char, "cells": len(todo), **stats}))
