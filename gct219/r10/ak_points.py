"""Rank of A_K at the exact points of the 18 zero-dimensional 𝒦 cells (over ℚ / algebraic numbers, sympy).
Each isolated point is a component of 𝒦, so the rank there is its generic rank."""
import json, sys, signal, sympy as sp
sys.path.insert(0, "r10")
from ak import A_of, fvec
res = []
for l in open("r10/kzero_Q.jsonl"):
    r = json.loads(l); S = r["S"]; gb = r["res"].split("GB=")[1]
    syms = {}
    rows = []
    for b, s in enumerate(S):
        row = {s: sp.Integer(1)}
        for c in range(s + 1, 12):
            if c not in S: nm = f"a{b}_{c}"; syms[nm] = sp.Symbol(nm); row[c] = syms[nm]
        rows.append(row)
    eqs = [sp.sympify(g.replace("^", "**"), locals=syms) for g in gb.split(",")]
    signal.alarm(120)
    try:
        sols = sp.solve(eqs, list(syms.values()), dict=True)
    except Exception as e:
        res.append({"S": S, "err": str(e)[:60]}); continue
    finally:
        signal.alarm(0)
    comp = [c for c in range(12) if c not in S]
    ranks = []
    for so in sols:
        K = [[sum(sp.nsimplify(row[c].subs(so)) * fvec(c)[x] for c in row) for x in range(15)] for row in rows]
        A, (r1, r2) = A_of(K, comp)
        A = A.applyfunc(sp.simplify); r1 = r1.applyfunc(sp.simplify); r2 = r2.applyfunc(sp.simplify)
        ranks.append((A.rank(simplify=True), A.row_join(r1).rank(simplify=True), A.row_join(r2).rank(simplify=True)))
    out = {"S": S, "vdim": r["res"].split("vdim=")[1].split()[0], "nsol": len(sols), "ranks(A,[A|r1],[A|r2])": ranks}
    res.append(out); print(json.dumps(out), flush=True)
json.dump(res, open("r10/ak_points.json", "w"))
