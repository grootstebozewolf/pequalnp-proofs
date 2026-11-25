"""Round 7 generator families, valid for EVERY level space L (cell coordinates a, basis rows B[b]).
FK separator for a block Bk = R×C with |R|+|C| >= q+1: 1_Bk ∉ π_Bk(L) (else F(J - t) = 0 for some t in L), i.e.
  ∃ λ ∈ C^Bk: <λ, π_Bk(row_b)> = 0 for all b, Σ λ = 1.   (new unknowns l<k>_<c>)
Row rank: rank π_i(L) <= q-1 for every matrix row i: all (q)x(q) minors of the d×q restriction vanish (no new vars).
(Row rank follows from the full-row separator; it is the λ-free form.)"""
import itertools, sys
sys.path.insert(0, ".")
import minorsw as MW
from cell_solve import script

def blocks(p, q, kinds):
    out = []
    for a in range(1, p + 1):
        b = q + 1 - a
        if b < 1 or b > q or (a, b) not in kinds: continue
        for R in itertools.combinations(range(p), a):
            for C in itertools.combinations(range(q), b):
                out.append([i * q + j for i in R for j in C])
    return out

def fk_eqs(B, blist, d):
    eqs, lv = [], []
    for k, Bk in enumerate(blist):
        names = {c: f"l{k}_{c}" for c in Bk}; lv += list(names.values())
        for b in range(d):
            terms = [f"{names[c]}*({B[b][c]})" for c in Bk if B[b][c] != "0"]
            if terms: eqs.append("+".join(terms))
        eqs.append("+".join(names.values()) + "-1")
    return eqs, lv

def rowrank_eqs(B, p, q, d):
    eqs = []
    for i in range(p):
        rows = [b for b in range(d) if any(B[b][i * q + j] != "0" for j in range(q))]
        if len(rows) < q: continue
        for sub in itertools.combinations(rows, q):
            e = MW.det_str([[B[b][i * q + j] for j in range(q)] for b in sub])
            if e: eqs.append(e)
    return eqs

def build(p, q, d, S, fr, char, mode="exp", mdeg=3, kinds=(), rowrank=True):
    n = p * q
    H, OM = MW.setup(p, q, mode)
    B = MW.entries(S, fr, n)
    ex = MW.extra(S, fr, p, q, H, OM, mdeg) if mdeg else []
    fe, lv = fk_eqs(B, blocks(p, q, set(kinds)), d) if kinds else ([], [])
    rr = rowrank_eqs(B, p, q, d) if rowrank else []
    s = script(p, q, d, S, fr, char)
    avars = s[s.index("ring A = "):].split("(")[1].split(")")[0]
    if lv:
        allv = avars + "," + ",".join(lv)
        s = s.replace(f",{avars}),dp;", f",{allv}),dp;").replace(f"({avars}),dp;", f"({allv}),dp;")
    s = s.replace("I = simplify(I, 2);", "".join(f"I = I + ({e});\n" for e in ex + fe + rr) + "I = simplify(I, 2);")
    return s, {"minors": len(ex), "fk_eqs": len(fe), "lambda_vars": len(lv), "rowrank": len(rr)}
