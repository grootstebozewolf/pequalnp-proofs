"""Kernel of A_K at the rational rank-drop points (zero-dim cells with rational points), as 3x5 matrices mod K;
plus row-intersection dims dim(K ∩ R°_i) (R°_i = sum-zero vectors supported on row i)."""
import sys, json, sympy as sp
sys.path.insert(0, "r10")
from ak import A_of, fvec, Bf, Cf
pts = {(4,9,10,11): {"a0_8": 0, "a0_7": -sp.Rational(1,4), "a0_6": -sp.Rational(1,4), "a0_5": -sp.Rational(1,4)},
       (5,8,10,11): {"a1_9": -sp.Rational(1,4), "a0_9": 0, "a0_7": -sp.Rational(1,3), "a0_6": -sp.Rational(1,3)},
       (6,8,9,11): {"a2_10": -sp.Rational(1,3), "a1_10": -sp.Rational(1,3), "a0_10": 0, "a0_7": -sp.Rational(1,2)},
       (7,8,9,10): {"a3_11": -sp.Rational(1,2), "a2_11": -sp.Rational(1,2), "a1_11": -sp.Rational(1,2), "a0_11": 0},
       (8,9,10,11): {}}
out = {}
for S, so in pts.items():
    rows = []
    for b, s in enumerate(S):
        v = [0] * 15
        for x in range(15): v[x] += fvec(s)[x]
        for c in range(s + 1, 12):
            if c not in S:
                coef = so.get(f"a{b}_{c}", 0)
                for x in range(15): v[x] += coef * fvec(c)[x]
        rows.append(v)
    comp = [c for c in range(12) if c not in S]
    A, (r1, r2) = A_of(rows, comp)
    ker = A.nullspace()
    Km = sp.Matrix(rows)
    rowdims = [sp.Matrix([[r[i*5+j] for j in range(5)] for r in rows]).rank() for i in range(3)]  # rank of K's projection to row i
    kers = []
    for z in ker:
        v = sp.zeros(1, 15)
        for n, c in enumerate(comp): v += z[n] * sp.Matrix([fvec(c)])
        kers.append(v.reshape(3, 5).tolist())
    out[str(S)] = {"K": [sp.Matrix([r]).reshape(3,5).tolist() for r in rows], "rankA": A.rank(), "rank_proj_rows": rowdims, "kernel": kers}
    print(S, "rankA", A.rank(), "proj-row ranks", rowdims)
    for r in rows: print("  K", sp.Matrix([r]).reshape(3, 5).tolist())
    for k in kers: print("  ker", k)
json.dump(out, open("r10/kernel.json", "w"), default=str)
