"""Independent (sympy, no Singular) check of a 4x5 d7 cell certificate r7/cert_<S>_<char>.txt:
(i) Σ cof_k * gen_k == 1 by exact expansion over Q; (ii) each gen_k is, up to a nonzero rational, one of the hypotheses,
recomputed from scratch here: an x-coefficient of P_k(Σ_b x_b row_b) (k=1..4, P_k = sum over k-matchings), a row-rank 5x5 minor of a row
restriction, or a colex minor p_K (min_h ω(hK) < ω(I), |K\\I|<=3)."""
import sys, itertools, sympy as sp, numpy as np
import os; p, q, d = map(int, os.environ.get("PQD", "4,5,7").split(",")); n = p * q
S = tuple(map(int, sys.argv[1].split(","))); char = sys.argv[2] if len(sys.argv) > 2 else "0"
sys.path.insert(0, ".")
from schubert import cells
S_, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == S)
A = {}
B = sp.zeros(d, n)
for b, s in enumerate(S):
    B[b, s] = 1
    for c in fr[b][:-1]: A[f"a{b}_{c}"] = sp.Symbol(f"a{b}_{c}"); B[b, c] = A[f"a{b}_{c}"]
    B[b, fr[b][-1]] = -1 - sum(A[f"a{b}_{c}"] for c in fr[b][:-1])
loc = dict(A)
lines = [l for l in open(f"r7/cert_{'-'.join(map(str, S))}_{char}.txt").read().splitlines() if ";" in l]
gens = [sp.sympify(l.split(";")[0].replace("^", "**"), locals=loc) for l in lines]
cofs = [sp.sympify(l.split(";")[1].replace("^", "**"), locals=loc) for l in lines]
tot = sp.expand(sum(g * c for g, c in zip(gens, cofs)))
print("identity Σ cof·gen = 1:", tot == 1, "| gens", len(gens), "| cofactor terms", sum(len(sp.Add.make_args(sp.expand(c))) for c in cofs))
X = sp.symbols(f"x1:{d+1}"); t = [sum(X[b] * B[b, c] for b in range(d)) for c in range(n)]
gs = sp.symbols(f"a0:{len(gens)}")
def norm(e):
    e = sp.Poly(sp.expand(e), *A.values()); return None if e.is_zero else (e.monic().as_expr())
want = {norm(g): k for k, g in enumerate(gens)}; found = {}
def hit(e, label):
    ne = norm(e)
    if ne is not None and ne in want and want[ne] not in found: found[want[ne]] = label
# row rank
for i in range(p):
    for sub in itertools.combinations(range(d), q):
        hit(sp.Matrix([[B[b, i * q + j] for j in range(q)] for b in sub]).det(), f"rowrank{i}")
# P_k coefficients
for k in range(1, p + 1):
    if len(found) == len(gens): break
    Pk = 0
    for R in itertools.combinations(range(p), k):
        for C in itertools.permutations(range(q), k):
            Pk += sp.prod([t[R[r] * q + C[r]] for r in range(k)])
    for mon, co in sp.Poly(sp.expand(Pk), *X).terms(): hit(co, f"P{k}")
# colex minors (independent criterion code)
if len(found) < len(gens):
    H = [[rp[c // q] * q + cp[c % q] for c in range(n)] for rp in itertools.permutations(range(p)) for cp in itertools.permutations(range(q))]
    wI = sum(2 ** s for s in S); nonS = [c for c in range(n) if c not in S]
    for m in range(1, 4):
        if m > d: break
        for drop in itertools.combinations(range(d), m):
            keep = [s for b, s in enumerate(S) if b not in drop]
            for add in itertools.combinations(nonS, m):
                K = keep + list(add)
                if min(sum(2 ** h[c] for c in K) for h in H) < wI:
                    hit(sp.Matrix([[B[b, c] for c in add] for b in drop]).det(), f"colexminor{m}")
import collections
print("gens identified:", len(found), "/", len(gens), dict(collections.Counter(found.values())), "unidentified:", [k for k in range(len(gens)) if k not in found])
