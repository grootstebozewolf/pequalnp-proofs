import sys, itertools
p, q, d = map(int, sys.argv[1:4]); sys.argv = ["x", str(p), str(q), str(d)]
sys.path.insert(0, ".")
import sympy as sp, minors as M
from schubert import cells
n = p * q
E = lambda i, j: [1 if c == i * q + j else 0 for c in range(n)]
for TYPE in ("row", "col"):
    if TYPE == "row": vs = [[x - y for x, y in zip(E(0, 0), E(0, j))] for j in range(1, q)] + [[x - y for x, y in zip(E(1, 0), E(i, 0))] for i in range(2, p)]
    else: vs = [[x - y for x, y in zip(E(0, 0), E(i, 0))] for i in range(1, p)] + [[x - y for x, y in zip(E(0, 1), E(0, j))] for j in range(2, q)]
    W = sp.Matrix(vs); best = None
    for h in M.perms:
        Wh = sp.zeros(d, n)
        for c in range(n): Wh[:, h[c]] = W[:, c]
        R, piv = Wh.rref()
        if best is None or tuple(piv) < best[0]: best = (tuple(piv), R)
    I, R = best
    S, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == I)
    B = M.entries(S, fr); Sset = set(S); nonS = [c for c in range(n) if c not in Sset]
    vals = {sp.Symbol(f"a{b}_{c}"): R[b, c] for b in range(d) for c in fr[b][:-1]}
    loc = {str(k): k for k in vals}
    cnt = bad = 0
    for drop in itertools.combinations(range(d), 3):
        for add in itertools.combinations(nonS, 3):
            K = sorted((Sset - {S[b] for b in drop}) | set(add))
            if M.orbit_min(K) < I:
                m = sp.Matrix([[sp.sympify(B[b][c], locals=loc) for c in add] for b in drop]).subs(vals)
                cnt += 1; bad += (m.det() != 0)
    print(p, q, d, TYPE, "canonical", I, "deg-3 minors required", cnt, "violated", bad, flush=True)
