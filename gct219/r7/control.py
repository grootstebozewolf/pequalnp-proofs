"""Item 1 positive control: witness canonical cell (colex), all R7 generators: (A) minors + rowrank vanish at the witness;
(B) a λ exists for every FK block (linear solve at the witness); (C) Singular with K cell coords free (λ free) is NOT unit."""
import sys, subprocess
p, q, d, K = map(int, sys.argv[1:5]); TYPE = sys.argv[5]; KINDS = eval(sys.argv[6])
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import sympy as sp, numpy as np
import minorsw as MW, gens as G
from schubert import cells
n = p * q; H, OM = MW.setup(p, q, "exp")
E = lambda i, j: [1 if c == i * q + j else 0 for c in range(n)]
if TYPE == "row": vs = [[x - y for x, y in zip(E(0, 0), E(0, j))] for j in range(1, q)] + [[x - y for x, y in zip(E(1, 0), E(i, 0))] for i in range(2, p)]
else: vs = [[x - y for x, y in zip(E(0, 0), E(i, 0))] for i in range(1, p)] + [[x - y for x, y in zip(E(0, 1), E(0, j))] for j in range(2, q)]
W = sp.Matrix(vs); best = None
for h in H:
    Wh = sp.zeros(d, n)
    for c in range(n): Wh[:, int(h[c])] = W[:, c]
    R, piv = Wh.rref(); w = int(OM[list(piv)].sum())
    if best is None or w < best[0]: best = (w, tuple(piv), R)
w, I, R = best
S, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == I)
B = MW.entries(S, fr, n)
vals = {sp.Symbol(f"a{b}_{c}"): R[b, c] for b in range(d) for c in fr[b][:-1]}
loc = {str(k): k for k in vals}
ev = lambda e: sp.expand(sp.sympify(e.replace("^", "**"), locals=loc).subs(vals))
rr = G.rowrank_eqs(B, p, q, d); badrr = sum(1 for e in rr if ev(e) != 0)
# λ existence per block: 1_B not in rowspace of R restricted to B
bl = G.blocks(p, q, set(KINDS)); nolam = 0
for Bk in bl:
    M = R[:, Bk]; one = sp.Matrix([[1] * len(Bk)])
    if sp.Matrix.vstack(M, one).rank() == M.rank(): nolam += 1
import os; MDEG = int(os.environ.get("MDEG", "3")); s, info = G.build(p, q, d, S, fr, 0, "exp", MDEG, KINDS, os.environ.get("RR", "1") == "1")
vl = [(str(k), v) for k, v in vals.items()][K:]
pre = s[:s.index("int t0 = timer;")]
sub = "".join(f"J = subst(J, {v}, {sp.sstr(x)});\n" for v, x in vl)
open(f"r7/ctl_{p}{q}{d}.sing", "w").write(pre + sub + 'option(redSB); ideal GG = std(J); print("B_unit=" + string(GG[1]==1) + " dim=" + string(dim(GG)));\nquit;\n')
out = subprocess.run(["Singular", "-q", f"r7/ctl_{p}{q}{d}.sing"], capture_output=True, text=True, timeout=900).stdout
err = "?" in out
print(f"{p}x{q} d{d} {TYPE}: canonical {I} unknowns {u} {info}; rowrank violated {badrr}/{len(rr)}; blocks {len(bl)} with NO λ: {nolam};",
      [l for l in out.splitlines() if l.startswith("B_unit")], "SINGULAR-ERROR" if err else "", flush=True)
