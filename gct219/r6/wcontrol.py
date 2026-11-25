"""Positive control under the WEIGHT criterion: canonical rep (g, I) of a witness = joint omega-weight minimum over G of
the RREF pivot set (= the min-weight chart). Check all minors (deg<=DEG) vanish at the witness and Singular with minors
and K free coordinates is not unit."""
import sys, subprocess
sys.path.insert(0, ".")
import sympy as sp, numpy as np
import minorsw as MW
from schubert import cells
from cell_solve import script
p, q, d, K, DEG = map(int, sys.argv[1:6]); TYPE = sys.argv[6]; mode = "exp"
n = p * q; H, OM = MW.setup(p, q, mode)
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
ex = MW.extra(S, fr, p, q, H, OM, DEG)
vals = {sp.Symbol(f"a{b}_{c}"): R[b, c] for b in range(d) for c in fr[b][:-1]}
loc = {str(k): k for k in vals}
bad = sum(1 for e in ex if sp.expand(sp.sympify(e.replace("^", "**"), locals=loc).subs(vals)) != 0)
vl = [(str(k), v) for k, v in vals.items()]
s = script(p, q, d, S, fr, 0).replace("I = simplify(I, 2);", "".join(f"I = I + ({e});\n" for e in ex) + "I = simplify(I, 2);")
pre = s[:s.index("int t0 = timer;")]
subA = "".join(f"JA = subst(JA, {v}, {sp.sstr(x)});\n" for v, x in vl)
subB = "".join(f"JB = subst(JB, {v}, {sp.sstr(x)});\n" for v, x in vl[K:])
tail = f"""ideal JA = J; {subA} print("A_allzero=" + string(size(simplify(JA,2)) == 0));
ideal JB = J; {subB} option(redSB); ideal G = std(JB); print("B_unit=" + string(G[1]==1) + " dim=" + string(dim(G)) + " free={K}");
quit;"""
open(f"r6/wc_{p}{q}{d}.sing", "w").write(pre + tail)
out = subprocess.run(["Singular", "-q", f"r6/wc_{p}{q}{d}.sing"], capture_output=True, text=True, timeout=900).stdout
print(f"[{mode}] {p}x{q} d{d} {TYPE}: canonical I={I} (unknowns {u}), minors deg<={DEG}: {len(ex)}, violated at witness: {bad};",
      " | ".join(l for l in out.splitlines() if "=" in l)[-200:])
