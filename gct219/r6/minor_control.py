"""Item 2: end-to-end positive control of the minor-hypothesis pipeline. Witness W = row0 sum-zero + column0 (below row 0)
sum-zero, dim p+q-3. Canonical representative g*W (lex-least RREF pivot set over G). Build the cell script WITH the
degree<=2 minors (minors.py), (A) substitute ALL coordinates = witness values: every generator must vanish;
(B) keep K coordinates free, substitute the rest: std must NOT be unit (witness is a solution)."""
import sys, subprocess
p, q, d, K = map(int, sys.argv[1:5]); TYPE = sys.argv[5] if len(sys.argv) > 5 else "row"
sys.argv = ["x", str(p), str(q), str(d)]
sys.path.insert(0, ".")
import sympy as sp
import minors as M
from schubert import cells
from cell_solve import script
n = p * q
E = lambda i, j: [1 if c == i * q + j else 0 for c in range(n)]
vs = [[x - y for x, y in zip(E(0, 0), E(0, j))] for j in range(1, q)] + [[x - y for x, y in zip(E(1, 0), E(i, 0))] for i in range(2, p)]
if TYPE == "col":
    vs = [[x - y for x, y in zip(E(0, 0), E(i, 0))] for i in range(1, p)] + [[x - y for x, y in zip(E(0, 1), E(0, j))] for j in range(2, q)]
W = sp.Matrix(vs); assert W.rank() == d == p + q - 3
best = None
for h in M.perms:
    Wh = sp.zeros(d, n)
    for c in range(n): Wh[:, h[c]] = W[:, c]
    R, piv = Wh.rref()
    if best is None or tuple(piv) < best[0]: best = (tuple(piv), R)
I, R = best
S, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == I)
ex = M.extra_polys(S, fr)
vals = [(f"a{b}_{c}", R[b, c]) for b in range(d) for c in fr[b][:-1]]
s = script(p, q, d, S, fr, 0).replace("I = simplify(I, 2);", "".join(f"I = I + ({e});\n" for e in ex) + "I = simplify(I, 2);")
pre = s[:s.index("int t0 = timer;")]
subA = "".join(f"JA = subst(JA, {v}, {sp.sstr(x)});\n" for v, x in vals)
subB = "".join(f"JB = subst(JB, {v}, {sp.sstr(x)});\n" for v, x in vals[K:])
tail = f"""ideal JA = J; {subA} print("A_allzero=" + string(size(simplify(JA,2)) == 0));
ideal JB = J; {subB} option(redSB); ideal G = std(JB); print("B_unit=" + string(G[1]==1) + " dim=" + string(dim(G)) + " free={K}");
quit;"""
open(f"r6/mc_{p}{q}{d}.sing", "w").write(pre + tail)
out = subprocess.run(["Singular", "-q", f"r6/mc_{p}{q}{d}.sing"], capture_output=True, text=True, timeout=900).stdout
print(f"{p}x{q} d{d} {TYPE}: canonical cell {I}, unknowns {u}, minors {len(ex)}:", " | ".join(l for l in out.splitlines() if "=" in l)[-300:])
