# Positive control for constant-pivot substitution: the witness's canonical colex cell; after substitution
# over Q, every reduced generator must vanish at the witness values of the surviving unknowns.
import sys, subprocess
p, q, d = map(int, sys.argv[1:4]); TYPE = sys.argv[4]
sys.path.insert(0, '/home/user/gct219-rounds/gct219'); sys.path.insert(0, '.')
import sympy as sp
import minorsw as MW
from schubert import cells
from mkcell import cell_script
n = p * q; H, OM = MW.setup(p, q, "exp")
E = lambda i, j: [1 if c == i * q + j else 0 for c in range(n)]
if TYPE == "row": vs = [[x - y for x, y in zip(E(0, 0), E(0, j))] for j in range(1, q)] + [[x - y for x, y in zip(E(1, 0), E(i, 0))] for i in range(2, p)]
else: vs = [[x - y for x, y in zip(E(0, 0), E(i, 0))] for i in range(1, p)] + [[x - y for x, y in zip(E(0, 1), E(0, j))] for j in range(2, q)]
vs = vs[:d]
W = sp.Matrix(vs); best = None
for h in H:
    Wh = sp.zeros(d, n)
    for c in range(n): Wh[:, int(h[c])] = W[:, c]
    R, piv = Wh.rref(); w = int(OM[list(piv)].sum())
    if best is None or w < best[0]: best = (w, tuple(piv), R)
w, I, R = best
S, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == I)
vals = {f"a{b}_{c}": R[b, c] for b in range(d) for c in fr[b][:-1]}
tag = f"{p}x{q}d{d}{TYPE}"
tail = open('clp_tail.sing').read().replace('OUTFILE', f'ctl_{tag}.txt')
s, _, ne = cell_script(p, q, d, I, 0, 3, tail); open(f'ctl_{tag}.sing', 'w').write(s)
out = subprocess.run(['Singular', '-q', f'ctl_{tag}.sing'], capture_output=True, text=True, timeout=1200).stdout
res = [l for l in out.splitlines() if 'RESULT' in l]
L = open(f'ctl_{tag}.txt').read().split('\n'); surv = L[0].split(','); polys = [x for x in L[1:] if x.strip()]
loc = {v: sp.Symbol(v) for v in surv}
bad = 0
for P in polys:
    e = sp.sympify(P.replace('^', '**'), locals=loc).subs({loc[v]: vals[v] for v in surv})
    if sp.nsimplify(e) != 0: bad += 1
print(f"{tag}: canonical cell {I}, unknowns {u}, minors {ne}; {res}; reduced generators nonzero at witness: {bad}/{len(polys)}", flush=True)
