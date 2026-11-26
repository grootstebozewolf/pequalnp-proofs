# Degree-bounded certificate: find c_i with sum c_i g_i = 1 and deg(c_i g_i) <= D, as a sparse
# linear system (Macaulay matrix) in the coefficients of the c_i. Solved mod several primes with a
# fixed pivot order (canonical solution: free unknowns 0), lifted by CRT and rational reconstruction,
# and verified exactly over Q with python-flint.
import sys, json, itertools, time
from fractions import Fraction
import flint
tag = sys.argv[1]; D = int(sys.argv[2])
idx = json.loads(open(f'lift_{tag}.log').readline())['original_indices']
L = open(f'cells/{tag}_0.txt').read().split('\n'); vs = L[0].split(','); G = [g for g in L[1:] if g.strip()]
n = len(vs)
R = flint.fmpq_mpoly_ctx.get(vs, 'degrevlex') if hasattr(flint, 'fmpq_mpoly_ctx') else None
def parse(s):
    return R.from_dict({}) if False else R.gens()  # placeholder, replaced below
gens_ = R.gens(); loc = {v: gens_[k] for k, v in enumerate(vs)}
def to_poly(s):
    return eval(s.replace('^', '**'), {}, loc)
polys = [to_poly(G[k]) for k in idx]
def monos(deg):
    out = []
    for d in range(deg + 1):
        for c in itertools.combinations_with_replacement(range(n), d):
            e = [0] * n
            for v in c: e[v] += 1
            out.append(tuple(e))
    return out
cols = []  # (generator position, multiplier exponent)
for i, g in enumerate(polys):
    dg = g.total_degree() if hasattr(g, 'total_degree') else max(sum(e) for e in g.to_dict())
    for m in monos(D - dg):
        cols.append((i, m))
gd = [{tuple(e): c for e, c in g.to_dict().items()} for g in polys]
# column j as {row monomial: rational coefficient}
rowid = {}; colent = []
for (i, m) in cols:
    ent = {}
    for e, c in gd[i].items():
        mm = tuple(a + b for a, b in zip(e, m))
        r = rowid.setdefault(mm, len(rowid)); ent[r] = Fraction(int(c.p), int(c.q))
    colent.append(ent)
one = rowid.get(tuple([0] * n))
print(json.dumps({'D': D, 'unknowns': len(cols), 'equations': len(rowid), 'has_const_row': one is not None}), flush=True)
if one is None: raise SystemExit('no constant term reachable')
def solve_mod(p):
    # equations as dict rows: row -> {col: val mod p}, rhs
    rows = [dict() for _ in range(len(rowid))]
    for j, ent in enumerate(colent):
        for r, c in ent.items():
            v = c.numerator * pow(c.denominator, -1, p) % p
            if v: rows[r][j] = v
    rhs = [0] * len(rowid); rhs[one] = 1
    colrows = {}
    for r, row in enumerate(rows):
        for j in row: colrows.setdefault(j, set()).add(r)
    piv = {}  # col -> row
    used = set()
    for j in range(len(cols)):
        cand = [r for r in colrows.get(j, ()) if r not in used and rows[r].get(j)]
        if not cand: continue
        r = min(cand, key=lambda x: (len(rows[x]), x)) if False else min(cand)
        used.add(r); piv[j] = r
        inv = pow(rows[r][j], -1, p)
        for k in list(rows[r]): rows[r][k] = rows[r][k] * inv % p
        rhs[r] = rhs[r] * inv % p
        for r2 in list(colrows[j]):
            if r2 == r or r2 in used: continue
            f = rows[r2].get(j)
            if not f: continue
            for k, v in rows[r].items():
                nv = (rows[r2].get(k, 0) - f * v) % p
                if nv: 
                    if k not in rows[r2]: colrows.setdefault(k, set()).add(r2)
                    rows[r2][k] = nv
                else:
                    rows[r2].pop(k, None)
            rhs[r2] = (rhs[r2] - f * rhs[r]) % p
    for r in range(len(rows)):
        if r not in used and rhs[r]: return None  # inconsistent
    x = {}
    for j in sorted(piv, reverse=True):
        r = piv[j]; s = rhs[r]
        for k, v in rows[r].items():
            if k != j: s = (s - v * x.get(k, 0)) % p
        if s: x[j] = s
    return x
def ratrec(a, m):
    a %= m
    r0, r1, s0, s1 = m, a, 0, 1
    import math
    B = math.isqrt(m // 2)
    while r1 > B:
        qq = r0 // r1; r0, r1 = r1, r0 - qq * r1; s0, s1 = s1, s0 - qq * s1
    if s1 == 0 or abs(s1) > B: return None
    return Fraction(r1, s1)
primes = [1000000007, 1000000009, 998244353, 1000000021, 1000000033, 1000000087, 1000000093, 1000000097]
mod = 1; acc = {}; t0 = time.time()
for p in primes:
    x = solve_mod(p)
    if x is None: raise SystemExit(f'no solution of degree <= {D} mod {p}')
    keys = set(acc) | set(x)
    acc = {j: (int(flint.fmpz.__new__(flint.fmpz)) if False else 0) for j in []} if False else {j: ( (acc.get(j, 0) + mod * (((x.get(j, 0) - acc.get(j, 0)) * pow(mod, -1, p)) % p)) ) for j in keys}
    mod *= p
    sol = {j: ratrec(v, mod) for j, v in acc.items()}
    if all(v is not None for v in sol.values()):
        # exact check over Q
        C = [R.from_dict({}) for _ in polys]
        cdict = [dict() for _ in polys]
        for j, v in sol.items():
            if v == 0: continue
            i, m = cols[j]; cdict[i][m] = cdict[i].get(m, 0) + v
        tot = R.from_dict({})
        for i in range(len(polys)):
            if cdict[i]:
                ci = R.from_dict({m: flint.fmpq(v.numerator, v.denominator) for m, v in cdict[i].items()})
                tot += ci * polys[i]
        ok = tot == R.from_dict({tuple([0] * n): 1})
        print(json.dumps({'primes': primes.index(p) + 1, 'nonzero_coeffs': sum(1 for v in sol.values() if v), 'identity_1': ok, 'sec': round(time.time() - t0, 1),
                          'max_height_bits': max((max(abs(v.numerator), v.denominator).bit_length() for v in sol.values() if v), default=0)}), flush=True)
        if ok:
            json.dump({'tag': tag, 'D': D, 'gens_q_indices': idx, 'cofactors': {str(i): {','.join(map(str, m)): str(v) for m, v in cdict[i].items()} for i in range(len(polys)) if cdict[i]}},
                      open(f'cert_{tag}_D{D}.json', 'w'))
            break
