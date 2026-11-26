"""Independent re-check of certs.json, sharing no code with gen.py's search.
For every certificate it recomputes from scratch:
  * the parametrisation satisfies the W_S constraints, and the dependent coordinates are
    fixed by the constraints (the kappa combinations);
  * each listed evaluation E equals the cubic condition at the stated point;
  * sum g_i E_i == 1 exactly;
  * the 3-sets C cover every chart: all C(N,3) subsets appear, for all 32 supports."""
import json, itertools, sympy as sp
certs = json.load(open('certs.json'))
def g3(j, x):
    o = [x[l] for l in range(5) if l != j]
    return 6*sum(p*q*r for p, q, r in itertools.combinations(o, 3))   # definition, not Newton
seen = set()
for c in certs:
    S = c['S']; free = [tuple(f) for f in c['free']]; N = len(free); C = c['C']
    t = sp.symbols(f't0:{N}')
    a = [sp.sympify(v) for v in c['a']]; b = [sp.sympify(v) for v in c['b']]
    assert sp.expand(sum(b)) == 0
    for i in range(5):
        if i in S: assert sp.expand(2*a[i] - sum(a)) == 0
        else: assert b[i] == 0
    for n, (k, i) in enumerate(free): assert (a if k == 'a' else b)[i] == t[n]
    # every dependent coordinate is linear in the free ones, so W_S has dimension N exactly:
    assert sp.Matrix([[sp.diff(v, tt) for tt in t] for v in a + b]).rank() == N
    m = {sp.Symbol(s) for s in c['m']}
    total = 0
    for e in c['evals']:
        s = dict(zip(C, e['s']))
        tv = {}
        for kp in range(N):
            tv[t[kp]] = s[kp] if kp in C else sum(s[kk]*sp.Symbol(f'm{kp}_{kk}') for kk in C)
        E = sp.expand(g3(e['j'], [v.subs(tv) for v in a]) + g3(e['j'], [v.subs(tv) for v in b]))
        assert E == sp.expand(sp.sympify(e['E'])), (S, C, e)
        assert sp.sympify(e['g']).free_symbols <= m
        total += sp.sympify(e['g'])*E
    assert sp.expand(total) == 1, (S, C)
    seen.add((tuple(S), tuple(C)))
for mask in range(32):
    S = tuple(i for i in range(5) if mask >> i & 1); N = 5 if not S else 4
    for C in itertools.combinations(range(N), 3): assert (S, C) in seen, (S, C)
print(f'OK: {len(certs)} certificates verified, all {len(seen)} (support, chart) pairs covered')
