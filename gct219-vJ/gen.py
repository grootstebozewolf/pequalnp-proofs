"""Certificate generator for the finite core of case vJ of L-gct-219.

Finite object.  In the branch `sum b = 0` of xO2 (see README.md), every support
S (a subset of {0..4}: i in S means 2 a_i = sum a, i not in S means b_i = 0) gives a
linear space W_S of coordinate vectors (a, b) in C^10, parametrised by N free
coordinates t (N = 4 for S nonempty, N = 5 for S empty).  A 3-dimensional P inside
W_S has a chart: a 3-set C of the free coordinates on which P projects onto C^3.
Taking y_k in P with t_{k'}(y_k) = [k = k'] for k, k' in C, the other free coordinates
of y_k are unknowns m.  Each evaluation point s in C^3 gives x = sum s_k y_k in P, and
the cubic condition at x gives a polynomial E(m) = 0.  The certificate for (S, C) is a
list of evaluations and rational cofactors g with sum g_i E_i = 1.

The search uses linear algebra over QQ (python-flint).  It is only a search: every
certificate is re-verified exactly by `check.py` (sympy) and, in the end, by Lean.
"""
import itertools, json, sys
import sympy as sp
import flint

def g3(j, x):
    s1 = sum(x) - x[j]
    s2 = sum(v**2 for v in x) - x[j]**2
    s3 = sum(v**3 for v in x) - x[j]**3
    return s1**3 - 3*s1*s2 + 2*s3          # = 6 * e3 of the four coordinates other than j

def param(S):
    """Free coordinates and the vectors a(t), b(t) of W_S (sympy, linear in t)."""
    S = sorted(S); k = len(S); outs = [i for i in range(5) if i not in S]
    if k == 0:
        t = sp.symbols('t0:5')
        return [('a', i) for i in range(5)], list(t), [0]*5, t
    free = [('b', i) for i in S[:-1]]
    if k != 2:
        free += [('a', o) for o in outs]
    else:
        free += [('a', S[0]), ('a', outs[0]), ('a', outs[1])]
    t = sp.symbols(f't0:{len(free)}')
    val = {f: t[n] for n, f in enumerate(free)}
    b = [val.get(('b', i), 0) for i in range(5)]
    b[S[-1]] = -sum(b[i] for i in S[:-1])
    a = [val.get(('a', i), None) for i in range(5)]
    if k != 2:
        for i in S:
            a[i] = sp.Rational(1, 2 - k) * sum(a[o] for o in outs) if outs else 0
    else:
        a[S[1]] = a[S[0]]
        a[outs[2]] = -a[outs[0]] - a[outs[1]]
    # sanity: the constraints hold
    assert sp.expand(sum(b)) == 0
    for i in range(5):
        if i in S: assert sp.expand(2*a[i] - sum(a)) == 0
        else: assert b[i] == 0
    return free, a, b, t

def constraints(S):
    """The linear constraints, as sympy expressions in symbols A0..A4, B0..B4 (each = 0)."""
    A = sp.symbols('A0:5'); B = sp.symbols('B0:5')
    cs = [('hb', sum(B))]
    for i in range(5):
        cs.append((f'h{i}', 2*A[i] - sum(A)) if i in S else (f'h{i}', B[i]))
    return A, B, cs

def kappa(S, free, a, b, t):
    """For every dependent coordinate: coefficients of the constraints proving its value."""
    A, B, cs = constraints(S)
    coord = {('a', i): A[i] for i in range(5)}; coord.update({('b', i): B[i] for i in range(5)})
    back = {t[n]: coord[f] for n, f in enumerate(free)}
    out = {}
    for kind, vec in (('a', a), ('b', b)):
        for i in range(5):
            if (kind, i) in free: continue
            target = sp.expand(coord[(kind, i)] - sp.sympify(vec[i]).subs(back))
            ks = sp.symbols(f'k0:{len(cs)}')
            comb = sp.expand(sum(kk*c for kk, (_, c) in zip(ks, cs)) - target)
            eqs = sp.Poly(comb, *(list(A) + list(B))).coeffs()
            sol = sp.solve(eqs, ks, dict=True)[0]
            out[(kind, i)] = {name: str(sol.get(kk, 0)) for kk, (name, _) in zip(ks, cs) if sol.get(kk, 0) != 0}
    return out

def grid(n=3, d=3):
    pts = [p for p in itertools.product(range(d + 1), repeat=n) if 0 < sum(p) <= d]
    return sorted(pts, key=lambda p: (sum(p), [-v for v in p]))

def chart_evals(S, C):
    free, a, b, t = param(S); N = len(free)
    nonpiv = [k for k in range(N) if k not in C]
    m = {(kp, kk): sp.Symbol(f'm{kp}_{kk}') for kp in nonpiv for kk in C}
    mv = [m[(kp, kk)] for kp in nonpiv for kk in C]
    evals = []
    for s in grid():
        sv = dict(zip(C, s))
        tv = {}
        for kp in range(N):
            tv[t[kp]] = sv[kp] if kp in C else sum(sv[kk]*m[(kp, kk)] for kk in C)
        av = [sp.sympify(v).subs(tv) for v in a]; bv = [sp.sympify(v).subs(tv) for v in b]
        for j in range(5):
            e = sp.expand(g3(j, av) + g3(j, bv))
            if e != 0: evals.append((s, j, e))
    return free, mv, evals

def monos(nv, d):
    out = []
    for tot in range(d + 1):
        for c in itertools.combinations_with_replacement(range(nv), tot):
            e = [0]*nv
            for i in c: e[i] += 1
            out.append(tuple(e))
    return out

def find_cofactors(mv, evals, dmax=10):
    nv = len(mv)
    polys = [sp.Poly(e, *mv) for (_, _, e) in evals]
    # dedupe identical (up to scalar) evaluation polynomials, keep the shortest first
    order = sorted(range(len(polys)), key=lambda i: (polys[i].total_degree(), len(polys[i].terms())))
    seen = set(); keep = []
    for i in order:
        p = polys[i]; lc = p.LC()
        key = tuple(sorted((mon, c/lc) for mon, c in p.terms()))
        if key in seen: continue
        seen.add(key); keep.append(i)
    for D in range(max(p.total_degree() for p in polys), dmax + 1):
        rows = monos(nv, D); ridx = {r: n for n, r in enumerate(rows)}
        cols = []
        for i in keep:
            p = polys[i]
            for u in monos(nv, D - p.total_degree()):
                cols.append((i, u))
        M = flint.fmpq_mat(len(rows), len(cols) + 1)
        for c, (i, u) in enumerate(cols):
            for mon, coef in polys[i].terms():
                r = ridx[tuple(x + y for x, y in zip(mon, u))]
                M[r, c] = flint.fmpq(int(coef.p), int(coef.q))
        M[ridx[tuple([0]*nv)], len(cols)] = 1
        R, rank = M.rref()
        # consistent iff no pivot in the last column
        piv = []
        r = 0
        for c in range(len(cols) + 1):
            if r < rank and R[r, c] != 0:
                piv.append(c); r += 1
        if len(cols) in piv:
            continue
        cof = {}
        for r, c in enumerate(piv):
            v = R[r, len(cols)]
            if v != 0:
                i, u = cols[c]
                cof.setdefault(i, 0)
                cof[i] += sp.Rational(int(v.p), int(v.q)) * sp.Mul(*[x**e for x, e in zip(mv, u)])
        total = sp.expand(sum(cof[i]*evals[i][2] for i in cof))
        assert total == 1, total
        return D, {i: sp.expand(g) for i, g in cof.items()}
    raise RuntimeError('no certificate up to degree %d' % dmax)

def all_supports():
    for mask in range(32):
        yield tuple(i for i in range(5) if mask >> i & 1)

def main(out='certs.json'):
    certs = []
    for S in all_supports():
        free, a, b, t = param(S); N = len(free)
        ks = kappa(S, free, a, b, t)
        for C in itertools.combinations(range(N), 3):
            free, mv, evals = chart_evals(S, C)
            D, cof = find_cofactors(mv, evals)
            used = sorted(cof)
            certs.append({
                'S': list(S), 'free': free, 'C': list(C), 'm': [str(x) for x in mv],
                'a': [str(v) for v in a], 'b': [str(v) for v in b],
                'kappa': {f'{k}{i}': v for (k, i), v in ks.items()},
                'degree': D,
                'evals': [{'s': list(evals[i][0]), 'j': evals[i][1], 'E': str(evals[i][2]),
                           'g': str(cof[i])} for i in used]})
            print(f'S={S} C={C} N={N} unknowns={len(mv)} D={D} used={len(used)}', flush=True)
    json.dump(certs, open(out, 'w'), indent=1)

if __name__ == '__main__':
    main(*sys.argv[1:])
