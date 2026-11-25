# Core slice of L-gct-219: level spaces L inside D = {4x5 matrices with all row and column sums 0}
# (dim 12). On D, P1 = 0 identically, so L is level iff P2, P3, P4 vanish on L.
# For each Schubert cell of Gr(d, 12) (pivot set S in the basis B_k of D, reduced echelon form),
# write the coefficient equations of P2..P4 in the cell coordinates and ask msolve mod p for 1 in I.
import itertools, sys, os, json, subprocess, time
import sympy as sp
p, q = 4, 5
basis = []  # B_(i,j) = E_ij - E_i4 - E_3j + E_34, i < 3, j < 4
for i in range(p - 1):
    for j in range(q - 1):
        M = [[0] * q for _ in range(p)]
        M[i][j] += 1; M[i][q - 1] -= 1; M[p - 1][j] -= 1; M[p - 1][q - 1] += 1
        basis.append(M)
n = len(basis)
def matchings(k):
    for R in itertools.combinations(range(p), k):
        for C in itertools.permutations(range(q), k):
            yield list(zip(R, C))
MATCH = {k: list(matchings(k)) for k in (2, 3, 4)}
def cell_system(S, d):
    S = sorted(S); xs = []; rows = []
    for r, s in enumerate(S):
        row = []
        for c in range(n):
            if c == s: row.append(sp.Integer(1))
            elif c in S or c < s: row.append(sp.Integer(0))
            else:
                v = sp.Symbol(f'a{r}_{c}'); xs.append(v); row.append(v)
        rows.append(row)
    lam = sp.symbols(f'l0:{d}')
    t = [[sp.expand(sum(lam[r] * sum(rows[r][c] * basis[c][i][j] for c in range(n)) for r in range(d)))
          for j in range(q)] for i in range(p)]
    gens = []
    for k in (2, 3, 4):
        Pk = sp.expand(sum(sp.Mul(*[t[i][j] for i, j in m]) for m in MATCH[k]))
        for _, co in sp.Poly(Pk, *lam).terms():
            co = sp.expand(co)
            if co != 0: gens.append(co)
    return xs, gens
def to_ms(xs, gens, prime):
    if not xs:
        return None
    body = ',\n'.join(str(g).replace('**', '^') for g in gens)
    return ','.join(map(str, xs)) + f'\n{prime}\n' + body + '\n'
MS = os.environ.get('MSOLVE', '/home/user/msolve/msolve')
def unit_mod_p(xs, gens, prime, cap=600):
    if not xs:  # no unknowns: the cell is a single point, check the constants
        return 'unit' if any(g != 0 for g in gens) else 'nonempty'
    if not gens: return 'nonempty'
    f = f'cells/tmp_{os.getpid()}.ms'; o = f + '.out'; open(f, 'w').write(to_ms(xs, gens, prime))
    try:
        r = subprocess.run(['bash', '-c', f'ulimit -v 6000000; {MS} -g 2 -t 1 --random-seed 42 -f {f} -o {o}'],
                           capture_output=True, text=True, timeout=cap)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    b = open(o).read().replace(' ', '').replace('\n', '') if os.path.exists(o) else ''
    return 'unit' if b.endswith('[1]:') else ('nonunit' if b else f'fail{r.returncode}')
if __name__ == '__main__':
    d = int(sys.argv[1]); prime = int(os.environ.get('PRIME', '32003'))
    out = f'core_d{d}_{prime}.jsonl'
    done = set()
    if os.path.exists(out): done = {tuple(json.loads(l)['S']) for l in open(out)}
    with open(out, 'a') as fh:
        for S in itertools.combinations(range(n), d):
            if S in done: continue
            t0 = time.time(); xs, gens = cell_system(S, d); res = unit_mod_p(xs, gens, prime)
            rec = {'S': S, 'unknowns': len(xs), 'gens': len(gens), 'res': res, 'sec': round(time.time() - t0, 1)}
            fh.write(json.dumps(rec) + '\n'); fh.flush()
            if res != 'unit': print(json.dumps(rec), flush=True)
