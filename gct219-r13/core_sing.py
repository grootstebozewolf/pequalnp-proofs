# Core slice via Singular: equations from F(J + s t) = sum_k (5-k)! s^k P_k(t), t = sum_r l_r v_r,
# v_r the reduced echelon basis of the cell S in the basis B_k of the doubly centred 4x5 matrices.
import itertools, sys, os, json, subprocess, time
p, q = 4, 5
basis = []
for i in range(p - 1):
    for j in range(q - 1):
        M = [[0] * q for _ in range(p)]
        M[i][j] += 1; M[i][q - 1] -= 1; M[p - 1][j] -= 1; M[p - 1][q - 1] += 1
        basis.append(M)
n = len(basis)
INJ = list(itertools.permutations(range(q), p))
def script(S, d, char, mode, out):
    S = sorted(S); xs = []; rows = []
    for r, s in enumerate(S):
        row = []
        for c in range(n):
            if c == s: row.append('1')
            elif c in S or c < s: row.append('0')
            else: v = f'a{r}_{c}'; xs.append(v); row.append(v)
        rows.append(row)
    ls = [f'l{r}' for r in range(d)]
    ent = []
    for i in range(p):
        for j in range(q):
            terms = []
            for r in range(d):
                co = [f'({basis[c][i][j]})*{rows[r][c]}' for c in range(n) if basis[c][i][j] != 0 and rows[r][c] != '0']
                if co: terms.append(f'{ls[r]}*(' + '+'.join(co) + ')')
            ent.append('+'.join(terms) if terms else '0')
    vs = ','.join(['s'] + ls + xs)
    L = [f'ring R = {char}, ({vs}), dp;', 'option(redSB);']
    L += [f'poly t{i}_{j} = {ent[i*q+j]};' for i in range(p) for j in range(q)]
    L += ['poly G = 0;']
    for f in INJ:
        L.append('G = G + ' + '*'.join(f'(1+s*t{i}_{f[i]})' for i in range(p)) + ';')
    L += ['int k; int m; matrix Cl;', 'matrix Cs = coeffs(G, s);',
          'ideal I;',
          'for (k = 3; k <= 5; k++) { Cl = coef(Cs[k,1], ' + '*'.join(ls) + '); for (m = 1; m <= ncols(Cl); m++) { I = I + ideal(Cl[2,m]); } }',
          'I = simplify(I, 2);']
    if mode == 'std':
        L += ['int t0 = rtimer;', 'ideal J = std(I);',
              f'write(":w {out}", "RESULT unit=" + string(J[1]==1) + " dim=" + string(dim(J)-1-{d}) + " sec=" + string(rtimer-t0) + " gens=" + string(ncols(I)));']
    else:
        L += [f'link l = ":w {out}";', 'write(l, "' + ','.join(xs) + '");', f'write(l, "{char}");',
              'for (k = 1; k <= ncols(I); k++) { if (k < ncols(I)) { write(l, string(I[k]) + ","); } else { write(l, string(I[k])); } }', 'close(l);']
    L += ['quit;']
    return '\n'.join(L), xs
if __name__ == '__main__':
    S = tuple(map(int, sys.argv[1].split(','))); d = len(S); char = int(sys.argv[2]); mode = sys.argv[3]
    tag = '-'.join(map(str, S)); out = f'cells/{tag}_{char}.{mode}'
    sc, xs = script(S, d, char, mode, out); open(f'cells/{tag}_{char}_{mode}.sing', 'w').write(sc)
    t = time.time()
    try:
        subprocess.run(['bash', '-c', f'ulimit -v 6000000; Singular -q cells/{tag}_{char}_{mode}.sing'], capture_output=True, text=True, timeout=int(os.environ.get('CAP', '300')))
        print(open(out).read().strip()[:300] if os.path.exists(out) else 'NOOUT', round(time.time() - t, 1))
    except subprocess.TimeoutExpired:
        print('TIMEOUT', round(time.time() - t, 1))
