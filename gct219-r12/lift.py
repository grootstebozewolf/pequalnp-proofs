# Rational certificate for a unit cell: map a mod-p unit support (from msolve --unit-support) to the
# same generators over Q, compute cofactors with Singular lift over Q, and verify 1 = sum c_i g_i in sympy.
# usage: lift.py <tag> <subset .ms the support indices refer to> <support file>
import sys, subprocess, json, re
import sympy as sp
tag, subms, supf = sys.argv[1:4]
P = 32003
def gens_of_ms(path):
    L = open(path).read().split('\n')
    return L[0], [g.strip() for g in '\n'.join(L[2:]).split(',\n') if g.strip()]
def gens_of_txt(path):
    L = open(path).read().split('\n')
    return L[0], [g.strip() for g in L[1:] if g.strip()]
vs, sub = gens_of_ms(subms)
idx = [int(l) for l in open(supf) if l.strip() and not l.startswith('#')]
vp, modp = gens_of_txt(f'cells/{tag}_{P}.txt')
vq, overq = gens_of_txt(f'cells/{tag}_0.txt')
assert vs == vp == vq, 'variable lists differ'
pos = {g: k for k, g in enumerate(modp)}
X = sp.symbols(vq.split(','))
loc = {str(x): x for x in X}
def poly(s): return sp.Poly(sp.sympify(s.replace('^', '**'), locals=loc), *X)
orig = []
for i in idx:
    k = pos[sub[i]]
    a, b = poly(modp[k]), poly(overq[k])
    # same generator: the rational one reduces to the mod-p one
    bp = sp.Poly({m: sp.Integer(c.p * pow(c.q, -1, P) % P) for m, c in b.terms()}, *X)
    ap = sp.Poly({m: sp.Integer(int(c) % P) for m, c in a.terms()}, *X)
    if (bp - ap).is_zero is False:
        raise SystemExit(f'generator {k}: rational and mod-p versions differ')
    orig.append(k)
print(json.dumps({'support': len(idx), 'original_indices': orig}))
G = [overq[k] for k in orig]
sing = f'''ring R = 0, ({vq}), dp;
ideal I = {", ".join(G)};
matrix T = lift(I, ideal(1));
link l = ":w cells/{tag}_lift.txt";
int k; for (k = 1; k <= ncols(I); k++) {{ write(l, string(T[k,1])); }}
close(l);
quit;
'''
open(f'cells/{tag}_lift.sing', 'w').write(sing)
r = subprocess.run(['bash', '-c', f'ulimit -v 12000000; Singular -q cells/{tag}_lift.sing'], capture_output=True, text=True, timeout=7000)
if r.returncode != 0: raise SystemExit('Singular failed: ' + r.stderr[-300:] + r.stdout[-300:])
C = [l.strip() for l in open(f'cells/{tag}_lift.txt') if l.strip()]
assert len(C) == len(G)
tot = sp.expand(sum(sp.sympify(c.replace('^', '**'), locals=loc) * sp.sympify(g.replace('^', '**'), locals=loc) for c, g in zip(C, G)))
terms = sum(len(sp.Add.make_args(sp.expand(sp.sympify(c.replace('^', '**'), locals=loc)))) for c in C)
print(json.dumps({'identity_1': tot == 1, 'cofactor_terms': terms, 'max_cofactor_chars': max(map(len, C))}))
json.dump({'tag': tag, 'gens_q_indices': orig, 'cofactors': C}, open(f'cert_{tag}.json', 'w'))
