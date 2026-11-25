"""Task 2 check: on H={P1=0}, t_ij=a_i+b_j+w_ij (centred), P2|_H vs 1/2(|w|^2 - q(q-1)|a|^2 - p(p-1)|b|^2)."""
import sympy as sp, itertools, sys
p, q = map(int, sys.argv[1:3])
a = sp.symbols(f"a0:{p-1}"); a = list(a) + [-sum(a)]
b = sp.symbols(f"b0:{q-1}"); b = list(b) + [-sum(b)]
W = sp.symbols(f"w0:{(p-1)*(q-1)}"); w = [[W[i*(q-1)+j] for j in range(q-1)] for i in range(p-1)]
for i in range(p-1): w[i].append(-sum(w[i]))
w.append([-sum(w[i][j] for i in range(p-1)) for j in range(q)])
t = [[a[i] + b[j] + w[i][j] for j in range(q)] for i in range(p)]
P2 = sum(t[i1][j1] * t[i2][j2] for i1, i2 in itertools.combinations(range(p), 2) for j1 in range(q) for j2 in range(q) if j1 != j2)
n2 = lambda v: sum(x**2 for x in v)
rhs = sp.Rational(1, 2) * (n2([x for r in w for x in r]) - q * (q - 1) * n2(a) - p * (p - 1) * n2(b))
print(f"{p}x{q}: P2|_H - formula =", sp.expand(P2 - rhs))
