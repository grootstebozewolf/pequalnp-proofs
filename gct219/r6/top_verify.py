"""Independent check (sympy, no Singular, no schubert.py): top cell of 4x5 d7 (pivots = row 0 + (1,0),(1,1)).
Basis rows b=0..4: e_(0,b) + free entries on positions 7..19 (last one eliminated by P1); rows 5,6 likewise.
t* = row_0 + ... + row_4 has matrix row 0 equal to (1,...,1); then F(J - t*) = 0 because J - t* has a zero row.
We check: (i) row 0 of t* is all ones, (ii) F(J + s t*) computed from all 120 injections is divisible by (1+s),
(iii) -P2/20 + P3/60 - P4/120 = 1 at t* with P_k from injections (the Singular certificate)."""
import itertools, sympy as sp
p, q, d = 4, 5, 7; n = p * q
S = list(range(7)); nonS = [c for c in range(n) if c not in S]
rows = []
for b, s in enumerate(S):
    fr = [c for c in nonS if c > s]
    a = [sp.Symbol(f"a{b}_{c}") for c in fr[:-1]]
    r = [sp.Integer(0)] * n; r[s] = sp.Integer(1)
    for c, v in zip(fr[:-1], a): r[c] = v
    r[fr[-1]] = -1 - sum(a)
    rows.append(r)
ts = [sum(rows[b][c] for b in range(5)) for c in range(n)]
print("(i) row 0 of t*:", ts[:5])
s = sp.Symbol("s")
inj = list(itertools.permutations(range(q), p))
F = sp.expand(sum(sp.prod([1 + s * ts[i * q + f[i]] for i in range(p)]) for f in inj))
print("(ii) F(J+s t*) at s=-1:", sp.expand(F.subs(s, -1)), "; F at s=0:", F.subs(s, 0))
def Pk(k):
    return sp.expand(sum(sp.prod([ts[R[j] * q + f[j]] for j in range(k)]) for R in itertools.combinations(range(p), k)
                         for f in itertools.permutations(range(q), k)))
P1 = Pk(1); print("P1(t*) =", P1)
cert = sp.expand(-Pk(2) / 20 + Pk(3) / 60 - Pk(4) / 120)
print("(iii) -P2/20 + P3/60 - P4/120 at t* =", cert)
