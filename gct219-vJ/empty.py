# S = {} : P inside C^5 (a only), cubics G3_j(a). 3-dim Q: pivots c (3 of 5), others = mu-combos.
import itertools, sympy as sp
from ws import G3
s=sp.symbols('s0:3')
for c in itertools.combinations(range(5),3):
    rest=[k for k in range(5) if k not in c]
    mu={k:sp.symbols(f'm{k}_0:3') for k in rest}
    x=[None]*5
    for n,k in enumerate(c): x[k]=s[n]
    for k in rest: x[k]=sum(mu[k][n]*s[n] for n in range(3))
    eqs=set()
    for j in range(5):
        p=sp.Poly(sp.expand(G3(j,x)),*s)
        eqs|=set(sp.expand(co) for co in p.coeffs())
    eqs=[e for e in eqs if e!=0]
    vars_=[v for k in rest for v in mu[k]]
    G=sp.groebner(eqs,*vars_,order='grevlex')
    print(c,len(eqs),list(G.exprs)==[1])
