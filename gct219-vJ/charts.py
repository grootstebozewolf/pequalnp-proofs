# For each case k (S={0..k-1}) and chart m: hyperplane U = {t_m = -sum_{n!=m} l_n t_n} in W_S.
# All five cubics vanish on U  <=>  coefficients (in the free t's) of c_j|U are 0.  Ideal in l.
import itertools, sympy as sp, json, sys
from ws import a,b,G3,WS
out={}
for k in range(1,6):
    S=tuple(range(k)); N=WS(S); d=len(N); assert d==4
    t=sp.symbols('t0:4'); vec=sum((t[i]*N[i] for i in range(4)), sp.zeros(10,1))
    cs=[sp.expand(sp.expand(G3(j,a)+G3(j,b)).subs(dict(zip(a+b,vec)))) for j in range(5)]
    for m in range(4):
        free=[n for n in range(4) if n!=m]
        lam=sp.symbols('l0:3')
        sub={t[m]:-sum(lam[i]*t[free[i]] for i in range(3))}
        eqs=[]
        for c in cs:
            p=sp.Poly(sp.expand(c.subs(sub)),*[t[n] for n in free])
            eqs+= [sp.expand(co) for co in p.coeffs()]
        eqs=[e for e in set(eqs) if e!=0]
        G=sp.groebner(eqs,*lam,order='grevlex')
        unit = (list(G.exprs)==[1])
        print(f"k={k} chart={m} eqs={len(eqs)} unit={unit}", "" if unit else G.exprs)
        out[f"{k},{m}"]=[str(e) for e in eqs]
json.dump(out,open('chart_ideals.json','w'),indent=0)
