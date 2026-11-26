# vJ (L-gct-219) residual: P inside W_S, cubics c_j = G3_j(a)+G3_j(b) must vanish on P.
# W_S: sum b = 0; b_i = 0 (i not in S); 2 a_i = sum a (i in S).  Question: does W_S contain a
# 3-dim subspace on which all five c_j vanish?
import itertools, sympy as sp
a = sp.symbols('a0:5'); b = sp.symbols('b0:5')
def G3(j, x):
    idx=[l for l in range(5) if l!=j]
    return 6*sum(x[l]*x[m]*x[n] for l,m,n in itertools.combinations(idx,3))
def WS(S):
    eqs=[sum(b)]+[b[i] for i in range(5) if i not in S]+[2*a[i]-sum(a) for i in S]
    M=sp.Matrix([[sp.diff(e,v) for v in a+b] for e in eqs])
    N=M.nullspace()
    return N
if __name__=="__main__":
    res={}
    for k in range(6):
        S=tuple(range(k))
        N=WS(S); d=len(N)
        t=sp.symbols(f't0:{d}')
        vec=sum((t[i]*N[i] for i in range(d)), sp.zeros(10,1))
        sub=dict(zip(a+b,vec))
        cs=[sp.expand(G3(j,a)+G3(j,b)).subs(sub) for j in range(5)]
        cs=[sp.factor(sp.expand(c)) for c in cs]
        g=0
        for c in cs: g=sp.gcd(g,c)
        print("k=",k,"dimW=",d,"gcd=",sp.factor(g))
        for j,c in enumerate(cs): print("   c",j,"=",c)
