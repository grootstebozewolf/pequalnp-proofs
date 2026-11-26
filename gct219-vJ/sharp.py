# Sanity: a 6-dimensional level space with a 4-dimensional row-0 part exists, so vJ's bound 7 is sharp.
# L = {row 0 sums to zero} + {rows 1..3 supported on column 0, column sum zero}.
import itertools, random
from fractions import Fraction as Q
def perm45(M): return sum(eval('*'.join(f'M[{r}][{e[r]}]' for r in range(4))) for e in itertools.permutations(range(5),4))
random.seed(1)
for trial in range(5):
    t=[[Q(0)]*5 for _ in range(4)]
    r0=[Q(random.randint(-9,9)) for _ in range(4)]; t[0]=r0+[-sum(r0)]
    c=[Q(random.randint(-9,9)) for _ in range(2)]; t[1][0],t[2][0],t[3][0]=c[0],c[1],-c[0]-c[1]
    M=[[1+t[i][j] for j in range(5)] for i in range(4)]
    assert perm45(M)==120, perm45(M)
print('6-dim level space with u(L,0)=4: perm(J+t)=120 on 5 random points; dims 4+2=6')
