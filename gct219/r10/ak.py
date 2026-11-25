"""R10 item 1: the linear part A_K of the fibre system over K ∈ 𝒦 (3x5, d=6, L = K ⊕ span{v_i + σ_i}, σ_i ∈ R°/K).
B = polarised P2, C = polarised P3 (inclusion–exclusion, symmetric multilinear). Linear-in-σ equations (coefficients of
y_a x_i and y_a y_b x_i in P2, P3 on L):  B(κ_a, v_i + σ_i) = 0  (4 rows),  C(κ_a, κ_b, v_i + σ_i) = 0, a ≤ b  (10 rows).
The 14x8 matrix A_K (columns = complement basis f_c, c ∉ piv(K)) is the same for i = 1, 2, so A_K(16) = A_K ⊕ A_K.
Library: forms + A(K) + full remaining equations."""
import itertools, sympy as sp
p, q = 3, 5
def P(k, t):
    return sum(sp.prod([t[R[a] * q + C[a]] for a in range(k)]) for R in itertools.combinations(range(p), k) for C in itertools.permutations(range(q), k))
add = lambda *vs: [sum(x) for x in zip(*vs)]
def Bf(x, y): return sp.expand(P(2, add(x, y)) - P(2, x) - P(2, y))
def Cf(x, y, z):
    return sp.expand(P(3, add(x, y, z)) - P(3, add(x, y)) - P(3, add(x, z)) - P(3, add(y, z)) + P(3, x) + P(3, y) + P(3, z))
def fvec(c):   # f_(i,j) = e_(i,j) - e_(i,4), c = 4i + j
    v = [0] * 15; i, j = divmod(c, 4); v[i * q + j] = 1; v[i * q + 4] = -1; return v
V = [[1] * 5 + [-1] * 5 + [0] * 5, [0] * 5 + [1] * 5 + [-1] * 5]
def A_of(Kvecs, comp):
    rows, rhs = [], [[], []]
    pairs = [(a,) for a in range(4)] + [(a, b) for a in range(4) for b in range(a, 4)]
    for pr in pairs:
        if len(pr) == 1:
            rows.append([Bf(Kvecs[pr[0]], fvec(c)) for c in comp])
            for i in range(2): rhs[i].append(Bf(Kvecs[pr[0]], V[i]))
        else:
            rows.append([Cf(Kvecs[pr[0]], Kvecs[pr[1]], fvec(c)) for c in comp])
            for i in range(2): rhs[i].append(Cf(Kvecs[pr[0]], Kvecs[pr[1]], V[i]))
    return sp.Matrix(rows), [sp.Matrix(r) for r in rhs]
if __name__ == "__main__":
    import json
    out = {}
    # positive-control point of 𝒦: K = row-0 sum-zero space (row witness), pivots f_00..f_03, complement c = 4..11
    for r0 in range(3):
        K = [fvec(4 * r0 + j) for j in range(4)]; comp = [c for c in range(12) if c // 4 != r0]
        assert all(P(2, add(*[[sp.Symbol(f"y{a}") * x for x in K[a]] for a in range(4)])) == 0 for _ in [0])
        A, (r1, r2) = A_of(K, comp)
        out[f"row{r0}"] = {"rank_A": A.rank(), "rank_[A|r1]": A.row_join(r1).rank(), "rank_[A|r2]": A.row_join(r2).rank(), "B_rows_rank": A[:4, :].rank(), "C_rows_rank": A[4:, :].rank()}
    print(json.dumps(out))
