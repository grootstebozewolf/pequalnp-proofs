"""Independent plain-Python re-implementation of the Lean criterion
   wt2 S ≤ wt2 (S.image fun p => (σ p.1, τ p.2))  for all σ τ,   wt2 S = Σ_{(i,j)∈S} 2^(q*i+j)
and comparison with orbitw.py (exp mode) for 3x3 d4, 3x5 d6, 4x5 d7."""
import itertools, json
for p, q, d in [(3, 3, 4), (3, 5, 6), (4, 5, 7)]:
    perms = [(s, t) for s in itertools.permutations(range(p)) for t in itertools.permutations(range(q))]
    reps = []
    for S in itertools.combinations([(i, j) for i in range(p) for j in range(q)], d):
        w = sum(2 ** (q * i + j) for i, j in S)
        if all(w <= sum(2 ** (q * s[i] + t[j]) for i, j in S) for s, t in perms):
            reps.append(sorted(q * i + j for i, j in S))
    py = sorted(o["S"] for o in json.load(open(f"orbitw_exp_{p}x{q}_d{d}.json")))
    print(p, q, d, "Lean-criterion reps:", len(reps), "orbitw exp reps:", len(py), "identical:", sorted(reps) == py)
