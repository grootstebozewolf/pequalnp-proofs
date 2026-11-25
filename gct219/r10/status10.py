import json, os
s9 = json.load(open("r9/status9.json"))
e18 = [tuple(map(int, l.strip().split(","))) for l in open("r10/e18.txt") if l.strip()]
V3, E3 = [], []
for S in e18:
    t = "-".join(map(str, S)); f = f"r10/verify_{t}.txt"
    ok = os.path.exists(f) and "Σ cof·gen = 1: True" in open(f).read() and "unidentified: []" in open(f).read()
    (V3 if ok else E3).append(S)
fib = {}
for l in open("r10/fibprime_final.jsonl"):
    r = json.loads(l); o = r["out"].splitlines()
    fib[str(r["S"])] = {"primes": int(o[0].split()[1]), "all_fibres_unit": all("fibre_unit=1" in x for x in o if "fibre_unit" in x),
                        "ranks_A(8x8 block)": [int(x.split()[2].split("=")[1]) for x in o if "rankA" in x],
                        "consistent": [x.split()[2].split("=")[1] == x.split()[3].split("=")[1] for x in o if "rankA" in x]}
out = {"round": 10, "vocabulary": "V > E > T > M_p > O (one per cell)",
       "3x5_d6": {"V": [list(x) for x in V3], "E": [list(x) for x in E3], "T": s9["3x5_d6"]["T"] if "3x5_d6" in s9 else None,
                  "counts": {"V": len(V3), "E": len(E3), "T": 2, "M_p": 2, "O": 4}},
       "4x5_d7": {"counts": {"V": 8, "E": 37, "T": 1, "M_p": 7, "O": 27}, "note": "unchanged from R9"},
       "K_route_3x5": {"zero_dim_cells_fibre_Q": fib,
                       "zero_dim_summary": "18/18 zero-dim 𝒦 cells: fibre empty over Q on every minimal prime of I_K (E, Singular std over Q)"},
       "status9_ref": "r9/status9.json"}
json.dump(out, open("status10.json", "w"), indent=1); json.dump(out, open("r10/status10.json", "w"), indent=1)
print(out["3x5_d6"]["counts"], len(fib), all(v["all_fibres_unit"] for v in fib.values()))
