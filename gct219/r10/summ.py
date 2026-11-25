import json, collections
pos = json.load(open("r10/poscells.json"))
A = collections.defaultdict(list); F = {}
for l in open("r10/akslice.jsonl"):
    r = json.loads(l); o = r["out"].splitlines()
    for x in o:
        if "rankA" in x: A[tuple(r["S"])].append((r["j"], int(x.split()[2].split("=")[1]), int(x.split()[3].split("=")[1])))
    if r["err"] == "TIMEOUT": A[tuple(r["S"])].append((r["j"], "TO", "TO"))
    fu = [x for x in o if "fibre_unit=0" in x]
    if fu: print("NONEMPTY sample fibre", r["S"], r["j"], fu)
for l in open("r10/fibcell.jsonl"):
    r = json.loads(l); o = [x for x in r["out"].splitlines() if "fullfibre" in x]
    F[tuple(r["S"])] = o[0] if o else r["err"][:20]
for S, d in pos:
    S = tuple(S)
    if S in A or S in F: print(S, d, "slice ranks(j,rA,rAb):", sorted(set(A.get(S, [])), key=str), "| whole-cell fibre:", F.get(S, "-"))
