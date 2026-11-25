import json, glob, collections
T = json.load(open("r6/table6_4x5_d7.json"))
st = {k: v[1] for k, v in T.items()}; un = {k: v[0] for k, v in T.items()}
for f in glob.glob("r7/cert_*_0.txt"):
    k = f.split("cert_")[1].rsplit("_", 1)[0].replace("-", ","); st[k] = "emptyQ(R7 cert, sympy-verified)"
for l in open("r7/modstd457.log"):
    r = json.loads(l)
    if "unit=1" in r["res"]: st[",".join(map(str, r["S"]))] = "emptyQ(R7 modStd exact)"
for l in open("r7/run_4x5_d7_rr_c32003.jsonl"):
    r = json.loads(l); k = ",".join(map(str, r["S"]))
    if st[k].startswith(("emptyQ", "FK")): continue
    st[k] = "modp(R7 rr)" if "unit=1" in r["res"] else ("timeout(R7 rr 180s)" if r["res"] == "TIMEOUT" else r["res"][:20])
json.dump({k: [un[k], st[k]] for k in st}, open("r7/table7_4x5_d7.json", "w"))
bins = [(0, 50), (50, 55), (55, 60), (60, 65), (65, 70), (70, 75), (75, 85)]
print("| unknowns | reps | closed over Q | open: mod-p only | open: timeout/OOM | open: not run in R7 |")
print("|---|---|---|---|---|---|")
tot = collections.Counter()
for a, b in bins:
    ks = [k for k in st if a <= un[k] < b]
    c = collections.Counter("Q" if st[k].startswith(("emptyQ", "FK")) else "modp" if st[k].startswith("modp") else "to" if "R7" in st[k] or st[k].startswith("timeout") and False else "nr" for k in ks)
    c = collections.Counter("Q" if st[k].startswith(("emptyQ", "FK")) else "modp" if st[k].startswith("modp") else "to" if "R7" in st[k] else "nr" for k in ks)
    tot += c; print(f"| {a}–{b-1} | {len(ks)} | {c['Q']} | {c['modp']} | {c['to']} | {c['nr']} |")
print(f"| all | {len(st)} | {tot['Q']} | {tot['modp']} | {tot['to']} | {tot['nr']} |")
print(collections.Counter(st.values()))
