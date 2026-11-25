import json, collections, os
W = json.load(open("r6/wstatus_4x5_d7.json"))
st = {tuple(S): [u, s] for S, u, s in W}
def load(f):
    return [json.loads(l) for l in open(f)] if os.path.exists(f) else []
for r in load("r6/mw_exp_4x5_d7_deg3_c32003.jsonl"):
    S = tuple(r["S"])
    if st[S][1] in ("FK", "emptyQ"): continue
    st[S][1] = "modp(deg3 minors)" if "unit=1" in r["res"] else ("NONEMPTY-modp" if "unit=0" in r["res"] else "timeout/OOM")
for r in load("r6/mw_exp_4x5_d7_deg3_c0.jsonl"):
    S = tuple(r["S"])
    if "unit=1" in r["res"]: st[S][1] = "emptyQ(deg3 minors)"
    elif "unit=0" in r["res"]: st[S][1] = "NONEMPTY-Q"
cols = ["FK", "emptyQ", "emptyQ(deg3 minors)", "modp(deg3 minors)", "timeout", "timeout/OOM", "unreached", "NONEMPTY-modp", "NONEMPTY-Q"]
tab = collections.defaultdict(collections.Counter)
for S, (u, s) in st.items(): tab[u // 10 * 10][s] += 1
print("unknowns | total | " + " | ".join(cols))
for b in sorted(tab): print(f"{b}-{b+9} | {sum(tab[b].values())} | " + " | ".join(str(tab[b][c]) for c in cols))
tot = collections.Counter(s for u, s in st.values()); print("total", dict(tot))
json.dump({",".join(map(str, S)): v for S, v in st.items()}, open("r6/table6_4x5_d7.json", "w"))
