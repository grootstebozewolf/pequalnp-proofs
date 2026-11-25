import json, glob, collections, sys
def status_map(p, q, d):
    st = {}
    def put(S, k):
        rank = {"emptyQ": 3, "nonempty": 3, "modp": 1, "timeout": 0}
        if S not in st or rank[k] > rank[st[S]]: st[S] = k
    for fn in glob.glob(f"cells_{p}x{q}_d{d}_*_c0.jsonl") + (["retry300.jsonl", "qsample_3x5.jsonl"] if True else []) + glob.glob(f"qtop_{p}x{q}_d{d}.jsonl"):
        for l in open(fn):
            r = json.loads(l); S = tuple(r["S"])
            if len(S) != d: continue
            put(S, "emptyQ" if "unit=1" in r["res"] else "nonempty" if "unit=0" in r["res"] else "timeout")
    for fn in glob.glob(f"ruleIU_{p}x{q}_d{d}*.jsonl"):
        for l in open(fn):
            r = json.loads(l)
            if r["k"]: put(tuple(r["S"]), "emptyQ")
    for fn in glob.glob(f"lp_{p}x{q}_d{d}.jsonl"):
        for l in open(fn):
            r = json.loads(l)
            if r["res"].startswith("LINUNIT"): put(tuple(r["S"]), "emptyQ")
            elif r["res"] == "TIMEOUT": put(tuple(r["S"]), "timeout")
    for fn in glob.glob(f"modp_{p}x{q}_d{d}.jsonl"):
        for l in open(fn):
            r = json.loads(l)
            put(tuple(r["S"]), "modp" if "unit=1" in r["res"] else "timeout")
    return st
if __name__ == "__main__":
    from schubert import cells
    p, q, d = map(int, sys.argv[1:4]); st = status_map(p, q, d)
    U = {tuple(S): u for S, fr, u in cells(p, q, d)}
    # by dimension (unknowns after P1), bins
    tab = collections.defaultdict(collections.Counter)
    for S, u in U.items(): tab[u][st.get(S, "unreached")] += 1
    om = [o for o in json.load(open(f"orbitmin_{p}x{q}_d{d}.json")) if not o["killed"]]
    tab2 = collections.defaultdict(collections.Counter)
    for o in om: tab2[o["unknowns"]][st.get(tuple(o["S"]), "unreached")] += 1
    json.dump({"all": {k: dict(v) for k, v in tab.items()}, "orbit": {k: dict(v) for k, v in tab2.items()},
               "orbit_cells": [[o["S"], o["unknowns"], st.get(tuple(o["S"]), "unreached")] for o in om]},
              open(f"tally5_{p}x{q}_d{d}.json", "w"))
    cols = ["emptyQ", "nonempty", "modp", "timeout", "unreached"]
    for name, T in [("ALL cells (P1-live)", tab), ("ORBIT-MINIMAL cells", tab2)]:
        print(name); print("unknowns-bin total " + " ".join(cols))
        for lo in range(0, 100, 10):
            c = collections.Counter()
            for u, v in T.items():
                if lo <= u < lo + 10: c.update(v)
            if sum(c.values()): print(f"{lo:>2}-{lo+9:<2} {sum(c.values()):>6} " + " ".join(f"{c[k]:>6}" for k in cols))
        c = collections.Counter(); [c.update(v) for v in T.values()]
        print("total", sum(c.values()), dict(c))
