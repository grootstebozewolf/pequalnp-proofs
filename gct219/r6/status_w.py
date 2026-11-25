import json, sys, collections, itertools
sys.path.insert(0, ".")
from tally5 import status_map
def fk(S, p, q):
    Ss = set(S)
    for a in range(1, p + 1):
        for R in itertools.combinations(range(p), a):
            if a + sum(all(i * q + j in Ss for i in R) for j in range(q)) >= q + 1: return True
    return False
import glob
for p, q, d in [(3, 3, 4), (3, 5, 6), (4, 5, 7)]:
    for mode in ("exp", "lin"):
        try: O = json.load(open(f"orbitw_{mode}_{p}x{q}_d{d}.json"))
        except FileNotFoundError: continue
        st = status_map(p, q, d)
        for fn in glob.glob(f"qorbit_{p}x{q}_d{d}.jsonl") + glob.glob(f"qtop_{p}x{q}_d{d}.jsonl"):
            for l in open(fn):
                r = json.loads(l)
                if "unit=1" in r["res"]: st[tuple(r["S"])] = "emptyQ"
        live = [o for o in O if not o["killed"]]
        c = collections.Counter(("FK" if fk(o["S"], p, q) else st.get(tuple(o["S"]), "unreached")) for o in live)
        us = sorted(o["unknowns"] for o in live)
        print(f"[{mode}] {p}x{q} d{d}: live {len(live)} status {dict(c)} unknowns min/med/max {us[0]}/{us[len(us)//2]}/{us[-1]}")
        if mode == "exp":
            json.dump([[o["S"], o["unknowns"], "FK" if fk(o["S"], p, q) else st.get(tuple(o["S"]), "unreached")] for o in live], open(f"r6/wstatus_{p}x{q}_d{d}.json", "w"))
