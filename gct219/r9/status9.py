"""One status per cell (V > E > T > M_p > O) for 3x5 d6 (26 colex reps) and 4x5 d7 (80)."""
import json, glob, collections
def V_cells():
    s = set()
    for f in glob.glob("r7/cert_*_0.txt") + glob.glob("r7/cert_*_r8.txt") + glob.glob("r7/cert_*_r9.txt"):
        s.add(f.split("cert_")[1].rsplit("_", 1)[0].replace("-", ","))
    return s
V = V_cells()
out = {}
# 4x5
T8 = json.load(open("r8/table8_4x5_d7.json"))
for k, (u, st) in T8.items():
    if k in V: c = "V"
    elif "modStd" in st: c = "T"
    elif st.startswith(("emptyQ", "FK")): c = "E"
    elif st.startswith("modp(R8 msolve"): c = "M_p"
    else: c = "O"
    out[("4x5", k)] = (u, c, st)
# 3x5
W = json.load(open("r6/wstatus_3x5_d6.json"))
q0 = {",".join(map(str, json.loads(l)["S"])): json.loads(l)["res"] for l in open("r7/run_3x5_d6_rr_c0.jsonl")}
ms = {",".join(map(str, json.loads(l)["S"])) for l in open("r7/modstd356.log") if "unit=1" in l}
mp = {"0,1,3,5,6,7", "0,1,2,3,5,10"}
for S, u, st in W:
    k = ",".join(map(str, S))
    if k in V: c = "V"
    elif st in ("FK", "emptyQ") or "unit=1" in q0.get(k, ""): c = "E"
    elif k in ms: c = "T"
    elif k in mp: c = "M_p"
    else: c = "O"
    out[("3x5", k)] = (u, c, st)
for grid in ("3x5", "4x5"):
    cs = {k: v for (g, k), v in out.items() if g == grid}
    print(grid, len(cs), dict(collections.Counter(v[1] for v in cs.values())))
    for c in ("V", "E", "T", "M_p", "O"):
        L = sorted((v[0], k) for k, v in cs.items() if v[1] == c)
        print(f"  {c} ({len(L)}): " + "; ".join(f"({k}) {u}u" for u, k in L))
json.dump({f"{g}:{k}": v for (g, k), v in out.items()}, open("r9/status9.json", "w"))
