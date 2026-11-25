"""Item 5: lex (R5) vs colex (R6/R7) orbit reps of 4x5 d7, weighted by unknowns."""
import json, sys
sys.path.insert(0, "."); sys.path.insert(0, "r6")
L = [o for o in json.load(open("orbitmin_4x5_d7.json")) if not o["killed"]]
closedL = set()
for fn in ["qorbit_4x5_d7.jsonl", "qtop_4x5_d7.jsonl", "minors_4x5_d7_c0.jsonl"]:
    for l in open(fn):
        r = json.loads(l)
        if "unit=1" in r["res"]: closedL.add(tuple(r["S"]))
from tally5 import status_map
closedL |= {k for k, v in status_map(4, 5, 7).items() if v == "emptyQ"}
def fk(S, p=4, q=5):
    import itertools; Ss = set(S)
    for a in range(1, p + 1):
        for R in itertools.combinations(range(p), a):
            if a + sum(all(i * q + j in Ss for i in R) for j in range(q)) >= q + 1: return True
    return False
T = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "r6/table6_4x5_d7.json"))
def summ(name, items):
    op = [u for u, c in items if not c]; cl = [u for u, c in items if c]
    print(f"{name}: reps {len(items)}, Σunknowns {sum(u for u,_ in items)}; closed {len(cl)} (Σu {sum(cl)}), open {len(op)} (Σu {sum(op)}, max {max(op) if op else '-'}, sorted {sorted(op)})")
summ("lex R5 ", [(o["unknowns"], tuple(o["S"]) in closedL or fk(o["S"])) for o in L])
summ("colex  ", [(u, st.startswith(("emptyQ", "FK"))) for k, (u, st) in T.items()])
