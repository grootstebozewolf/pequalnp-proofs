"""Re-run mod-p units of the weight-minor (deg<=3) run over Q, smallest time first; skip done ones. Loops until stopped."""
import json, time, sys, os
sys.path.insert(0, ".")
import minorsw as MW
from schubert import cells
C = {tuple(S): (S, fr, u) for S, fr, u in cells(4, 5, 7)}
outf = "r6/mw_exp_4x5_d7_deg3_c0.jsonl"
done = set()
if os.path.exists(outf):
    done = {tuple(json.loads(l)["S"]) for l in open(outf)}
tout = int(sys.argv[1])
while True:
    rs = [json.loads(l) for l in open("r6/mw_exp_4x5_d7_deg3_c32003.jsonl")]
    todo = sorted([r for r in rs if "unit=1" in r["res"] and tuple(r["S"]) not in done], key=lambda r: r["sec"])
    if not todo:
        time.sleep(30); continue
    r = todo[0]; S, fr, u = C[tuple(r["S"])]
    o = MW.run((4, 5, 7, S, fr, u, 0, tout, "exp", 3))
    done.add(tuple(S))
    with open(outf, "a") as fh: fh.write(json.dumps(o) + "\n")
    print(o, flush=True)
