"""Item 3: lift 1 into the (rr) ideal of a 4x5 cell mod p; report certificate size. args: char tout S(comma) [mdeg]"""
import sys, subprocess, time, json
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
char, tout = int(sys.argv[1]), int(sys.argv[2]); S = tuple(map(int, sys.argv[3].split(","))); mdeg = int(sys.argv[4]) if len(sys.argv) > 4 else 3
import os; PP, QQ, DD = map(int, os.environ.get("PQD", "4,5,7").split(","))
S_, fr, u = next(c for c in cells(PP, QQ, DD) if tuple(c[0]) == S)
s, info = G.build(PP, QQ, DD, S_, fr, char, "exp", mdeg, [], os.environ.get("RR", "1") == "1")
tail = s[s.index("option(redSB);"):]
s = s.replace(tail, """J = simplify(J, 2);
matrix Ml = lift(J, ideal(1));
int nz = 0; int tt = 0; int md = 0; int k;
for (k = 1; k <= nrows(Ml); k++) { if (Ml[k,1] != 0) { nz++; tt = tt + size(Ml[k,1]); if (deg(Ml[k,1]) > md) { md = deg(Ml[k,1]); } } }
matrix Jm = matrix(J);
poly chk = (Jm * Ml)[1,1] - 1;
string cf = "r7/cert_SS_CH.txt"; write(":w " + cf, "");
for (k = 1; k <= nrows(Ml); k++) { if (Ml[k,1] != 0) { write(":a " + cf, string(Jm[1,k]) + " ; " + string(Ml[k,1])); } }
print("LIFT ngens=" + string(ncols(Jm)) + " nonzero=" + string(nz) + " terms=" + string(tt) + " maxdeg=" + string(md) + " check=" + string(chk == 0));
quit;
""")
s = s.replace("SS_CH", sys.argv[3].replace(",", "-") + f"_{char}")
fn = f"cells/lift_{sys.argv[3]}_{char}.sing"; open(fn, "w").write(s); t0 = time.time()
try:
    out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
    r = [l for l in out.splitlines() if l.startswith("LIFT")] or [out[-200:]]
except subprocess.TimeoutExpired:
    subprocess.run(["pkill", "-f", fn]); r = ["TIMEOUT"]
print(json.dumps({"S": S, "unknowns": u, **info, "char": char, "res": r[0], "sec": round(time.time() - t0, 1)}), flush=True)
