"""Exact std over Q via Singular modStd(J, 1) (multi-modular + rational reconstruction + exactness verification). args: tout S [mdeg]; env PQD."""
import sys, subprocess, time, json, os
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
PP, QQ, DD = map(int, os.environ.get("PQD", "4,5,7").split(","))
tout = int(sys.argv[1]); S = tuple(map(int, sys.argv[2].split(","))); mdeg = int(sys.argv[3]) if len(sys.argv) > 3 else 3
S_, fr, u = next(c for c in cells(PP, QQ, DD) if tuple(c[0]) == S)
s, info = G.build(PP, QQ, DD, S_, fr, 0, "exp", mdeg, [], True)
s = 'LIB "modstd.lib";\n' + s.replace("ideal G = std(J);", "ideal G = modStd(J, 1);")
fn = f"cells/ms_{PP}{QQ}{DD}_{sys.argv[2].replace(',', '-')}.sing"; open(fn, "w").write(s); t0 = time.time()
try:
    out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
    r = [l for l in out.splitlines() if l.startswith("RESULT")] or [out[-200:]]
except subprocess.TimeoutExpired:
    subprocess.run(["pkill", "-f", fn]); r = ["TIMEOUT"]
print(json.dumps({"S": S, "unknowns": u, **info, "res": r[0], "sec": round(time.time() - t0, 1)}), flush=True)
