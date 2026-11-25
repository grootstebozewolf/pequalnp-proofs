"""Benchmark: export a cell ideal (P_k coefficients + colex minors deg<=3) mod 32003 to msolve format; run msolve (built from source, git HEAD 0ae16f2) -g 2."""
import sys, os, subprocess, time, json
sys.path.insert(0, "."); sys.path.insert(0, "r7")
import gens as G
from schubert import cells
PP, QQ, DD = map(int, os.environ.get("PQD", "4,5,7").split(","))
S = tuple(map(int, sys.argv[1].split(","))); tout = int(sys.argv[2]); tag = sys.argv[1].replace(",", "-") + os.environ.get("TAGX", "")
EX = os.environ.get("EXTRA", ""); YV = os.environ.get("YVAR", "")
S_, fr, u = next(c for c in cells(PP, QQ, DD) if tuple(c[0]) == S)
s, info = G.build(PP, QQ, DD, S_, fr, 32003, "exp", 3, [], False)
avars = s[s.index("ring A = "):].split("(")[1].split(")")[0]
s = s.replace(f'ring A = 32003,({avars}),dp;', f'ring A = 32003,({avars}{YV}),dp;')
dump = s[:s.index("int t0 = timer;")] + f'J = simplify(J, 2); int i; write(":w r8/ms_{tag}.in", "{avars}{YV}"); if ("{EX}" != "") {{ J = J + ({EX}); }} write(":a r8/ms_{tag}.in", "32003");\nfor (i = 1; i <= ncols(J); i++) {{ if (i < ncols(J)) {{ write(":a r8/ms_{tag}.in", string(J[i]) + ","); }} else {{ write(":a r8/ms_{tag}.in", string(J[i])); }} }}\nquit;\n'
open(f"cells/msd_{tag}.sing", "w").write(dump); subprocess.run(["Singular", "-q", f"cells/msd_{tag}.sing"], capture_output=True)
t0 = time.time()
try:
    out = subprocess.run(["bash", "-c", f"ulimit -v 4000000; /workspace/msolve-src/inst/bin/msolve -g 2 -t 2 -f r8/ms_{tag}.in -o r8/ms_{tag}.out"], capture_output=True, text=True, timeout=tout)
    res = open(f"r8/ms_{tag}.out").read()[:200] if os.path.exists(f"r8/ms_{tag}.out") else ("rc=%d " % out.returncode) + (out.stderr[-200:] or out.stdout[-200:])
except subprocess.TimeoutExpired:
    subprocess.run(["pkill", "-f", f"ms_{tag}.in"]); res = "TIMEOUT"
print(json.dumps({"S": list(S), "unknowns": u, "minors": info["minors"], "msolve": res.replace("\n", " ")[:200], "sec": round(time.time() - t0, 1)}))
