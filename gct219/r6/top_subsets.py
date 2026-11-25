import sys, subprocess, time
sys.path.insert(0, ".")
from schubert import cells
from cell_solve import script
p, q, d = map(int, sys.argv[1:4]); ks = list(map(int, sys.argv[4].split(","))); char = int(sys.argv[5])
S, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == tuple(range(d)))
s = script(p, q, d, S, fr, char)
lines = s.split("\n")
lines = [l for l in lines if not (l.startswith("C = coef(f(P") and int(l[len("C = coef(f(P")]) not in ks)]
s = "\n".join(lines)
open(f"r6/tmp_{p}{q}{d}_{sys.argv[4]}.sing", "w").write(s)
t0 = time.time()
out = subprocess.run(["Singular", "-q", f"r6/tmp_{p}{q}{d}_{sys.argv[4]}.sing"], capture_output=True, text=True, timeout=600).stdout
print(p, q, d, "ks", ks, "char", char, "unknowns", u, out.strip()[-200:], round(time.time() - t0, 1), "s")
