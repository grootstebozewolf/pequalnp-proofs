import sys, subprocess, time
sys.path.insert(0, ".")
from schubert import cells
from cell_solve import script
S, fr, u = next(c for c in cells(4, 5, 7) if tuple(c[0]) == tuple(range(7)))
s = script(4, 5, 7, S, fr, 0)
s = s[:s.index("int t0 = timer;")] + '''
write(":w r6/top_gens.txt", J);
print("NGENS " + string(ncols(J)));
option(redSB); int k;
matrix Mlift = lift(J, ideal(1));
for (k = 1; k <= nrows(Mlift); k++) { if (Mlift[k,1] != 0) { write(":a r6/top_cof.txt", string(k) + " : " + string(Mlift[k,1])); } }
int tot = 0; for (k = 1; k <= nrows(Mlift); k++) { tot = tot + size(Mlift[k,1]); }
print("LIFT rows=" + string(nrows(Mlift)) + " terms=" + string(tot));
quit;
'''
open("r6/top_lift.sing", "w").write(s)
t0 = time.time()
out = subprocess.run(["Singular", "-q", "r6/top_lift.sing"], capture_output=True, text=True, timeout=1500).stdout
print(out[-400:], round(time.time() - t0), "s")
