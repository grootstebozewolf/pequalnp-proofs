"""Q certificate from a mod-p support: take the generators with nonzero cofactor in r7/cert_<S>_<p>.txt (small integer coeffs survive mod p;
each is re-identified as a hypothesis over Q by cert_verify.py), lift 1 over Q with only those; write r7/cert_<S>_0.txt."""
import sys, subprocess, re
S = sys.argv[1]; pr = sys.argv[2]; tag = S.replace(",", "-")
gens = [l.split(";")[0].strip() for l in open(f"r7/cert_{tag}_{pr}.txt") if ";" in l]
vs = sorted(set(re.findall(r"a\d+_\d+", " ".join(gens))))
s = f"""ring A = 0,({",".join(vs)}),dp;
ideal J = {",".join(gens)};
matrix Jm = matrix(J); matrix Ml = lift(J, ideal(1)); int k;
string cf = "r7/cert_{tag}_0.txt"; write(":w " + cf, "");
for (k = 1; k <= nrows(Ml); k++) {{ if (Ml[k,1] != 0) {{ write(":a " + cf, string(Jm[1,k]) + " ; " + string(Ml[k,1])); }} }}
print("SUBLIFT gens=" + string(ncols(Jm)) + " check=" + string((Jm*Ml)[1,1]-1 == 0));
quit;
"""
open(f"cells/sub_{tag}.sing", "w").write(s)
print(subprocess.run(["bash", "-c", f"ulimit -v 4000000; Singular -q cells/sub_{tag}.sing"], capture_output=True, text=True, timeout=600).stdout[-300:])
