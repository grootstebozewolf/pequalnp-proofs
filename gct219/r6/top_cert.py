"""Top cell 4x5 d7: Singular lift with labelled generators (k, x-monomial). Writes r6/top_cert.json."""
import sys, subprocess, json, re
sys.path.insert(0, ".")
from schubert import cells
from cell_solve import script
p, q, d = map(int, sys.argv[1:4]); Starg = tuple(map(int, sys.argv[4].split(","))) if len(sys.argv) > 4 else tuple(range(d))
S, fr, u = next(c for c in cells(p, q, d) if tuple(c[0]) == Starg)
s = script(p, q, d, S, fr, 0)
head = s[:s.index("ideal I; matrix C; int i;")]
xs = "*".join(f"x({i+1})" for i in range(d))
body = "ideal I; matrix C; int i; int n = 0;\n"
for k in range(2, p + 1):
    body += (f"C = coef(f(P{k}), {xs}); for (i = 1; i <= ncols(C); i++) {{ if (C[2,i] != 0) {{ n++; I[n] = C[2,i]; "
             f"print(\"LAB \" + string(n) + \" {k} \" + string(C[1,i])); }} }}\n")
avars = s[s.index("ring A = 0,(") + len("ring A = 0,("):].split(")")[0]
body += f"""ring A = 0,({avars}),dp;
ideal J = imap(R, I);
option(redSB);
matrix Mlift = lift(J, ideal(1)); int k;
for (k = 1; k <= nrows(Mlift); k++) {{ if (Mlift[k,1] != 0) {{ print("COF " + string(k) + " " + string(Mlift[k,1])); }} }}
quit;
"""
open("r6/top_cert.sing", "w").write(head + body)
out = subprocess.run(["Singular", "-q", "r6/top_cert.sing"], capture_output=True, text=True, timeout=1200).stdout
lab = {int(l.split()[1]): (int(l.split()[2]), l.split()[3]) for l in out.splitlines() if l.startswith("LAB ")}
cof = {int(l.split()[1]): l.split(maxsplit=2)[2] for l in out.splitlines() if l.startswith("COF ")}
assert cof, out[-800:]
json.dump({"S": list(S), "ngens": len(lab), "cert": [[lab[i][0], lab[i][1], cof[i]] for i in sorted(cof)]},
          open(f"r6/cert_{p}x{q}_d{d}_" + "-".join(map(str, S)) + ".json", "w"))
print("gens", len(lab), "nonzero cofactors", len(cof), "all constant:", all(re.fullmatch(r"-?\d+(/\d+)?", c) for c in cof.values()))
print(sorted(set((lab[i][0], cof[i]) for i in cof)))
