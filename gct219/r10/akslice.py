"""R10 item 1 (slices): generic rank of A_K on positive-dim 𝒦 components via j random rational hyperplane slices (j = 1..d); zero-dim primes of a j-slice are generic points of j-dim components. Derived from fibprime.py. exact (char 0) per-component fibre over the zero-dim 𝒦 cells.
For each prime P of I_K (minAssGTZ over ℚ): rank of A_K mod P (8x8 / 7x7 / ... minors), consistency, and the full fibre
ideal P + {all P2,P3 coefficients on L = K ⊕ <v_i + σ_i>} (σ_i = Σ_{c∉S} s_i_c f_c), std over ℚ -> unit or not.
On rank-8 primes this is literally 'σ solved, remaining equations pushed down to K' (σ is a unique Q[a]/P-point);
on rank-drop primes the remaining σ freedom is kept as variables. args: tout; reads r10/kzero_Q.jsonl; env ONLY"""
import json, sys, subprocess, os, time
sys.path.insert(0, ".")
from cell_solve import P_string
tout = int(sys.argv[1]); p, q, m, k = 3, 5, 12, 4
V = [[1] * 5 + [-1] * 5 + [0] * 5, [0] * 5 + [1] * 5 + [-1] * 5]
def script(S, gb):
    names, rows = [], []
    for b, s in enumerate(S):
        row = ["0"] * m; row[s] = "1"
        for c in range(s + 1, m):
            if c in S: continue
            nm = f"a{b}_{c}"; names.append(nm); row[c] = nm
        rows.append(row)
    comp = [c for c in range(m) if c not in S]
    sv = [[f"s{i}_{c}" for c in comp] for i in range(2)]
    coord = []
    for c in range(m):
        terms = [f"({rows[b][c]})*x({b+1})" for b in range(k) if rows[b][c] != "0"]
        for i in range(2):
            if c in comp: terms.append(f"s{i}_{c}*x({5+i})")
        coord.append("+".join(terms) or "0")
    tmap = []
    for i in range(p):
        for j in range(q):
            base = coord[4 * i + j] if j < 4 else "-(" + "+".join(f"({coord[4*i+jj]})" for jj in range(4)) + ")"
            extra = "+".join(f"({V[ii][i*q+j]})*x({5+ii})" for ii in range(2) if V[ii][i*q+j])
            tmap.append(f"{base}+{extra}" if extra else base)
    Ps = ";\n".join(f"poly P{kk} = {P_string(p, q, kk)}" for kk in (2, 3))
    av = ",".join(names + sv[0] + sv[1])
    # A_K rows from σ_0 (identical structure for σ_1): coefficients of x(b)x(5) in P2 and x(b)x(b')x(5) in P3
    arows = [("P2", f"x({b})*x(5)") for b in range(1, 5)] + [("P3", f"x({b})*x({bb})*x(5)") for b in range(1, 5) for bb in range(b, 5)]
    aget = "\n".join(f"e = jet(subst(coeffs(coeffs(coeffs(f(P{pp[1]}), x(1)),x(2)),x(3))[1,1],x(1),0),0);" for pp in [] )
    s = f"""ring T = 0,(t(1..15)),dp;
{Ps};
ring R = 0,(x(1..6),{av}),dp;
map f = T,{",".join(tmap)};
poly F2 = f(P2); poly F3 = f(P3);
ideal I; ideal IKR; matrix C; int i; int j;
C = coef(subst(F2,x(5),0,x(6),0), x(1)*x(2)*x(3)*x(4)); for (i = 1; i <= ncols(C); i++) {{ IKR = IKR + C[2, i]; }}
C = coef(subst(F3,x(5),0,x(6),0), x(1)*x(2)*x(3)*x(4)); for (i = 1; i <= ncols(C); i++) {{ IKR = IKR + C[2, i]; }}
C = coef(F2, x(1)*x(2)*x(3)*x(4)*x(5)*x(6)); for (i = 1; i <= ncols(C); i++) {{ I = I + C[2, i]; }}
C = coef(F3, x(1)*x(2)*x(3)*x(4)*x(5)*x(6)); for (i = 1; i <= ncols(C); i++) {{ I = I + C[2, i]; }}
list ms = {",".join(mm for _,mm in arows)};
matrix A[14][8]; matrix bb[14][1];
for (i = 1; i <= 14; i++) {{
  poly g; if (i <= 4) {{ g = F2; }} else {{ g = F3; }}
  C = coef(g, x(1)*x(2)*x(3)*x(4)*x(5)*x(6)); poly e = 0;
  for (j = 1; j <= ncols(C); j++) {{ if (C[1, j] == ms[i]) {{ e = C[2, j]; }} }}
  {"".join(f"A[i,{n+1}] = diff(e, {sv[0][n]}); " for n in range(8))}
  bb[i,1] = subst(e, {", ".join(f"{x}, 0" for x in sv[0])});
  kill g; kill e;
}}
ring Q = 0,({av}),dp;
ideal I = imap(R, I); matrix A = imap(R, A); matrix bb = imap(R, bb);
ideal IK = imap(R, IKR) + ideal({gb});
LIB "primdec.lib";
list PR = minAssGTZ(IK);
write(":a OUTF", "nprimes " + string(size(PR)));
for (i = 1; i <= size(PR); i++) {{
  ideal Pi = std(PR[i]);
  if (dim(Pi) != 16) {{ write(":a OUTF", "prime " + string(i) + " skip dim " + string(dim(Pi) - 16)); }}
  else {{
  option(redSB); ideal G = std(Pi + I);
  write(":a OUTF", "prime " + string(i) + " fibre_unit=" + string(G[1]==1) + " fibre_dim=" + string(dim(G)));
  ring Z = 0,({av},z(1..9)),dp;
  ideal Pz = imap(Q, Pi); matrix Az = imap(Q, A); matrix bz = imap(Q, bb);
  matrix zz[8][1] = z(1..8); matrix ker = Az * zz; matrix kerb = Az * zz + bz * z(9);
  int r = 8 - (dim(std(Pz + ideal(ker))) - 17); int rc = 9 - (dim(std(Pz + ideal(kerb))) - 16);
  setring Q;
  write(":a OUTF", "prime " + string(i) + " rankA=" + string(r) + " rank[A|b0]=" + string(rc) + " P=" + string(PR[i]));
  kill G; kill Z;
  }}
  kill Pi;
}}
quit;
"""
    return s
import random
cells = json.loads(os.environ["CELLS"])   # [[S, d], ...]
random.seed(int(os.environ.get("SEED", "10")))
for S, d in cells:
    names = [f"a{b}_{c}" for b, s0 in enumerate(S) for c in range(s0 + 1, m) if c not in S]
    for j in (range(1, d + 1) if names else [0]):
        forms = ["+".join(f"({random.randint(-5,5)})*{nm}" for nm in names) + f"+({random.randint(-7,7)})" for _ in range(j)]
        tag = "-".join(map(str, S)) + f"_j{j}"; fn = f"r10/sl_{tag}.sing"; outf = f"r10/sl_{tag}.out"
        open(fn, "w").write(script(S, ",".join(forms) or "0").replace("OUTF", outf))
        if os.path.exists(outf): os.remove(outf)
        t0 = time.time()
        try:
            o = subprocess.run(["bash", "-c", f"ulimit -v 3500000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout)
            err = o.stdout[-300:] if "error" in o.stdout or "?" in o.stdout else ""
        except subprocess.TimeoutExpired:
            subprocess.run(["pkill", "-f", fn]); err = "TIMEOUT"
        body = open(outf).read() if os.path.exists(outf) else ""
        print(json.dumps({"S": S, "j": j, "forms": forms, "sec": round(time.time() - t0, 1), "err": err, "out": body}), flush=True)
