"""Task 2 fibre system (3x5, d=6): L = K ⊕ span{v1+σ1, v2+σ2}, K in the 𝒦-cell S (Gr(4,R°), f-coordinates as in kgate.py),
v1 = row0 - row1 (all-ones rows), v2 = row1 - row2 (V_r basis), σ_i = Σ_{c∉S} s_i_c f_c (8+8 = 16 unknowns).
Level <=> all x-coefficients of P2, P3 vanish on L (P1 = 0 on H = V_r ⊕ R°). Singular std mod p; unit => no level L over this cell.
args: char tout S-list-json"""
import sys, json, subprocess, os, time
sys.path.insert(0, ".")
from cell_solve import P_string
char, tout = int(sys.argv[1]), int(sys.argv[2]); NE = int(os.environ.get("NEXTRA", "2")); cellsS = json.loads(sys.argv[3]); p, q, m, k = 3, 5, 12, 4
def run(S):
    names, rows = [], []
    for b, s in enumerate(S):
        row = ["0"] * m; row[s] = "1"
        for c in range(s + 1, m):
            if c in S: continue
            nm = f"a{b}_{c}"; names.append(nm); row[c] = nm
        rows.append(row)
    sig = []
    for i in (1, 2)[2 - NE:]:
        row = ["0"] * m
        for c in range(m):
            if c not in S: nm = f"s{i}_{c}"; names.append(nm); row[c] = nm
        sig.append(row)
    def tvec(row, vr):
        out = []
        for i in range(p):
            for j in range(q):
                base = row[4 * i + j] if j < 4 else "-(" + "+".join(f"({row[4*i+jj]})" for jj in range(4)) + ")"
                out.append(f"({base})+({vr[i]})")
        return out
    zero = [0, 0, 0]
    T = [tvec(r, zero) for r in rows] + ([tvec(sig[0], [1, -1, 0]), tvec(sig[1], [0, 1, -1])] if NE == 2 else [tvec(sig[0], [0, 1, -1])])
    D = 4 + NE
    tmap = ",".join("+".join(f"({T[b][c]})*x({b+1})" for b in range(D)) for c in range(15))
    xs = "*".join(f"x({i+1})" for i in range(D))
    Ps = ";\n".join(f"poly P{kk} = {P_string(p, q, kk)}" for kk in (2, 3))
    co = "\n".join(f"C = coef(f(P{kk}), {xs}); for (i = 1; i <= ncols(C); i++) {{ I = I + C[2, i]; }}" for kk in (2, 3))
    av = ",".join(names)
    s = f"""ring T = {char},(t(1..15)),dp;
{Ps};
ring R = {char},(x(1..{D}),{av}),dp;
map f = T,{tmap};
ideal I; matrix C; int i;
{co}
I = simplify(I, 2);
ring A = {char},({av}),dp;
ideal J = imap(R, I); FIXK option(redSB); ideal G = std(J);
print("RES unit=" + string(G[1]==1) + " dim=" + string(dim(G)));
quit;
"""
    s = s.replace("FIXK", "".join(f"J = subst(J, {nm}, 0); " for nm in names if nm.startswith("a")) if os.environ.get("FIXK") else "")
    fn = f"cells/fb_{'-'.join(map(str, S))}.sing"; open(fn, "w").write(s); t0 = time.time()
    try:
        out = subprocess.run(["bash", "-c", f"ulimit -v 3000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
        r = [l for l in out.splitlines() if l.startswith("RES")]; r = r[0][4:] if r else ("OOM" if "memory" in out else "ERR " + out[-100:])
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", fn]); r = "TIMEOUT"
    os.remove(fn)
    print(json.dumps({"S": S, "unknowns": len(names), "res": r, "sec": round(time.time() - t0, 1)}), flush=True)
for S in cellsS: run(S)
