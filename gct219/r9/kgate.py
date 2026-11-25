"""Task 2 GATE: K-variety  𝒦 = {K in Gr(4, R°) : K level},  R° = {3x5 matrices with every row sum 0} (dim 12).
Coordinates of R°: f_(i,j) = e_(i,j) - e_(i,4), j=0..3 (12 coords, index c = 4i+j). Schubert cells of Gr(k,12) = RREF pivot
sets; level <=> all x-coefficients of P2, P3 vanish (P1 = 0 on R°). Per cell: Singular std mod p, Krull dim (-1 = empty).
args: k char tout jobs"""
import itertools, sys, subprocess, json, os, time
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, ".")
from cell_solve import P_string
k, char, tout, jobs = map(int, sys.argv[1:5]); p, q, m = 3, 5, 12
def cell(S):
    names, rows = [], []
    for b, s in enumerate(S):
        row = ["0"] * m; row[s] = "1"
        for c in range(s + 1, m):
            if c in S: continue
            nm = f"a{b}_{c}"; names.append(nm); row[c] = nm
        rows.append(row)
    # t in R°: coordinate c of t = sum_b x_b rows[b][c]; t_(i,4) = -sum_j t_(i,j)
    coord = ["+".join(f"({rows[b][c]})*x({b+1})" for b in range(k) if rows[b][c] != "0") or "0" for c in range(m)]
    tmap = []
    for i in range(p):
        for j in range(q):
            tmap.append(coord[4 * i + j] if j < 4 else "-(" + "+".join(f"({coord[4*i+jj]})" for jj in range(4)) + ")")
    av = ",".join(names) if names else "dummy"
    xs = "*".join(f"x({i+1})" for i in range(k))
    Ps = ";\n".join(f"poly P{kk} = {P_string(p, q, kk)}" for kk in (2, 3))
    co = "\n".join(f"C = coef(f(P{kk}), {xs}); for (i = 1; i <= ncols(C); i++) {{ I = I + C[2, i]; }}" for kk in (2, 3))
    s = f"""ring T = {char},(t(1..15)),dp;
{Ps};
ring R = {char},(x(1..{k}),{av}),dp;
map f = T,{",".join(tmap)};
ideal I; matrix C; int i;
{co}
I = simplify(I, 2);
ring A = {char},({av}),dp;
ideal J = imap(R, I); option(redSB); ideal G = std(J);
print("RES unit=" + string(G[1]==1) + " dim=" + string(dim(G)));
quit;
"""
    fn = f"cells/kg_{k}_{'-'.join(map(str, S))}.sing"; open(fn, "w").write(s); t0 = time.time()
    try:
        out = subprocess.run(["bash", "-c", f"ulimit -v 3000000; Singular -q {fn}"], capture_output=True, text=True, timeout=tout).stdout
        r = [l for l in out.splitlines() if l.startswith("RES")]; r = r[0][4:] if r else ("OOM" if "memory" in out else "ERR " + out[-80:])
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", fn]); r = "TIMEOUT"
    os.remove(fn)
    return {"S": list(S), "unknowns": len(names), "res": r, "sec": round(time.time() - t0, 1)}
HH = [[rp[c // 4] * 4 + cp[c % 4] for c in range(m)] for rp in itertools.permutations(range(3)) for cp in itertools.permutations(range(4))]
def lexmin(S): return all(tuple(S) <= tuple(sorted(h[c] for c in S)) for h in HH)
# orbit reduction under S3 x S4 (rows, columns 0..3), which permutes the f-coordinates: choose g with lex-least pivot set of gK;
# then I = piv(gK) <= piv(hgK) <= sorted(hI) for all h, so only lex-orbit-minimal pivot sets are needed (no extra minors used).
done = {}
if os.path.exists(f"r9/kgate_k{k}_c{char}.jsonl"):
    for l in open(f"r9/kgate_k{k}_c{char}.jsonl"):
        r = json.loads(l)
        if r["res"] != "TIMEOUT": done[tuple(r["S"])] = r
todo = sorted(itertools.combinations(range(m), k), key=lambda S: sum(m - 1 - s for s in S) - k * (k - 1) // 2)
todo = [S for S in todo if lexmin(S)] if not os.environ.get("ONLY") else [tuple(json.loads(os.environ["ONLY"]))]
print('orbit-min cells', len(todo), 'already done', sum(1 for S in todo if S in done), flush=True)
todo = [S for S in todo if S not in done]
with ThreadPoolExecutor(jobs) as ex, open(f"r9/kgate_k{k}_c{char}.jsonl", "a") as fh:
    for r in ex.map(cell, todo):
        fh.write(json.dumps(r) + "\n"); fh.flush()
