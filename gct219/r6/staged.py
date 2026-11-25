"""Item 3: staged Groebner on the open orbit-minimal 4x5 d7 cells, mod p, ulimit'd.
Stage A: P2 coefficients + minors deg<=2; B: + P3 coefficients + minors deg 3 (if enabled); C: + P4 coefficients.
Block order: variables of basis row b form block A_b (a0_* < ... ), dp within (we use the cell's natural order).
Records Krull dim after each stage. Usage: staged.py char tout jobs deg3(0/1)"""
import sys, json, subprocess, os, time, itertools
sys.argv, args = ["x", "4", "5", "7"], sys.argv[1:]
sys.path.insert(0, ".")
import minors as M
from schubert import cells
from cell_solve import script
char, tout, jobs, deg3 = map(int, args)
p, q, d, n = 4, 5, 7, 20
def minors3(S, fr):
    I = tuple(S); B = M.entries(S, fr); Sset = set(S); nonS = [c for c in range(n) if c not in Sset]; out = []
    for drop in itertools.combinations(range(d), 3):
        for add in itertools.combinations(nonS, 3):
            K = sorted((Sset - {S[b] for b in drop}) | set(add))
            if M.orbit_min(K) < I:
                m = [[B[b][c] for c in add] for b in drop]
                terms = []
                for perm in itertools.permutations(range(3)):
                    sgn = (-1) ** sum(1 for i in range(3) for j in range(i + 1, 3) if perm[i] > perm[j])
                    if any(m[i][perm[i]] == "0" for i in range(3)): continue
                    terms.append(("+" if sgn > 0 else "-") + "*".join(f"({m[i][perm[i]]})" for i in range(3)))
                if terms: out.append("".join(terms))
    return out
def run(cell):
    S, fr, u = cell
    m12 = M.extra_polys(S, fr); m3 = minors3(S, fr) if deg3 else []
    s = script(p, q, d, S, fr, char)
    head = s[:s.index("ideal I; matrix C; int i;")]
    avars = s[s.index("ring A = ") :].split("(")[1].split(")")[0]
    xs = "*".join(f"x({i+1})" for i in range(d))
    body = "matrix C; int i; ideal I2; ideal I3; ideal I4; ideal MA; ideal MB;\n"
    for e in m12: body += f"MA = MA + ({e});\n"
    for e in m3: body += f"MB = MB + ({e});\n"
    for k in (2, 3):
        body += f"C = coef(f(P{k}), {xs}); for (i = 1; i <= ncols(C); i++) {{ I{k} = I{k} + C[2, i]; }}\n"
    body += f"""ring A = {char},({avars}),dp; option(redSB);
ideal G = std(imap(R, I2) + imap(R, MA)); print("STAGE A dim=" + string(dim(G)) + " unit=" + string(G[1]==1));
if (G[1] != 1) {{ G = std(G + imap(R, I3) + imap(R, MB)); print("STAGE B dim=" + string(dim(G)) + " unit=" + string(G[1]==1)); }}
if (G[1] != 1) {{ setring R; C = coef(f(P4), {xs}); for (i = 1; i <= ncols(C); i++) {{ I4 = I4 + C[2, i]; }} setring A;
  G = std(G + imap(R, I4)); print("STAGE C dim=" + string(dim(G)) + " unit=" + string(G[1]==1)); }}
quit;
"""
    fn = f"cells/st_{char}_" + "-".join(map(str, S)) + ".sing"; open(fn, "w").write(head + body)
    t0 = time.time()
    try:
        out = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True, timeout=tout).stdout
        st = [l for l in out.splitlines() if l.startswith("STAGE")]
        err = "no more memory" in out or "?" in out
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        st = [l for l in out.splitlines() if l.startswith("STAGE")] + ["TIMEOUT"]; err = False
    os.remove(fn)
    return {"S": list(S), "unknowns": u, "m12": len(m12), "m3": len(m3), "stages": st + (["ERROR/OOM"] if err else []), "sec": round(time.time() - t0, 1)}
if __name__ == "__main__":
    T = json.load(open("tally5_4x5_d7.json"))
    closedQ = {tuple(S) for S, u, st in T["orbit_cells"] if st == "emptyQ"}
    for l in open("minors_4x5_d7_c0.jsonl"):
        r = json.loads(l)
        if "unit=1" in r["res"]: closedQ.add(tuple(r["S"]))
    todo = sorted([c for c in cells(p, q, d) if tuple(c[0]) in {tuple(S) for S, u, st in T["orbit_cells"]} and tuple(c[0]) not in closedQ], key=lambda c: c[2])
    print("open", len(todo), flush=True)
    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(jobs) as ex, open(f"r6/staged_c{char}_d3{deg3}.jsonl", "w") as fh:
        for r in ex.map(run, todo):
            fh.write(json.dumps(r) + "\n"); fh.flush(); print(r, flush=True)
