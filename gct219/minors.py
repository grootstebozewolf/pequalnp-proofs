"""Round 5 item 3: add Plücker-minor hypotheses p_K(L) = 0 of degree <= 2 (|K ∩ S| >= d-2) for every K whose
G-orbit minimum is lex-smaller than the cell's pivot set I (valid for the canonical, lex-least representative).
Then Singular std (char given). Usage: minors.py p q d char tout jobs"""
import itertools, sys, json, subprocess, os, time, numpy as np
from concurrent.futures import ThreadPoolExecutor
from schubert import cells
from cell_solve import script
p, q, d, char, tout, jobs = map(int, sys.argv[1:7]) if __name__ == "__main__" else map(int, sys.argv[1:4] + ["0", "0", "0"]); n = p * q
perms = []
for rp in itertools.permutations(range(p)):
    for cp in itertools.permutations(range(q)):
        perms.append([rp[c // q] * q + cp[c % q] for c in range(n)])
H = np.array(perms, dtype=np.int16)
def orbit_min(K):
    img = np.sort(H[:, list(K)], axis=1)
    return tuple(int(x) for x in min(map(tuple, img)))
def entries(S, free):
    entry = {}
    for b, fr in enumerate(free):
        for c in fr[:-1]: entry[(b, c)] = f"a{b}_{c}"
        entry[(b, fr[-1])] = "(-1" + "".join(f"-a{b}_{c}" for c in fr[:-1]) + ")"
    B = [["0"] * n for _ in S]
    for b, s in enumerate(S):
        B[b][s] = "1"
        for c in free[b]: B[b][c] = entry[(b, c)]
    return B
def extra_polys(S, free):
    I = tuple(S); B = entries(S, free); Sset = set(S); nonS = [c for c in range(n) if c not in Sset]
    polys = []
    for m in (1, 2):
        for drop in itertools.combinations(range(d), m):
            for add in itertools.combinations(nonS, m):
                K = sorted((Sset - {S[b] for b in drop}) | set(add))
                if orbit_min(K) < I:
                    # p_K = ± det of B restricted to rows `drop`, columns `add`
                    if m == 1: poly = B[drop[0]][add[0]]
                    else:
                        (b1, b2), (c1, c2) = drop, add
                        poly = f"({B[b1][c1]})*({B[b2][c2]})-({B[b1][c2]})*({B[b2][c1]})"
                    if poly not in ("0",): polys.append(poly)
    return polys
def run(a):
    S, fr, u = a
    ex = extra_polys(S, fr)
    s = script(p, q, d, S, fr, char)
    s = s.replace("I = simplify(I, 2);", "".join(f"I = I + ({e});\n" for e in ex) + "I = simplify(I, 2);")
    fn = f"cells/mn_{p}x{q}_d{d}_" + "-".join(map(str, S)) + f"_{char}.sing"; open(fn, "w").write(s)
    t0 = time.time()
    try:
        out = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True, timeout=tout).stdout
        res = [l for l in out.splitlines() if l.startswith("RESULT")]
        r = res[0] if res and "?" not in out else "ERROR " + out[-120:]
    except subprocess.TimeoutExpired:
        r = "TIMEOUT"
    os.remove(fn)
    return {"S": list(S), "unknowns": u, "minors": len(ex), "res": r, "sec": round(time.time() - t0, 1)}
if __name__ == "__main__":
    T = json.load(open(f"tally5_{p}x{q}_d{d}.json"))
    need = {tuple(S) for S, u, st in T["orbit_cells"] if st != "emptyQ"}
    todo = [(S, fr, u) for S, fr, u in cells(p, q, d) if tuple(S) in need]
    nm = {tuple(S): len(extra_polys(S, fr)) for S, fr, u in todo}
    todo.sort(key=lambda a: (a[2], -nm[tuple(a[0])]))
    print("todo", len(todo), "minor counts", [nm[tuple(a[0])] for a in todo], flush=True)
    with ThreadPoolExecutor(jobs) as ex, open(f"minors_{p}x{q}_d{d}_c{char}.jsonl", "w") as fh:
        for r in ex.map(run, todo):
            fh.write(json.dumps(r) + "\n"); fh.flush(); print(r, flush=True)
