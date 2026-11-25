"""Minor hypotheses under the WEIGHT criterion (omega(c) = 2^c, or c for 'lin'): with (g, I) minimising omega-weight
jointly over all g in G and charts I of gL, every K with min_h omega(hK) < omega(I) has p_K(gL) = 0
(else hK would be a lighter chart of hgL). We add those of degree <= DEG (|K \\ I| <= DEG).
Library + CLI: minorsw.py p q d mode deg char tout jobs"""
import itertools, sys, json, subprocess, os, time, numpy as np
from schubert import cells
from cell_solve import script
def setup(p, q, mode):
    n = p * q
    H = np.array([[rp[c // q] * q + cp[c % q] for c in range(n)] for rp in itertools.permutations(range(p))
                  for cp in itertools.permutations(range(q))], dtype=np.int64)
    OM = np.array([(2 ** c if mode == "exp" else c) for c in range(n)], dtype=np.int64)
    return H, OM
def entries(S, free, n):
    entry = {}
    for b, fr in enumerate(free):
        for c in fr[:-1]: entry[(b, c)] = f"a{b}_{c}"
        entry[(b, fr[-1])] = "(-1" + "".join(f"-a{b}_{c}" for c in fr[:-1]) + ")"
    B = [["0"] * n for _ in S]
    for b, s in enumerate(S):
        B[b][s] = "1"
        for c in free[b]: B[b][c] = entry[(b, c)]
    return B
def det_str(m):
    k = len(m); terms = []
    for perm in itertools.permutations(range(k)):
        if any(m[i][perm[i]] == "0" for i in range(k)): continue
        sgn = (-1) ** sum(1 for i in range(k) for j in range(i + 1, k) if perm[i] > perm[j])
        terms.append(("+" if sgn > 0 else "-") + "*".join(f"({m[i][perm[i]]})" for i in range(k)))
    s = "".join(terms)
    return s[1:] if s.startswith("+") else s
def extra(S, free, p, q, H, OM, deg):
    n = p * q; d = len(S); B = entries(S, free, n); Sset = set(S); nonS = [c for c in range(n) if c not in Sset]
    wI = int(OM[list(S)].sum()); out = []
    for m in range(1, deg + 1):
        for drop in itertools.combinations(range(d), m):
            keepS = [s for b, s in enumerate(S) if b not in drop]
            for add in itertools.combinations(nonS, m):
                K = keepS + list(add)
                if int(OM[H[:, K]].sum(axis=1).min()) < wI:
                    e = det_str([[B[b][c] for c in add] for b in drop])
                    if e: out.append(e)
    return out
def run(a):
    p, q, d, S, fr, u, char, tout, mode, deg = a
    H, OM = setup(p, q, mode)
    ex = extra(S, fr, p, q, H, OM, deg)
    s = script(p, q, d, S, fr, char).replace("I = simplify(I, 2);", "".join(f"I = I + ({e});\n" for e in ex) + "I = simplify(I, 2);")
    fn = f"cells/mw_{p}x{q}_d{d}_" + "-".join(map(str, S)) + f"_{char}_{deg}.sing"; open(fn, "w").write(s)
    t0 = time.time()
    try:
        out = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True, timeout=tout).stdout
        res = [l for l in out.splitlines() if l.startswith("RESULT")]
        r = res[0] if res and "?" not in out else ("OOM" if "no more memory" in out else "ERROR " + out[-120:])
    except subprocess.TimeoutExpired:
        r = "TIMEOUT"
    os.remove(fn)
    return {"S": list(S), "unknowns": u, "minors": len(ex), "deg": deg, "char": char, "res": r, "sec": round(time.time() - t0, 1)}
if __name__ == "__main__":
    p, q, d = map(int, sys.argv[1:4]); mode = sys.argv[4]; deg, char, tout, jobs = map(int, sys.argv[5:9])
    W = json.load(open(f"r6/wstatus_{p}x{q}_d{d}.json"))
    need = {tuple(S) for S, u, st in W if st not in ("emptyQ", "FK")}
    todo = sorted([(p, q, d, S, fr, u, char, tout, mode, deg) for S, fr, u in cells(p, q, d) if tuple(S) in need], key=lambda a: a[5])
    print("todo", len(todo), flush=True)
    from concurrent.futures import ProcessPoolExecutor
    with ProcessPoolExecutor(jobs) as ex, open(f"r6/mw_{mode}_{p}x{q}_d{d}_deg{deg}_c{char}.jsonl", "w") as fh:
        for r in ex.map(run, todo):
            fh.write(json.dumps(r) + "\n"); fh.flush(); print(r, flush=True)
