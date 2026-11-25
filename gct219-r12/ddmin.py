# Shrink the generators of a unit cell system to a 1-minimal subset that is still unit mod p,
# testing membership with the msolve fork (-g 2). A timeout counts as "not unit" (conservative).
import sys, os, subprocess, json, tempfile, time
MS = os.environ.get('MSOLVE', '/home/user/msolve/msolve'); CAP = float(os.environ.get('CAP', '20'))
def read_ms(path):
    L = open(path).read().split('\n'); vs, p = L[0], L[1]
    gens = [g.strip().rstrip(',') for g in ' '.join(L[2:]).replace(',\n', '\n').split(',') if g.strip()]
    return vs, p, gens
tests = 0
def unit(vs, p, gens):
    global tests; tests += 1
    with tempfile.TemporaryDirectory() as d:
        f, o = f'{d}/i.ms', f'{d}/o.txt'
        open(f, 'w').write(vs + '\n' + p + '\n' + ',\n'.join(gens) + '\n')
        try:
            subprocess.run(['bash', '-c', f'ulimit -v 7000000; {MS} -g 2 -t 1 --random-seed 42 -f {f} -o {o}'],
                           capture_output=True, timeout=CAP)
        except subprocess.TimeoutExpired:
            return False
        b = open(o).read().replace(' ', '').replace('\n', '') if os.path.exists(o) else ''
        return b.endswith('[1]:')
def ddmin(vs, p, G):
    n = 2
    while len(G) >= 2:
        k = len(G); chunk = (k + n - 1) // n; reduced = False
        for i in range(0, k, chunk):
            rest = G[:i] + G[i + chunk:]
            if rest and unit(vs, p, rest):
                G = rest; n = max(n - 1, 2); reduced = True; break
        if not reduced:
            if n >= k: break
            n = min(k, 2 * n)
    return G
if __name__ == '__main__':
    path = sys.argv[1]; vs, p, G = read_ms(path); t = time.time()
    assert unit(vs, p, G), 'not unit to begin with'
    # order: by length (shorter first), then shortest unit prefix by bisection
    G = sorted(G, key=len); lo, hi = 1, len(G)
    while lo < hi:
        m = (lo + hi) // 2
        if unit(vs, p, G[:m]): hi = m
        else: lo = m + 1
    pre = lo; M = ddmin(vs, p, G[:pre])
    out = path.replace('.ms', '.min.ms'); open(out, 'w').write(vs + '\n' + p + '\n' + ',\n'.join(M) + '\n')
    print(json.dumps({'cell': os.path.basename(path), 'gens': len(G), 'prefix': pre, 'support': len(M),
                      'tests': tests, 'sec': round(time.time() - t, 1)}), flush=True)
