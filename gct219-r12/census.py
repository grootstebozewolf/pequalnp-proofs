# Round 12 census: constant-pivot substitution mod 32003 (Singular), then the fork's msolve
# (allocation-checked, exit 75 on OOM) on every 4x5 d7 cell that is O, M_p or T in r9/status9.json.
import json, sys, subprocess, time, os
sys.path.insert(0, '../gct219-r11')
from mkcell import cell_script
from concurrent.futures import ThreadPoolExecutor
MS = os.environ.get('MSOLVE', '/home/user/msolve/msolve')
P = int(os.environ.get('PRIME', '32003'))
st = json.load(open('/home/user/gct219-rounds/gct219/r9/status9.json'))
todo = sorted((u, tuple(map(int, k[4:].split(','))), s) for k, (u, s, why) in st.items()
              if k.startswith('4x5:') and s in ('O', 'M_p', 'T'))
tail = open('../gct219-r11/clp_tail.sing').read()
os.makedirs('cells', exist_ok=True)
def ms_result(path):
    if not os.path.exists(path): return None
    t = open(path).read().replace(' ', '').replace('\n', '')
    return 'unit' if t.endswith('[1]:') or t in ('[1]:', '[1]') or '[1]:' == t[-4:] or t.endswith('[1]') else t
def run(a):
    u, S, s = a; tag = '-'.join(map(str, S)); res = {'S': S, 'status9': s, 'unknowns': u}
    ms = f'cells/{tag}_{P}.ms'
    if not os.path.exists(ms):
        sc, _, ne = cell_script(4, 5, 7, S, P, 3, tail.replace('OUTFILE', f'cells/{tag}_{P}.txt'))
        open(f'cells/{tag}_{P}.sing', 'w').write(sc); t = time.time()
        try:
            o = subprocess.run(['bash', '-c', f'ulimit -v 6000000; Singular -q cells/{tag}_{P}.sing'],
                               capture_output=True, text=True, timeout=900).stdout
            r = [l for l in o.splitlines() if l.startswith('RESULT')]; res['clp'] = r[0] if r else 'ERR ' + o[-200:]
        except subprocess.TimeoutExpired:
            res['clp'] = 'TIMEOUT'; return res
        res['clp_sec'] = round(time.time() - t, 1)
        L = open(f'cells/{tag}_{P}.txt').read().split('\n')
        open(ms, 'w').write(L[0] + f'\n{P}\n' + ',\n'.join(x for x in L[1:] if x.strip()) + '\n')
    t = time.time(); out = f'cells/{tag}_{P}.out'
    try:
        r = subprocess.run(['bash', '-c', f'ulimit -v 7000000; {MS} -g 2 -t 2 --random-seed 42 -f {ms} -o {out}'],
                           capture_output=True, text=True, timeout=1800)
        res['ms_rc'] = r.returncode; res['ms_err'] = r.stderr[-200:]
        body = open(out).read() if os.path.exists(out) else ''
        res['msolve'] = ('unit' if body.strip().replace(' ', '').replace('\n', '').endswith('[1]:') or
                         body.replace(' ', '').replace('\n', '') in ('[1]:', '[1]', '[1];')
                         else ('nonunit' if body.strip() else ('oom' if r.returncode == 75 else 'fail')))
        res['ms_head'] = body[:120]
    except subprocess.TimeoutExpired:
        res['msolve'] = 'TIMEOUT'
    res['ms_sec'] = round(time.time() - t, 1)
    return res
if __name__ == '__main__':
    if len(sys.argv) > 1: todo = todo[:int(sys.argv[1])]
    with ThreadPoolExecutor(2) as ex, open(f'census_{P}.jsonl', 'a') as fh:
        for r in ex.map(run, todo):
            fh.write(json.dumps(r) + '\n'); fh.flush(); print(json.dumps(r), flush=True)
