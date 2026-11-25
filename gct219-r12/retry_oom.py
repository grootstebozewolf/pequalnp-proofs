# Retry the census cells that ran out of memory at 7 GB, one at a time with a larger cap.
import json, os, subprocess, time, sys
MS = os.environ.get('MSOLVE', '/home/user/msolve/msolve'); P = 32003
MEM = int(os.environ.get('MEMKB', '13000000')); CAP = int(os.environ.get('CAP', '3600'))
rows = [json.loads(l) for l in open(f'census_{P}.jsonl')]
done = set()
if os.path.exists('retry_oom.jsonl'):
    done = {tuple(json.loads(l)['S']) for l in open('retry_oom.jsonl') if l.strip()}
todo = sorted((r for r in rows if r.get('msolve') == 'oom' and tuple(r['S']) not in done), key=lambda r: r['ms_sec'], reverse=True)
for r in todo:
    tag = '-'.join(map(str, r['S'])); ms = f'cells/{tag}_{P}.ms'; out = f'cells/{tag}_{P}.big.out'
    t = time.time(); res = {'S': r['S'], 'status9': r['status9'], 'mem_kb': MEM}
    try:
        p = subprocess.run(['bash', '-c', f'ulimit -v {MEM}; {MS} -g 2 -t 2 --random-seed 42 -f {ms} -o {out}'],
                           capture_output=True, text=True, timeout=CAP)
        b = open(out).read().replace(' ', '').replace('\n', '') if os.path.exists(out) else ''
        res['msolve'] = 'unit' if b.endswith('[1]:') else ('nonunit' if b else ('oom' if p.returncode == 75 else 'fail'))
        res['ms_err'] = p.stderr[-160:]
    except subprocess.TimeoutExpired:
        res['msolve'] = 'TIMEOUT'
    res['ms_sec'] = round(time.time() - t, 1)
    open('retry_oom.jsonl', 'a').write(json.dumps(res) + '\n'); print(json.dumps(res), flush=True)
