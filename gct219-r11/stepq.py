# Rung step 2: constant-pivot substitution over Q, then std over Q, smallest reduced cell first.
import json, sys, subprocess, time, os
sys.path.insert(0,'.')
from mkcell import cell_script
from concurrent.futures import ThreadPoolExecutor
rows=[json.loads(l) for l in open('batch_clp.log')]
def left(r):
    c=r.get('clp','')
    return int(c.split('unknowns_left=')[1].split()[0]) if 'unknowns_left=' in c else 999
todo=sorted(rows,key=left)
todo=[r for r in todo if left(r)<999]
if len(sys.argv)>1: todo=todo[:int(sys.argv[1])]
tail=open('clp_tail.sing').read()
STD='option(redSB);\nint t0=rtimer;\nideal G = std(K);\nprint("RESULT stdQ unit=" + string(G[1]==1) + " dim=" + string(dim(G)) + " sec=" + string(rtimer-t0));\nquit;\n'
def run(r):
    S=tuple(r['S']); tag='-'.join(map(str,S))
    t=tail.replace('OUTFILE',f'cells/{tag}_q.txt').replace('quit;\n','')+STD
    sc,_,_=cell_script(4,5,7,S,0,3,t); fn=f'cells/{tag}_q.sing'; open(fn,'w').write(sc)
    t0=time.time(); out={'S':list(S),'status9':r['status9'],'unknowns':r['unknowns'],'reduced':left(r)}
    try:
        o=subprocess.run(['bash','-c',f'ulimit -v 6500000; Singular -q {fn}'],capture_output=True,text=True,timeout=1000).stdout
        out['res']=[l for l in o.splitlines() if l.startswith('RESULT')] or ['ERR '+o[-150:]]
    except subprocess.TimeoutExpired: out['res']=['TIMEOUT']
    out['sec']=round(time.time()-t0,1); return out
with ThreadPoolExecutor(2) as ex, open('stepq.jsonl','a') as fh:
    for o in ex.map(run,todo):
        fh.write(json.dumps(o)+'\n'); fh.flush(); print(json.dumps(o),flush=True)
