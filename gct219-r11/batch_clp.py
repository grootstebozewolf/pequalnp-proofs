import json, sys, subprocess, time, os
sys.path.insert(0,'.')
from mkcell import cell_script
from concurrent.futures import ThreadPoolExecutor
st=json.load(open('/home/user/gct219-rounds/gct219/r9/status9.json'))
skip={(1,2,5,7,10,11,15),(2,3,5,6,7,10,11)}
todo=[]
for k,(u,s,why) in st.items():
    if k.startswith('4x5:') and s in ('O','M_p'):
        S=tuple(map(int,k[4:].split(',')))
        if S not in skip: todo.append((u,S,s))
todo.sort()
tail=open('clp_tail.sing').read()
def run(a):
    u,S,s=a; tag='-'.join(map(str,S)); os.makedirs('cells',exist_ok=True)
    sc,_,ne=cell_script(4,5,7,S,32003,3,tail.replace('OUTFILE',f'cells/{tag}.txt')); fn=f'cells/{tag}.sing'; open(fn,'w').write(sc)
    t=time.time(); res={'S':S,'status9':s,'unknowns':u,'minors':ne}
    try:
        o=subprocess.run(['bash','-c',f'ulimit -v 4000000; Singular -q {fn}'],capture_output=True,text=True,timeout=600).stdout
        r=[l for l in o.splitlines() if l.startswith('RESULT')]; res['clp']=r[0] if r else 'ERR '+o[-200:]
    except subprocess.TimeoutExpired: res['clp']='TIMEOUT'; return res
    res['clp_sec']=round(time.time()-t,1)
    L=open(f'cells/{tag}.txt').read().split('\n'); open(f'cells/{tag}.ms','w').write(L[0]+'\n32003\n'+',\n'.join(x for x in L[1:] if x.strip())+'\n')
    t=time.time()
    try:
        subprocess.run(['bash','-c',f'ulimit -v 4000000; msolve -g 2 -t 1 -f cells/{tag}.ms -o cells/{tag}.out'],capture_output=True,text=True,timeout=300)
        out=open(f'cells/{tag}.out').read() if os.path.exists(f'cells/{tag}.out') else ''
        res['msolve']='unit' if 'length of basis:      1 element' in out and '[1]:\n1' in out.replace(' ','') or ('length of basis:      1 element' in out) else ('nonunit' if 'length of basis' in out else 'fail')
    except subprocess.TimeoutExpired: res['msolve']='TIMEOUT'
    res['ms_sec']=round(time.time()-t,1)
    return res
with ThreadPoolExecutor(2) as ex, open('batch_clp.jsonl','w') as fh:
    for r in ex.map(run,todo):
        fh.write(json.dumps(r)+'\n'); fh.flush(); print(json.dumps(r),flush=True)
