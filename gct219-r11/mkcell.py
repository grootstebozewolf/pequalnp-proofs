# Build the Singular ideal of a 4x5 d7 cell (P2..P4 coefficients + colex minors deg<=DEG), as in minorsw.py.
import sys, json
sys.path.insert(0, '/home/user/gct219-rounds/gct219')
from schubert import cells
from cell_solve import script
from minorsw import setup, extra
def cell_script(p,q,d,S,char,deg,tail):
    fr = None
    for S2, f2, u in cells(p,q,d):
        if tuple(S2)==tuple(S): fr=f2; break
    H,OM = setup(p,q,'exp')
    ex = extra(S,fr,p,q,H,OM,deg)
    s = script(p,q,d,S,fr,char).replace("I = simplify(I, 2);", "".join(f"I = I + ({e});\n" for e in ex) + "I = simplify(I, 2);")
    # cut after J is built
    i = s.index("int t0 = timer;")
    return s[:i] + tail, fr, len(ex)
if __name__=="__main__":
    S=tuple(map(int,sys.argv[1].split(','))); char=int(sys.argv[2]); deg=int(sys.argv[3]); out=sys.argv[4]
    tail=open(sys.argv[5]).read()
    s,fr,ne=cell_script(4,5,7,S,char,deg,tail); open(out,'w').write(s)
    print(json.dumps({"free":fr,"minors":ne}))
