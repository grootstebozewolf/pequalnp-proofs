"""Rebuilt status tables (fixes r7/table7 'not run'=2 bug: those are OOM). Status classes:
 Q-cert  = sympy-verified certificate (r7/cert_*_0.txt or _r8.txt) or R6 exact closure (FK / emptyQ via std over Q)
 Q-trusted = Singular modStd(J,1) only (no exported certificate)
 open    = mod-p only / timeout / OOM"""
import json, glob, collections, os
def cls(st):
    if "modStd" in st: return "Q-trusted"
    if st.startswith(("emptyQ", "FK")): return "Q"
    return "open"
T = json.load(open("r7/table7_4x5_d7.json"))
for f in glob.glob("r7/cert_*_r8.txt"):
    k = f.split("cert_")[1].rsplit("_", 1)[0].replace("-", ",")
    if k in T: T[k][1] = "emptyQ(R8 cert, sympy-verified)"
for l in open("r8/ms457_status.txt"):
    k, v = l.split()
    if v == "1" and cls(T[k][1]) == "open": T[k][1] = "modp(R8 msolve, p=32003 and 65521)"
bins = [(0, 50), (50, 55), (55, 60), (60, 65), (65, 70), (70, 75), (75, 85)]
print("4x5 d7 colex (80 reps)\n| unknowns | reps | closed Q (certified/exact) | closed Q-trusted (modStd) | open: mod-p unit (msolve) | open: no result |\n|---|---|---|---|---|---|")
tot = collections.Counter()
for a, b in bins:
    c = collections.Counter(("modp" if st.startswith("modp") else cls(st)) for u, st in T.values() if a <= u < b); tot += c
    print(f"| {a}–{b-1} | {sum(c.values())} | {c['Q']} | {c['Q-trusted']} | {c['modp']} | {c['open']} |")
print(f"| all | {sum(tot.values())} | {tot['Q']} | {tot['Q-trusted']} | {tot['modp']} | {tot['open']} |")
print(collections.Counter(st for u, st in T.values()))
json.dump(T, open("r8/table8_4x5_d7.json", "w"))
