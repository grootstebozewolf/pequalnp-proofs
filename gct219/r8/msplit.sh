# case split with msolve: v=0 and v invertible (v*yy-1, extra var yy appended last)
s=$1; v=$2
PQD=3,5,6 TAGX=_v0 EXTRA="$v" timeout 200 ../venv/bin/python r8/msolve_bench.py $s 150 > /dev/null 2>&1
PQD=3,5,6 TAGX=_v1 EXTRA="$v*yy-1" YVAR=",yy" timeout 200 ../venv/bin/python r8/msolve_bench.py $s 150 > /dev/null 2>&1
t=$(echo $s | tr , -)
for b in v0 v1; do f=r8/ms_${t}_$b.out; echo "$s $v $b $(grep -o 'length of basis: *[0-9]* element' $f 2>/dev/null || echo crash/timeout)"; done
