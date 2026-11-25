# lift 1 over Q for one E cell (3x5 d6), generators = P_k coefficients + colex minors deg<=3 (no row rank), then sympy re-check
s=$1; t=$(echo $s | tr , -)
RR=0 PQD=3,5,6 timeout 900 ../venv/bin/python r7/lift.py 0 800 $s 3 > r10/lift_$t.json 2>&1
if grep -q "check=1" r10/lift_$t.json; then PQD=3,5,6 timeout 900 ../venv/bin/python r7/cert_verify.py $s 0 > r10/verify_$t.txt 2>&1; fi
