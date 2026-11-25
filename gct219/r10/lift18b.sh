s=$1; md=$2; t=$(echo $s | tr , -)
RR=0 PQD=3,5,6 timeout 900 ../venv/bin/python r7/lift.py 0 800 $s $md > r10/lift_${t}_m$md.json 2>&1
if grep -q "check=1" r10/lift_${t}_m$md.json; then PQD=3,5,6 timeout 900 ../venv/bin/python r7/cert_verify.py $s 0 > r10/verify_$t.txt 2>&1; fi
