#!/bin/bash

dir="$1"

mkdir -p "$dir/analytics/terms"
mkdir -p "$dir/analytics/qids"

for file in $dir/out/*; do
    if [[ -s "$file" ]]; then
        basefile="$(basename $file)"
        terms="$dir/analytics/terms/$basefile.txt"
        qids="$dir/analytics/qids/$basefile.txt"
        
        timeout 10 python -m qifac analyze "$file" "$terms" terms
        ret_val1=$?
        timeout 10 python -m qifac analyze "$file" "$qids" qids
        ret_val2=$?
        ret_val=$(( ret_val1 > ret_val2 ? ret_val1 : ret_val2 ))

        if (( ret_val == 124 )); then
            echo "Timeout for $basefile"
        elif (( ret_val != 0 )); then
            echo "Other problem with $basefile"
        else
            echo "Success $basefile"
        fi
    fi
done