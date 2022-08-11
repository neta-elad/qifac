#!/bin/bash

dir="$1"

for file in $dir/out/*; do
    if [[ -s "$file" ]]; then
        basefile="$(basename $file)"
        depth="$dir/analytics/$basefile-depths.txt"
        qids="$dir/analytics/$basefile-qids.txt"
        
        timeout 10 python -m qifac analyze "$file" "$depth" terms
        timeout 10 python -m qifac analyze "$file" "$qids" qids
        ret_val=$?

        if (( ret_val == 124 )); then
            echo "Timeout for $basefile"
        elif (( ret_val != 0 )); then
            echo "Other problem with $basefile"
        else
            echo "Success $basefile"
        fi
    fi
done