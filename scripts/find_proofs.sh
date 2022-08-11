#!/bin/bash

EXECUTABLE="/Users/neta.e/Code/other/z3-versions/4.10.2/bin/z3"
TRACER="/Users/neta.e/Code/vmware/smt2utils/target/debug/z3tracer"

dir="$1"

for file in $dir/*; do
    if [[ -f "$file" ]]; then
        basefile="$(basename $file)"
        output="$dir/out/$basefile"
        
        timeout 90 python -m qifac find-proof -p -e "$EXECUTABLE" -t "$TRACER" "$file" "$output"
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