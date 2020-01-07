#!/bin/bash -u
#****h* hscc2020/run_table4_breach.sh
# NAME
#  run_table4_breach
# DESCRIPTION
#  Execute the suggested counterexamples on Breach
#
# USAGE
#  ./run_table4_breach.sh 
#
# PORTABILITY
#  This script requires LTSMin, MATLAB/Simulink, and Breach.
#******

mkdir -p results/
for spec in S1_90 S4_90_40 S4_90_50 S4_90_60; do 
    echo $spec
    for model in "./results/table4_M3-${spec//_/-}"*.gcf; do
        if [ ! -f "$model" ]; then
            continue;
        fi
        echo "$model"
        TMP=$(mktemp -t run_breach.sh.XXXXXX)
        trap 'rm -f $TMP* 2>/dev/null' EXIT
        
        ltsmin-printtrace "$model" |
            awk '/input:input/{print $3}' |
            tr -d '",' |
            fold -w 1 |
            xargs -n 2 |
            awk '$1 == "a"{$1=0.0}$1 == "b"{$1=100.0}$2 == "a"{$2=0.0}$2 == "b"{$2=325.0}1;' > "$TMP"
        throttles=$(cut -d ' ' -f 1 < "$TMP" | xargs | sed 's/ /, /g;s/^/[/;s/$/]/;')
        brakes=$(cut -d ' ' -f 2 < "$TMP" | xargs | sed 's/ /, /g;s/^/[/;s/$/]/;')
        m4 -DSPEC=$spec -DID="$(basename "$model" | sed 's/\.gcf//')" -Dthrottles="$throttles" -Dbrakes="$brakes" run_table4.m.m4 |
            cat run_table4.m.header - | 
            matlab
        rm "$TMP"* 2>/dev/null
    done
done
