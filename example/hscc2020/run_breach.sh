#!/bin/bash -u
#****h* hscc2020/run_breach.sh
# NAME
#  run_breach
# DESCRIPTION
#  Script to execute an experiment using Breach
#
# USAGE
#  Usage: ./run_breach.sh [Spec]
#
# EXAMPLE
#  ./run_breach.sh AT_S1
#  ./run_breach.sh AT_M1_16
#******

if (($# < 1)); then
    echo 'Usage: ./run_breach.sh [Spec]'
    echo 'Example: ./run_breach.sh AT_S1'
    echo 'Example: ./run_breach.sh AT_M1_16'
    exit
else
    spec=$1
fi

matlab -nodesktop -nosplash <<EOF|tee ./results/result-$spec-breach.txt
cd breach_scripts/
run_breach_$spec
EOF
