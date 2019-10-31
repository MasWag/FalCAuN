#!/bin/bash -u
#****h* hscc2020/run_table4.sh
# NAME
#  run
# DESCRIPTION
#  Model check LTL formulas using pre-learned Mealy machines
#
# USAGE
#  ./run_table4.sh 
#******

mkdir -p results
readonly model=./results/learned-AT_M1-gigantic-GA.etf
for ltl in ./table4_ltl/*.ltl; do
    ltlFilename=$(basename "$ltl")
    etf2lts-mc --buchi-type=monitor $model --ltl="$ltl" --trace="./results/table4_${ltlFilename/ltl/}$(basename $model).gcf"  > "./results/table4_${ltlFilename/ltl/}$(basename $model).result" 2>&1
    echo -e "$ltlFilename\t$model\t$?"
done | tee ./results/table4.tsv
