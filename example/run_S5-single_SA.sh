#!/bin/bash -ue
#****h* example/run_S5-single_SA
# NAME
#  run_S5-signle_SA.sh
# DESCRIPTION
#  An example usage of CyVeriA for S5 using Simulated Annealing. In this example, only one specification is taken from S5.
#
# USAGE
#  ./run_S5-single_SA.sh
#
#******

cd $(dirname $0)

## Configuration

readonly MAX_TESTS=50000
readonly ALPHA=0.3
readonly STL=./AT_S5.stl
readonly IMAP=./AT.imap.tsv
readonly OMAP=./AT_S5.omap.tsv
readonly KIND=SA
readonly SIGNAL_STEP=2.0
readonly LENGTH=15
readonly INIT="cd $PWD;initAT"
readonly PARAM_NAMES="throttle brake"
readonly TIMEOUT=$((30 * 60)) # 30 min.

## Actual execution

../cyveria --stl="alw((signal(1) < 4770) || (X (signal(1) > 600)))" --input-mapper=$IMAP --output-mapper=$OMAP --equiv=$KIND -s=$SIGNAL_STEP -l=$LENGTH -i="$INIT" -M=$MAX_TESTS --param-names="$PARAM_NAMES" -t=$TIMEOUT --sa-alpha=$ALPHA
