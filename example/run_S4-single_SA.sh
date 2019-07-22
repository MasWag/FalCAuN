#!/bin/bash -ue
#****h* example/run_S4-single_SA
# NAME
#  run_S4-single_SA.sh
# DESCRIPTION
#  An example usage of CyVeriA for S4 using Simulated Annealing. In this example, only one specification is taken from S4.
#
# USAGE
#  ./run_S4-single_SA.sh
#
#******

cd $(dirname $0)

## Configuration

readonly MAX_TESTS=50000
readonly ALPHA=0.3
readonly STL=./AT_S4.stl
readonly IMAP=./AT.imap.tsv
readonly OMAP=./AT_S4.omap.tsv
readonly KIND=SA
readonly SIGNAL_STEP=2.0
readonly LENGTH=15
readonly INIT="cd $PWD;initAT"
readonly PARAM_NAMES="throttle brake"
readonly TIMEOUT=$((30 * 60)) # 30 min.

## Actual execution

../cyveria --stl="([]_[0,13] (signal(0) < 100)) || ([]_[14,14] (signal(0) > 65.0))" --input-mapper=$IMAP --output-mapper=$OMAP --equiv=$KIND -s=$SIGNAL_STEP -l=$LENGTH -i="$INIT" -M=$MAX_TESTS --param-names="$PARAM_NAMES" -t=$TIMEOUT --sa-alpha=$ALPHA
