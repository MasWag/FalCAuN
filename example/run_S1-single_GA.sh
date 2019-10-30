#!/bin/bash -ue
#****h* example/run_S1-single_GA
# NAME
#  run_S1-single_GA.sh
# DESCRIPTION
#  An example usage of FalCAuN for S1 using Genetic algorithm. In this example, only one specification is taken from S1.
#
# USAGE
#  ./run_S1-single_GA.sh
#
#******

cd $(dirname $0)

## Configuration

readonly MAX_TESTS=50000
readonly POPULATION_SIZE=150
readonly CROSSOVER_PROB=0.5
readonly MUTATION_PROB=0.01
readonly STL=./AT_S1.stl
readonly IMAP=./AT.imap.tsv
readonly OMAP=./AT_S1.omap.tsv
readonly KIND=GA
readonly SIGNAL_STEP=2.0
readonly LENGTH=15
readonly INIT="cd $PWD;initAT"
readonly PARAM_NAMES="throttle brake"
readonly TIMEOUT=$((120 * 60)) # 120 min.

## Actual execution

../falcaun --stl="[] (signal(0) < 120)" --input-mapper=$IMAP --output-mapper=$OMAP --equiv=$KIND -s=$SIGNAL_STEP -l=$LENGTH -i="$INIT" -M=$MAX_TESTS --param-names="$PARAM_NAMES" -t=$TIMEOUT --ga-crossover-prob=$CROSSOVER_PROB --ga-mutation-prob=$MUTATION_PROB --population-size=$POPULATION_SIZE
