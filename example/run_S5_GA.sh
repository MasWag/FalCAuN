#!/bin/bash -ue
#****h* example/run_S5_GA
# NAME
#  run_S5_GA.sh
# DESCRIPTION
#  An example usage of FalCAuN for S5 using genetic algorithm
#
# USAGE
#  ./run_S5_GA.sh
#
#******

cd $(dirname $0)

## Configuration

readonly MAX_TESTS=50000
readonly POPULATION_SIZE=150
readonly CROSSOVER_PROB=0.5
readonly MUTATION_PROB=0.01
readonly SELECTION_KIND=Tournament
readonly STL=./AT_S5.stl
readonly IMAP=./AT.imap.tsv
readonly OMAP=./AT_S5.omap.tsv
readonly KIND=GA
readonly SIGNAL_STEP=2.0
readonly LENGTH=15
readonly INIT="cd $PWD;initAT"
readonly PARAM_NAMES="throttle brake"
readonly TIMEOUT=$((120 * 60)) # 120 min.

## Actual execution

../falcaun --stl-file=$STL --input-mapper=$IMAP --output-mapper=$OMAP --equiv=$KIND -s=$SIGNAL_STEP -l=$LENGTH -i="$INIT" -M=$MAX_TESTS --param-names="$PARAM_NAMES" -t=$TIMEOUT --ga-crossover-prob=$CROSSOVER_PROB --ga-mutation-prob=$MUTATION_PROB --population-size=$POPULATION_SIZE --ga-selection-kind=$SELECTION_KIND
