#!/bin/bash -ue
#****h* example/run_S3_GA
# NAME
#  run_S3_GA.sh
# DESCRIPTION
#  An example usage of CyVeriA for S3 using genetic algorithm
#
# USAGE
#  ./run_S3_GA.sh
#
#******

cd $(dirname $0)

## Configuration

### Configuration for the SUT and the specification
readonly STL=./AT_S3.stl
readonly IMAP=./AT.imap.tsv
readonly OMAP=./AT_S3.omap.tsv
readonly INIT="cd $PWD;initAT"
readonly PARAM_NAMES="throttle brake"

### Configuration for the signals
readonly LENGTH=30
readonly SIGNAL_STEP=1.0

### Configiration for the equivalence testing
readonly KIND=GA
readonly POPULATION_SIZE=150
readonly CROSSOVER_PROB=0.5
readonly MUTATION_PROB=0.01
readonly SELECTION_KIND=Tournament
readonly MAX_TESTS=50000
readonly TIMEOUT=$((240 * 60)) # 240 min.

## Actual execution

../cyveria --stl-file=$STL --input-mapper=$IMAP --output-mapper=$OMAP --equiv=$KIND -s=$SIGNAL_STEP -l=$LENGTH -i="$INIT" -M=$MAX_TESTS --param-names="$PARAM_NAMES" -t=$TIMEOUT --ga-crossover-prob=$CROSSOVER_PROB --ga-mutation-prob=$MUTATION_PROB --population-size=$POPULATION_SIZE --ga-selection-kind=$SELECTION_KIND
