#!/bin/bash -u
#****h* hscc2020/run_falcaun.sh
# NAME
#  run_falcaun
# DESCRIPTION
#  Script to execute an experiment using FalCAuN
#
# USAGE
#  Usage: ./run_falcaun.sh [kind] [Spec]
#
# EXAMPLE
#  ./run_falcaun.sh GA AT_S1
#  ./run_falcaun.sh HC AT_M1-large
#******

readonly LENGTH=30
readonly SIGNAL_STEP=1.0
readonly POPULATION_SIZE=150
readonly CROSSOVER_PROB=0.50
readonly MUTATION_PROB=0.01
readonly TIMEOUT=$((240 * 60)) # 240 min.
readonly SELECTION_KIND=Tournament
readonly MAX_TEST=50000

if (($# < 2)); then
    echo 'Usage: ./run_falcaun.sh [kind] [Spec]'
    echo 'Example: ./run_falcaun.sh GA AT_S1'
    echo 'Example: ./run_falcaun.sh GA AT_M1-large'
    exit
else
    kind=$1
    spec=$2
fi

rm -f /home/mwaga/CyVeriA/src/test/resources/MATLAB/Autotrans_shift.mdl.autosave

if sed -h 2>&1 | grep GNU > /dev/null; then
    SED='sed -u'
else
    SED='sed -l'
fi

mkdir -p ./results

../../falcaun \
     --stl-file=./$spec.stl \
     --input-mapper=./AT.imap.tsv \
     --output-mapper=./$spec.omap.tsv \
     --equiv=$kind \
     -l=$LENGTH \
     -s=$SIGNAL_STEP \
     -i="initAT" \
     --param-names="throttle brake" \
     --output-dot=./results/learned-$kind-$POPULATION_SIZE-$CROSSOVER_PROB-$MUTATION_PROB.dot \
     --output-etf=./results/learned-$kind-$POPULATION_SIZE-$CROSSOVER_PROB-$MUTATION_PROB.etf \
     -M=$MAX_TEST \
     -t $TIMEOUT \
     --ga-crossover-prob=$CROSSOVER_PROB \
     --ga-mutation-prob=$MUTATION_PROB \
     --population-size=$POPULATION_SIZE \
     --ga-selection-kind=$SELECTION_KIND | 
    $SED '/DEBUG/ d' |
    tee ./results/result-$spec-$kind.txt