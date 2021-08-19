#!/bin/bash -u
#****h* rv2021/run_falcaun_adaptive.sh
# NAME
#  run_falcaun_adaptive
# DESCRIPTION
#  Script to execute an experiment using FalCAuN with adaptive STL. By default, the timeout is 240 min.
#
# USAGE
#  ./run_falcaun_adaptive.sh [kind] [Spec]
#  ./run_falcaun_adaptive.sh [kind] [Spec] [timeout in sec.]
#
# EXAMPLE
#  ./run_falcaun_adaptive.sh GA AT_F1
#  ./run_falcaun_adaptive.sh HC AT_F2
#  ./run_falcaun_adaptive.sh GA AT_F2 $((240 * 60))
#******

if (($# < 2)); then
    echo 'Usage: ./run_falcaun_adaptive.sh [kind] [Spec]'
    echo 'Usage: ./run_falcaun_adaptive.sh [kind] [Spec] [timeout in sec.]'
    echo 'Example: ./run_falcaun_adaptive.sh GA AT_F1'
    echo 'Example: ./run_falcaun_adaptive.sh GA AT_F2'
    echo 'Example: ./run_falcaun_adaptive.sh GA AT_F2 $((240 * 60))'
    exit
else
    kind=$1
    spec=$2
fi

readonly LENGTH=30
readonly SIGNAL_STEP=1.0
readonly POPULATION_SIZE=150
readonly CROSSOVER_PROB=0.50
readonly MUTATION_PROB=0.01
readonly TIMEOUT=${3:-$((240 * 60))} # by default, timeout is 240 min.
readonly SELECTION_KIND=Tournament
readonly MAX_TEST=50000
readonly WP_MAX_DEPTH=30

rm -f ./Autotrans_shift.mdl.autosave

if sed -h 2>&1 | grep GNU > /dev/null; then
    SED='sed -u'
else
    SED='sed -l'
fi

mkdir -p ./results

../../falcaun \
     --adaptive-stl \
     --stl-file="./$spec.stl" \
     --input-mapper="./AT.imap.tsv" \
     --output-mapper="./$spec.omap.tsv" \
     --equiv="$kind" \
     -l=$LENGTH \
     -s=$SIGNAL_STEP \
     -i="initAT" \
     --param-names="throttle brake" \
     --output-dot="./results/learned-$spec-$kind.dot" \
     --output-etf="./results/learned-$spec-$kind.etf" \
     -M=$MAX_TEST \
     -t "$TIMEOUT" \
     --ga-crossover-prob=$CROSSOVER_PROB \
     --ga-mutation-prob=$MUTATION_PROB \
     --population-size=$POPULATION_SIZE \
     --ga-selection-kind=$SELECTION_KIND \
     --wp-max-depth=$WP_MAX_DEPTH | 
    $SED '/DEBUG/ d' |
    tee "./results/result-$spec-$kind.txt"
