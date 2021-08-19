#!/bin/bash -ue
#****h* rv2021/run_falcaun_many.sh
# NAME
#  run_falcaun_many
# DESCRIPTION
#  Script to execute the experiments using FalCAuN. By default, the timeout is 240 min.
#
# USAGE
#  Usage: ./run_falcaun_many.sh [kind] [Spec] [experiments count]
#  Usage: ./run_falcaun_many.sh [kind] [Spec] [experiments count] [timeout in sec.]
#
# EXAMPLE
#  ./run_falcaun_many.sh GA AT_F1 50
#  ./run_falcaun_many.sh GA AT_F1 50 $((240 * 60)) ## This means, the timeout is 240 min.
#******

if (($# < 3)); then
    echo 'Usage: ./run_falcaun_many.sh [kind] [Spec] [experiments count]'
    echo 'Usage: ./run_falcaun_many.sh [kind] [Spec] [experiments count] [timeout in sec.]'
    echo 'Example: ./run_falcaun_many.sh GA AT_F1 30'
    echo 'Example: ./run_falcaun_many.sh GA AT_F2 50'
    echo 'Example: ./run_falcaun_many.sh GA AT_F2 50 $((240 * 60))'
    exit
else
    kind=$1
    spec=$2
    count=$3
fi

for i in `seq 1 $count` do
    echo "==== Start experiment$i for $kind $spec ===="
    ./run_falcaun_adaptive.sh $kind $spec "${4:-$((240 * 60))}"
    DATETIME=`date '+%Y%m%d_%H%M'`
    mv ./results/ "./$spec-$kind-Adaptive/results${DATETIME}/"

    ./run_falcaun_static.sh $kind $spec "${4:-$((240 * 60))}"
    DATETIME=`date '+%Y%m%d_%H%M'`
    mv ./results/ "./$spec-$kind-Static/results${DATETIME}/"
    echo "==== Finished experiment$i for $kind $spec ===="
done
