#!/bin/bash -ue
#****h* hscc2020/run_falcaun_all.sh
# NAME
#  run_falcaun_all
# DESCRIPTION
#  Script to execute all the experiments using FalCAuN. By default, the timeout is 240 min.
#
# USAGE
#  Usage: ./run_falcaun_all.sh
#  Usage: ./run_falcaun_all.sh [timeout in sec.]
#
# EXAMPLE
#  ./run_falcaun_all.sh
#  ./run_falcaun_all.sh $((240 * 60)) ## This means, the timeout is 240 min.
#******

echo "==== Timeout: ${1:-$((240 * 60))} [sec.] ======"

for experiment in *.stl; do
    spec=${experiment/.stl/}
    for kind in GA HC RANDOM; do
        echo "==== Start experiment $kind $spec ======"
           ./run_falcaun.sh $kind $spec $1
        echo "==== Finished experiment $kind $spec ======"
    done
done
