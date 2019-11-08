#!/bin/bash -u
#****h* hscc2020/run_falcaun_all.sh
# NAME
#  run_falcaun_all
# DESCRIPTION
#  Script to execute all the experiments using FalCAuN
#
# USAGE
#  Usage: ./run_falcaun_all.sh
#
# EXAMPLE
#  ./run_falcaun_all.sh
#******

for experiment in *.stl; do
    spec=${experiment/.stl/}
    for kind in GA HC RANDOM; do
        echo "==== Start experiment $kind $spec ======"
           ./run_falcaun.sh $kind $spec
        echo "==== Finished experiment $kind $spec ======"
    done
done
