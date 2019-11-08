#!/bin/bash -u
#****h* hscc2020/run_breach_all.sh
# NAME
#  run_breach_all
# DESCRIPTION
#  Script to execute all the experiments using Breach
#
# USAGE
#  Usage: ./run_breach_all.sh
#
# EXAMPLE
#  ./run_breach_all.sh
#******

for experiment in ./breach_scripts/*.m; do
    tmp=${experiment/.m/}
    spec=${tmp/.\/breach_scripts\/run_breach_/}
    echo "==== Start experiment $spec ======"
    ./run_breach.sh $spec
    echo "==== Finished experiment $spec ======"
done
