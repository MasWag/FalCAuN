#!/bin/bash -ue
#****h* rv2021/run_falcaun_all.sh
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
    echo "==== Start experiment $kind $spec ======"
        ./run_falcaun_many.sh GA "$spec" 50 "${1:-$((240 * 60))}"
    echo "==== Finished experiment $kind $spec ======"
done
