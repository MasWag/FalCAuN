#!/bin/bash -u
#****h* utils/makeM3STL
# NAME
#  makeM3
# DESCRIPTION
#  Make the `M3'-style specification
#
# The template of the `M3'-style specification is as follows.
# > [] (signal(0) < P1 -> []_[0,P3] (signal(0) < P2))
# USAGE
#  ./makeM3.sh <P1> <P2> <P3>
#
# EXAMPLE
#  ./makeM3.sh 30,40,50 90,80,70,60 3,4,5
#******

readonly P1Params=${1//,/ }
readonly P2Params=${2//,/ }
readonly P3Params=${3//,/ }

for p3 in $P3Params; do
    for p2 in $P2Params; do
        for p1 in $P1Params; do
            echo "[] (signal(0) < $p1 -> []_[0,$p3] (signal(0) < $p2))"
        done
    done
done
