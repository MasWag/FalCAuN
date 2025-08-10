#!/bin/bash -u
#****h* utils/makeM3-omap
# NAME
#  makeM3
# DESCRIPTION
#  Make the output mapper for a `M3'-style specification
#
# The template of the `M3'-style specification is as follows.
# > [] (signal(0) < P1 -> []_[0,P3] (signal(0) < P2))
# USAGE
#  ./makeM3-omap.sh <P1> <P2>
#
# EXAMPLE
#  ./makeM3-omap.sh 30,40,50 90,80,70,60
#******

if (($# < 2)); then
    echo "usage: ./makeM3-omap.sh <P1> <P2>"
    exit 0
fi

readonly P1Params=$1
readonly P2Params=$2

echo $P1Params,$P2Params | tr , '\n' | sort -n | uniq | awk 'BEGIN{ORS="\t"}$1=$1".0";END{ORS="\n";print "inf"}' | cat - <(echo inf) <(echo inf)
