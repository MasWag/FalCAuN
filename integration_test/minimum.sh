#!/bin/sh -u
#****h* integration_test/minimum
# NAME
#  minimum
# DESCRIPTION
#  Script for a minimum integration test
#
# USAGE
#  ./integration_test/minimum.sh
#
#******

cd "$(dirname "$0")/../" || exit 1

mvn install &&
    ./falcaun \
        --stl='((signal(2) == 1 U signal(2) == 2 U signal(2) == 3 U signal(2) == 4)   && <>_[0,10](signal(2) == 4 && <>_[0,2](signal(1) > 4500))) -> <>_[0,10](signal(2) == 4 -> X(signal(2) == 4 && X (signal(0) > 160)))' \
        --output-mapper=./example/AT_M4.omap.tsv \
        --input-mapper=./example/AT.imap.tsv \
        --equiv=GA \
        --step-time=1.0 \
        --signal-length=30 \
        --init='cd ./example; initAT' \
        --max-test=1 \
        --param-names="throttle brake" \
        --ga-crossover-prob=0.5 \
        --ga-mutation-prob=0.01 \
        --population-size=1 \
        --ga-selection-kind=Tournament || exit 1
