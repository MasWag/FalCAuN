#!/bin/bash -u

echo TEST FOR makeM3STL.sh
if diff <(./makeM3STL.sh 30,40,50 90,80,70,60 3,4,5) ../AT_M3.stl; then
    echo The test PASSED!!
else
    echo The test FAILED!!
    exit 1;
fi

echo TEST FOR makeM3-omap.sh
if diff <(./makeM3-omap.sh 30,40,50 90,80,70,60 3,4,5) ../AT_M3.omap.tsv; then
    echo The test PASSED!!
    exit 0;
else
    echo The test FAILED!!
    exit 1;
fi
