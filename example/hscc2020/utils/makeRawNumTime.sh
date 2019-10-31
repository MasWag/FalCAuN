#!/bin/bash -u
#****h* utils/makeRawNumTime
# NAME
#  makeRawNumTime
# DESCRIPTION
#  make .num.time file
#
# USAGE
#  ./makeRawNumTime.sh <result-file1> <result-file2> ...
#******

if [[ "$@" =~ breach ]]; then
    for result in $@; do
        grep -Fv '>>' $result | tail -n 2  | awk 'NR == 2 {print $10} NR == 1 {print $1}' | xargs -n 2 | tr ' ' '\t'
    done    
else
    paste <(
        for result in $@; do
            $(dirname $0)/extractFalsified.sh < $result | grep 'Property STL' | wc -l
        done) <(
        for result in $@; do
            $(dirname $0)/extractBeginningTime.sh < $result
            $(dirname $0)/extractFalsifiedTime.sh < $result | tail -n 1
        done |  $(dirname $0)/diffDate.sh | awk '(NR%2)')
fi
