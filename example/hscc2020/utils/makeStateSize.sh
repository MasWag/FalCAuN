#!/bin/bash -u
#****h* utils/makeStateSize
# NAME
#  makeStateSize
# DESCRIPTION
#  make .states file
#
# USAGE
#  ./makeStateSize.sh <result-file1> <result-file2> ...
#******

for result in $@; do
    awk '/shape/ && $0=$1' $result |
        grep -v '__start0' |
        tr -d s |
        sort -n |
        tail -n 1
done | sort -n
