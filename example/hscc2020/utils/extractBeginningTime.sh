#!/bin/bash -u
#****h* utils/extractBeginningTime
# NAME
#  extractBeginningTime
# DESCRIPTION
#  extract the timestamp when the BBC started
#
# USAGE
#  ./extractBeginningTime.sh < <result-file>
#
# EXAMPLE
#  ./extractBeginningTime.sh < result-hc-1.txt
#******

grep 'Starting round 1$' | cut -d ' ' -f 1
