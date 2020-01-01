#!/bin/bash -u
#****h* utils/extractBBCElapsedTime
# NAME
#  extractBBCElapsedTime
# DESCRIPTION
#  extract the elapsed time of BBC. The result is second.
#
# USAGE
#  ./extractBBCElapsedTime.sh < <result-file>
#
# EXAMPLE
#  ./extractBBCElapsedTime.sh < result-hc-1.txt
#******

awk '/BBC Elapsed Time:/{print $4}'
