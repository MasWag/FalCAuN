#!/bin/bash -u
#****h* utils/extractFalsifiedTime
# NAME
#  extractFalsifiedTime
# DESCRIPTION
#  extract the timestamp when a specification is falsified
#
# USAGE
#  ./extractFalsifiedTime.sh < <result-file>
#
# EXAMPLE
#  ./extractFalsifiedTime.sh < result-hc-1.txt
#******

grep violated | cut -d ' ' -f 1
