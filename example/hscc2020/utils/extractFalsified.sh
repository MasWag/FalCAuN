#!/bin/bash -u
#****h* utils/extractFalsified
# NAME
#  extractFalsified
# DESCRIPTION
#  extract the falsified specifications and the counter examples (i.e., inputs/outputs)
#
# USAGE
#  ./extractFalsified.sh < <result-file>
#
# EXAMPLE
#  ./extractFalsified.sh < result-hc-1.txt
#******

awk 's;/The following properties are falsified/{s=1}'
