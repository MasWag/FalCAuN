#!/bin/bash -ue
#****h* utils/CV2Br_stl.sh
# NAME
#  CV2Br_stl
# DESCRIPTION
#  Convert the STL file for CyVeriA to Breach
#
# USAGE
#  ./CV2Br_stl.sh [SpecName] [CyVeriA-STL-file ...] > <Breach-STL-file>
#  ./CV2Br_stl.sh [SpecName] < <CyVeriA-STL-file> <Breach-STL-file>
#  ./CV2Br_stl.sh < <CyVeriA-STL-file> > <Breach-STL-file>
#
# EXAMPLE
#  ./CV2Br_stl.sh AT_S1 AT_S1.stl
#  ./CV2Br_stl.sh AT_S1.stl AT_S2.stl
#  ./CV2Br_stl.sh < AT_S1.stl
#******

readonly SPEC_NAME="${1:-Spec}"
[[ $# -ge 1 ]] && shift # Remove the first argument only if such an argument exists
cat $@ | # Read the files if the filenames are given. Otherwise, read the standard input
    sed 's/\[\]/alw/g;s/<>/ev/g;s/||/ or /g;s/&&/ and /g;s/->/=>/g;s/signal(0)/speed[t]/g;s/signal(1)/RPM[t]/g;s/signal(2)/gear[t]/g;' | # Replace the signatures
    awk -vname=$SPEC_NAME '{print name"_"NR" := "$0}' # Assigns the specification names
