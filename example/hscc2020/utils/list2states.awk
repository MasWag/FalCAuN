#!/usr/bin/awk -f
#****h* utils/list2states.awk
# NAME
#  list2states
# DESCRIPTION
#  Construct the number of states TSV from a TSV of experiment directories
#******

{
    result = ""
    cmd = "./utils/makeStateSize.sh results/result-"$3"-"$2"-*.dot | datamash -R 2 mean 1 pstdev 1 max 1 min 1"
    cmd | getline result
    $3 = result
    close(cmd)
}
result;
