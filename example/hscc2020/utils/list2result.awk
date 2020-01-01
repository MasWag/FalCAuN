#!/usr/bin/awk -f
#****h* utils/list2result.awk
# NAME
#  list2result
# DESCRIPTION
#  Construct the result TSV from a TSV of experiment directories
# NOTE
#  The time unit in the result is minuites
#******

{
    result = ""
    cmd = "./utils/makeRawNumTime.sh results/result-"$3"-"$2"*.txt | awk '{$2 = $2 / 60}1;' | tr ' ' '\t' | datamash -R 2 mean 1 pstdev 1 max 1 min 1 mean 2 pstdev 2 max 2 min 2"
    cmd | getline result
    $3 = result
    close(cmd)
}
result;
