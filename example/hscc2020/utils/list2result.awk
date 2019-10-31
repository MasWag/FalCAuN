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
    cmd = "./utils/makeRawNumTime.sh results/result-"$3"-"$2"*.txt | awk '{$2 = $2 / 60}1;' | tr ' ' '\t' | datamash mean 1 pstdev 1 max 1 min 1 mean 2 pstdev 2 max 2 min 2"
    cmd | getline result
    close(cmd)
}
result {
    split(result, data, "\t")
    printf "%s\t%s\t%.2f\t%.2f\t%.2f\t%.2f\t%.2f\t%.2f\t%.2f\t%.2f\n",$1,$2,data[1],data[2],data[3],data[4],data[5],data[6],data[7],data[8]
}
