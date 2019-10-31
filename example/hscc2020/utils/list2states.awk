#!/usr/bin/awk -f
#****h* utils/list2states.awk
# NAME
#  list2states
# DESCRIPTION
#  Construct the number of states TSV from a TSV of experiment directories
#******

{
    result = ""
    cmd = "./utils/makeStateSize.sh results/learned-"$3"-"$2"*.dot | datamash mean 1 pstdev 1 max 1 min 1"
    cmd | getline result
    close(cmd)
}
result {
    split(result, data, "\t")
    printf "%s\t%s\t%.2f\t%.2f\t%.2f\t%.2f\n",$1,$2,data[1],data[2],data[3],data[4]
}
