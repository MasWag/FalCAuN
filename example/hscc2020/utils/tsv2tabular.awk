#!/usr/bin/awk -f

{
    OFS="&";
    ORS = "\\\\ \\hline\n";
    $1=$1;
    print
}
END {
    ORS = "\n";
    print "\\end{tabular}"
}
