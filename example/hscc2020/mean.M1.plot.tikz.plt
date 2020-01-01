# -*- mode: gnuplot; -*-
set terminal tikz font ',15pt'
set output 'mean.M1.plot.tikz.tex'
set key outside center top horizontal samplen 1.0
set tics font "\\huge"
set xlabel font "\\huge"
set ylabel font "\\huge"
set key font "\\large"
set xlabel 'The number of the falsified properites'
set ylabel offset -1,0
set ylabel "The execution time [min.]"
set yrange [0:40]
plot 'mean.M1.summary.tsv' using 1:3 with linespoints title '\random\hspace{0mm}' lw 5 pt 5 ps 2, 'mean.M1.summary.tsv' using 1:5 with linespoints title '\hc' lw 5 ps 2 pt 7, 'mean.M1.summary.tsv' using 1:7 with linespoints title '\ga' lw 5 ps 2 pt 6, 'mean.M1.summary.tsv' using 1:9 with linespoints title '\breach' lw 5 ps 2

