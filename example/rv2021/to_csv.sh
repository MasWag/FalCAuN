#!/bin/bash

mkdir -p './experiment_results/'

experiment_dirs=`find ./* -maxdepth 0 -type d -name "*-Adaptive" -or -name "*-Static"`

for rootdir in $experiment_dirs; do
	echo 'Round,BBC Elapsed Time (sec.),Simulink Execution,Data directory name' > "./experiment_results/$rootdir.csv"
	ls $rootdir | while read dirname; do
		if [ -d "$rootdir/$dirname" ]; then
			cd "$rootdir/$dirname"
			grep -e 'round' "$(find . -name 'result-*.txt' | head -1)" | tail -1 | awk '{print $8}' | tr -d '\n' > tmp.txt &&
			echo -n ',' >> tmp.txt &&
			grep -e 'BBC Elapsed Time' "$(find . -name 'result-*.txt' | head -1)" | tail -1 | awk '{print $4}' | tr -d '\n' >> tmp.txt &&
			echo -n ',' >> tmp.txt &&
			grep -e 'Simulink Execution' "$(find . -name 'result-*.txt' | head -1)" | tail -1 | awk '{print $3}' | tr -d '\n' >> tmp.txt &&
			echo -n ',' >> tmp.txt &&
			echo "$dirname" >> tmp.txt &&
			cat tmp.txt >> "../../experiment_results/$rootdir.csv"
			rm -f tmp.txt
			cd '../../'
		fi
	done
done