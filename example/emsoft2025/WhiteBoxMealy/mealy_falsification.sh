for numOfSpec in 10
do
  for mode in original partial abstract
  do 
    for index in 22 24 27 41 45 49 54 55 65 76 95 106 131 135 158 159 164 167 172  173 181 182 183 185 189 190 196 199 201
    do
      for iteration in {1..60}
      do
        echo "$mode"_ 
        (time (./mealy_falsification.kts $mode $index $numOfSpec)) 2>&1 | cat> ./result/mealy_falsification/m"$index"_"$numOfSpec"_"$mode"_"$iteration".txt
      done
    done
  done
done