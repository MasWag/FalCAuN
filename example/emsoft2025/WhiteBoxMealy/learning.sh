for numOfSpec in 10
do
  for mode in original partial abstract
  do
    for index in 24 45 54 55 76 95 135 158 159 164 172 183 185 201 181 
    do
      for iteration in {1..10}
      do
	      echo "$numOfSpec"specs_m"$index"_"$mode"_"$iteration"
        (time (./learning.kts $mode $index $numOfSpec)) 2>&1 | cat> ./result/learning_whitebox/"$numOfSpec"specs_m"$index"_"$mode"_"$iteration".txt
      done
    done
  done
done