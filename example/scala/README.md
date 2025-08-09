FalCAuN Examples with Scala
============================

This directory contains examples to directly execute FalCAuN via Scala. Our examples depends on [scala-cli](https://scala-cli.virtuslab.org/). We tested these examples using Scala 3.7.2 and Scala CLI 1.8.5.

After installing FalCAuN, you can directly execute the example scripts, for example, `./mealy.sc`. For the examples using MATLAB/Simulink, you need to specify the pass of the MATLAB library, for example as `JDK_JAVA_OPTIONS="-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64" ./ATS1.sc`.
