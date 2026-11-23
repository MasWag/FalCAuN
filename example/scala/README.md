FalCAuN Examples with Scala
============================

This directory contains examples to directly execute FalCAuN via Scala. Our examples depend on [scala-cli](https://scala-cli.virtuslab.org/). We tested these examples using Scala 3.7.2 and Scala CLI 1.8.5.

After installing FalCAuN, you can directly execute the example scripts, for example, `./mealy.sc`. The MATLAB examples declare `//> using dep "com.mathworks:engine:1.1"`, which is the `engine.jar` of your MATLAB installation installed to your local Maven repository by `mvn clean --projects matlab`; FalCAuN does not bundle it. For the examples using MATLAB/Simulink, you need to specify the path of the MATLAB library, for example as `JDK_JAVA_OPTIONS="-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64" ./ATS1.sc`.

The Simulink models used by the MATLAB examples (the automatic transmission model in `AutoTrans.scala`) are set up by the shared benchmark definitions in [`benchmarks/simulink`](../../benchmarks/simulink/README.md), and the models are provided by Git submodules. Initialize them with `git submodule update --init --recursive` and run the examples from inside the FalCAuN repository: the path of the benchmark definition is resolved by searching upwards from the current working directory.
