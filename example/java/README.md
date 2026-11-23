FalCAuN Example with Java
=========================

`src/main/java/net/maswag/falcaun/ATS1ETF.java` learns a Mealy machine of the automatic transmission (AT) benchmark against the property `alw(signal(0) <= 120.0)`, using hill-climbing equivalence testing. It writes the learned Mealy machine in the ETF format to `/tmp/ATS1.etf`.

The model is set up by `src/resources/MATLAB/initAT.m`, a thin wrapper of the shared benchmark definition [`benchmarks/simulink/AT/initAT.m`](../../benchmarks/simulink/AT/initAT.m). The Simulink model is provided by a Git submodule; initialize it with `git submodule update --init --recursive`.

Requirements
------------

- FalCAuN installed by `mvn install` (see [../../README.md](../../README.md)), including the matlab module
- Java 21
- The environment variable `MATLAB_HOME` set to the root directory of MATLAB

Usage
-----

Run the following commands in this directory. The example changes MATLAB's current directory with the relative path `./src/resources/MATLAB/`, so it must be started from here.

```sh
FALCAUN_JAR="$HOME/.m2/repository/net/maswag/falcaun/FalCAuN-matlab/1.0-SNAPSHOT/FalCAuN-matlab-1.0-SNAPSHOT-jar-with-dependencies.jar"
CLASSPATH="$FALCAUN_JAR:$MATLAB_HOME/extern/engines/java/jar/engine.jar"
javac -cp "$CLASSPATH" -d target/classes src/main/java/net/maswag/falcaun/ATS1ETF.java
java -cp "target/classes:$CLASSPATH" \
     -Djava.library.path="$MATLAB_HOME/bin/maca64:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64" \
     net.maswag.falcaun.ATS1ETF
```
