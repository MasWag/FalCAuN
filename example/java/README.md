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

The MATLAB Engine API for Java (`engine.jar`) is not bundled with FalCAuN, so it is added to the classpath explicitly above. The native library path (`-Djava.library.path`) of MATLAB is a separate requirement.

Using FalCAuN-matlab from a Maven project
-----------------------------------------

`FalCAuN-matlab` declares the MATLAB Engine API with the `provided` scope, so it is not passed to your project as a transitive dependency. Install the `engine.jar` of your MATLAB installation into your local Maven repository (this is also done by `mvn clean --projects matlab` in FalCAuN):

```sh
mvn install:install-file -Dfile="$MATLAB_HOME/extern/engines/java/jar/engine.jar" \
    -DgroupId=com.mathworks -DartifactId=engine -Dversion=1.1 -Dpackaging=jar -DgeneratePom=true
```

Then, declare it next to FalCAuN:

```xml
<dependency>
    <groupId>net.maswag.falcaun</groupId>
    <artifactId>FalCAuN-matlab</artifactId>
    <version>1.0-SNAPSHOT</version>
</dependency>
<dependency>
    <groupId>com.mathworks</groupId>
    <artifactId>engine</artifactId>
    <version>1.1</version>
    <!-- provided: supplied by MATLAB at run time, not bundled into your artifacts -->
    <scope>provided</scope>
</dependency>
```

At run time, put `$MATLAB_HOME/extern/engines/java/jar/engine.jar` in the classpath and set `-Djava.library.path` as above.
