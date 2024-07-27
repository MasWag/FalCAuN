FalCAuN Examples with Kotlin
============================

This directory contains examples to directly execute FalCAuN via Kotlin. Our examples depends on [kscript](https://github.com/kscripting/kscript) or [kotlin-jupyter kernel](https://github.com/Kotlin/kotlin-jupyter) to execute the examples.

Usage of kotlin scripts
-----------------------

To execute the examples with `.kts` suffixes, you need to install kscript first. Then, please install FalCAuN using the following commands at the root of FalCAuN.

```bash
mvn clean --projects matlab
mvn install
```

After that, you can directly execute the example scripts, for example, `./ATS1.kts`.

Usage of Jupyter Notebook
-------------------------

To execute the examples with `.ipynb` suffixes, you need to install jupyter and kotlin-jupyter kernel.

```bash
python3 -m venv .venv
. .venv/bin/activate
pip install jupyter kotlin-jupyter-kernel
```

Then, install FalCAuN using the following commands at the root of FalCAuN.

```bash
mvn clean --projects matlab
mvn install
```

After that, execute `jupyter` with suitable environmental variables. The following shows an example on macOS.

```sh
JAVA_HOME=$(/usr/libexec/java_home -v 17) KOTLIN_JUPYTER_JAVA_OPTS="-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64" jupyter notebook
```

On Linux, you can likely find suitable directory to set `JAVA_HOME` by `ls /usr/lib/jvm/`.
