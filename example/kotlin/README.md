FalCAuN Examples with Kotlin
============================

This directory contains examples to directly execute FalCAuN via Kotlin. Our examples depends on [kscript](https://github.com/kscripting/kscript) or [kotlin-jupyter kernel](https://github.com/Kotlin/kotlin-jupyter) to execute the examples.

For the scripts using python, probably you have to set some environment variables appropriately, such as:

```sh
export JEP_JAVA_LIBRARY_PATH="$PWD/.venv/lib/python3.10/site-packages/jep"
export PYTHONEXECUTABLE="$PWD/.venv/bin/python3.10"
```

Usage of kotlin scripts
-----------------------

To execute the examples with `.kts` suffixes, you need to install `kotlin<2.0` and `kscript` first (*kotlin 2.x series are not supported yet*). Then, please install FalCAuN using the following commands at the root of FalCAuN.

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

After that, execute `jupyter` with suitable environmental variables.

On macOS, the following is an example.

```sh
JAVA_HOME=$(/usr/libexec/java_home -v 17) KOTLIN_JUPYTER_JAVA_OPTS="-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64" jupyter notebook
```

On Linux, you can likely find suitable directory to set `JAVA_HOME` by `ls /usr/lib/jvm/`.

## Note
### Installation of LTSMin with a newer Spot
Some STL properties require building LTSMin by yourself with a newer library.
For example, the commented-out lines in `stlList` in [simglucose2.kts](./simglucose2.kts) applies.
It is because of the inefficient old Spot, which LTSMin internally uses.

First, install Spot using https://spot.lre.epita.fr/install.html as a reference.

Then build LTSMin following https://github.com/Meijuh/ltsmin/tree/v3.1.0-beta2.

```
./configure --disable-dependency-tracking --prefix /path
make
make install
```

It will generate the artifacts under `/path` directory.
Finally install them similarly to [../../README.md#installation](../../README.md#1-install-the-requirements)

```
cd /path
sudo cp -r ./share /usr/local/share
sudo cp -r ./include /usr/local/include
sudo install ./bin/* /usr/local/bin
```
