Installation
============

FalCAuN is fully implemented in Java. FalCAuN works on many UNIX-like operating systems. We tested FalCAuN on macOS Sequoia 15.5, Ubuntu 24.04, Ubuntu 22.04, and Arch Linux.

Requirements
------------

The requirements for the core and examples modules of FalCAuN are as follows.

- Java 21
- Maven
- LTSMin 3.1.0
    - This is not officially released yet.
    - You can download it from [HERE](https://github.com/Meijuh/ltsmin/releases/tag/v3.1.0).
- Owl 21.0: https://owl.model.in.tum.de/

The matlab module also requires the following.

- MATLAB/Simulink R2024b or later
    - R2024b is the first release that supports Java 21, which FalCAuN uses.
    - On Linux, we recommend R2026b or later. With R2024b and R2025b, repeated simulations with Fast Restart in accelerator mode, which FalCAuN uses, can corrupt the MATLAB heap, and MATLAB crashes or hangs within a few simulations. We reproduced this on Ubuntu 24.04 in plain MATLAB without FalCAuN. R2026b does not have this problem.
    - If you use R2024b on Linux, use OpenJDK 21.0.2+13 or earlier, the newest version that R2024b supports on Linux. See [Versions of OpenJDK Compatible with MATLAB by Release](https://www.mathworks.com/support/requirements/openjdk.html).

Installation of the core Module
-------------------------------

Here, we provide the instructions to install the core module of FalCAuN.

### 1. Install the Requirements

You need to install the requirements above. For example, on Ubuntu, you can install Java 21 and Maven by the following command.

=== "Ubuntu"
    ```bash
    sudo apt-get install maven openjdk-21-jdk-headless -y
    ```
=== "macOS"
    ```bash
    brew install maven openjdk@21
    ```

You have to manually install LTSMin 3.1.0, Owl 21.0, and MATLAB/Simulink. For example, you can install LTSMin 3.1.0 and Owl 21.0 with the following commands after installing Maven.

```sh
wget https://github.com/Meijuh/ltsmin/releases/download/v3.1.0/ltsmin-v3.1.0-linux.tgz -O ltsmin-v3.1.0-linux.tgz
tar xvf ltsmin-v3.1.0-linux.tgz
sudo cp -r ./v3.1.0/share /usr/local/share
sudo cp -r ./v3.1.0/include /usr/local/include
sudo install ./v3.1.0/bin/* /usr/local/bin
```

```sh
./utils/install_owl.sh
```

We provide a script to check if some of the requirements are installed. You can run the script by the following command. Since this script also checks the dependencies of the matlab module, you can ignore the error messages related to the matlab module.

```sh
./utils/check_env.sh
```

### 2. Build and Install FalCAuN

You can build and install FalCAuN using Maven. An example of installing the core module and the top-level module is as follows.

```sh
mvn install --also-make --projects core
```

You can also install the examples module as follows.

```sh
mvn install --also-make --projects core, examples
```

Installation of the matlab Module
---------------------------------

Here, we provide the instructions to install the matlab module.

!!! note
    For the matlab module, the unit test on `mvn install` is disabled by default because it can be time-consuming. If you want, you can run it by `mvn test -DskipTests=false`.

### 1. Install the Requirements

You need to install MATLAB/Simulink manually. Please follow the instructions on the official website of MathWorks.

### 2. Set up the environment variable

We assume that the environment variable `MATLAB_HOME` shows where MATLAB is installed. An example is as follows.

```sh
export MATLAB_HOME=<path/to/matlab/home>
## Example:
# export MATLAB_HOME=/usr/local/MATLAB/R2024b/
```

### 3. Build and Install FalCAuN

You can build and install FalCAuN using Maven. You have to execute `mvn clean` to set up the Java API of MATLAB. An example to install the matlab module, as well as the others, is as follows.

```sh
mvn clean --projects matlab
mvn install
```

Installation of the python binding Module
----------------------------------------

Here, we provide the instructions to install the python binding module.

### 1. Install the Requirements

You need to install [Jep](https://github.com/ninia/jep) in the Python environment that Maven should use. For example, create and activate a virtual environment and install Jep there.

```sh
python3 -m venv venv
. venv/bin/activate
pip install jep
```

### 2. Set up the environment variable

Set `PYTHONEXECUTABLE` to the absolute path of the Python executable that has Jep installed. This is required because Maven runs tests in forked JVMs, and Jep initializes Python from that executable. Do not use a relative path such as `./venv/bin/python`; use `$PWD/venv/bin/python` instead.

```sh
export PYTHONEXECUTABLE="$PWD/venv/bin/python"
```

The Python binding tests are skipped when `PYTHONEXECUTABLE` is not set to an absolute executable path.

### 3. Build and Install FalCAuN

```sh
JAVA_HOME=/path/to/jdk21 PYTHONEXECUTABLE="$PWD/venv/bin/python" mvn install --also-make --projects python
```

If the tests fail with `UnsatisfiedLinkError: no jep in java.library.path`, pass the directory containing the native library of Jep to `java.library.path` explicitly. On Linux, you can instead add the directory to `LD_LIBRARY_PATH`. On macOS, this is necessary because `DYLD_LIBRARY_PATH` is removed when Maven starts.

```sh
JEP_PATH="$(venv/bin/python -c 'import sysconfig; print(sysconfig.get_paths()["purelib"])')/jep"
JAVA_HOME=/path/to/jdk21 PYTHONEXECUTABLE="$PWD/venv/bin/python" mvn install --also-make --projects python -DargLine="-Djava.library.path=$JEP_PATH"
```

Installation of LTSMin 3.1.0 on macOS with ARM processors
---------------------------------------------------------

FalCAuN works on macOS with ARM processors, but the setup of LTSMin is a bit tricky because it only supports x86\_64. One can still run LTSMin using Rosetta and libtool for x86\_64. You can also build and install LTSMin using Homebrew (for x86\_64) by `brew install maswag/scientific/ltsmin-beta`.

1. Set up Rosetta on the macOS
2. Install Homebrew for Intel processors with `arch -x86_64 /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"`
3. Install `libtool` for x86\_64 with `/usr/local/bin/brew install libtool`

Notes
-----

- You may have to explicitly specify `JAVA_HOME`, for example, `JAVA_HOME=$(/usr/libexec/java_home -v 21) mvn test -DskipTests=false`.
- The automatic transmission model requires parameters defined in an example by MathWorks. To load it, you probably need to set up the example by MathWorks and the path beforehand.
    - The example by MathWorks can be opened with `openExample('simulink_automotive/ModelingAnAutomaticTransmissionControllerExample')`
    - See `./src/test/resources/MATLAB/initAT.m` for an example to set the path.
