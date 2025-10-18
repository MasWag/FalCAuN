Installation
============

FalCAuN is fully implemented in Java. FalCAuN works on many UNIX-like operating systems. We tested FalCAuN on macOS Sequoia 15.5, Ubuntu 24.04, Ubuntu 22.04, and Arch Linux.

Requirements
------------

The requirements for the core and examples modules of FalCAuN are as follows.

- Java 17
- Maven
- LTSMin 3.1.0
    - This is not officially released yet.
    - You can download it from [HERE](https://github.com/Meijuh/ltsmin/releases/tag/v3.1.0).
- Owl 21.0: https://owl.model.in.tum.de/

The matlab module also requires the following.

- MATLAB/Simulink
    - We tested with MATLAB R2024a, but any later version should be fine.

Installation of the core Module
-------------------------------

Here, we provide the instructions to install the core module of FalCAuN.

### 1. Install the Requirements

You need to install the requirements above. For example, on Ubuntu, you can install Java 17 and Maven by the following command.

=== "Ubuntu"
    ```bash
    sudo apt-get install maven openjdk-17-jdk-headless -y
    ```
=== "macOS"
    ```bash
    brew install maven openjdk@17
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
# export MATLAB_HOME=/usr/local/MATLAB/R2024a/
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

You need to install Jep manually. Follow the instructions on the [official site](https://github.com/ninia/jep)

### 2. Set up the environment variable

Add the installed path, which has the JEP native library including `jep-VERSION.jar`, to the environment variable `LD_LIBRARY_PATH`.

```sh
export LD_LIBRARY_PATH=<path/to/jep>:${LD_LIBRARY_PATH}
# Example:
# export LD_LIBRARY_PATH=${LD_LIBRARY_PATH}:$PYENV_ROOT/versions/3.10.15/lib/python3.10/site-packages/jep
```

### 3. Build and Install FalCAuN

Build FalCAuN using Maven. You may need to set the environment variable `PYTHONEXECUTABLE` to the full path of the Python executable, for example: `export PYTHONEXECUTABLE="$PWD/.venv/bin/python3"`.

```sh
mvn install --also-make --projects python
```

Installation of LTSMin 3.1.0 on macOS with ARM processors
---------------------------------------------------------

FalCAuN works on macOS with ARM processors, but the setup of LTSMin is a bit tricky because it only supports x86\_64. One can still run LTSMin using Rosetta and libtool for x86\_64. You can also build and install LTSMin using Homebrew (for x86\_64) by `brew install maswag/scientific/ltsmin-beta`.

1. Set up Rosetta on the macOS
2. Install Homebrew for Intel processors with `arch -x86_64 /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"`
3. Install `libtool` for x86\_64 with `/usr/local/bin/brew install libtool`

Notes
-----

- You may have to explicitly specify `JAVA_HOME`, for example, `JAVA_HOME=$(/usr/libexec/java_home -v 17) mvn test -DskipTests=false`.
- The automatic transmission model requires parameters defined in an example by MathWorks. To load it, you probably need to set up the example by MathWorks and the path beforehand.
    - The example by MathWorks can be opened with `openExample('simulink_automotive/ModelingAnAutomaticTransmissionControllerExample')`
    - See `./src/test/resources/MATLAB/initAT.m` for an example to set the path.
