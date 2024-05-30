FalCAuN
=======

[![JUnit](https://github.com/MasWag/FalCAuN/workflows/JUnit/badge.svg)](https://github.com/MasWag/FalCAuN/actions?query=workflow%3AJUnit)
[![CircleCI](https://circleci.com/gh/MasWag/FalCAuN/tree/master.svg?style=svg)](https://circleci.com/gh/MasWag/FalCAuN/tree/master)
[![Javadoc](https://img.shields.io/badge/Javadoc-latest-green)](https://maswag.github.io/FalCAuN/maven-site/latest/apidocs/)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](./LICENSE)

This is the source code repository for FalCAuN ---  Falsification of CPSs via Automata Learning.
FalCAuN is a toolkit for testing black-box systems (e.g., cyber-physical systems) based on automata learning and model checking. Currently, systems implemented in Java and Simulink are supported.

Installation
------------

FalCAuN is implemented in Java. We suppose FalCAuN works on many UNIX-like operating systems. We tested FalCAuN on macOS 14.4.1 Sonoma, Ubuntu 22.04, and Arch Linux.

### Requirements

The requirements for the core module of FalCAuN are as follows.

- Java 11
- Maven
- LTSMin 3.1.0
  - This is not officially released yet.
  - You can download it from [HERE](https://github.com/Meijuh/ltsmin/releases/tag/v3.1.0).

The matlab module also requires the following.

- MATLAB/Simulink
  - We tested with MATLAB R2024a but any later version should be fine.

### Installation of the core Module

Here, we provide the instructions to install the core module of FalCAuN.

#### 1. Install the Requirements

You need to install the requirements above. For example, on Ubuntu, you can install Java 11 and Maven by the following command.

```sh
sudo apt-get install maven openjdk-11-jdk-headless -y
```

You have to manually install LTSMin 3.1.0 and MATLAB/Simulink. For example, you can install LTSMin 3.1.0 with the following commands.

```sh
wget https://github.com/Meijuh/ltsmin/releases/download/v3.1.0/ltsmin-v3.1.0-linux.tgz -O ltsmin-v3.1.0-linux.tgz
tar xvf ltsmin-v3.1.0-linux.tgz
sudo cp -r ./v3.1.0/share /usr/local/share
sudo cp -r ./v3.1.0/include /usr/local/include
sudo install ./v3.1.0/bin/* /usr/local/bin
```

We provide a script to check if some of the requirements are installed. You can run the script by the following command. Since this script also checks the dependencies of the matlab module, you can ignore the error messages related to the matlab module.

```sh
./utils/check_env.sh
```

#### 2. Build and Install FalCAuN

You can build and install FalCAuN using Maven. An example of installing the core module and the top-level module is as follows.

```sh
mvn install --projects core,
```

### Installation of the matlab Module

Here, we provide the instructions to install the matlab module.

#### 1. Install the Requirements

You need to install MATLAB/Simulink manually. Please follow the instructions on the official website of Mathworks.

#### 2. Setup the environment variable

We assume that the environment variable `MATLAB_HOME` shows where MATLAB is installed. An example is as follows.

```sh
export MATLAB_HOME=<path/to/matlab/home>
## Example:
# export MATLAB_HOME=/usr/local/MATLAB/R2024a/
```

#### 3. Build and Install FalCAuN

You can build and install FalCAuN using Maven. You have to execute `mvn clean` to set up the Java API of MATLAB. An example to install the matlab module, as well as the others, is as follows.

```sh
mvn clean --projects matlab
mvn install
```

### Installation of LTSMin 3.1.0 on macOS with ARM Processors

FalCAuN works on macOS with ARM Processors, but the setup of LTSMin is a bit tricky because it only supports x86\_64. One can still run LTSMin using Rosetta and libtool for x86\_64.

1. Set up Rosetta on the macOS
2. Install Homebrew for intel processors with `arch -x86_64 /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"`
3. Install `libtool` for x86_64 with `/usr/local/bin/brew install libtool`

### Notes

- For the matlab module, the unit test on `mvn install` is disabled by default because it takes much time. If you want, you can run it by `mvn test -DskipTests=false`.
    - Perhaps you have to explicitly specify `JAVA_HOME`, for example, `JAVA_HOME=$(/usr/libexec/java_home -v 11) mvn test -DskipTests=False`.
    - Also, the automatic transmission model requires parameters defined in an example by Mathworks. To load it, you probably need to set up the example by Mathworks and the path beforehand. 
        - The example by Mathworks can be opened with `openExample('simulink_automotive/ModelingAnAutomaticTransmissionControllerExample')`
        - See `./src/test/resources/MATLAB/initAT.m` for an example to set the path.

Examples
--------

We provide some examples in the `./example/kotlin` directory. The following is the list of examples. To run the examples, you need to install [kscript](https://github.com/kscripting/kscript) because the examples are written in Kotlin script.

The following example does not require MATLAB/Simulink.

- `./example/kotlin/mealy.main.kts`
  - This example is a simple example to test some properties of a Mealy machine, which is handled as black-box.

The following examples require MATLAB/Simulink.

- `./example/kotlin/ATS1.main.kts`
- `./example/kotlin/ATS2.kts`
- `./example/kotlin/ATS6a.main.kts`
- `./example/kotlin/ATS6b.main.kts`
- `./example/kotlin/pacemaker.main.kts`

STL
---

The definition of signal temporal logic in FalCAuN is as follows.

```
expr : atomic
     | expr && expr
     | expr || expr
     | expr -> expr
     | ! expr
     | GLOBALLY expr
     | EVENTUALLY expr
     | X expr
     | expr U expr
     | GLOBALLY_interval expr
     | EVENTUALLY_interval expr
     | expr U_interval expr
     | ( expr )

atomic : signal(NATURAL) == value
       | signal(NATURAL) < value
       | signal(NATURAL) > value
       | signal(NATURAL) != value
       | input(NATURAL) == value
       | input(NATURAL) < value
       | input(NATURAL) > value
       | input(NATURAL) != value
       | output(NATURAL) == value
       | output(NATURAL) < value
       | output(NATURAL) > value
       | output(NATURAL) != value

value : -? NATURAL | -? FLOAT

GLOBALLY : '[]' | 'alw' | 'G'

EVENTUALLY : '<>' | 'ev' | 'F'
```

Javadoc
--------

The source code is partially commented on using the Javadoc syntax. The document is hosted on [GitHub Pages](https://maswag.github.io/FalCAuN/maven-site/latest/apidocs/).
If you want to generate the document locally under `./target/site/apidocs/` by `mvn javadoc:aggregate.`

Obsolete CLI interface
-----------------------

After FalCAuN 1.0, FalCAuN is mainly intended to be used as a library called from a program written in some JVM language, such as Kotlin. The CLI interface is still available for backward compatibility, but it is not actively maintained.

To execute FalCAuN via the CLI interface, you can use the helper shell script `falcaun` in the root directory of the repository. The script is a wrapper of the CLI interface of FalCAuN. The script is written in POSIX sh and should work on most UNIX-like operating systems.
An example of usage is as follows. This takes at least a few minutes for MATLAB to start up and another few minutes to falsify all the STL formulas in `./example/AT_M4.stl`. Please be patient!!

```sh
./falcaun --stl-file=./example/AT_M4.stl --output-mapper=./example/AT_M4.omap.tsv --input-mapper=./example/AT.imap.tsv --equiv=GA --step-time=1.0 --signal-length=30  --init='cd ./example; initAT' --max-test=50000 --param-names="throttle brake" --ga-crossover-prob=0.5 --ga-mutation-prob=0.01 --population-size=150 --ga-selection-kind=Tournament
```

You can also install this script as follows.

```sh
sudo install falcaun /usr/local/bin
```

### Usage of the CLI interface

#### Symopsis

     ./falcaun [OPTIONS] --stl=[STLFormula] --input-mapper=[InputMapperFile] --output-mapper=[OutputMapperFile] --equiv=[HC|random|WP|SA|GA]

#### General Options

**-h**, **--help** Print a help message. <br />
**-v**, **--verbose** It outputs extra information, mainly for debugging. <br />
**-V**, **--version** Print the version <br />
**-t** *timeout*, **--timeout** *timeout* Set timeout [seconds]
**-f** *file*, **--stl-file** *file* Read a STL formula from *file*. <br />
**-e** *STLFormula*, **--stl** *STLFormula* Specify *STLFormula* by signal temporal logic. <br />
**-I** *file*, **--input-mapper** *file* Read the input mapper configuration from *file*. <br />
**-O** *file*, **--output-mapper** *file* Read the output mapper configuration from *file*. <br />
**-S** *file*, **--signal-mapper** *file* Read the signal mapper from *file*. <br />
**-E** *algorithm*, **--equiv** *algorithm* Specify the equivalence testing algorithm. See below for the detail. <br />
**-o** *file*, **--output-dot** *file* Write the learned Mealy machine to *file* in DOT format. <br />
**--output-etf** *file* Write the learned Mealy machine to *file* in ETF format. <br />
**-s** *step-time*, **--step-time** *step-time* Specify the step time of the sampling. <br />
**-l** *length*, **--signal-length** *length* Specify the length of the sampled signals. <br />
**-i** *script*, **--init** *script* The initial script of MATLAB <br />
**-p** *param1 param2 ... paramN*, **--param-names** *param1 param2 ... paramN* The parameter names of the Simulink
model <br />
**-M** *test-size*, **--max-test** *test-size* The maximum test size <br />
**--disable-adaptive-stl** Disable the adaptive STL updater in [Shijubo+, RV'21]

#### Options Specific to the Equivalence Testing

When you use GA, SA, or WP for the equivalence testing, you have to specify the following options in addition.

#### GA (Genetic Algorithm)

**--population-size** *size* The size of the population <br />
**--ga-crossover-prob** *prob* The crossover probability (should be between 0 and 1) <br />
**--ga-mutation-prob** *prob* The mutation probability (should be between 0 and 1) <br />
**--ga-selection-kind** *[bestsolution|tournament]* The selection in the genetic algorithm. Either best solution selection or binary tournament.

#### SA (Simulated Annealing)

**--sa-alpha** *alpha* The alpha parameter for simulated annealing (should be between 0 and 1)

##### WP (Wp-method)

**--wp-max-depth** *depth* The maximum depth in the Wp-method

### File format of the mapper

Both input and output mappers are specified by TSV files.

#### Input mapper

Input mapper specifies the possible input values of each signal (e.g., break and throttle). Each signal can take different number of inputs i.e., N0 and N1 can be different.

```
<value 1 of signal(0)>	<value 2 of signal(0)>	...	<value N0 of signal(0)>
<value 1 of signal(1)>	<value 2 of signal(1)>	...	<value N1 of signal(1)>
...						
```

For example, the following shows that:

- the domain of `signal(0)` is 10 and 40; and
- the domain of `signal(1)` is 0, 50, and 100.

```
10	40
0	50	100
```

#### Output mapper

Output mapper specifies how we map the real-valued signal to an atomic proposition. Precisely, we split the vector space R^n by grids. Each grid is one atomic proposition. Since the maximum upper bound is the positive infinity, the last cell for each signal must be `inf`.

```
<upper bound of signal(0) for AP0-1>	<upper bound of signal(0) for AP0-2>	...	<upper bound of signal(0) for AP0-N0>
<upper bound of signal(0) for AP1-1>	<upper bound of signal(1) for AP1-2>	...	<upper bound of signal(1) for AP1-N1>
...
```
For example, the following output mapper stands for as follows.

- For `signal(0)`:
  - `AP0-1` holds if `signal(0)` <= 10;
  - `AP0-2` holds if 10 < `signal(0)` <= 40; and
  - `AP0-3` holds if 40 < `signal(0)`.
- For `signal(1)`:
  - `AP1-1` holds if `signal(1)` <= 0;
  - `AP1-2` holds if 0 < `signal(1)` <= 50;
  - `AP1-3` holds if 50 < `signal(1)` <= 100; and
  - `AP1-4` holds if 100 < `signal(1)`.
- For `signal(2)`, `AP2-1` always holds.

```
10	40	inf
0	50	100	inf
inf
```

Contributors
------------

- Masaki Waga: 2019--
- Junya Shijubo: 2021--2022


FAQ
---

- FalCAuN says ``infinite robustness''. What should I do?
    - It can be because the generated signal is too short for the temporal formula. Please make "--signal-length" as
      long as the time window of the STL formulas.


References
----------

- [Shijubo+, RV'21] Efficient Black-Box Checking via Model Checking with Strengthened Specifications. Junya Shijubo, Masaki Waga, and Kohei Suenaga
- [Waga, HSCC'20] Falsification of cyber-physical systems with robustness-guided black-box checking. Masaki Waga
