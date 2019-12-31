FalCAuN
=======

[![CircleCI](https://circleci.com/gh/MasWag/FalCAuN.svg?style=svg&circle-token=529c89869f5a7b6e9f957ee656ffc55349d050ca)](https://circleci.com/gh/MasWag/FalCAuN)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](./LICENSE)

This is the source code repository for FalCAuN ---  Falsification of CPSs via Automata Learning.

Usage
-----

### Symopsis

     ./falcaun [OPTIONS] --stl=[STLFormula] --input-mapper=[InputMapperFile] --output-mapper=[OutputMapperFile] --equiv=[HC|random|WP|SA|GA]

### Options

**-h**, **--help** Print a help message. <br />
**-v**, **--verbose** It outputs extra information, mainly for debugging. <br />
**-V**, **--version** Print the version <br />
**-t** *timeout*, **--timeout** *timeout* Set timeout [seconds]
**-f** *file*, **--stl-file** *file* Read a STL formula from *file*. <br />
**-e** *pattern*, **--stl** *STLFormula* Specify *STLFormula* by signal temporal logic. <br />
**-I** *file*, **--input-mapper** *file* Read the input mapper configuration from *file*. <br />
**-O** *file*, **--output-mapper** *file* Read the output mapper configuration from *file*. <br />
**-E** *algorithm*, **--equiv** *algorithm* Specify the equivalence query algorithm. See below for the detail. <br />
**-o** *file*, **--output-dot** *file* Write the learned Mealy machine to *file* in DOT format. <br />
**--output-etf** *file* Write the learned Mealy machine to *file* in ETF format. <br />
**-s** *step-time*, **--step-time** *step-time* Specify the step time of the sampling. <br />
**-l** *length*, **--signal-length** *length* Specify the length of the sampled signals. <br />
**-i** *script*, **--init** *script* The initial script of MATLAB <br />
**-p** *param1 param2 ... paramN*, **--param-names** *param1 param2 ... paramN* The parameter names of the Simulink model <br />
**-M** *test-size*, **--max-test** *test-size* The maximum test size

Algorithms for equivalence query
--------------------------------

### HC (Hill Climbing)

### Random

### Wp-method

When you use Wp-method, the following option is necessary

**--wp-max-depth** *depth* The maximum depth in the Wp-method

### SA (Simulated Annealing)

When you use simulated annealing, the following option is necessary

**--sa-alpha** *alpha* The alpha parameter for simulated annealing (should be between 0 and 1)

### GA (Genetic Algorithm)

When you use genetic algorithm, the following option is necessary

**--population-size** *size* The size of the population <br />
**--ga-crossover-prob** *prob* The crossover probability (should be between 0 and 1) <br />
**--ga-mutation-prob** *prob* The mutation probability (should be between 0 and 1) <br />
**--ga-selection-kind** *[bestsolution|tournament]* The selection in the genetic algorithm. Either best solution selection or binary tournament.

File format of the mapper
-------------------------

Both input and output mappers are specified by TSV files.

### Input mapper

Input mapper specifies the possible input values of each signal (e.g., break and throttle). Each signal can take different number of inputs i.e., N1 and N2 can be different.

```
<value 1 of signal(1)>	<value 2 of signal(1)>	...	<value N1 of signal(1)>
<value 1 of signal(2)>	<value 2 of signal(2)>	...	<value N2 of signal(2)>
...						
```

### Output mapper

Output mapper specifies how we map the real-valued signal to an atomic proposition. Precisely, we split the vector space R^n by grids. Each grid is one atomic proposition. Since the maximum upper bound is the positive infinity, the last cell for each signal must be `inf`.

```
<upper bound of signal(1) for AP1-1>	<upper bound of signal(1) for AP1-2>	...	<upper bound of signal(1) for AP1-N1>
<upper bound of signal(2) for AP2-1>	<upper bound of signal(2) for AP2-2>	...	<upper bound of signal(2) for AP2-N2>
...
```

Installation
------------

FalCAuN is implemented in Java using MATLAB/Simulink. We suppose FalCAuN works on many UNIX-like operating systems. We tested FalCAuN on macOS 10.15 Catalina, Ubuntu 18.04, and Arch Linux.

### Requirements

- Java 8
- Maven
- LTSMin 3.1.0
  - This is not officially released yet.
  - You have to download it from [HERE](https://github.com/Meijuh/ltsmin/releases/tag/v3.1.0).
- MATLAB/Simulink
  - We tested with MATLAB R2018b but any later version should be fine.

### Instructions

#### 0. Install the Requirements

You need to install the aforementioned requirements. For example, on Ubuntu, you can install Java 8 and Maven by the following command.

```sh
sudo apt-get install maven openjdk-8-jdk-headless -y
```

You have to manually install LTSMin 3.1.0 and MATLAB/Simulink. For example, you can install LTSMin 3.1.0 by the following commands.

```sh
wget https://github.com/Meijuh/ltsmin/releases/download/v3.1.0/ltsmin-v3.1.0-linux.tgz -O ltsmin-v3.1.0-linux.tgz
tar xvf ltsmin-v3.1.0-linux.tgz
sudo cp -r ./v3.1.0/share /usr/local/share
sudo cp -r ./v3.1.0/include /usr/local/include
sudo install ./v3.1.0/bin/* /usr/local/bin
```

#### 1. Setup the environment variable

We assume that the environment variable `MATLAB_HOME` shows where MATLAB is installed. An example is as follows.

```sh
export MATLAB_HOME=<path/to/matlab/home>
## Example:
# export MATLAB_HOME=/usr/local/MATLAB/R2018b/
```

#### 2. Build and Install FalCAuN

You can build and install FalCAuN using maven. You have to execute `mvn clean` to setup the Java API of MATLAB. An example is as follows.

```sh
mvn clean
mvn install
```

#### 3. (Optional) Use/Install the Helper Script

You can use the helper shell script `falcaun` to launch FalCAuN easily. An example usage is as follows. This takes at least a few minutes for MATLAB start up and another few minutes to falsify all the STL formulas in `./example/AT_M4.stl`. Please be patient!!

```sh
./falcaun --stl-file=./example/AT_M4.stl --output-mapper=./example/AT_M4.omap.tsv --input-mapper=./example/AT.imap.tsv --equiv=GA --step-time=1.0 --signal-length=30  --init='cd ./example; initAT' --max-test=50000 --param-names="throttle brake" --ga-crossover-prob=0.5 --ga-mutation-prob=0.01 --population-size=150 --ga-selection-kind=Tournament
```

You can also install this script as follows.

```sh
sudo install falcaun /usr/local/bin
```

### Notes

- The unit test on `mvn install` is disabled by default because it takes much time. If you want, you can run it by `mvn test`
