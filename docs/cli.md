Obsolete CLI interface
======================

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

Usage of the CLI interface
--------------------------

### Synopsis

     ./falcaun [OPTIONS] --stl=[STLFormula] --input-mapper=[InputMapperFile] --output-mapper=[OutputMapperFile] --equiv=[HC|random|WP|SA|GA]

### General Options

**-h**, **--help** Print a help message. <br />
**-v**, **--verbose** It outputs extra information, mainly for debugging. <br />
**-V**, **--version** Print the version <br />
**-t** *timeout*, **--timeout** *timeout* Set timeout [seconds]
**-f** *file*, **--stl-file** *file* Read an STL formula from *file*. <br />
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

### Options Specific to the Equivalence Testing

When you use GA, SA, or WP for the equivalence testing, you have to specify the following options in addition.

### GA (Genetic Algorithm)

**--population-size** *size* The size of the population <br />
**--ga-crossover-prob** *prob* The crossover probability (should be between 0 and 1) <br />
**--ga-mutation-prob** *prob* The mutation probability (should be between 0 and 1) <br />
**--ga-selection-kind** *[bestsolution|tournament]* The selection in the genetic algorithm. Either best solution selection or binary tournament.

### SA (Simulated Annealing)

**--sa-alpha** *alpha* The alpha parameter for simulated annealing (should be between 0 and 1)

#### WP (Wp-method)

**--wp-max-depth** *depth* The maximum depth in the Wp-method

File format of the mapper
-------------------------

Both input and output mappers are specified by TSV files.

### Input mapper

Input mapper specifies the possible input values of each signal (e.g., break and throttle). Each signal can take a different number of inputs i.e., N0 and N1 can be different.

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

### Output mapper

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
