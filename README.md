CyVeriA
=======

[![CircleCI](https://circleci.com/gh/MasWag/CyVeriA.svg?style=svg&circle-token=529c89869f5a7b6e9f957ee656ffc55349d050ca)](https://circleci.com/gh/MasWag/CyVeriA)

This is the source code repository for CyVeriA ---  Cyber-Physical System Verifier via Automata Learning.

Usage
-----

### Symopsis

    cyveria [OPTIONS] --stl=[STLFormula] --input-mapper=[InputMapperFile] --output-mapper=[OutputMapperFile] --equiv=[HC|random|WP]

### Options

**-h**, **--help** Print a help message. <br />
**-v**, **--verbose** It outputs extra information, mainly for debugging. <br />
**-V**, **--version** Print the version <br />
**-f** *file*, **--stl-file** *file* Read a STL formula from *file*. <br />
**-e** *pattern*, **--stl** *STLFormula* Specify *STLFormula* by signal temporal logic. <br />
**-I** *file*, **--input-mapper** *file* Read the input mapper configuration from *file*. <br />
**-O** *file*, **--output-mapper** *file* Read the output mapper configuration from *file*. <br />
**-E** *algorithm*, **--equiv** *algorithm* Specify the equivalence query algorithm. See below for the detail. <br />
**-o** *file*, **--output** *file* Write the learned Mealy machine to *file* in DOT format. <br />
**-s** *step-time*, **--step-time** *step-time* Specify the step time of the sampling.
**-l** *length*, **--signal-length** *length* Specify the length of the sampled signals.

Algorithms for equivalence query
--------------------------------

### HC (Hill Climbing)

### Random

### WP-method

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

### Requirements

- Java 8
- Maven
- LTSMin 3.1.0
  - This is not officially released yet.
  - You have to download it from [HERE](https://github.com/Meijuh/ltsmin/releases/tag/v3.1.0).
- MATLAB


### Instructions

```sh
export MATLAB_HOME=<path/to/matlab/home>
mvn clean
mvn install
```

