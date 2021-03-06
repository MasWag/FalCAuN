Experiments Data for HSCC 2020
==============================

This is a document on the experiment data for the HSCC 2020 paper [Waga20].
We implemented and evaluated our tool FalCAuN. See also [README.md](../../README.md).

Breach
------

As a baseline, we used [*Breach*](https://github.com/decyphir/breach), which is one of the state-of-the-art falsification tool. We used [Breach version 1.5.2](https://github.com/decyphir/breach/releases/tag/1.5.2). See https://github.com/decyphir/breach/blob/1.5.2/README.md for the installation instruction of Breach.

How to reproduce the experiment results
---------------------------------------

### Experiments

The scripts and data to reproduce the experiment results is included in this directory. We note that these scripts do not repeat the experiments while in the paper, we repeated the experiments 10 times and computed their means and standard deviations. The results are saved under `./results`. 

The experiments take more time than the timeout because we check the timeout only at the beginning of the equivalence testing. The time for the initialization of MATLAB/Simulink is not excluded from the timeout.

#### FalCAuN

You can run the experiment on FalCAuN for all the setting simply by the following command.

```bash
./run_falcaun_all.sh
```

Since the timeout is 4 hour by default, it may take quite a lot of time. If you want to make the timeout shorter, you can specify as follows.

```bash
./run_falcaun_all.sh $((30 * 60)) # The timeout is in seconds. Here, the timeout is 30 minutes for each benchmark.
```

If you want to run the experiments one by one, you can use `./run_falcaun.sh`. The following is an example.

```bash
./run_falcaun.sh GA AT_M1-large $((30 * 60)) #  [kind] [Spec] [timeout in sec.]
```

#### Breach

You can run the experiment on Breach for all the setting simply by the following command.

```bash
./run_breach_all.sh
```

If you want to run the experiments one by one, you can use `./run_breach.sh`. The following is an example.

```bash
./run_breach.sh AT_M1_16 # [Spec]
```

### Analysis

The table and the plot similar to the paper can be generated by

```bash
make
```

The name of the generated table and plot are `mean.summary.standalone.pdf` and `mean.M1.plot.standalone.pdf`, respectively.

The analysis requires the following commands.

- pdflatex
- [gnuplot](http://www.gnuplot.info/)
- [GNU datamash](https://www.gnu.org/software/datamash/)
- GNU date
- the standard *nix command e.g., awk, sed, m4, ...

Files
-----

The files in this directory is as follows.

    .
    ├── README.md
    << Scripts to Run the Experiments >>
    ├── run_breach.sh
    ├── run_breach_all.sh
    ├── run_falcaun.sh
    ├── run_falcaun_all.sh
    << Scripts for Analysis >>
    ├── Makefile
    ├── summary.standalone.tex.m4
    ├── mean.M1.plot.tikz.plt
    ├── all.summary.header
    ├── mean-std.summary.header
    ├── mean.states.summary.header
    ├── mean.summary.header
    ├── result_name.yaml
    ├── utils/
    │   ├── CV2Br_stl.sh
    │   ├── README.md
    │   ├── diffDate.sh
    │   ├── extractBBCElapsedTime.sh
    │   ├── extractBeginningTime.sh
    │   ├── extractFalsified.sh
    │   ├── extractFalsifiedTime.sh
    │   ├── list2result.awk
    │   ├── list2states.awk
    │   ├── makeRawNumTime.sh
    │   ├── makeStateSize.sh
    │   ├── parsrj.sh
    │   └── tsv2tabular.awk
    << Files for FalCAuN >>
    ├── AT.imap.tsv
    ├── AT_M1-gigantic.omap.tsv
    ├── AT_M1-gigantic.stl
    ├── AT_M1-huge.omap.tsv
    ├── AT_M1-huge.stl
    ├── AT_M1-large.omap.tsv
    ├── AT_M1-large.stl
    ├── AT_M1-medium.omap.tsv
    ├── AT_M1-medium.stl
    ├── AT_M1-small.omap.tsv
    ├── AT_M1-small.stl
    ├── AT_M1-tiny.omap.tsv
    ├── AT_M1-tiny.stl
    ├── AT_M2.omap.tsv
    ├── AT_M2.stl
    ├── AT_S1.omap.tsv
    ├── AT_S1.stl
    ├── AT_S2.omap.tsv
    ├── AT_S2.stl
    ├── AT_S3.omap.tsv
    ├── AT_S3.stl
    ├── AT_S4.omap.tsv
    ├── AT_S4.stl
    ├── AT_S5.omap.tsv
    ├── AT_S5.stl
    ├── Autotrans_shift.mdl
    ├── initAT.m
    << Files for Breach >>
    ├── breach_scripts
    │   ├── InitAT.m
    │   ├── run_breach_AT_M1_12.m
    │   ├── run_breach_AT_M1_18.m
    │   ├── run_breach_AT_M1_2.m
    │   ├── run_breach_AT_M1_36.m
    │   ├── run_breach_AT_M1_4.m
    │   ├── run_breach_AT_M1_8.m
    │   ├── run_breach_AT_M2.m
    │   ├── run_breach_AT_S1.m
    │   ├── run_breach_AT_S2.m
    │   ├── run_breach_AT_S3.m
    │   ├── run_breach_AT_S4.m
    │   └── run_breach_AT_S5.m
    └── breach_stl
        ├── AT_M1_12.stl
        ├── AT_M1_18.stl
        ├── AT_M1_2.stl
        ├── AT_M1_36.stl
        ├── AT_M1_4.stl
        ├── AT_M1_8.stl
        ├── AT_M2.stl
        ├── AT_S1.stl
        ├── AT_S2.stl
        ├── AT_S3.stl
        ├── AT_S4.stl
        └── AT_S5.stl


Experimental raw data
---------------------

We conducted the experiments on an Amazon EC2 c4.large instance (2.9 GHz Intel Xeon E5-2666 v3, 2 vCPUs, and 3.75 GiB RAM).

The input/output mapper definition and STL files are in this directory. Namely, the following are the files for the input/output mapper and STL.

    .
    ├── AT.imap.tsv
    ├── AT_M1-gigantic.omap.tsv
    ├── AT_M1-gigantic.stl
    ├── AT_M1-huge.omap.tsv
    ├── AT_M1-huge.stl
    ├── AT_M1-large.omap.tsv
    ├── AT_M1-large.stl
    ├── AT_M1-medium.omap.tsv
    ├── AT_M1-medium.stl
    ├── AT_M1-small.omap.tsv
    ├── AT_M1-small.stl
    ├── AT_M1-tiny.omap.tsv
    ├── AT_M1-tiny.stl
    ├── AT_M2.omap.tsv
    ├── AT_M2.stl
    ├── AT_S1.omap.tsv
    ├── AT_S1.stl
    ├── AT_S2.omap.tsv
    ├── AT_S2.stl
    ├── AT_S3.omap.tsv
    ├── AT_S3.stl
    ├── AT_S4.omap.tsv
    ├── AT_S4.stl
    ├── AT_S5.omap.tsv
    └── AT_S5.stl

Description of the Benchmarks
-----------------------------

In all of the benchmarks, we use the Simulink model (`Autotrans_shift.mdl`) of an automatic transmission system [HAF14]. The STL formulas in S1--S5 are taken from [ZESAH18] and the STL formulas in M1 and M2 are our original.

### S1

The intuition of S1 specification is the velocity should not change too much in a short period. The amount of "too much" is different among the instances.

### S2

The intuition of S2 specification is if the gear is 3, the velocity should be high enough. The amount of "high enough" is different among the instances.

### S3

The intuition of S3 specification is we cannot keep constant velocity in a certain range for a while. The length of "for a while" and the "certain range" are different among the instances.

### S4

The intuition of S4 specification is the velocity should not change too much in a short period. The amount of "too much" is different among the instances.

### S5

The intuition of S5 specification is the engine rotation should not change too much in a short period. The amount of "too much" is different among the instances.

### M1

The intuition of M1 specifications is "the velocity of a car should not increase too suddenly". The amount of "suddenly" is different among the concrete specifications.

- tiny
- small
- medium
- large
- huge
- gigantic

### M2

The intuition of M2 specifications is "The gear should not change too soon after the latest gear change". The amount of "soon" is different among the concrete specifications.

References
----------

<dl>
<dt>[Waga20]</dt>
<dd>Masaki Waga, Falsification of Cyber-Physical Systems with Robustness-Guided Black-Box Checking, To appear in Proc. HSCC 2020.</dd>
<dt>[HAF14]</dt>
<dd>Bardh Hoxha, Houssam Abbas, and Georgios E. Fainekos, Benchmarks for Temporal Logic Requirements for Automotive
Systems, Proc. ARCH@CPSWeek / ARCH@CPSWeek 2015, Vol. 34. EasyChair, 25–30.</dd>
<dt>[ZESAH18]</dt>
<dd>Zhenya Zhang, Gidon Ernst, Sean Sedwards, Paolo Arcaini, and Ichiro Hasuo, Two-Layered Falsification of Hybrid Systems Guided by Monte Carlo Tree Search, IEEE Trans. on CAD of Integrated Circuits and Systems 37, 11 (2018), 2894–2905</dd>
</dl>

<!--  LocalWords:  HSCC FalCAuN README md Xeon STL Autotrans mdl HAF
 -->
<!--  LocalWords:  ZESAH
 -->
