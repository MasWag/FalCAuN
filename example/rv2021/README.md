Experiments Data for RV 2021
==============================

This is a document on the experiment data for the RV 2021 paper.
We implemented and evaluated our enhancement of BBC based on FalCAuN [Waga20].

### Experiments

The scripts and data to reproduce the experiment results is included in this directory.
We note that these scripts only generate CSV files that contains experiments data. In the paper, we computed their means and standard deviations. The results are saved under `./experiment_results`.

The experiments take more time than the timeout because we check the timeout only at the beginning of the equivalence testing. The time for the initialization of MATLAB/Simulink is not excluded from the timeout.

#### FalCAuN

As a baseline, we used [*FalCAuN*](https://github.com/MasWag/FalCAuN), which is black box checking tool.
We implemented BBC enhanced via model checking with strengthened formulas based on FalCAuN.

You can run the experiments 50 times on FalCAuN and enhanced FalCAuN for all the settings simply by the following command.

```bash
./run_falcaun_all.sh
```

Since the timeout is 4 hour by default, it may take quite a lot of time. If you want to make the timeout shorter, you can specify as follows.

```bash
./run_falcaun_all.sh $((30 * 60)) # The timeout is in seconds. Here, the timeout is 30 minutes for each benchmark.
```

If you want to run the experiments one by one, you can use `./run_falcaun_static.sh` for baseline, or `./run_falcaun_adaptive` for enhanced FalCAuN. The following is an example.

```bash
./run_falcaun_adaptive.sh GA AT_F1 $((30 * 60)) #  [kind] [Spec] [timeout in sec.]
```

### Analysis

The following command generates CSV files that contains the experiment result under `./experiment_results` folder.

```bash
./to_csv.sh
```

Files
-----

The files in this directory is as follows.

    .
    ├── README.md
    << Scripts to Run the Experiments >>
    ├── run_falcaun_adaptive.sh
    ├── run_falcaun_static.sh
    ├── run_falcaun_many.sh
    ├── run_falcaun_all.sh
    << Files for FalCAuN >>
    ├── AT.imap.tsv
    ├── AT_F1.omap.tsv
    ├── AT_F1.stl
    ├── AT_F2.omap.tsv
    ├── AT_F2.stl
    ├── AT_F3.omap.tsv
    ├── AT_F3.stl
    ├── AT_F4.omap.tsv
    ├── AT_F4.stl
    ├── AT_F5.omap.tsv
    ├── AT_F5.stl
    ├── Autotrans_shift.mdl
    └── initAT.m


Description of the Benchmarks
-----------------------------

In all of the benchmarks, we use the Simulink model (`Autotrans_shift.mdl`) of an automatic transmission system [HAF14]. The STL formulas in F1 and F2 are taken from [ZESAH18] and the STL formulas in F3--F5 are our original.

### F1

The intuition of S4 specification is the velocity should not change too much in a short period. The amount of "too much" is different among the instances.

### F2

The intuition of S5 specification is the engine rotation should not change too much in a short period. The amount of "too much" is different among the instances.

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
