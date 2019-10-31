Experiments Data for HSCC 2020
==============================

This is a document on the experiment data for the HSCC 2020 paper [Waga20].
We implemented and evaluated our tool FalCAuN. See also [README.md](../README.md).

Breach
------

As a baseline, we used [*Breach*](https://github.com/decyphir/breach), which is one of the state-of-the-art falsification tool. We used [Breach version 1.5.2](https://github.com/decyphir/breach/releases/tag/1.5.2).

Experimental raw data
---------------------

We conducted the experiments on an Amazon EC2 c4.large instance (2.9 GHz Intel Xeon E5-2666 v3, 2 vCPUs, and 3.75 GiB RAM).

The input/output mapper definition and STL files are in this directory. 

Description of the Benchmarks
-----------------------------

### S1

### S2

### S3

### S4

### S5

### M1

- tiny
- small
- medium
- large
- huge
- gigantic

### M2

Benchmark Copy is inspired by the monitoring of variable updates much like the scenario in [BDSV14]. The action is `update` and `update` has one string and one integer values. The string value is the name of the updated variable and the integer value is the updated value.

### Dominant

Benchmark Dominant is inspired by the monitoring of withdrawals from bank accounts of various users much like the scenario in [BKZ17]. The action is `withdraw` and `withdraw` has one string and one integer values. The string value is the user name and the integer value is the amount of the withdrawals.

### Periodic

Benchmark Periodic is inspired by a parameter identification of periodic withdrawals from one bank account. The action is `withdraw` and `withdraw` has one integer value. The the integer value is the amount of the withdrawals.


Calling FalCAuN
---------------

For all case studies, the following command was used for PTPM:

>  ./build/symon -pf [ptda.dot] < [timed_data_word.txt]

References
----------

<dl>
<dt>[Waga20]</dt>
<dd>Masaki Waga, Falsification of Cyber-Physical Systems with Robustness-Guided Black-Box Checking, Proc. HSCC 2020, <del>LNCS 11561, pp. 520-539</del>.</dd>
<dt>[HAF14]</dt>
<dd>Bardh Hoxha, Houssam Abbas, and Georgios E. Fainekos, Benchmarks for Temporal Logic Requirements for Automotive
Systems, Proc. ARCH@CPSWeek / ARCH@CPSWeek 2015, Vol. 34. EasyChair, 25–30.</dd>
<dt>[ZESAH18]</dt>
<dd>Zhenya Zhang, Gidon Ernst, Sean Sedwards, Paolo Arcaini, and Ichiro Hasuo, Two-Layered Falsification of Hybrid Systems Guided by Monte Carlo Tree Search, IEEE Trans. on CAD of Integrated Circuits and Systems 37, 11 (2018), 2894–2905</dd>
</dl>
