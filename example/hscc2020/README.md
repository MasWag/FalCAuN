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


Benchmark Copy is inspired by the monitoring of variable updates much like the scenario in [BDSV14]. The action is `update` and `update` has one string and one integer values. The string value is the name of the updated variable and the integer value is the updated value.

### Dominant

Benchmark Dominant is inspired by the monitoring of withdrawals from bank accounts of various users much like the scenario in [BKZ17]. The action is `withdraw` and `withdraw` has one string and one integer values. The string value is the user name and the integer value is the amount of the withdrawals.

### Periodic

Benchmark Periodic is inspired by a parameter identification of periodic withdrawals from one bank account. The action is `withdraw` and `withdraw` has one integer value. The the integer value is the amount of the withdrawals.


Calling FalCAuN
---------------

For all case studies, the following command was used for PTPM:

>  ../../falcaun 

Calling Breach
--------------

For all case studies, the following command was used for PTPM:

>  ../../falcaun 

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

<!--  LocalWords:  HSCC FalCAuN README md Xeon STL Autotrans mdl HAF
 -->
<!--  LocalWords:  ZESAH
 -->
