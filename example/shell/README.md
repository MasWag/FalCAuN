This directory contains the example input/output mappers and STL. The examples in this directory use the obsolete CLI interface of FalCAuN.

Files
=====

Autotrans
---------

- `Autotrans_shift.mdl`: Autotrans Simulink model
- `initAT.m`: init script for Autotrans model
- `AT.imap.tsv`: input mapper for Autotrans model
- `AT_M3.omap.tsv`: output mapper for Autotrans M3 benchmark
- `AT_M3.stl`: STL specifications for Autotrans M3 benchmark
- `utils/makeM3-omap.sh`: script to generate omap file for M3-style specifications
- `utils/makeM3STL.sh`: script to generate STL file for M3-style specifications
- `utils/makeM3Test.sh`: test script for M3-style specification
- `AT_M4.omap.tsv`: output mapper for Autotrans M4 benchmark
- `AT_M4.stl`: STL specifications for Autotrans M4 benchmark
- `AT_S1.omap.tsv`: output mapper for Autotrans S1 benchmark
- `AT_S1.stl`: STL specifications for Autotrans S1 benchmark
- `AT_S2.omap.tsv`: output mapper for Autotrans S2 benchmark
- `AT_S2.stl`: STL specifications for Autotrans S2 benchmark
- `AT_S4.omap.tsv`: output mapper for Autotrans S4 benchmark
- `AT_S4.stl`: STL specifications for Autotrans S4 benchmark
- `AT_S5.omap.tsv`: output mapper for Autotrans S5 benchmark
- `AT_S5.stl`: STL specifications for Autotrans S5 benchmark

Abstractfuelcontrol
-------------------

- `Abstractfuelcontrol_breach.slxc`: Abstract fuel control Simulink model
- `initAFC.m`: init script for Abstract fuel control model

Benchmarks
==========

Autotrans is an automatic transmission model in [HAF14]. 

S1
--

This benchmark is taken from [ZGS+18].
The intuition of the benchmark S1 is "the velocity should not be too high".

S2
--

This benchmark is taken from [ZGS+18].
The intuition of the benchmark S2 is "when the gear is 3, the velocity should be reasonably high".

S4
--

This benchmark is taken from [ZGS+18].
The intuition of the benchmark S4 is "the velocity should not drop too much in a short period".

S5
--

This benchmark is taken from [ZGS+18].
The intuition of the benchmark S5 is "the engine rotation should not drop too much in a short period".

M3
--

This is our original benchmark.
The intuition of the benchmark M3 is "the velocity should not increase too much in a short period".

M4
--

This is our original benchmark.
The intuition of the benchmark M4 is "the gear should not change too frequently".

References
==========

- [HAF14]: Bardh Hoxha, Houssam Abbas, and Georgios E. Fainekos. **Benchmarks for Temporal Logic Requirements for Automotive Systems**. *ARCH@CPSWeek 2014*
- [ZGS+18]: Zhenya Zhang, Gidon Ernst, Sean Sedwards, Paolo Arcaini, and Ichiro Hasuo. **Two-Layered Falsification of Hybrid Systems Guided by Monte Carlo Tree Search**. *IEEE Trans. on CAD of Integrated Circuits and Systems vol. 37 2018*
