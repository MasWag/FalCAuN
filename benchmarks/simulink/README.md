# Simulink benchmarks

This directory defines the Simulink benchmarks shared by FalCAuN's MATLAB tests, examples, and experiment scripts.
Each benchmark has one MATLAB initialization script that sets up the model for FalCAuN.
The models themselves come from upstream projects, included as pinned Git submodules under [`third_party/`](third_party/README.md).

| Benchmark | Initialization script | Model | Reference |
|---|---|---|---|
| Automatic transmission (AT) | `AT/initAT.m` | `third_party/breach/Ext/Models/Autotrans_shift.mdl` | [Hoxha et al., ARCH@CPSWeek 2014] |
| Abstract fuel control (AFC) | `AFC/initAFC.m` | `third_party/breach/Ext/Models/AbstractFuelControl.slx` | [Jin et al., HSCC 2014] |
| Chasing cars (CC) | `CC/initCC.m` | `third_party/chasing_cars/cars.mdl` | [Hoxha et al., ARCH@CPSWeek 2014] |

The scripts are plain MATLAB files in the repository; they are not packaged in any FalCAuN JAR file.

## Setup

The submodules are not checked out by a plain `git clone`. Clone FalCAuN with

```sh
git clone --recurse-submodules https://github.com/MasWag/FalCAuN.git
```

or, in an existing clone,

```sh
git submodule update --init --recursive
```

The AT model additionally loads `sldemo_autotrans_data` from the example by MathWorks, which you can set up with `openExample('simulink_automotive/ModelingAnAutomaticTransmissionControllerExample')` in MATLAB.

## Usage

Run an initialization script by its **absolute path** as (a part of) FalCAuN's initialization script, for example:

```matlab
run('/path/to/FalCAuN/benchmarks/simulink/AT/initAT.m');
```

`run` executes exactly the given file, so another `initAT.m` on the MATLAB path is never used by mistake, and the command works regardless of MATLAB's current directory.
Each script defines `mdl` and the model parameters in the caller's workspace, as FalCAuN expects from an initialization script.

- **Kotlin, Scala, and Clojure examples** generate this command with a small helper (`benchmarkInitScript("AT/initAT.m")` in Kotlin and Scala, `benchmark-init-script` in Clojure). The helper finds the FalCAuN repository by searching upwards from the current working directory, so run the examples inside the repository.
- **`example/kotlin/autotrans_matlab.py`** runs `AT/initAT.m` by its path relative to the Python file.
- **The MATLAB tests and the CLI-based examples** (`matlab/src/test/resources/MATLAB`, `example/shell`, `example/hscc2020`, `example/rv2021`, and `example/java`) keep their own `initAT.m` and `initAFC.m`. These are thin wrappers that run the scripts here, so `cd <directory>; initAT` keeps working.

## Behavior

- Each model is loaded by its absolute path in the submodule. A model with the same name that is already loaded from another file is closed first. Another model with the same name on the MATLAB path is never used.
- If a submodule is missing, the script stops with the error `FalCAuN:missingSubmodule`, which explains how to initialize the submodules. Nothing is downloaded at runtime.
- **AT:** since R2026b, the example by MathWorks provides `sldemo_autotrans_data` in SI units, while the model and the benchmark properties assume US customary units (rpm, mph, lbf·ft). `AT/initAT.m` detects SI data and converts it back. With older releases, the data is already in US customary units and is used as is.
- **AFC:** `AFC/initAFC.m` also defines the model parameters (tolerances, fault time, and controller gains) used by FalCAuN's tests.

## Adding a benchmark

1. Add the upstream repository as a submodule under `third_party/`, pinned to a specific commit, and document it in [`third_party/README.md`](third_party/README.md).
2. Add `<NAME>/init<NAME>.m`, following the existing scripts: resolve the model path relative to the script, check that the file exists, load it by its absolute path, and define `mdl` and the parameters.

## References

- [Hoxha et al., ARCH@CPSWeek 2014]: Bardh Hoxha, Houssam Abbas, Georgios E. Fainekos. *Benchmarks for Temporal Logic Requirements for Automotive Systems*. ARCH@CPSWeek 2014.
- [Jin et al., HSCC 2014]: X. Jin, J. V. Deshmukh, J. Kapinski, K. Ueda, and K. Butts. *Powertrain Control Verification Benchmark*. HSCC 2014.
