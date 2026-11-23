# Third-party Simulink models

The Simulink models of FalCAuN's benchmarks (see [`../README.md`](../README.md)) are not part of FalCAuN.
They are developed by separate upstream projects and included here as [Git submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules), each pinned to a specific upstream commit for reproducibility.

The submodules are not checked out by a plain `git clone`. To obtain them, clone FalCAuN with

```sh
git clone --recurse-submodules https://github.com/MasWag/FalCAuN.git
```

or, in an existing clone,

```sh
git submodule update --init --recursive
```

The core module, the Python module, and the examples that do not use these Simulink models work without the submodules.
The benchmark definitions in [`..`](../README.md) (e.g., `AT/initAT.m`) load the models below **by their absolute paths in these submodules**.
If a submodule is missing, they stop with an error explaining how to initialize it. They never fall back to a model with the same name elsewhere on the MATLAB path, and they never download models at runtime.

## Models

| Submodule (in this directory) | Upstream repository | Pinned commit | Model used by FalCAuN | Last upstream change of the model |
|---|---|---|---|---|
| `breach` | <https://github.com/decyphir/breach> | `1f8a495727eb04bf849175d33963be5e26a8bfdd` | `Ext/Models/Autotrans_shift.mdl` (automatic transmission, AT) | `a65304c` (2018-06-18) |
| | | | `Ext/Models/AbstractFuelControl.slx` (abstract fuel control, AFC) | `4fe0293` (2018-12-17) |
| `chasing_cars` | <https://github.com/lassekotz/Chasing_Cars> | `7f254bf1818c17af83819e076a8d27c2819dcf4e` | `cars.mdl` (chasing cars, CC) | `9c610f6` (2026-01-28) |

### Relation to the copies previously committed to FalCAuN

Earlier versions of FalCAuN contained copies of these models. They were removed from the source tree; the Git history still contains them.

- `Autotrans_shift.mdl` (8 copies), `AbstractFuelControl.slx`, and `cars.mdl` were byte-identical to the files at the pinned commits.
- `example/java/src/resources/MATLAB/Autotrans_shift.mdl` was a re-save (Simulink 9.2, R2017b) of the Breach model. The only semantic differences were `StopTime` (70 instead of 30) and test points on the `throttle` and `brake` signals. FalCAuN overrides `StopTime` and the solver settings for every simulation, and test points only affect signal logging. In MATLAB R2026b, simulating it and the Breach model with FalCAuN's settings gave identical outputs (maximum absolute difference 0) on 10 throttle/brake input traces (corner cases and random), so the Breach model replaces it.

## Licenses

The submodules are separate works by their respective authors.
They are **not** licensed under FalCAuN's GPLv3 just because this repository refers to them: each one is governed by its own upstream terms.

- **Breach** is distributed under a BSD-style license (see `breach/LICENSE`, "Copyright (c) 2017, Decyphir, Inc").
  **Open question:** `Autotrans_shift.mdl` derives from the automatic transmission example by MathWorks ([Hoxha et al., ARCH@CPSWeek 2014]). It also loads `sldemo_autotrans_data` from the MathWorks example at load time. It hasn't been established whether Breach's license covers this MathWorks-derived content.
- **Chasing Cars**: no explicit upstream license has been established. The repository contains no license file, and its `README.md` doesn't state license terms.

## Redistribution

Do not bundle the contents of these submodules into FalCAuN release archives, JAR files, or Docker images without first reviewing the redistribution rights for each model.
The Docker image built from `docker/Dockerfile` intentionally clones FalCAuN **without** submodules.

## Updating a submodule

To move a submodule to another upstream commit, check out the commit inside the submodule, then stage the submodule path in FalCAuN:

```sh
git -C benchmarks/simulink/third_party/breach fetch
git -C benchmarks/simulink/third_party/breach checkout <commit>
git add benchmarks/simulink/third_party/breach
```

Update the table above, and rerun the MATLAB integration tests to check that the benchmark behavior is unchanged.

## References

- [Hoxha et al., ARCH@CPSWeek 2014]: Bardh Hoxha, Houssam Abbas, Georgios E. Fainekos. *Benchmarks for Temporal Logic Requirements for Automotive Systems*. ARCH@CPSWeek 2014.
- [Jin et al., HSCC 2014]: X. Jin, J. V. Deshmukh, J. Kapinski, K. Ueda, and K. Butts. *Powertrain Control Verification Benchmark*. HSCC 2014.
