FalCAuN Examples with Clojure
=============================

This directory contains examples to directly execute FalCAuN via Clojure. 

Requirements
------------

- [Leiningen](https://leiningen.org/)
- FalCAuN

We assume that the environment variable `MATLAB_HOME` is appropriately specified.

`project.clj` declares the MATLAB Engine API for Java (`[com.mathworks/engine "1.1" :scope "provided"]`) explicitly because FalCAuN does not bundle it. It is the `engine.jar` of your MATLAB installation, installed to your local Maven repository by `mvn clean --projects matlab` in FalCAuN. The native library path of MATLAB is set separately in `:jvm-opts`.

The Simulink models used by the MATLAB examples (the automatic transmission model in `auto_trans.clj`) are set up by the shared benchmark definitions in [`benchmarks/simulink`](../../benchmarks/simulink/README.md), and the models are provided by Git submodules. Initialize them with `git submodule update --init --recursive` and run the examples from inside the FalCAuN repository: the path of the benchmark definition is resolved by searching upwards from the current working directory.

Usage
-----

```sh
lein exec -p cart-pole.clj
```

For the scripts using Python, you probably have to set some environment variables appropriately, such as:

```sh
export JEP_JAVA_LIBRARY_PATH="$PWD/.venv/lib/python3.10/site-packages/jep"
export PYTHONEXECUTABLE="$PWD/.venv/bin/python3.10"
```
