FalCAuN Examples with Clojure
=============================

This directory contains examples to directly execute FalCAuN via Clojure. 

Requirements
------------

- [Leiningen](https://leiningen.org/)
- FalCAuN

We assume that the environment variable `MATLAB_HOME` is appropriately specified.

Usage
-----

```sh
lein exec -p cart-pole.clj
```

For the scripts using python, probably you have to set some environment variables appropriately, such as:

```sh
export JEP_JAVA_LIBRARY_PATH="$PWD/.venv/lib/python3.10/site-packages/jep"
export PYTHONEXECUTABLE="$PWD/.venv/bin/python3.10"
```
