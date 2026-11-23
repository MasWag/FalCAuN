docker
======

This directory contains `Dockerfile` to run FalCAuN on Docker. We tested this environment on linux/amd64.

How to build
------------

You can build the docker image as follows.

```sh
docker build -t falcaun .
```

How to use this image
---------------------

### Start a docker container

First, start a docker container as follows.

```sh
docker run --rm --shm-size=512M -p 5901:5901 -p 6080:6080 -it falcaun -vnc
```

### Connect to the VNC environment

Then, connect to the container via VNC. We have the following two methods.

- If you use a VNC client, connect to display 1 (or port 5901).
- If you do not use a VNC client, open http://localhost:6080 with a browser.

If you are asked to enter a password, please type `matlab`.

### Open MATLAB and activate

Click the MATLAB icon on the desktop and activate the MATLAB license.

### Enable MATLAB engine

Then, execute `matlab.engine.shareEngine` to share this MATLAB session with FalCAuN.

### (Optional) Set up AT environment

If you use the AT environment, run `openExample('simulink_automotive/ModelingAnAutomaticTransmissionControllerExample')` in MATLAB. A window of the AT model will open.

### Run the scripts

The Docker image clones FalCAuN **without** its Git submodules: the third-party Simulink models are not redistributed in the image (see `benchmarks/simulink/third_party/README.md`). To run the examples that use these models, initialize them in the container first: `cd /home/matlab/FalCAuN && git submodule update --init --recursive`.

Finally, you can run the Kotlin scripts. Open a terminal at the bottom of the desktop. Move to the directory containing examples of FalCAuN with `cd /home/matlab/FalCAuN/example/kotlin` and run a script, e.g., `./mealy-nox.main.kts` or `./ATS1.main.kts`. The examples using the Simulink benchmarks (e.g., `ATS1.main.kts`) run the shared definitions in `benchmarks/simulink` by their absolute paths, so the current directory of the MATLAB session does not matter for them.
