FROM debian:bookworm

### Build LTSMin

# 1) Base tools & Spot repo key
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      ca-certificates wget gnupg lsb-release

# 2) Add Spot’s Debian repo (stable)
RUN wget -qO- https://www.lrde.epita.fr/repo/debian.gpg | apt-key add - && \
    echo "deb http://www.lrde.epita.fr/repo/debian/ stable/" >> /etc/apt/sources.list

# 3) Install ALL build deps + Spot
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      autoconf automake bison build-essential curl \
      doxygen flex git libpopt-dev libtool libltdl-dev liblzma-dev \
      libxml2-dev pkgconf python3 python3-dev python3-pip xmlto zlib1g-dev \
      asciidoc openjdk-17-jdk ant unzip \
      spot libspot-dev maven python3-notebook python3-ipykernel \
    && rm -rf /var/lib/apt/lists/*

# 4) Clone LTSmin (with submodules) & bootstrap autotools
WORKDIR /build
RUN git clone --branch v3.1.0-beta2 --recursive https://github.com/Meijuh/ltsmin.git
WORKDIR /build/ltsmin
RUN ./ltsminreconf

# 5) Update ltl2ba to avoid its link-time conflict
RUN cd ltl2ba && git checkout master && git pull

# Make some variables extern to avoid link errors.
RUN sed -i 's/^ltsmin_expr_t/extern ltsmin_expr_t/;s/^ltsmin_parse_env_t/extern ltsmin_parse_env_t/;' ./src/pins2lts-sym/aux/options.h

# 6) Configure, build & install
RUN ./configure --disable-dependency-tracking && \
    make -j$(nproc) && \
    make install

# Install Kotlin 1.9.x and Kscript with SDK
RUN apt update && apt install zip -y
RUN curl -s "https://get.sdkman.io" | bash && chmod +x $HOME/.sdkman/bin/sdkman-init.sh && bash -c "source $HOME/.sdkman/bin/sdkman-init.sh && sdk install kotlin 1.9.24 && sdk install kscript"

# Install
RUN apt update && apt install python3.11-full -y
RUN python3 -m venv /jupyter-env
RUN . /jupyter-env/bin/activate && pip install kotlin-jupyter-kernel jupyter

WORKDIR /
RUN git clone https://github.com/MasWag/FalCAuN.git
WORKDIR /FalCAuN
RUN cd /FalCAuN && mvn install --projects examples,core,

WORKDIR /FalCAuN/example/kotlin
CMD bash -c '. $HOME/.sdkman/bin/sdkman-init.sh && . /jupyter-env/bin/activate && cd /FalCAuN/ && mvn install --projects examples,core, && cd example/kotlin && jupyter notebook --ip=0.0.0.0 --allow-root'
