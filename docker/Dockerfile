FROM debian:bookworm

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ARG LTSMIN_VERSION=v3.1.0-beta2
ARG KOTLIN_VERSION=1.9.24

# 1) Add Spot’s GPG key & repo, install all system dependencies in one go
ADD https://www.lrde.epita.fr/repo/debian.gpg \
    /usr/share/keyrings/spot-archive-keyring.gpg

RUN echo "deb [signed-by=/usr/share/keyrings/spot-archive-keyring.gpg] \
          http://www.lrde.epita.fr/repo/debian/ stable/" \
     > /etc/apt/sources.list.d/spot.list && \
    apt-get update && \
    apt-get install -y --no-install-recommends \
      ca-certificates lsb-release curl unzip zip \
      autoconf automake bison build-essential flex \
      doxygen git libpopt-dev libtool libltdl-dev \
      liblzma-dev libxml2-dev pkgconf \
      python3 python3-venv python3-dev python3-pip \
      xmlto asciidoc openjdk-17-jdk ant maven \
      zlib1g-dev spot libspot-dev && \
    rm -rf /var/lib/apt/lists/*

# 2) Build & install LTSmin (incl. latest ltl2ba & autotools bootstrap)
WORKDIR /build

RUN git clone --branch ${LTSMIN_VERSION} --recursive \
        https://github.com/Meijuh/ltsmin.git ltsmin && \
    cd ltsmin && \
    ./ltsminreconf && \
    cd ltl2ba && git pull origin master && cd .. && \
    sed -i \
      -e 's/^ltsmin_expr_t/extern ltsmin_expr_t/' \
      -e 's/^ltsmin_parse_env_t/extern ltsmin_parse_env_t/' \
      src/pins2lts-sym/aux/options.h && \
    ./configure --disable-dependency-tracking && \
    make -j"$(nproc)" && \
    make install

# 3) Install SDKMAN + Kotlin + kscript
ENV SDKMAN_DIR=/usr/local/sdkman

RUN curl -s "https://get.sdkman.io" | bash && \
    bash -lc "source ${SDKMAN_DIR}/bin/sdkman-init.sh && \
              sdk install kotlin ${KOTLIN_VERSION} && \
              sdk install kscript"

# 4) Create a Python venv and install Jupyter + Kotlin kernel via pip
ENV PATH="/opt/jupyter-env/bin:${PATH}"

RUN python3 -m venv /opt/jupyter-env && \
    /opt/jupyter-env/bin/pip install --upgrade pip && \
    /opt/jupyter-env/bin/pip install kotlin-jupyter-kernel jupyter

# 5) Clone & build FalCAuN examples (single mvn invocation)
WORKDIR /FalCAuN

RUN git clone https://github.com/MasWag/FalCAuN.git . && \
    mvn install -DskipTests -pl examples,core

# 6) Final working dir & default command
WORKDIR /FalCAuN/example/kotlin
EXPOSE 8888

CMD bash -lc "\
    source ${SDKMAN_DIR}/bin/sdkman-init.sh && \
    source /opt/jupyter-env/bin/activate && \
    jupyter notebook --ip=0.0.0.0 --allow-root \
"
