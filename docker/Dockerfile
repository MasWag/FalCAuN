ARG MATLAB_RELEASE="R2024b"
FROM mathworks/matlab:${MATLAB_RELEASE}
LABEL maintainer="Masaki Waga <masakiwaga@gmail.com>"

ARG MATLAB_RELEASE
ARG MATLAB_PRODUCT_LIST="MATLAB Simulink"
ARG MATLAB_INSTALL_LOCATION="/opt/matlab/${MATLAB_RELEASE}"

USER root
# Install the dependencies
RUN export DEBIAN_FRONTEND=noninteractive \
    && apt update \
    && apt-get install --no-install-recommends --yes \
    wget \
    ca-certificates \
    curl \
    git \
    build-essential \
    python3 \
    python3-dev \
    zip \
    && apt-get clean \
    && apt-get autoremove \
    && rm -rf /var/lib/apt/lists/*


USER matlab
WORKDIR /home/matlab

# Install Simulink
RUN wget -q https://www.mathworks.com/mpm/glnxa64/mpm \
    && chmod +x mpm \
    && sudo HOME=${HOME} ./mpm install \
    --release=${MATLAB_RELEASE} \
    --destination=${MATLAB_INSTALL_LOCATION} \
    --products ${MATLAB_PRODUCT_LIST} \
    || (echo "MPM Installation Failure. See below for more information:" && cat /tmp/mathworks_root.log && false) \
    && sudo rm -rf mpm /tmp/mathworks_root.log \
    && sudo ln -s ${MATLAB_INSTALL_LOCATION}/bin/matlab /usr/bin/matlab

# We need to use bash rather than sh
SHELL ["/bin/bash", "-c"]

# Install Java, Kotlin, and kscript with sdkman
RUN curl -s "https://get.sdkman.io?ci=true" | bash \
    && source ~/.sdkman/bin/sdkman-init.sh \
    # MATLAB R2024b on Linux supports only OpenJDK 21.0.2+13 and earlier, which sdkman no longer lists
    && wget -q https://github.com/adoptium/temurin21-binaries/releases/download/jdk-21.0.2%2B13/OpenJDK21U-jdk_x64_linux_hotspot_21.0.2_13.tar.gz \
    && mkdir -p ~/jdk && tar xzf OpenJDK21U-jdk_x64_linux_hotspot_21.0.2_13.tar.gz -C ~/jdk \
    && rm OpenJDK21U-jdk_x64_linux_hotspot_21.0.2_13.tar.gz \
    && sdk install java 21.0.2-tem ~/jdk/jdk-21.0.2+13 \
    && sdk default java 21.0.2-tem \
    && sdk install kotlin 1.9.24 \
    && sdk install kscript \
    && sdk install maven

# Install LTSMin 3.1.0
RUN wget https://github.com/Meijuh/ltsmin/releases/download/v3.1.0/ltsmin-v3.1.0-linux.tgz \
    && tar xvf ltsmin-v3.1.0-linux.tgz \
    && sudo cp -r v3.1.0/* /usr

# Install Python and Jep
RUN source ~/.sdkman/bin/sdkman-init.sh \
    && pip install --upgrade setuptools wheel \
    && pip install --no-cache-dir --no-build-isolation jep \
    && pip show jep

# Install FalCAuN
ENV MATLAB_HOME="/opt/matlab/${MATLAB_RELEASE}"
RUN git clone https://github.com/MasWag/FalCAuN.git /home/matlab/FalCAuN
WORKDIR /home/matlab/FalCAuN
RUN source ~/.sdkman/bin/sdkman-init.sh \
    && mvn clean \
    && mvn install

RUN echo 'source ~/.sdkman/bin/sdkman-init.sh' >> ~/.bashrc
