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
    # 11.0.27-tem
    && sdk install java 17.0.12-oracle \
    && sdk install kotlin 1.9.24 \
    && sdk install kscript \
    && sdk install maven

# Install LTSMin 3.1.0
RUN wget https://github.com/Meijuh/ltsmin/releases/download/v3.1.0/ltsmin-v3.1.0-linux.tgz \
    && tar xvf ltsmin-v3.1.0-linux.tgz \
    && sudo cp -r v3.1.0/* /usr

# Install Python and Jep
RUN source ~/.sdkman/bin/sdkman-init.sh \
    pip install --upgrade setuptools wheel \
    && pip install --no-cache-dir --no-build-isolation jep==4.2.1 \
    && pip show jep

# Install FalCAuN
ENV MATLAB_HOME="/opt/matlab/${MATLAB_RELEASE}"
RUN git clone https://github.com/MasWag/FalCAuN.git /home/matlab/FalCAuN
WORKDIR /home/matlab/FalCAuN
RUN source ~/.sdkman/bin/sdkman-init.sh \
    && mvn clean \
    && mvn install

RUN echo 'source ~/.sdkman/bin/sdkman-init.sh' >> ~/.bashrc
