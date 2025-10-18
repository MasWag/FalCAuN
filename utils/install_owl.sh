#!/bin/sh -u
############################################################
# Name
#  install_owl
# Description
#  Script to install Owl library: https://owl.model.in.tum.de/
#
# Usage
#  ./install_owl.sh
############################################################

## Utility functions for logging
log () {
    # When it is neutral (blue color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [install_owl] \033[0;34mINFO\033[0m %s\n" "$1"
}

log_ok () {
    # When it is OK (green color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [install_owl] \033[0;32mOK\033[0m %s\n" "$1"
}

log_error () {
    # When it is not OK (red color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [install_owl] \033[0;31mERROR\033[0m %s\n" "$1"
}

log_warn () {
    # When it is warning (yellow color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [install_owl] \033[0;33mWARN\033[0m %s\n" "$1"
}

## Check Java
log "Check if Java 17 is installed"

## Use JAVA_HOME if it is set
set +u
if [ -n "$JAVA_HOME" ]; then
    log "JAVA_HOME is set to $JAVA_HOME"
    PATH="$JAVA_HOME/bin:$PATH"
fi
set -u
if which java > /dev/null; then
    JAVA_VERSION=$(java -version 2>&1 | awk -F '"' '/version/ {print $2}')
    JAVA_VERSION_MAJOR=$(echo "$JAVA_VERSION" | cut -d '.' -f1)
    if [ "$JAVA_VERSION_MAJOR" = "17" ]; then
        log_ok "Detected Java $JAVA_VERSION"
    else
        log_error "Detected Java $JAVA_VERSION"
        log_error "FalCAuN requires Java 17"
        log "Maybe you need to set JAVA_HOME to the correct Java 17 installation"
        exit 1
    fi
else
    log_error "Java is not installed"
    exit 1
fi

## Check Maven
log "Check if Maven is installed"
if which mvn > /dev/null; then
    MAVEN_VERSION=$(mvn -v | head -n 1 | awk '{print $3}')
    log_ok "Detected Maven $MAVEN_VERSION"
else
    log_error "Maven is not installed"
    exit 1
fi

## Check if unzip is installed
log "Check if unzip is installed"
if which unzip > /dev/null; then
    UNZIP_VERSION=$(unzip -v | head -n 1)
    log_ok "Detected unzip: $UNZIP_VERSION"
else
    log_error "unzip is not installed"
    exit 1
fi

## Check if wget is installed
log "Check if wget is installed"
if which wget > /dev/null; then
    WGET_VERSION=$(wget --version | head -n 1)
    log_ok "Detected wget: $WGET_VERSION"
else
    log_error "wget is not installed"
    exit 1
fi

## Download Owl release
readonly OWL_VERSION="21.0"
log "Download Owl release version $OWL_VERSION"
tmp_dir="$(mktemp -d)"

case "$(uname -s)" in
    Linux*)
        readonly uname=linux
        readonly OWL_PATH="owl-${uname}-musl-amd64-${OWL_VERSION}/jar"
        ;;
    Darwin*)
        readonly uname=macos
        readonly OWL_PATH="jar"
        ;;
    *)
        log_error "Unsupported OS: $(uname -s)";
        exit 1;;
esac
wget "https://github.com/owl-toolkit/owl/releases/download/release-${OWL_VERSION}/owl-${uname}-amd64-${OWL_VERSION}.zip" -O "$tmp_dir/owl.zip"

log "Install Owl"
unzip "$tmp_dir/owl.zip" -d "$tmp_dir/owl"

if mvn install:install-file -N \
       -Dfile="$tmp_dir/owl/${OWL_PATH}/owl-${OWL_VERSION}.jar" \
       -DgroupId=de.tum.in \
       -DartifactId=owl \
       -Dversion="${OWL_VERSION}" \
       -Dpackaging=jar \
       -DgeneratePom=true; then
    log_ok "Owl version $OWL_VERSION installed successfully"
else
    log_error "Failed to install Owl version $OWL_VERSION"
    exit 1
fi
