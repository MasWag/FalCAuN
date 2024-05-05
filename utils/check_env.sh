#!/bin/sh -u
#****h* FalCAuN/check_env
# NAME
#  check_env
# DESCRIPTION
#  Check if the environment is correctly set up for FalCAuN
#
# USAGE
#  ./check_env.sh
#
#******

## Utility functions for logging
log () {
    # When it is neutral (blue color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [check_env] \033[0;34mINFO\033[0m %s\n" "$1"
}

log_ok () {
    # When it is OK (green color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [check_env] \033[0;32mOK\033[0m %s\n" "$1"
}

log_error () {
    # When it is not OK (red color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [check_env] \033[0;31mERROR\033[0m %s\n" "$1"
}

log_warn () {
    # When it is warning (yellow color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [check_env] \033[0;33mWARN\033[0m %s\n" "$1"
}

## Check Java
log "Check if Java 11 is installed"

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
    if [ "$JAVA_VERSION_MAJOR" = "11" ]; then
        log_ok "Detected Java $JAVA_VERSION"
    else
        log_error "Detected Java $JAVA_VERSION"
        log_error "FalCAuN requires Java 11"
        log "Maybe you need to set JAVA_HOME to the correct Java 11 installation"
        exit 1
    fi
else
    log_error "Java is not installed"
    exit 1
fi

## Check LTSMin
log "Check if LTSMin is installed"
if which etf2lts-mc > /dev/null; then
    log_ok "LTSMin is installed"
else
    log_error "LTSMin is not installed"
    exit 1
fi

log "Check the version of LTSMin (= v3.1.0)"
LTSMin_version="$(etf2lts-mc --version)"

if [ "$LTSMin_version" = "v3.1.0" ]; then
    log_ok "Detected LTSMin $LTSMin_version"
else
    log_error "Detected LTSMin $LTSMin_version"
    log_error "FalCAuN requires LTSMin version v3.1.0"
    exit 1
fi

## Check MATLAB
log "Check if the environment variable MATLAB_HOME is set"
set +u
if [ -z "$MATLAB_HOME" ]; then
    log_error "MATLAB_HOME is not set"
    exit 1
else
    log_ok "MATLAB_HOME is set to $MATLAB_HOME"
fi
set -u

if [ -f "$MATLAB_HOME/bin/matlab" ]; then
    log_ok "MATLAB is detected at $MATLAB_HOME"
else
    log_error "MATLAB is not installed"
    exit 1
fi

log "Check if the MATLAB version is at least R2024a"
MATLAB_version="$("$MATLAB_HOME/bin/matlab" -nodisplay -nosplash -r "disp(version('-release')); exit" 2>/dev/null | grep -o 'R[0-9]\{4\}[ab]')"
MATLAB_version_year="$(echo "$MATLAB_version" | tr -d 'abR')"
if [ "$MATLAB_version_year" -ge 2024 ]; then
    log_ok "Detected MATLAB $MATLAB_version"
else
    log_error "Detected MATLAB $MATLAB_version"
    log_error "FalCAuN requires MATLAB version R2024a or later"
    exit 1
fi

log "Check if C/C++ compiler is configured in MATLAB"
MATLAB_compiler_configuration="$("$MATLAB_HOME/bin/matlab" -nodisplay -nosplash -r "mex -setup; exit" 2>/dev/null | grep configured)"
log "$MATLAB_compiler_configuration"
if [ -n "$MATLAB_compiler_configuration" ]; then
    log_ok "C/C++ compiler is configured in MATLAB"
else
    log_error "C/C++ compiler is not configured in MATLAB"
    exit 1
fi

log "Check if the AT example is installed"
if [ -d "$HOME/Documents/MATLAB/Examples/$MATLAB_version/simulink_automotive/ModelingAnAutomaticTransmissionControllerExample/" ] ; then
    log_ok "The AT example by Mathworks is detected"
else
    log_warn "The AT example by Mathworks is not detected"
    log_warn "To use the AT example, please run the following command on MATLAB: openExample('simulink_automotive/ModelingAnAutomaticTransmissionControllerExample')"
    exit 1
fi
