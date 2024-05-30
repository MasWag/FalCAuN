#!/bin/sh -ue
#****h* FalCAuN/deploy_javadoc
# NAME
#  deploy_javadoc
# DESCRIPTION
#  Deploy the javadoc to GitHub pages. If no tag or branch is specified, the master branch will be used.
#  We cannot use GitHub Actions to deploy the javadoc because FalCAuN depends on MATLAB engine, which is not supported by GitHub Actions.
# USAGE
#  ./deploy_javadoc.sh [tag]
#
#******

## Utility functions for logging
log () {
    # When it is neutral (blue color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [deploy_javadoc] \033[0;34mINFO\033[0m %s\n" "$1"
}

log_ok () {
    # When it is OK (green color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [deploy_javadoc] \033[0;32mOK\033[0m %s\n" "$1"
}

log_error () {
    # When it is not OK (red color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [deploy_javadoc] \033[0;31mERROR\033[0m %s\n" "$1"
}

log_warn () {
    # When it is warning (yellow color)
    printf "$(date +'%Y-%m-%d %H:%M:%S') [deploy_javadoc] \033[0;33mWARN\033[0m %s\n" "$1"
}

## Define the constants
readonly TARGET_BRANCH="gh-pages"

## Move to the project root directory
cd "$(dirname "$0")/.." || exit 1

## Check the arguments
if [ $# -eq 0 ]; then
    log 'No tag or branch is specified. The master branch will be used.'
    GITHUB_REF="master"
    TARGET_NAME='latest'
elif [ $# -eq 1 ]; then
    log "The tag or branch $1 will be used."
    GITHUB_REF="$1"
    TARGET_NAME="$1"
else
    log_error 'Invalid number of arguments'
    exit 1
fi

TARGET_DIR="maven-site/$TARGET_NAME/apidocs"

## Build the javadoc
log "Build the javadoc"
git switch "$GITHUB_REF"
mvn javadoc:aggregate

## Move the javadoc to the target directory
log "Move the javadoc to the target directory"
temp_dir=$(mktemp -d)
cp -r target/site/apidocs/* "$temp_dir"
git switch "$TARGET_BRANCH"
mkdir -p "$TARGET_DIR"
rsync -av "$temp_dir/" "$TARGET_DIR"
git add "$TARGET_DIR"
git commit -m "Deploy the javadoc for $TARGET_NAME"
rm -rf "$temp_dir"
git push origin "$TARGET_BRANCH"
log "The javadoc is deployed to the $TARGET_BRANCH branch."
