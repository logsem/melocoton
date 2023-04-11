#!/bin/bash

set -euo pipefail

## Run this script by passing it an empty directory as argument

if [ -z "$1" ]; then
    echo "Usage: make-artifact.sh <name of empty artifact directory>"
    exit 1
fi

DIR=$1

if [ -d "$DIR" ]; then
    if [ "$(ls -A $DIR)" ]; then
        echo "Artifact directory $DIR is not empty. Aborting."
        exit 1
    fi
else
    echo "Directory $DIR does not exist"
    exit 1
fi

CWD=$(pwd)

cd "$DIR"
echo "Changing directory to $DIR."

# clone git repos
git clone -b oopsla23_artifact git@github.com:logsem/melocoton.git
git clone -b simon/parametric-index git-rts@gitlab.mpi-sws.org:simonspies/iris-parametric-index.git
git clone -b simon/parametric-index git-rts@gitlab.mpi-sws.org:simonspies/transfinite-parametric-stepindex.git

# cleanup
rm -rf melocoton/.git iris-parametric-index/.git transfinite-parametric-stepindex/.git

echo "Changing directory to $CWD."
cd "$CWD"

# create archive; do not store the user name in the archive
tar cvzf "$DIR.tar.gz" --owner=0 --group=0 --no-same-owner --no-same-permissions "$DIR"

echo "Created archive $DIR.tar.gz"
