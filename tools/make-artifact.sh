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
git clone git@github.com:logsem/melocoton.git
git clone -b simon/parametric-index git-rts@gitlab.mpi-sws.org:simonspies/iris-parametric-index.git
git clone -b simon/parametric-index git-rts@gitlab.mpi-sws.org:simonspies/transfinite-parametric-stepindex.git
git clone -b master https://github.com/coq-community/autosubst

# fix the autosubst opam file...
sed -i s/8.16/8.17/g autosubst/coq-autosubst.opam

# move the setup script and artifact readme at the root of the archive
mv melocoton/tools/setup-artifact.sh .
mv melocoton/tools/README_artifact.md README.md

# build the html docs
cd melocoton
make html
cd ..

# cleanup
rm -rf melocoton/.git iris-parametric-index/.git transfinite-parametric-stepindex/.git autosubst/.git
rm -rf melocoton/_build
rm -r melocoton/tools
rm -r melocoton/examples
rm -r melocoton/extra
rm melocoton/opam
rm melocoton/install-transfinite-iris.sh

echo "Changing directory to $CWD."
cd "$CWD"

# create archive; do not store the user name in the archive
tar cvzf "$DIR.tar.gz" --owner=0 --group=0 --no-same-owner --no-same-permissions "$DIR"

echo "Created archive $DIR.tar.gz"
