#!/bin/bash

set -euo pipefail

## Run this script by passing it an empty directory as argument

## This script must be run in an environment that can build melocoton (we need
## this in order to generate the html documentation with coqdoc and include it
## in the archive). For some reason, odoc also needs to be installed in the
## ambient opam switch for the html docs to build successfully.

if [ $# -eq 0 ]; then
    echo "Usage: make-artifact.sh <name of empty artifact directory>"
    exit 1
fi

DIR=$1

if [ -d "$DIR" ]; then
    if [ "$(ls -A "$DIR")" ]; then
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

# clone git repos (the branches or commit hashes must match the ones in coq-melocoton.opam)
git clone git@github.com:logsem/melocoton.git
git clone -b simon/parametric-index git-rts@gitlab.mpi-sws.org:simonspies/iris-parametric-index.git
git clone -b simon/parametric-index git-rts@gitlab.mpi-sws.org:simonspies/transfinite-parametric-stepindex.git
git clone https://github.com/coq-community/autosubst
( cd autosubst && git checkout e20eee1 )
git clone https://gitlab.mpi-sws.org/iris/stdpp
( cd stdpp && git checkout 0231fed2 )

echo "Generation data for the artifact
================================
melocoton-project/melocoton.git: $(git -C melocoton rev-parse HEAD)
simonspies/iris-parametric-index.git: $(git -C iris-parametric-index rev-parse HEAD)
simonspies/transfinite-parametric-stepindex.git: $(git -C transfinite-parametric-stepindex rev-parse HEAD)
coq-community/autosubst.git: $(git -C autosubst rev-parse HEAD)
iris/stdpp.git: $(git -C stdpp rev-parse HEAD)
" > generation_data.txt

# move the setup script and artifact readme at the root of the archive
mv melocoton/tools/build-artifact.sh .
mv melocoton/tools/README_artifact.md README.md

# build the html docs
cd melocoton
make html
cd ..

# cleanup
rm -rf melocoton/.git iris-parametric-index/.git transfinite-parametric-stepindex/.git autosubst/.git stdpp/.git
rm -rf melocoton/_build
rm -r melocoton/tools
rm -r melocoton/examples
rm -r melocoton/extra
rm melocoton/coq-melocoton.opam

echo "Changing directory to $CWD."
cd "$CWD"

# create archive; do not store the user name in the archive
tar cvzf "$DIR.tar.gz" --owner=0 --group=0 --no-same-owner --no-same-permissions "$DIR"

echo "Created archive $DIR.tar.gz"
