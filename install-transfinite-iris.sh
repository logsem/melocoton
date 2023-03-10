#!/bin/bash
if git rev-parse --is-inside-work-tree > /dev/null 2>&1 ; then
  echo "Still in melocoton folder? Going one up.."
  cd ..;
fi

opam switch create melocoton-transfinite 4.14.0
eval $(opam env --set-switch --switch melocoton-transfinite)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install -y coq.8.16.1 coqide coq-autosubst

if [ ! -d iris-parametric-index ]; then git clone git-rts@gitlab.mpi-sws.org:simonspies/iris-parametric-index.git; fi
cd iris-parametric-index
git clean -f -x -d
git fetch
git checkout origin/simon/parametric-index
make clean
opam install -y .
eval $(opam env)
cd ..

if [ ! -d transfinite-parametric-index ]; then git clone git-rts@gitlab.mpi-sws.org:simonspies/transfinite-parametric-stepindex.git; fi
cd transfinite-parametric-stepindex
git clean -f -x -d
git fetch
git checkout origin/simon/parametric-index
make clean
make -j8
make install
cd ..
