# Artifact build instructions

Requirements: you need `opam` to be installed on your computer, and have gone
through the initial `opam init` setup.

From the directory containing this README file, run the `setup-artifact.sh`
script (or read it and execute its commands). Nothing will be installed or
written outside of this directory. The directory can be safely removed
afterwards.

```
    ./setup-artifact.sh
```

The Coq development accompanying our submission lives in the `melocoton`
subdirectory. The other directories (`iris-parametric-index`,
`transfinite-parametric-stepindex`, `autosubst`) bundle the versions of
Transfinite Iris and Autosubst that our development uses. They are not part of
the submission.

See `melocoton/README.md` for more information about the structure of the
development and how it relates to the paper.


## Troubleshooting

- When visiting the artifact from a new terminal session, one needs to call opam
to re-setup the terminal environment. To do this, call:

```
    # From the directory containing this README
    eval $(opam env)
```


- If the setup script fails for some reason, to restart from the beginning, it
should be enough to remove the `_opam` subdirectory created by the script, and
launch the script again.

```
    rm -rf ./_opam
    ./setup-artifact.sh
```
