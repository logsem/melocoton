# Melocoton: a Coq model and separation logic for verified interoperability between OCaml and C

## Building

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The simplest option is to create a fresh *local* opam switch with everything
needed, by running the following commands:

```
opam switch create -y --repositories=default,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git . ocaml-base-compiler.4.14.1
eval $(opam env)
```

Then run:

```
make
make html # optional, builds an html rendering of the sources
```

### Troubleshooting

- When visiting the artifact from a new terminal session, one needs to call opam
 to re-setup the terminal environment. To do this, call `eval $(opam env)` from
 the root of the repository.

- If the `opam switch` invocation fails at some point, either remove the `_opam`
 directory and re-run the command (this will redo everything), or do `eval
 $(opam env)` and then `opam install -y .` (this will continue from where it
 failed).

## Browsing the development

An easy way to browse the development is to open [html/toc.html](html/toc.html)
in a web browser after running `make html`. The webpage contains an HTML
rendering of the Coq scripts of the development.

Alternatively, using an IDE with Coq support is recommended.

## Navigating the Coq development

- [OVERVIEW.md](OVERVIEW.md) describes the structure of the Coq development
- [PAPER.md](PAPER.md) is a guide through the development following the paper
