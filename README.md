# MetaCoq plugins for nested inductive types

## Installation

```sh
opam repo add coq-released https://coq.inria.fr/opam/released

METACOQ_VERSION=7281139
opam pin add -n -y -k git coq-metacoq-template.dev "https://github.com/MetaCoq/metacoq.git#$METACOQ_VERSION"
opam pin add -n -y -k git coq-metacoq-pcuic.dev "https://github.com/MetaCoq/metacoq.git#$METACOQ_VERSION"
opam pin add -n -y -k git coq-metacoq-translations.dev "https://github.com/MetaCoq/metacoq.git#$METACOQ_VERSION"

opam install .
```

## Development setup

```sh
opam repo add coq-released https://coq.inria.fr/opam/released

METACOQ_VERSION=7281139
opam pin add -n -y -k git coq-metacoq-template.dev "https://github.com/MetaCoq/metacoq.git#$METACOQ_VERSION"
opam pin add -n -y -k git coq-metacoq-pcuic.dev "https://github.com/MetaCoq/metacoq.git#$METACOQ_VERSION"
opam pin add -n -y -k git coq-metacoq-translations.dev "https://github.com/MetaCoq/metacoq.git#$METACOQ_VERSION"
```

To compile a subproject with name `SUBPROJECT` use `make -C SUBPROJECT`. E.g. use `make -C parametricity` to compile the parametricity plugin.

To install a subproject with name `SUBPROJECT` use `make -C SUBPROJECT install`. E.g. use `make -C parametricity install` to install the parametricity plugin.

Some subprojects may depend on others, for instance the nested induction plugin depends on the parametricity plugin.
This means one needs to run `make -C parametricity && make -C parametricity install` before running `make -C nested-induction`.

<!-- ## Nested Induction Principles -->


<!-- ## Subterm Relations -->


<!-- ## Pickle/Unpickle -->


