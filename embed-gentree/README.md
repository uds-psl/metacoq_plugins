
# GHERKIN 
*gherkin, noun: a small type of cucumber that is often pickled (= preserved in vinegar)*

This repository contains a small plugin which allows to derive pickle and unpickle functions for a large class of inductive types.  

The project is organized in some coq files:
- The file ``demo.v`` contains a demo, using the plugin to derive Pickle and Unpickle for rose trees and forms (of propositional modal logic). After the cancellation property has been proven manually, we also obtain equality deciders / countability proofs for the types without a lot of effort.
- ``gherkin.v`` contains all the code related to generating the pickle and unpickle functions. 
- ``examples.v`` showcases the capabilities of the plugin to generate pickle and unpickle functions for some more complicated types (the proofs of the cancellation property are not done for theses types; it only showcases that the functions can be derived)
- ``gentree.v`` contains the definition of ``Ntree``, the generic tree type. It also features a proof of decidability for Ntrees and some frameworks for decidability / countability taken from [uds-psl/coq-library-undecidability](https://github.com/uds-psl/coq-library-undecidability) .
## Compiling the project
The project was compiled with Coq 12.0.0. Using MetaCoq **coq-metacoq**.1.0~beta1+8.12 . (This is the only dependency; the normal acp-switch works fine for compiling).
1. Create the makefile using ``coq_makefile -f _CoqProject -o CoqMakefile``
2. Run make (it can take some to compile demo.v - 10s on my machine)
3. Open demo.v using ProofGeneral 
4. Enjoy!

## Github
The github-repo for this project can be found [here](https://github.com/christ2go/gherkin).