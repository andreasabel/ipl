# ipl [![Build Status](https://travis-ci.org/andreasabel/ipl.svg?branch=master)](https://travis-ci.org/andreasabel/ipl)
Agda formalization of Intuitionistic Propositional Logic (IPL)

[Agda HTML listing](https://andreasabel.github.io/ipl/html/Everything.html).

## Normalization by Evaluation for IPL (without soundness)

The simple Normalization by Evaluation (NbE) algorithm
that produces from every IPL derivation a normal derivation.

Version presented 2018-07-19 at the
[Initial Types Club](https://github.com/InitialTypes/Club):

* [PDF Handout](https://andreasabel.github.io/ipl/nbeSum.pdf)
* [Agda HTML listing](https://andreasabel.github.io/ipl/html/NfModelCaseTree.html)

## Soundness

Soundness of NbE means that the computational behavior (functional
interpretation) of IPL proofs is preserved by normalization.

We implement sound-by-construction NbE using Kripke predicates.

* [Agda HTML listing](https://andreasabel.github.io/ipl/html/NbeModel.html).
