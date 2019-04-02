# ipl [![Build Status](https://travis-ci.org/andreasabel/ipl.svg?branch=master)](https://travis-ci.org/andreasabel/ipl)
Agda formalization of Intuitionistic Propositional Logic (IPL)

[Agda HTML listing](https://andreasabel.github.io/ipl/html/Everything.html).

## Normalization by Evaluation for IPL (without soundness)

The simple Normalization by Evaluation (NbE) algorithm
that produces from every IPL derivation a normal derivation.

Version published 2019-02-16 on arXiv:

* Article [Normalization by Evaluation for Call-by-Push-Value and Polarized Lambda-Calculus](https://arxiv.org/abs/1902.06097)
* Formalization of Section 2, [NbE of IPL using a Cover Monad](https://andreasabel.github.io/ipl/html/NfModelMonad.html)
* Partial formalization of Section 4, [Syntax and Semantics of Polarized Lambda-Calculus](https://github.com/andreasabel/ipl/blob/master/src-focusing/Formulas.agda)

Version presented 2018-07-19 at the
[Initial Types Club](https://github.com/InitialTypes/Club):

* [PDF Handout](https://andreasabel.github.io/ipl/nbeSum.pdf)
* [Agda HTML listing](https://andreasabel.github.io/ipl/html/NfModelCaseTree.html)

## Soundness

Soundness of NbE means that the computational behavior (functional
interpretation) of IPL proofs is preserved by normalization.

We implement sound-by-construction NbE using Kripke predicates.

* [Agda HTML listing](https://andreasabel.github.io/ipl/html/NbeModel.html).
