Multi-dimensional Arrays in Agda
================================


This repository contains a formalisation of multi-dimensional
arrays a la APL in Agda.  The layout of the repo is similar to
the one used in Agda's standard library.

`Array/APL.agda` contains an implementation of some of the APL
operators.  Their use can be seen in `CNN.agda` that defies a
Convolutional Neural network, following the code from
[https://github.com/ashinkarov/cnn-in-apl](https://github.com/ashinkarov/cnn-in-apl)
and [the paper](https://dl.acm.org/citation.cfm?id=3329960)

Technical notes
---------------

Agda code has been developed with agda version `2.6.0.1`, using
a pretty late version of the standard library `v1.1-70-g4aecce24`.

