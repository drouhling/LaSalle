# A formal proof of LaSalle's invariance principle

This repository contains a formal proof in Coq of LaSalle's invariance
principle.

This branch requires the [mathcomp-analysis
library](https://github.com/math-comp/analysis) and its dependencies and the
ssring.v file from [jasmin](https://github.com/jasmin-lang/jasmin).

It is organised as follows:

- lasalle.v: this file contains the actual proof of LaSalle's invariance
  principle.

- pendulum.v : in this file we apply LaSalle's invariance principle to an
  inverted pendulum.

# Authors

Cyril Cohen and Damien Rouhling.