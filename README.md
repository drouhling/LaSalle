# A formal proof of LaSalle's invariance principle

This repository contains a formal proof in Coq of LaSalle's invariance
principle.

This branch requires the [mathcomp-analysis
library](https://github.com/math-comp/analysis) and its dependencies and the
[ssring.v](https://raw.githubusercontent.com/jasmin-lang/jasmin/f1f8b193591d369296d5661f0ae8a09f3b6eaa9b/proofs/3rdparty/ssrring.v)
file from [jasmin](https://github.com/jasmin-lang/jasmin).

It is organised as follows:

- lasalle.v: this file contains the actual proof of LaSalle's invariance
  principle.

- pendulum.v : in this file we apply LaSalle's invariance principle to an
  inverted pendulum.

# Authors

Cyril Cohen and Damien Rouhling.