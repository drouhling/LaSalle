# A formal proof of LaSalle's invariance principle

This repository contains a formal proof in Coq of LaSalle's invariance
principle.

This branch requires the [mathcomp-analysis
library](https://github.com/math-comp/analysis) and [algebra
tactics](https://github.com/math-comp/algebra-tactics). More
precisely, as of 2025-08-25. it compiles with the following versions:
- Rocq 9.0
- MathComp 2.4.0
- MathComp-Analysis 1.12.0
- algebra-tactics 1.2.6

It is organised as follows:

- lasalle.v: this file contains the actual proof of LaSalle's invariance
  principle.

- pendulum.v : in this file we apply LaSalle's invariance principle to an
  inverted pendulum.

# Authors

Cyril Cohen and Damien Rouhling.

Reynald Affeldt ported the development from MathComp-Analysis 0.2.0 to
MathComp-Analysis 1.12.0 during the summer 2025.
