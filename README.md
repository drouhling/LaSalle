# A formal proof of LaSalle's invariance principle

This repository contains a formal proof in Coq of LaSalle's invariance
principle.

It requires Coq v8.6, the Mathematical Components library v1.6.1 and the
Coquelicot library v3.0.0.

It is organised as follows:

- coquelicotComplements.v: this file extends the Coquelicot library with
  set-theoretic notations and results on convergence, closed sets and compact
  sets.

- lasalle.v: this file contains the actual proof of LaSalle's invariance
  principle.

- vect.v: in this file we prove that Mathematical Components' row vectors
  inherit Coquelicot's topological structures.

# Authors

Cyril Cohen and Damien Rouhling.