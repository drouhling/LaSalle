# A formal proof of LaSalle's invariance principle

This repository contains a formal proof in Coq of LaSalle's invariance
principle.

It is tested with Coq v8.10.2, the Mathematical Components library v1.10.0 and
the Coquelicot library v3.0.3. It also depends on Daniel Schepler's proof of
[Zorn's lemma](https://github.com/coq-contribs/zorns-lemma).

It is organised as follows:

- coquelicotComplements.v: this file extends the Coquelicot library with
  set-theoretic notations and results on convergence, closed sets and compact
  sets.

- lasalle.v: this file contains the actual proof of LaSalle's invariance
  principle.

- vect.v: in this file we prove that Mathematical Components' row vectors
  inherit Coquelicot's topological structures.

- tychonoff.v: this file contains a proof of Tychonoff's theorem.

- pendulum.v : in this file we will apply LaSalle's invariance principle to an
  inverted pendulum.

# Authors

Cyril Cohen and Damien Rouhling.