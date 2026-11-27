module -- shake: keep-all

public import MSSS.Lattice.MarkovField
public import MSSS.Lattice.GaussianMarkov
public import MSSS.Lattice.Gibbs
public import MSSS.Lattice.SPDE

/-!
# Part 3: Lattice models, Markov random fields, and Gibbs measures

Entry module for the formalization of the GAPS entries of SYNOPSIS Part 3. Most statements are
proved; the existence and uniqueness of the Gibbs measure of a Markov specification, the
specification of a transition kernel (item 63), and the Ising phase transition and critical value
(item 64) are admitted.

* `MSSS.Lattice.MarkovField`: Brook's lemma, the Hammersley–Clifford theorem, auto-models, and
  coding sets (GAPS 47, 49, 50, 65);
* `MSSS.Lattice.GaussianMarkov`: Gaussian Markov random fields (GAPS 55, 56);
* `MSSS.Lattice.Gibbs`: Gibbs measures on infinite lattices (GAPS 60–64);
* `MSSS.Lattice.SPDE`: Whittle's equation and finite-element approximations (GAPS 66, 67).
-/
