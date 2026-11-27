module -- shake: keep-all

public import MSSS.StochasticGeometry.RandomClosedSets
public import MSSS.StochasticGeometry.IntegralGeometry
public import MSSS.StochasticGeometry.MeanValues

/-!
# Part 6: Stochastic and integral geometry

Entry module for the formalization of the GAPS entries of SYNOPSIS Part 6. The statements of
`RandomClosedSets` are proved, those of `IntegralGeometry` are partly proved and partly admitted,
and those of `MeanValues` are admitted.

* `MSSS.StochasticGeometry.RandomClosedSets`: the Choquet–Matheron theorem and the Boolean model
  (GAPS 112, 113);
* `MSSS.StochasticGeometry.IntegralGeometry`: intrinsic volumes, Hadwiger's theorem, and the
  Crofton and principal kinematic formulas (GAPS 114–117);
* `MSSS.StochasticGeometry.MeanValues`: Miles' formulas and mean values for Poisson line,
  hyperplane, and Voronoi tessellations (GAPS 119, 121, 122).
-/
