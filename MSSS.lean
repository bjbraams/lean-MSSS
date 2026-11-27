module -- shake: keep-all

public import MSSS.RandomFields
public import MSSS.Geostatistics
public import MSSS.Lattice
public import MSSS.PointProcesses
public import MSSS.GibbsPointProcesses
public import MSSS.StochasticGeometry

/-! # Mathematical statistics: spatial statistics

Public entry point. All project declarations live in namespace `MSSS`. Statements carry the
SYNOPSIS item numbers of the GAPS entries they formalize.

* `MSSS.RandomFields`: random fields and covariance functions (SYNOPSIS Part 1).
* `MSSS.Geostatistics`: spatial prediction and covariance-parameter inference (SYNOPSIS Part 2).
* `MSSS.Lattice`: lattice models, Markov random fields, and Gibbs measures (SYNOPSIS Part 3).
* `MSSS.PointProcesses`: point processes and random measures (SYNOPSIS Part 4).
* `MSSS.GibbsPointProcesses`: Gibbs point processes and statistics of point patterns
  (SYNOPSIS Part 5).
* `MSSS.StochasticGeometry`: stochastic and integral geometry (SYNOPSIS Part 6).
-/
