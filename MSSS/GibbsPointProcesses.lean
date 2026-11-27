module -- shake: keep-all

public import MSSS.GibbsPointProcesses.Finite
public import MSSS.GibbsPointProcesses.InfiniteVolume
public import MSSS.GibbsPointProcesses.SummaryStatistics
public import MSSS.GibbsPointProcesses.PoissonLikelihood
public import MSSS.GibbsPointProcesses.BirthDeath

/-!
# Part 5: Gibbs point processes and statistics of point patterns

Entry module for the formalization of the GAPS entries of SYNOPSIS Part 5. All statements are
currently admitted.

* `MSSS.GibbsPointProcesses.Finite`: densities, stability, the Georgii–Nguyen–Zessin formula,
  Markov point processes, the Strauss process, finite-volume Gibbs measures, and the
  pseudolikelihood (GAPS 94, 95, 97–99, 107);
* `MSSS.GibbsPointProcesses.InfiniteVolume`: infinite-volume Gibbs measures, uniqueness and phase
  transition, and Takacs–Fiksel estimation (GAPS 100, 101, 108);
* `MSSS.GibbsPointProcesses.SummaryStatistics`: estimation of the intensity and of `K`, and the
  `F`, `G`, and `J` functions (GAPS 103, 104);
* `MSSS.GibbsPointProcesses.PoissonLikelihood`: the Poisson likelihood and Kutoyants' asymptotic
  theory (GAPS 105, 106);
* `MSSS.GibbsPointProcesses.BirthDeath`: the birth–death Metropolis–Hastings algorithm (GAPS 110).
-/
