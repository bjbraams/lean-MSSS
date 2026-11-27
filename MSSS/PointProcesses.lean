module -- shake: keep-all

public import MSSS.PointProcesses.Basic
public import MSSS.PointProcesses.Poisson
public import MSSS.PointProcesses.Palm
public import MSSS.PointProcesses.Cox
public import MSSS.PointProcesses.Determinantal

/-!
# Part 4: Point processes and random measures

Entry module for the formalization of the GAPS entries of SYNOPSIS Part 4. All statements are
currently admitted.

* `MSSS.PointProcesses.Basic`: point processes given by their points, factorial measures, and
  stationarity;
* `MSSS.PointProcesses.Poisson`: marking, Rényi's theorem, the Mecke equations, and the Poincaré
  inequality (GAPS 75, 78–81);
* `MSSS.PointProcesses.Palm`: stationary point processes, Palm distributions, and the
  Slivnyak–Mecke theorem (GAPS 82–84);
* `MSSS.PointProcesses.Cox`: Cox and log-Gaussian Cox processes (GAPS 85, 86);
* `MSSS.PointProcesses.Determinantal`: determinantal point processes (GAPS 88–90).
-/
