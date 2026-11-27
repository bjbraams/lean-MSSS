module -- shake: keep-all

public import MSSS.RandomFields.Basic
public import MSSS.RandomFields.Spectral
public import MSSS.RandomFields.Isotropic
public import MSSS.RandomFields.Matern
public import MSSS.RandomFields.Variogram
public import MSSS.RandomFields.SpaceTime
public import MSSS.RandomFields.Sphere
public import MSSS.RandomFields.GaussianSuprema
public import MSSS.RandomFields.Excursion

/-!
# Part 1: Random fields and covariance functions

Entry module for the formalization of the GAPS entries of SYNOPSIS Part 1. All statements are
currently admitted.

* `MSSS.RandomFields.Basic`: second-order and stationary fields; Gaussian fields with given
  mean and covariance (GAPS 2);
* `MSSS.RandomFields.Spectral`: spectral representation and mean-square differentiability
  (GAPS 5, 7);
* `MSSS.RandomFields.Isotropic`: Schoenberg's theorem in `ℝ^d`, the class `Φ_∞`, and Pólya-type
  criteria (GAPS 8, 10, 11);
* `MSSS.RandomFields.Matern`: the Matérn family and the smoothness of Matérn fields
  (GAPS 12, 13);
* `MSSS.RandomFields.Variogram`: the Schoenberg–von Neumann characterisation of variograms
  (GAPS 15);
* `MSSS.RandomFields.SpaceTime`: the Cressie–Huang criterion and Gneiting's class (GAPS 16, 17);
* `MSSS.RandomFields.Sphere`: Schoenberg's theorem on spheres (GAPS 18);
* `MSSS.RandomFields.GaussianSuprema`: Dudley's bound and the Borell–TIS inequality
  (GAPS 20, 21);
* `MSSS.RandomFields.Excursion`: Rice's formula and the expected Euler characteristic on the
  line (GAPS 22, 23).
-/
