module -- shake: keep-all

public import MSSS.Geostatistics.Kriging
public import MSSS.Geostatistics.Equivalence
public import MSSS.Geostatistics.Likelihood
public import MSSS.Geostatistics.MaternInference
public import MSSS.Geostatistics.VariogramEstimation

/-!
# Part 2: Geostatistics

Entry module for the formalization of the GAPS entries of SYNOPSIS Part 2. All statements are
currently admitted.

* `MSSS.Geostatistics.Kriging`: simple and universal kriging (GAPS 24, 27);
* `MSSS.Geostatistics.Equivalence`: misspecified covariances, equivalence of Gaussian measures,
  and microergodicity (GAPS 34–37, 39);
* `MSSS.Geostatistics.Likelihood`: the Mardia–Marshall theorem and restricted maximum
  likelihood (GAPS 42, 44);
* `MSSS.Geostatistics.MaternInference`: Zhang's theorem and the microergodic parameter of the
  Matérn family (GAPS 40, 41);
* `MSSS.Geostatistics.VariogramEstimation`: Matheron's variogram estimator (GAPS 45).
-/
