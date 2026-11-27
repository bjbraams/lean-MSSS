# Credits

## Mathematical sources

- Winkler gives detailed balance and convergence for deterministic-sweep and random-scan
  finite Gibbs sampling in [item 123](SYNOPSIS.md#finite-gibbs-sampling).
  [Winkler, second edition](References/Winkler2003ImageAnalysisRandomFieldsMarkovChainMonteCarloMethodsMathematicalIntroduction2ndEd-Springer.pdf)
- Brémaud gives the Poisson martingale characterisation, time rescaling, and Palm inversion.
  Karr gives the compensator and conditional hazard formulations and the likelihood ratio.
  Reiss gives the compensator exposition and the Campbell–Mecke formula for local Palm
  kernels. See [temporal counts](SYNOPSIS.md#temporal-counting-processes) and
  [Palm theory](SYNOPSIS.md#stationarity-and-palm-theory).
  [Brémaud](References/Brémaud2020PointProcessCalculusTimeSpaceIntroductionApplication-Sprīnger.PTSM98.pdf) ·
  [Karr](References/Karr1991PointProcessesStatisticalInference2ndEd-MarcelDekker.pdf) ·
  [Reiss](References/Reiss1993CoursePointProcesses-Springer.SSS.pdf)
- Baddeley's chapter in the volume edited by Barndorff-Nielsen, Kendall, and van Lieshout
  supplies the Campbell formula, independent Poisson marking, and the Campbell–Mecke
  formula used in [Part 4](SYNOPSIS.md#reference-guide-for-part-4).
  [Local 1998 printing](References/BarndorffNielsenKendallVanLieshout1998StochasticGeometryLikelihoodComputation-CRC.ChapmanHall.pdf)
- Illian, Penttinen, Helga Stoyan, and Dietrich Stoyan give the mark-weighted $K$-function
  and its translation correction. Diggle gives the one-sided space–time $K$-function for
  Cox processes. See [items 128–129](SYNOPSIS.md#summary-statistics).
  [Illian et al.](References/IllianPenttinenStoyanStoyan2008StatisticalAnalysisModellingSpatialPointPatterns-Wiley.pdf) ·
  [Diggle, third edition](References/Diggle2014StatisticalAnalysisSpatialSpatioTemporalPointPatterns3rdEd-CRC.ChapmanHall.pdf)
- Molchanov gives the Choquet representation for capacity functionals and the support
  function of the selection expectation. Calka's chapters in the volumes edited by
  Kendall and Molchanov and by Coupier give typical-cell volume bias and the
  Poisson–Voronoi containment law. See [Part 6](SYNOPSIS.md#reference-guide-for-part-6).
  [Molchanov, second edition](References/Molchanov2017TheoryRandomSets2ndEd-Springer.PTSM87.pdf) ·
  [Kendall and Molchanov](References/KendallMolchanov2010NewPerspectivesStochasticGeometry-OxfordUP.pdf) ·
  [Coupier](References/CoupierEd2019stochasticGeometryModernResearchFrontiers-Springer.LNM2237.pdf)

## Lean library reuse

- Mathlib supplies square-integrable integration, positive semidefinite matrix algebra, and
  the characteristic-polynomial identity used in [Matheron's estimator](MSSS/Geostatistics/VariogramEstimation.lean).
- TauCeti supplies the Poisson count law and the variance of a Poisson variable used in
  [Poisson count variance](MSSS/PointProcesses/Poisson.lean).
- TauCeti supplies measurability of countable sums of measures, optional tuple marking, and
  the Poisson Laplace functional and its characterization used in
  [Poisson marking](MSSS/PointProcesses/Poisson.lean). Mathlib supplies Haar uniqueness and
  Euclidean cube volume for [stationary intensity and the reduced second factorial moment](MSSS/PointProcesses/Palm.lean).
- TauCeti supplies Euler characteristic for spaces of finite CW type and Mathlib supplies the
  probabilists' Hermite polynomials used in [the cube excursion formula](MSSS/RandomFields/Excursion.lean).
- Mathlib supplies the Chebyshev cosine identity, shifted Legendre coefficients, binomial
  identities, and the Schur product and closedness results for positive semidefinite matrices for
  [Schoenberg's theorem on spheres](MSSS/RandomFields/Sphere.lean).
- Mathlib supplies the Hilbert adjoint and orthogonal projection results used in
  [Galerkin covariance convergence](MSSS/Lattice/SPDE.lean).
- Mathlib supplies Kolmogorov extension, restriction of multivariate Gaussian measures, and
  the variance of a finite sum for [Gaussian fields](MSSS/RandomFields/Basic.lean). The
  construction follows Mathlib's Brownian Gaussian projective family. TauCeti supplies
  the characterization of a finite Gaussian law by its coordinate moments.
- TauCeti supplies the centring criterion for conditionally negative semidefinite kernels
  used to construct [Gaussian fields with a prescribed semivariogram](MSSS/RandomFields/Variogram.lean).
- TauCeti supplies the block-matrix range inclusion for positive semidefinite matrices used
  in [simple kriging](MSSS/Geostatistics/Kriging.lean). Mathlib supplies the moment and matrix
  identities used in the prediction and generalised least-squares proofs.
- TauCeti supplies the multivariate Gaussian density used in
  [restricted maximum likelihood](MSSS/Geostatistics/Likelihood.lean). Mathlib supplies the
  block determinant formulas and strict logarithm inequality.
- Mathlib supplies the discriminant criterion for the sharp
  [prediction risk bounds](MSSS/Geostatistics/Equivalence.lean), and the change of variables
  for Lebesgue measure used with TauCeti’s standard Gaussian density in the proof of
  finite-dimensional Gaussian equivalence.
- Mathlib supplies the finite-product telescoping identity and positivity of the normalising
  sums for [Brook's factorisation](MSSS/Lattice/MarkovField.lean), and the change of density,
  Laplacian basis formula, graph-distance bound, and cosine remainder used in the
  [Whittle and lattice precision results](MSSS/Lattice/SPDE.lean).
- TauCeti supplies the alternating sum over finite-set inclusion intervals used in the Möbius
  inversion for the [Hammersley–Clifford theorem](MSSS/Lattice/MarkovField.lean) and the
  nonnegative summable-product formula used in the coding-set conditional law.
- TauCeti supplies the affine image, coordinate means, and independence criteria for
  multivariate Gaussian laws used in the
  [Gaussian conditional moments and precision criteria](MSSS/Lattice/GaussianMarkov.lean).
- TauCeti supplies the Hausdorff–Bernstein–Widder representation, Gaussian kernel positivity,
  and Bernstein function composition rules used for
  [isotropic correlation functions](MSSS/RandomFields/Isotropic.lean). Its Schoenberg criterion
  and positive-definite function closure results are used for
  [power semivariograms](MSSS/RandomFields/Variogram.lean) and the
  [space–time Fourier criterion](MSSS/RandomFields/SpaceTime.lean).
- Mathlib supplies the inner product and isometry results for
  [spectral integrals](MSSS/RandomFields/Spectral.lean), and the substitution, Gaussian integral,
  and Gamma identities for [half-integer Matérn correlations](MSSS/RandomFields/Matern.lean).
- Mathlib supplies interval-volume and indicator-integral identities used with TauCeti’s
  finite quadratic-form criterion in the
  [triangular covariance dimension cutoff](MSSS/RandomFields/Isotropic.lean).
- TauCeti supplies the Cauchy characteristic function used with Mathlib’s trigonometric
  integration and independence results in the
  [Cauchy cosine example](MSSS/RandomFields/Spectral.lean).
- Mathlib supplies substitutions in real integrals and gamma integrability estimates used
  with TauCeti’s gamma law density and complete monotonicity of Laplace transforms in the
  [Matérn covariance proof](MSSS/RandomFields/Matern.lean).
- Mathlib supplies the measure-preserving identification of one-coordinate products and the
  determinant formulas used for [determinantal intensities and correlations](MSSS/PointProcesses/Determinantal.lean).
  Its finite-product projections, measurable density representatives, and determinant
  multiplicativity combine with TauCeti's measurable measure sums for independent thinning.
- TauCeti supplies the integral of a measure bind for the
  [Poisson composite score](MSSS/GibbsPointProcesses/PoissonLikelihood.lean).
- Mathlib supplies differentiation under the integral for the
  [log-linear Poisson likelihood](MSSS/GibbsPointProcesses/PoissonLikelihood.lean).
- Mathlib supplies finite powerset product identities and finite Poisson integration
  ingredients used in the [Markov and Strauss density proofs](MSSS/GibbsPointProcesses/Finite.lean).
- Mathlib supplies Lagrange interpolation and the volume scaling of balls for
  [intrinsic volumes](MSSS/StochasticGeometry/IntegralGeometry.lean). TauCeti supplies volume
  preservation under affine isometries and the volume of nonempty zero-dimensional sets.
  Mathlib’s separation theorem and nullity of convex frontiers give Hausdorff continuity.
- Mathlib supplies spectral decomposition and variance of independent sums for the Gaussian
  law and moments of [Matheron's estimator](MSSS/Geostatistics/VariogramEstimation.lean).
  TauCeti supplies the covariance square-root sandwich, Gaussian second and fourth moments,
  and the trace identity for eigenvalues.
- Mathlib supplies the mean value theorem, Gaussian increment laws, and the subsequence
  criterion for convergence in measure for
  [quadratic variation and singularity of Gaussian laws](MSSS/Geostatistics/Equivalence.lean).
  TauCeti supplies Isserlis's formula and Chebyshev's inequality.
- Mathlib supplies the finite graph, product, and subset identities for
  [finite Markov random fields](MSSS/Lattice/MarkovField.lean), as well as Radon–Nikodym
  derivatives, trimmed measures, and countable exhaustion for
  [Gibbs tail laws](MSSS/Lattice/Gibbs/Basic.lean).
- Mathlib supplies marginal integration, ultrafilter limits, simple-function approximation,
  and Kolmogorov extension for [Gibbs existence and compactness](MSSS/Lattice/Gibbs/Existence.lean).
  Its layer-cake integral and dominated series convergence are used with TauCeti's integration
  against measure binds for [Dobrushin existence and uniqueness](MSSS/Lattice/Gibbs/Dobrushin.lean).
  The interaction oscillation bound also uses Mathlib's mean value inequality for log odds.
  Mathlib's Gaussian Fourier and Gamma integrals and the local Matérn characteristic function
  give the [Whittle covariance formula](MSSS/Lattice/SPDE.lean).
- Mathlib supplies nullity of Lebesgue diagonals and the exponential series estimates used with
  TauCeti's product-coordinate measure equivalence in
  [finite Gibbs point processes](MSSS/GibbsPointProcesses/Finite.lean).
- TauCeti supplies the measurable Poisson family, independent Poisson factorial moments,
  products of density changes, and the extended negative exponential used in
  [Cox density moments and void probabilities](MSSS/PointProcesses/Cox.lean).
- Mathlib supplies the variance identity, Lebesgue translations, and nullity of singletons for
  [point process summary statistics](MSSS/GibbsPointProcesses/SummaryStatistics.lean).
  TauCeti supplies change of density under measurable embeddings and the finite-product
  Poisson Mecke identity.
- Mathlib supplies measurable embeddings and Prokhorov compactness for
  [Palm kernels](MSSS/PointProcesses/Palm.lean). TauCeti supplies separability of probability
  measures, measurability of parametrized pushforwards, and sigma-finite disintegration and
  uniqueness.
- Mathlib supplies Gaussian Fourier transforms, Fubini, and Gaussian approximation for the
  [space–time covariance criteria](MSSS/RandomFields/SpaceTime.lean). TauCeti supplies
  positive definiteness of characteristic functions and the Bernstein and Laplace results.
- Mathlib supplies uniqueness of characteristic functions and extension of linear isometries
  from dense subspaces for the [spectral representation](MSSS/RandomFields/Spectral.lean).
  TauCeti supplies the finite Gram criterion for positive definiteness.
- Mathlib supplies Gamma and Beta integral identities, substitutions, and the improper
  fundamental theorem of calculus for the [Matérn covariance formulas](MSSS/RandomFields/Matern/Basic.lean).
  TauCeti supplies Gamma and Beta probability laws and the Gaussian characteristic function.
  Mathlib's Taylor remainder, dilation of integrals, and dominated convergence are used with
  TauCeti's Gamma fractional moments and integration against its density for the
  [Matérn asymptotics](MSSS/RandomFields/Matern.lean).
- Mathlib supplies compact-subcover results and Kolmogorov extension for
  [Choquet–Matheron existence](MSSS/StochasticGeometry/ClosedSetCapacity.lean).
  TauCeti supplies Möbius inversion sums on intervals of finite subsets.
- Mathlib supplies compactness of pointwise sums, Haar uniqueness, Fubini, and uniqueness on
  generating intersections for the [Boolean model](MSSS/StochasticGeometry/RandomClosedSets.lean).
  The hit count uses the local Poisson marking construction and TauCeti's Poisson count law.
- Mathlib supplies real Hilbert-space differentiation and uniform convergence of continuous
  functions for [mean-square derivatives of stationary fields](MSSS/RandomFields/Spectral.lean).
- Mathlib supplies product-coordinate integration and nullity of singleton sets, and TauCeti
  supplies a product-coordinate measure equivalence for the finite Poisson identity used in
  [the Georgii–Nguyen–Zessin formula](MSSS/GibbsPointProcesses/Finite.lean).
- Mathlib supplies dominated differentiation, factorial bounds from the exponential series,
  and measurable minorants for [finite Gibbs moment derivatives](MSSS/GibbsPointProcesses/Finite.lean).
