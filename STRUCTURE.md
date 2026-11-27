# Spatial statistics: Mathlib and TauCeti coverage

This file describes the definitions, structures, and proved results in Mathlib and TauCeti
that bear on the numbered entries of the [mathematical synopsis](SYNOPSIS.md). Its parts and
topic headings follow the synopsis, which follows the [bibliography](MSSS-bib.md). It follows
the conventions of the coverage inventories of the sibling statistics project,
[CKSD STRUCTURE.md](../lean-CKSD/STRUCTURE.md), whose files are cited where the probability,
statistics, and analysis on which spatial statistics builds are described there.

Each section distinguishes Mathlib and TauCeti within a topic. TauCeti is developed on top of
Mathlib; a TauCeti result is recorded only where Mathlib lacks it. The inventory retains source
locations, declaration names, hypotheses, and scope qualifications. Supporting constructions
are identified as such: a library definition of a Gaussian law, a kernel, or a Fourier
multiplier supports, but does not itself prove, a theorem of spatial statistics that uses it.
Placement under a synopsis heading does not claim that every numbered result under that
heading is formalized.

Each section ends with a **Synopsis entries** line that sorts every numbered entry under that
heading into *covered* (the result as stated, with its hypotheses, is proved in one or both
libraries, possibly in an equivalent formulation), *partly covered* (with a note on what is
present), or *not covered*. An entry is *partly covered* when a library declaration proves one
of the claims that the entry itself makes, or a special case of the entry, either in an
equivalent formulation or as a direct instance of the declaration's hypotheses. An entry is
*not covered* when the libraries supply only ingredients from which the statement, or a part
of it, would follow by a further argument, however short, or only supporting definitions;
such entries carry the note *ingredients only*, naming what is present, or *absent*. This is
the rule of the CKSD inventories. In particular, a property proved for positive definite
functions does not cover a claim about the covariance of a stationary field, since neither
library proves that such a covariance is positive definite.

Across the 133 synopsis entries, the two libraries together cover 4, partly cover 15, and do
not cover 114. The [gap inventory](GAPS.md) selects the principal missing results, restates
them, and assesses what the libraries supply towards each.

## Source baseline

The coverage inventory uses source inspection of the local checkouts at the dependency pins
of this project. Only completed proofs count. Roadmap and acquisition files are excluded.

- **Mathlib:** commit
  [`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842)
  of 2026-11-16, using Lean `v4.36.0`.
- **TauCeti:** commit
  [`d91980bdc255e6e50506be147ad9bcb88eb9fcc0`](https://github.com/TauCetiProject/TauCeti/tree/d91980bdc255e6e50506be147ad9bcb88eb9fcc0)
  of 2026-11-19.

These are later than the revisions recorded in the CKSD inventories, which in particular
predate TauCeti's theory of Poisson random measures. Mathlib paths are given relative to
`Mathlib/`; TauCeti paths begin with `TauCeti/`.

## Summary by part

* [1. Random fields and covariance functions](#1-random-fields-and-covariance-functions),
  items 1–23: covered 1; partly covered 2, 4, 10, 12, 15; not covered 17.
  Mathlib: Kolmogorov extension, the Brownian Gaussian family, characteristic functions,
  Fernique. TauCeti: positive definite functions, Bochner, Herglotz, Bernstein, Schoenberg's
  kernel theorem, the Gaussian kernel, Cauchy and stable characteristic functions, Euler
  characteristic for spaces of finite CW type.
* [2. Geostatistics](#2-geostatistics-spatial-prediction-and-covariance-parameter-inference),
  items 24–46: partly covered 24, 25, 26; not covered 20. Mathlib: Hilbert-space projection.
  TauCeti: Gaussian conditioning, pseudoinverse block identities, Gaussian densities and
  quadratic forms.
* [3. Lattice models, Markov random fields, and Gibbs measures](#3-lattice-models-markov-random-fields-and-gibbs-measures),
  items 47–67 and 123: partly covered 123; not covered 21. Mathlib: Möbius inversion,
  conditional independence, graph Laplacians, Bessel potentials. TauCeti: Gaussian conditioning,
  Cholesky factors, Perron–Frobenius, a hard-core heat-bath sampler, Sobolev spaces,
  deterministic Galerkin equations.
* [4. Point processes and random measures](#4-point-processes-and-random-measures),
  items 68–91 and 124–127: covered 68, 73, 74; partly covered 69, 72, 77, 79, 124;
  not covered 20. Mathlib: Giry-monad integration, martingales and predictability. TauCeti:
  random measures and their laws, Poisson random measures, compensated Poisson counts.
* [5. Gibbs point processes and statistics of point patterns](#5-gibbs-point-processes-and-statistics-of-point-patterns),
  items 92–111 and 128–129: partly covered 95; not covered 21. TauCeti: the finite-intensity Mecke
  equation, relative-entropy variational identities.
* [6. Stochastic and integral geometry](#6-stochastic-and-integral-geometry),
  items 112–122, 130–132 and 168: not covered 15. Mathlib: convex bodies and hyperspace topologies.
  TauCeti: measurable selection, Brunn–Minkowski, parallel volume, isoperimetry.

## 1. Random fields and covariance functions

Mathlib has the Kolmogorov extension theorem, Gaussian processes as a predicate, and
multivariate Gaussian laws for arbitrary covariance matrices. TauCeti adds a developed theory
of positive definite functions, including Bochner's theorem on $\mathbb R^d$, Herglotz's
theorem, Bernstein's theorem for completely monotone functions, and Schoenberg's theorem for
conditionally negative definite kernels, together with the uniform law on the sphere and
harmonic polynomials. Neither library defines a stationary or intrinsically stationary field,
a spectral representation of a field, the modified Bessel function $K_\nu$, Gegenbauer
polynomials, or any result on suprema or excursion sets of Gaussian fields.

### Existence and stationarity

[Mathematical scope](SYNOPSIS.md#existence-and-stationarity).

#### Mathlib

**Kolmogorov's extension theorem (item 1).** For a projective family of finite measures on the
products $\prod_{j\in J}\alpha_j$ over finite subsets $J$ of an arbitrary index set, with each
$\alpha_j$ second countable and completely pseudo-metrisable, in particular $\mathbb R^m$, the
measure `projectiveLimit` is a projective limit, and the limit is unique
(`MeasureTheory.projectiveLimit`, `MeasureTheory.isProjectiveLimit_projectiveLimit`,
`MeasureTheory/Constructions/KolmogorovExtension.lean`; `MeasureTheory.IsProjectiveLimit.unique`,
`MeasureTheory/Constructions/Projective.lean`). Consistency is stated for restriction between
finite index sets (`IsProjectiveMeasureFamily`). This is item 1 with families indexed by
finite sets; the formulation by ordered tuples with permutation consistency is equivalent, and
the translation is not stated.

**Gaussian processes (item 2).** `ProbabilityTheory.IsGaussianProcess`
(`Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`) states that all
finite-dimensional laws are Gaussian. The only covariance for which a consistent Gaussian
family is constructed is $\min(s,t)$ on $[0,\infty)$
(`ProbabilityTheory.BrownianReal.isProjectiveMeasureFamily_projectiveFamily`,
`Probability/BrownianMotion/GaussianProjectiveFamily.lean`); with the projective limit this
gives a centred Gaussian field with that covariance. For an arbitrary finite index type,
`ProbabilityTheory.multivariateGaussian μ S` is the Gaussian law with mean $\mu$ and, for
positive semidefinite $S$, covariance matrix $S$
(`ProbabilityTheory.covariance_eval_multivariateGaussian`), and its restriction to a subset of
coordinates is the Gaussian law of the corresponding submatrix
(`ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian`, both in
`Probability/Distributions/Gaussian/Multivariate.lean`). These are the consistency conditions
of a projective Gaussian family for an arbitrary positive definite kernel on an arbitrary
index set; the family itself, and the Gaussian field it gives, are not stated. The covariance
bilinear form of a measure is positive semidefinite
(`ProbabilityTheory.isPosSemidef_covarianceBilin`, `Probability/Moments/CovarianceBilin.lean`),
and the variance of a finite sum is the double sum of covariances
(`ProbabilityTheory.variance_sum`, `Probability/Moments/Variance.lean`). No notion of
stationarity of a random field was found.

#### TauCeti

**Covariance matrices (item 2).** The covariance matrix of a finite measure with finite second
moment on $\mathbb R^\iota$ is positive semidefinite (`TauCeti.posSemidef_covMatrix`,
`TauCeti/Probability/Moments/Covariance.lean`); applied to the law of
$(Z(t_1),\dots,Z(t_n))$ this is the necessity of positive semidefiniteness in item 2. A
countable-time version of the Brownian construction is in
`TauCeti/Probability/BrownianMotion/Countable.lean`. A positive semidefinite kernel on an
arbitrary set has a canonical Hilbert-space feature map with
$\langle\Phi(s),\Phi(t)\rangle=C(s,t)$ (`Matrix.PosSemidef.kolmogorovFeature`,
`Matrix.PosSemidef.inner_kolmogorovFeature`,
`TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean`); composed with an isonormal
Gaussian process, which neither library constructs, it would give the field of item 2.

**Positive definite functions (supporting, item 3).** For $F$ on an additive commutative group
with $\sum_{i,j}c_i\bar c_jF(v_i-v_j)\ge0$ (`TauCeti.IsPositiveDefiniteSub`,
`TauCeti/Analysis/PositiveDefinite/AddGroup.lean`): $F(0)\ge0$, $F(-a)=\overline{F(a)}$,
$|F(a)|\le\mathop{\mathrm{Re}}F(0)$, closure under sums, nonnegative multiples, products,
pullback along additive maps, and pointwise limits, and uniform continuity from continuity at
$0$ (`map_zero_nonneg`, `map_neg`, `norm_apply_le_map_zero_re`, `add`, `real_smul`, `mul`,
`prod`, `comp_addMonoidHom`, `of_tendsto`, `uniformContinuous_of_continuousAt_zero`, in
namespace `TauCeti.IsPositiveDefiniteSub`). The continuity estimate
$|F(x)-F(y)|^2\le2\mathop{\mathrm{Re}}F(0)(\mathop{\mathrm{Re}}F(0)-\mathop{\mathrm{Re}}F(x-y))$ is
`TauCeti.IsPositiveDefinite.norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_forall_star_eq_neg`
(`TauCeti/Analysis/PositiveDefinite/Continuity.lean`). These are the claims of item 3 for a
positive definite function; neither library proves that the covariance of a second-order
stationary field is positive definite, and closure under integral mixtures is absent.

**Synopsis entries.** Covered: 1 (Mathlib, with families indexed by finite sets). Partly
covered: 2 (positive semidefiniteness of the covariance is necessary, in TauCeti and Mathlib;
existence is proved only for the covariance $\min(s,t)$ on $[0,\infty)$; for general
$(m,C)$ Mathlib has the consistent multivariate Gaussian laws, but the projective family, the
field and uniqueness of its law are absent). Not covered: 3 (ingredients only: the
properties of positive definite functions and positive semidefiniteness of covariance
matrices; the link between them and closure under mixtures are absent).

### Spectral theory

[Mathematical scope](SYNOPSIS.md#spectral-theory).

#### Mathlib

**Characteristic functions (supporting, items 4, 7).** The characteristic function determines a
finite measure (`MeasureTheory.Measure.ext_of_charFun`,
`MeasureTheory/Measure/CharacteristicFunction/Basic.lean`). For a measure with finite $n$th
moment, the characteristic function is $n$ times continuously differentiable with the moment
formula at $0$ (`MeasureTheory.iteratedDeriv_charFun`, `MeasureTheory.iteratedDeriv_charFun_zero`,
`MeasureTheory.contDiff_charFun`,
`MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean`); this is the direction
"finite spectral moment implies differentiability of $C$" of item 7, without the field. No
orthogonal random measure, stochastic spectral integral, mean-square continuity, or
mean-square derivative is defined.

#### TauCeti

**Bochner's and Herglotz's theorems (item 4).** On a finite-dimensional real inner-product
space, a function is continuous and positive definite if and only if it is the characteristic
function $\int e^{i\langle\omega,h\rangle}F(d\omega)$ of a unique finite Borel measure
(`TauCeti.bochner_charFun`, `TauCeti.bochner_charFun_probabilityMeasure`,
`TauCeti.bochner_charFun_real`, `TauCeti/Analysis/Bochner/CharFun/Bochner.lean`), with the same
statement in the convention $e^{-2\pi i\langle v,q\rangle}$ (`TauCeti.bochner_euclideanSpace`,
`TauCeti.bochnerMeasure_univ`, `TauCeti/Analysis/Bochner/BochnerTheorem.lean`). The measure of
$\bar C$ is the reflected measure, and pullback along a linear map pushes the measure forward
by the adjoint (`TauCeti.bochnerMeasure_conj`, `TauCeti.bochnerMeasure_comp_neg`,
`ContinuousLinearMap.bochnerMeasure_comp_continuousLinearMap`,
`TauCeti/Analysis/Bochner/Operations.lean`). A finite measure with integrable characteristic
function has the Fourier-inverse density
(`MeasureTheory.Measure.eq_withDensity_re_fourierInv_charFun`;
`MeasureTheory.Measure.eq_withDensity_charFunDensity` on $\mathbb R$,
`TauCeti/Analysis/Bochner/CharFun/Inversion.lean`). Herglotz's theorem holds on $\mathbb Z$ with
a measure on the circle and on every discrete abelian group, so on $\mathbb Z^d$, with a measure
on the Pontryagin dual
(`TauCeti.isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq`,
`TauCeti/Analysis/Bochner/Herglotz.lean`;
`TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq`,
`TauCeti/Analysis/Bochner/DiscreteGroup.lean`); the version on locally compact abelian groups
with uniqueness is in `TauCeti/Analysis/Bochner/LocallyCompactGroup.lean`. A positive definite
function also has a Hilbert-space realisation with a unitary representation of translations
(`TauCeti.IsPositiveDefiniteSub.gnsSpace`, `gnsRepresentation`,
`TauCeti/Analysis/PositiveDefinite/Function/GNS.lean`), the Hilbert-space analogue of the
spectral representation of item 5 without a probability space.

**Continuity (item 6).** A positive definite function continuous at $0$ is continuous
(`TauCeti.IsPositiveDefiniteSub.continuous_of_continuousAt_zero`), the last clause of item 6
once $C$ is known to be positive definite.

**Synopsis entries.** Partly covered: 4 (Bochner's theorem with uniqueness on $\mathbb R^d$,
the total mass $C(0)$, the density for integrable $C$, and Herglotz's theorem on
$\mathbb Z^d$ in Pontryagin-dual form, in TauCeti; the equivalence of reality of $C$ with
symmetry of $F$, which follows from `bochnerMeasure_conj` and uniqueness, and the
identification with covariances of mean-square continuous stationary fields are not stated).
Not covered: 5 (ingredients only: Bochner measures and the Hilbert-space realisation), 6
(ingredients only: continuity of positive definite functions; mean-square continuity is not
defined), 7 (ingredients only: differentiability of characteristic functions with finite
moments).

### Isotropic covariances

[Mathematical scope](SYNOPSIS.md#isotropic-covariances).

#### Mathlib

**Supporting (item 8).** The Bessel function of the first kind (`Complex.besselJ`,
`Analysis/SpecialFunctions/Bessel.lean`; definition by a hypergeometric series, parity,
analyticity, recurrence), without integral representation, zeros, asymptotics, or minimum. No
characteristic function of the uniform law on the sphere, Hankel transform, Schoenberg radial
theorem, or Pólya criterion was found.

#### TauCeti

**Completely monotone functions (supporting, items 10, 17).** Completely monotone functions, in
two conventions, one with continuity at $0$ as in the synopsis
(`TauCeti.IsContinuousCompletelyMonotoneOnIoi`,
`TauCeti/Analysis/CompletelyMonotone/Basic.lean`), Bernstein's theorem
(`TauCeti.exists_representsLaplace_of_isCompletelyMonotone`,
`TauCeti/Analysis/CompletelyMonotone/Bernstein/Theorem.lean`), and complete monotonicity of
Laplace transforms (`TauCeti.isContinuousCompletelyMonotoneOnIoi_laplaceTransform`,
`TauCeti/Analysis/CompletelyMonotone/Laplace/Representation.lean`).

**Gaussian and stable kernels (item 10).** For $c\ge0$ the kernel $e^{-c\|a-b\|^2}$ is positive
semidefinite on every real inner-product space (`TauCeti.posSemidef_cexp_neg_mul_sq_norm`,
`TauCeti/Analysis/Bochner/Gaussian/Basic.lean`), so $t\mapsto e^{-r^2t^2}$ belongs to every
$\Phi_d$. The real part of the characteristic function of a symmetric stable law is
$e^{-|st|^\alpha}$, $0<\alpha\le2$
(`TauCeti.Probability.charFun_stableMeasure_zero_skew_zero_location_re`,
`TauCeti/Probability/Distributions/Stable/Basic.lean`), so $e^{-c|t|^\alpha}\in\Phi_1$. Only the
modified Bessel function $I_\nu$ is defined (`Real.besselI`,
`TauCeti/Analysis/SpecialFunctions/BesselI.lean`). The Fejér kernel exists only on the circle
(`TauCeti/Analysis/Fourier/Fejer.lean`).

**The uniform law on the sphere (supporting, item 8).** TauCeti defines the uniform law on the
unit sphere of a finite-dimensional real inner-product space
(`TauCeti.Probability.uniformSphereMeasure`,
`TauCeti/Probability/Distributions/Uniform/Sphere/Basic.lean`), proves its invariance under
linear isometries (`LinearIsometryEquiv.map_uniformSphereMeasure`), and factorises a radial
density: direction and radius are independent, with the direction uniform
(`TauCeti.Probability.map_sphereDirection_prod_norm_withDensity`). A coordinate of a uniform
point of the sphere of $\mathbb R^d$, $d\ge2$, has the symmetric Beta law
$\tfrac12(1+X)\sim\mathrm{Beta}(\tfrac{d-1}2,\tfrac{d-1}2)$
(`TauCeti.Probability.map_eval_uniformSphereMeasure`,
`TauCeti/Probability/Distributions/Uniform/Sphere/Coordinate.lean`), and the exponential moment
is $\int e^{\langle\eta,x\rangle}\,dx=\Gamma(d/2)(\|\eta\|/2)^{-(d/2-1)}I_{d/2-1}(\|\eta\|)$
(`TauCeti.Probability.integral_exp_inner_uniformSphereMeasure_eq_besselI`,
`TauCeti/Probability/Distributions/VonMisesFisher/Normalizer.lean`). The characteristic
function $\Omega_d(\|\cdot\|)$ itself, the polar decomposition of a rotation-invariant measure
that has no density, and the radial representation of item 8 are absent.

**Synopsis entries.** Partly covered: 10 (the Gaussian functions $e^{-r^2t^2}$ lie in every
$\Phi_d$, in TauCeti; the characterisation of $\Phi_\infty$ as Gaussian scale mixtures, the
limit of $\Omega_d$, and the completely monotone examples are absent). Not covered: 8
(ingredients only: Bochner's theorem with linear pullbacks, the definition of $J_\nu$, and the
uniform law on the sphere with the polar factorisation of radial densities), 9
(ingredients only: $|C|\le C(0)$ for positive definite functions), 11 (absent).

### The Matérn family

[Mathematical scope](SYNOPSIS.md#the-matérn-family).

Neither library defines the modified Bessel function of the second kind $K_\nu$ or the Matérn
covariance. TauCeti computes the characteristic function of the Cauchy law,
$e^{ix_0t-\gamma|t|}$, and its density (`TauCeti.Probability.charFun_cauchyMeasure`,
`TauCeti/Probability/Distributions/Cauchy/Basic.lean`). For $\nu=\tfrac12$ and $d=1$ this is the
Matérn covariance $e^{-|h|/\theta}$ with its spectral density $\theta/(\pi(1+\theta^2\omega^2))$.
Mathlib's Fourier transform of the Gaussian on an inner-product space
(`Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`) is the input for the general
spectral density by subordination.

**Synopsis entries.** Partly covered: 12 (the case $\nu=\tfrac12$, $d=1$ through the Cauchy
characteristic function, in TauCeti; the general case is absent). Not covered: 13 (absent,
including the $t^2\log(1/t)$ small-lag order at $\nu=1$).

### Variograms

[Mathematical scope](SYNOPSIS.md#variograms).

#### Mathlib

**Supporting (item 14).** The variance of a finite sum (`ProbabilityTheory.variance_sum`) and
bilinearity of covariance (`ProbabilityTheory.covariance_sum_sum`,
`Probability/Moments/Covariance.lean`) give the variance
identity of item 14 by a computation. No intrinsically stationary field or variogram is
defined.

#### TauCeti

**Conditionally negative definite kernels (items 14, 15).** Conditionally negative semidefinite
Hermitian matrices, with coefficient vectors summing to zero, and their closure under sums,
nonnegative multiples, and submatrices (`Matrix.CondNegSemidef`,
`TauCeti/LinearAlgebra/Matrix/CondNegSemidef.lean`). Schoenberg's theorem for kernels: $\psi$ is
conditionally negative semidefinite if and only if $e^{-t\psi}$ is positive semidefinite for
every $t>0$ (`Matrix.condNegSemidef_iff_forall_posSemidef_cexp_neg_mul`), and
$\|f(a)-f(b)\|^2$ is conditionally negative semidefinite for every map into a real
inner-product space (`Matrix.condNegSemidef_sq_norm_sub`), both in
`TauCeti/Analysis/PositiveDefinite/Kernel/Schoenberg.lean`. The Lévy–Khintchine material
concerns Bernstein functions on the half-line, not negative definite functions on
$\mathbb R^d$.

**Synopsis entries.** Partly covered: 15 (for even $\gamma$, the equivalence of conditional
negative definiteness with positive definiteness of $e^{-t\gamma}$ for all $t>0$ is a direct
instance of TauCeti's kernel theorem, and the example $\|h\|^2$ is TauCeti's
`Matrix.condNegSemidef_sq_norm_sub`; the Lévy–Khintchine representation, the realisation as a
Gaussian intrinsically stationary field, and $\|h\|^\alpha$ for $\alpha<2$ are absent). Not
covered: 14 (ingredients only: the variance of finite sums and conditionally negative
semidefinite matrices).

### Space–time covariances and spheres

[Mathematical scope](SYNOPSIS.md#spacetime-covariances-and-spheres).

#### Mathlib

**Supporting (item 18).** Gram matrices are positive semidefinite (`Matrix.posSemidef_gram`,
`Analysis/InnerProductSpace/GramMatrix.lean`), and the Schur product theorem
(`Matrix.PosSemidef.hadamard`, `Analysis/Matrix/Order.lean`) then makes
$\langle x,y\rangle^n$ positive definite on the sphere. Chebyshev and shifted Legendre
polynomials are defined (`RingTheory/Polynomial/Chebyshev.lean`,
`RingTheory/Polynomial/ShiftedLegendre.lean`). No Gegenbauer polynomials, addition theorem for
spherical harmonics, or positive definite functions on spheres were found.

#### TauCeti

**Supporting (items 16, 17).** Bochner's theorem on $\mathbb R^{d+1}$, products of positive
definite functions on a product group (`TauCeti.IsPositiveDefinite.mul_comp_fst_snd`,
`TauCeti/Analysis/PositiveDefinite/Pullback.lean`), completely monotone functions with
composition lemmas (`TauCeti/Analysis/CompletelyMonotone/Composition.lean`), and the
Berg–Christensen–Ressel representation of bounded positive definite functions on the
semigroup $[0,\infty)\times V$ (`TauCeti.bcr_semigroup_bochner`,
`TauCeti/Analysis/PositiveDefinite/SemigroupGroup/FourierLaplace/Existence.lean`), which is a
Fourier–Laplace theorem in a different setting from the Cressie–Huang criterion.

**Harmonic polynomials (supporting, item 18).** The Laplacian on polynomials in finitely many
variables, the harmonic homogeneous polynomials of each degree
(`MvPolynomial.harmonicSubmodule`), the Fischer decomposition
$P_{e+2}=H_{e+2}\oplus r^2P_e$ (`MvPolynomial.harmonicSubmodule_sup_map_mulLeft_normSq`), and
the dimension of $H_d$ (`MvPolynomial.finrank_harmonicSubmodule_add_two`), in
`TauCeti/RingTheory/MvPolynomial/Harmonic.lean`. The restriction of harmonic polynomials to
the sphere, spherical harmonics, their addition theorem, and Gegenbauer polynomials are
absent.

**Synopsis entries.** Not covered: 16 (ingredients only: Bochner's theorem and Fourier
inversion; the criterion using continuous temporal representatives of the partial spatial
Fourier transform is absent), 17 (ingredients only: Bernstein's theorem, the Gaussian kernel,
and products of positive definite functions), 18 (ingredients only: Gram matrices, the Schur
product theorem, and harmonic polynomials with the Fischer decomposition), 19 (absent).

### Gaussian fields: continuity, suprema, and excursion sets

[Mathematical scope](SYNOPSIS.md#gaussian-fields-continuity-suprema-and-excursion-sets).

#### Mathlib

**Supporting (items 20, 21, 23).** The Kolmogorov moment condition is defined
(`ProbabilityTheory.IsKolmogorovProcess`, `Probability/Process/Kolmogorov.lean`), without a
continuity theorem. Covering and packing numbers (`Metric.coveringNumber`,
`Metric.packingNumber`, `Topology/MetricSpace/CoveringNumbers.lean`), polynomial covering
bounds (`Metric.HasCoveringExponent`, `Topology/MetricSpace/CoveringExponent.lean`), and the
pair-reduction lemma of chaining arguments, which bounds the supremum of increments over the
close pairs of a finite set by a supremum over a set of pairs of linear size
(`EMetric.pair_reduction`, `Topology/EMetricSpace/PairReduction.lean`). Fernique's theorem for
Gaussian measures on separable Banach spaces
(`ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`,
`Probability/Distributions/Gaussian/Fernique.lean`). Hermite polynomials
(`Polynomial.hermite`, `RingTheory/Polynomial/Hermite/Basic.lean`).

#### TauCeti

**Supporting (items 20, 21).** Gaussian increments with variance $d(s,t)$ satisfy the Kolmogorov
moment bounds (`ProbabilityTheory.isKolmogorovProcess_of_hasLaw_sub_gaussianReal`,
`TauCeti/Probability/Process/Kolmogorov.lean`), with chaining edge estimates that do not by
themselves give a continuous modification (`TauCeti/Probability/Process/Kolmogorov/Edges.lean`).
Gaussian concentration for continuously differentiable functions on a separable Banach space
with a non-sharp constant
(`ProbabilityTheory.IsGaussian.hasSubgaussianMGF_sub_integral_of_variance_fderiv_le`,
`TauCeti/Probability/Distributions/Gaussian/Concentration.lean`), and the lower bound
$\sqrt{\log m}/32\le\mathbb E\max_j|g_j|$ for i.i.d. standard Gaussians
(`TauCeti.Probability.sqrt_log_card_div_le_integral_sup'_abs`,
`TauCeti/Probability/Distributions/Gaussian/Maximum.lean`). No Kolmogorov–Chentsov continuity
theorem, Dudley bound, Borell–TIS inequality, or Rice formula was found.

**Euler characteristic (supporting, item 23).** `TauCeti.eulerChar` is defined for spaces of
finite CW type. `TauCeti.eulerChar_eq_finsum_finrank_singularHomology` identifies it with the
alternating sum of the singular homology dimensions
(`TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/FiniteCWType.lean`). The expected
Euler characteristic of Gaussian excursion sets and the Gaussian kinematic formula are
absent.

**Synopsis entries.** Not covered: 20 (ingredients only: covering numbers, the
pair-reduction lemma, and Kolmogorov moment bounds), 21 (ingredients only: Fernique's theorem
and non-sharp Gaussian concentration), 22 (absent), 23 (ingredients only: Hermite polynomials
and Euler characteristic for spaces of finite CW type).

## 2. Geostatistics: spatial prediction and covariance-parameter inference

The libraries supply Hilbert-space projection, conditional expectation in $L^2$, reproducing
kernel Hilbert spaces, Gaussian processes as a predicate, Gaussian conditioning, and the matrix
algebra of positive semidefinite block matrices. No predictor, kriging system, generalised least
squares estimator, equivalence theory for Gaussian measures on infinite-dimensional spaces, or
likelihood asymptotics for dependent observations is present.

### Linear prediction

[Mathematical scope](SYNOPSIS.md#linear-prediction).

#### Mathlib

**Projection (item 25).** In a real inner-product space, the distance to a complete subspace is
attained, the minimiser is characterised by orthogonality of the residual, and Pythagoras
holds (`Submodule.exists_norm_eq_iInf_of_complete_subspace`,
`Submodule.norm_eq_iInf_iff_real_inner_eq_zero`,
`Analysis/InnerProductSpace/Projection/Minimal.lean`; `Submodule.starProjection_minimal`,
`Submodule.norm_sq_eq_add_norm_sq_starProjection`,
`Analysis/InnerProductSpace/Projection/Basic.lean`). In $L^2(\mathbb P)$, with the closed linear
span of the centred observations, these are the claims of item 25. Conditional expectation is
defined in $L^2$ as an orthogonal projection (`MeasureTheory.condExpL2`,
`MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean`), and the law of total variance
is `ProbabilityTheory.integral_condVar_add_variance_condExp` (`Probability/CondVar.lean`).
Positive definiteness of block matrices through Schur complements is in
`LinearAlgebra/Matrix/PosDef.lean` and `LinearAlgebra/Matrix/SchurComplement.lean`.

**Reproducing kernel Hilbert spaces (supporting, item 31).** The class `RKHS` of Hilbert spaces
of functions with continuous evaluations, the kernel functions `RKHS.kerFun` and their density
(`RKHS.kerFun_dense`), positive semidefiniteness of the kernel (`RKHS.posSemidef_kernel`), and
Moore's construction of the space of a positive semidefinite kernel (`RKHS.OfKernel`,
`RKHS.kernel_ofKernel`) are in `Analysis/InnerProductSpace/Reproducing.lean`. The interpolant of
item 31 without drift is the minimum-norm interpolant in the space of $K$, which follows by a
further argument. No kriging, best linear unbiased predictor, generalised least squares, or
radial basis interpolation was found.

#### TauCeti

**Gaussian conditioning (item 26).** For $X\sim N(m,S)$ on $\mathbb R^{\iota\sqcup\kappa}$ with
$S$ positive semidefinite, the conditional law of the first block given the second is almost
surely $N(m_1+S_{12}S_{22}^+(x_2-m_2),\,S_{11}-S_{12}S_{22}^+S_{21})$, with the classical forms
when $S_{22}$ is positive definite and independence of the residual from the conditioning
block (`TauCeti.Probability.condDistrib_multivariateGaussian`,
`EuclideanSpace.gaussianCondMean_of_posDef`, `Matrix.gaussianCondCov_of_posDef`,
`ProbabilityTheory.HasLaw.indepFun_gaussianResidual`,
`TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean`).

**Positive semidefinite block matrices (item 24).** In a positive semidefinite block matrix the
range of each off-diagonal block lies in the range of the diagonal block in its row
(`Matrix.PosSemidef.range_toEuclideanLin_toBlocks₁₂_le`,
`Matrix.PosSemidef.range_toEuclideanLin_toBlocks₂₁_le`,
`TauCeti/Analysis/Matrix/PosSemidef/Block.lean`); equivalently $S_{12}S_{22}^+S_{22}=S_{12}$,
and the generalised Schur complement is positive semidefinite
(`Matrix.PosSemidef.toBlocks₁₂_mul_covariancePseudoInverse_mul`,
`Matrix.PosSemidef.schur_complement₂₂_covariancePseudoInverse`,
`TauCeti/Analysis/Matrix/SchurComplement.lean`; `Matrix.covariancePseudoInverse`,
`TauCeti/Analysis/Matrix/CovariancePseudoInverse.lean`). Applied to the joint covariance of
$(Z(x_0),\mathbf Z)$, positive semidefinite by `TauCeti.posSemidef_covMatrix`
(`TauCeti/Probability/Moments/Covariance.lean`), the range inclusion says that $\mathbf k$ lies
in the column space of $\mathbf K$. Moore–Penrose inverses of linear maps are in
`TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean`.

**Synopsis entries.** Partly covered: 24 (the column-space claim, through TauCeti's range
inclusion for positive semidefinite block matrices; the mean squared error expansion, the
characterisation of minimisers, and the kriging predictor and variance are absent), 25
(existence, orthogonality characterisation, and Pythagoras for orthogonal projection, in
Mathlib, applied in $L^2$; not stated in covariance form), 26 (the Gaussian conditional law, in
TauCeti, more generally for positive semidefinite covariance; the mean squared error
decomposition for a general predictor $t(Y)$ and uniqueness of the best predictor are absent,
with only the case of a constant predictor as the law of total variance in Mathlib). Not
covered: 27 (ingredients only: Moore–Penrose inverses, Schur complements, and the Gaussian
density), 28 (absent), 29 (ingredients only: conditionally negative semidefinite matrices), 30
(absent), 31 (ingredients only: reproducing kernel Hilbert spaces), 32 (ingredients only:
projection theorems), 33 (ingredients only: Gaussian conditioning).

### Misspecified covariances and equivalence of Gaussian measures

[Mathematical scope](SYNOPSIS.md#misspecified-covariances-and-equivalence-of-gaussian-measures).

#### Mathlib

**Supporting.** Hilbert-space projection gives the orthogonality of the optimal prediction
error in item 34. The relative prediction-error bounds with positive optimal prediction
error are absent, as is the Kantorovich inequality used for the upper bound. For the
equivalence results there are absolute continuity
(`MeasureTheory.Measure.AbsolutelyContinuous`), mutual singularity
(`MeasureTheory.Measure.MutuallySingular`), and the Lebesgue decomposition of measures;
Gaussian processes as a predicate (`ProbabilityTheory.IsGaussianProcess`,
`Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`); convergence in measure; and the
total variation distance (`MeasureTheory.tvDist`,
`MeasureTheory/Measure/TotalVariation/Defs.lean`), in which the merging of conditional laws in
item 40 is stated. The reproducing kernel Hilbert space of a positive semidefinite kernel
(`RKHS.OfKernel`) is the Cameron–Martin space of the corresponding Gaussian field, but no
Gaussian measure is attached to it. The Feldman–Hájek theorem, Kakutani's dichotomy for
product measures, and the Blackwell–Dubins merging theorem are absent.

#### TauCeti

**Gaussian laws on $\mathbb R^n$ (supporting, item 35).** For $S$ positive definite, $N(m,S)$ has a
positive density with respect to Lebesgue measure; otherwise it is singular to Lebesgue
measure; and its support is the affine range $m+\mathop{\mathrm{ran}}S$
(`TauCeti.Probability.multivariateGaussian_eq_withDensity`,
`TauCeti.Probability.mutuallySingular_multivariateGaussian_volume`,
`TauCeti.Probability.support_multivariateGaussian`,
`TauCeti/Probability/Distributions/Gaussian/Density.lean`). The finite-dimensional case of item
35 follows by a further argument.

**Quadratic variation (supporting, item 39).** Brownian quadratic sums converge to elapsed time
in $L^2$ (`ProbabilityTheory.IsPreBrownianReal.tendsto_integral_sq_quadraticSum_sub`,
`TauCeti/Probability/BrownianMotion/QuadraticVariation.lean`), an analogue of item 39 without
stationarity. The fourth mixed moments of a Gaussian vector,
$\mathbb E[Z_iZ_jZ_kZ_l]=S_{ij}S_{kl}+S_{ik}S_{jl}+S_{il}S_{jk}$ for centred coordinates, on which
the variance of $U_n$ rests, are `TauCeti.Probability.integral_mul_mul_mul_multivariateGaussian`
and its centred and random-vector forms
(`TauCeti/Probability/Distributions/Gaussian/MixedMoments.lean`). Girsanov's theorem for
Brownian motion is in `TauCeti/Probability/BrownianMotion/Girsanov.lean`.

**Bessel kernel (supporting, item 40).** The Bessel kernel $G_\delta$ on a finite-dimensional
inner-product space is nonnegative with mass one and has Fourier transform
$(1+\|\xi\|^2)^{-\delta/2}$ in Mathlib's normalisation (`TauCeti.besselKernel`,
`TauCeti.integral_besselKernel`, `TauCeti.fourier_besselKernel`,
`TauCeti/Analysis/Sobolev/BesselPotential/Kernel.lean`). For $\delta>d$ it is, up to scaling,
the Matérn covariance of smoothness $(\delta-d)/2$, given through its spectral density; its
closed form in $\mathcal K_\nu$ is absent, and TauCeti has $I_\nu$ but not $\mathcal K_\nu$.

**Synopsis entries.** Not covered: 34 (ingredients only: Hilbert-space projection),
35 (ingredients only: density, singularity, and support of finite-dimensional Gaussian laws), 36
(absent), 37 (ingredients only: Hilbert-space projection and Gaussian processes as a predicate),
38 (absent), 39 (ingredients only: Brownian quadratic variation and Gaussian fourth moments), 40
(ingredients only: the Bessel kernel and the total variation distance), 41 (absent).

### Likelihood inference under increasing-domain asymptotics

[Mathematical scope](SYNOPSIS.md#likelihood-inference-under-increasing-domain-asymptotics).

Mathlib has block determinants and the matrix determinant lemma
(`Matrix.det_fromBlocks₂₂`, `Matrix.det_add_mul`, `LinearAlgebra/Matrix/SchurComplement.lean`)
and the multivariate Gaussian law (`ProbabilityTheory.multivariateGaussian`,
`Probability/Distributions/Gaussian/Multivariate.lean`). TauCeti has its density and affine
images (`TauCeti.Probability.multivariateGaussianPDFReal`,
`TauCeti/Probability/Distributions/Gaussian/Density.lean`;
`TauCeti.Probability.map_affine_multivariateGaussian`,
`TauCeti/Probability/Distributions/Gaussian/Affine.lean`), and the characterisation of
independence of linear images by vanishing cross-covariance
(`TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff`,
`TauCeti/Probability/Distributions/Gaussian/Independence.lean`). No maximum likelihood
estimator, restricted likelihood, profile likelihood, or Fisher information is defined.

**Synopsis entries.** Not covered: 42 (absent), 43 (ingredients only: the Gaussian density and
determinants), 44 (ingredients only: the Gaussian density, affine images, and block
determinants).

### Variogram estimation and generalised linear models

[Mathematical scope](SYNOPSIS.md#variogram-estimation-and-generalised-linear-models).

TauCeti proves $\mathbb E\langle B(x-m),x-m\rangle=\mathop{\mathrm{tr}}(B\Sigma)$ for every law
with finite second moment
(`TauCeti.integral_inner_toEuclideanLin_sub_integral_eq_trace_mul_covMatrix`,
`TauCeti/Probability/Moments/Covariance.lean`), the moment generating function
$\det(I-2t\Theta S)^{-1/2}$ of a Gaussian quadratic form on its exact domain
(`TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian`,
`TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean`), and the moment generating
function of a weighted sum of squares of independent standard Gaussians
(`TauCeti.Probability.mgf_sum_mul_sq_pi_gaussianReal`,
`TauCeti/Probability/Distributions/Gaussian/ChiSquared.lean`). At a lag with
$N(h)\ne\emptyset$, the quadratic-form representation with $A(h)\mathbf 1=0$ lets one derive the
mean and the weighted $\chi^2_1$ law from these results. The estimator and its properties,
including the trend correction for intrinsically stationary residuals, are absent from both
libraries.

**Synopsis entries.** Not covered: 45 (ingredients only: the trace formula, the moment
generating function of Gaussian quadratic forms, and weighted sums of squared Gaussians), 46
(absent).

## 3. Lattice models, Markov random fields, and Gibbs measures

Neither library defines a Markov random field, a conditional or simultaneous
autoregression, a Gibbs specification, or a pseudolikelihood. The material recorded here is
the finite combinatorics, conditional independence, Gaussian conditioning, matrix
factorisation, and kernel vocabulary from which Part 3 would be built.

### Conditional specification and the Hammersley–Clifford theorem

[Mathematical scope](SYNOPSIS.md#conditional-specification-and-the-hammersleyclifford-theorem).

#### Mathlib

**Möbius inversion and subset sums (supporting, items 48, 49).** Möbius inversion on a
locally finite order (`IncidenceAlgebra.moebius_inversion_top`,
`IncidenceAlgebra.moebius_inversion_bot`, `Combinatorics/Enumerative/IncidenceAlgebra.lean`),
with the Möbius function of a product order (`IncidenceAlgebra.mu_prod_mu`). The Möbius
function of the lattice of subsets of a finite set, $(-1)^{|B\setminus A|}$, is not computed
as such; the alternating subset sums from which it follows are
`Finset.sum_powerset_neg_one_pow_card` and `Finset.sum_powerset_neg_one_pow_card_of_nonempty`
(`Data/Nat/Choose/Sum.lean`), and inclusion–exclusion is in
`Combinatorics/Enumerative/InclusionExclusion.lean`.

**Graphs and conditional independence (supporting, item 49).** Cliques of a simple graph
(`SimpleGraph.IsClique`, `Combinatorics/SimpleGraph/Clique.lean`) and the cycle graph
(`SimpleGraph.cycleGraph`, `Combinatorics/SimpleGraph/CycleGraph.lean`), on which the
$2\times2$-grid example lives. Conditional independence of random variables given a third
(`ProbabilityTheory.CondIndepFun`), with characterisations by conditional expectations and by
conditional distributions (`ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul`,
`ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`,
`Probability/Independence/Conditional.lean`). No full conditional distribution of a site, no
positivity condition, no potential, and no local or global Markov property for a graph are
defined. The scalar Poisson law is `ProbabilityTheory.poissonMeasure`
(`Probability/Distributions/Poisson/Basic.lean`).

#### TauCeti

**Conditional independence (supporting, item 49).** Weak union and decomposition for
Mathlib's conditional independence (`TauCeti.Probability.condIndep_of_condIndep_of_le_of_le`,
`TauCeti.Probability.iCondIndep_of_condIndep_compl`, and for coordinate restrictions
`TauCeti.Probability.condIndepFun_domRestrict_of_subset`,
`TauCeti/Probability/Independence/Conditional.lean`); the intersection property, on which the
equivalence of the Markov properties under positivity rests, is not stated. Ring-valued
alternating sums over subsets and over inclusion intervals are
`Finset.sum_powerset_neg_one_pow_card_of_ring` and
`Finset.sum_Icc_neg_one_pow_card_sub_card_left` (`TauCeti/Data/Finset/Basic.lean`); the
second is the Möbius inversion step for the lattice of subsets.

**A finite Gibbs law (supporting).** The hard-core law on the independent sets of a finite
graph with its single-site balance relation (`SimpleGraph.hardCorePMF`,
`SimpleGraph.hardCorePMF_single_site_balance`,
`TauCeti/Probability/Distributions/HardCore.lean`). It is one model, not a factorisation
theorem.

**Synopsis entries.** Not covered: 47 (absent), 48 (ingredients only: Möbius inversion on
locally finite orders and alternating subset and interval sums), 49 (ingredients only:
cliques, conditional independence and its weak-union and decomposition lemmas; the graph
Markov property and the almost-sure implication from normalised nonnegative clique products
are absent), 50 (absent; the auto-model representation from nondegenerate one-parameter full
conditionals), 51 (absent; the scalar Poisson law is present).

### Conditional and simultaneous autoregressions

[Mathematical scope](SYNOPSIS.md#conditional-and-simultaneous-autoregressions).

#### Mathlib

**Gaussian vectors and block matrices (supporting, items 52, 53).** The multivariate Gaussian
with given mean and positive semidefinite covariance (`ProbabilityTheory.multivariateGaussian`,
`Probability/Distributions/Gaussian/Multivariate.lean`), positive definite matrices
(`Matrix.PosDef`, `LinearAlgebra/Matrix/PosDef.lean`), and block inverses and determinants by
Schur complements (`Matrix.invOf_fromBlocks₂₂_eq`, `Matrix.invOf_fromBlocks₁₁_eq`,
`Matrix.det_fromBlocks₂₂`, `LinearAlgebra/Matrix/SchurComplement.lean`). No spectral density of
a field on $\mathbb Z^d$ is defined.

#### TauCeti

**Gaussian algebra (supporting, items 52, 53).** The image of $N(m,S)$ under $x\mapsto Lx+c$,
for a rectangular matrix $L$ and positive semidefinite $S$, is $N(Lm+c,LSL^\top)$
(`TauCeti.Probability.map_affine_multivariateGaussian`,
`TauCeti/Probability/Distributions/Gaussian/Affine.lean`); applied to
$X=\mu+(I-B)^{-1}\varepsilon$ this is the law of a simultaneous autoregression once the
defining equation is solved. The Gaussian density for positive definite $S$
(`TauCeti.Probability.multivariateGaussian_eq_withDensity`, `.../Gaussian/Density.lean`) and
Gaussian conditioning (`TauCeti.Probability.condDistrib_multivariateGaussian`,
`.../Gaussian/Conditional/Basic.lean`) are the remaining inputs for item 52.

**Positive-definite functions (supporting, item 54).** Positive-definite functions on groups
and Bochner's theorem (`TauCeti/Analysis/PositiveDefinite/AddGroup.lean`,
`TauCeti/Analysis/Bochner/BochnerTheorem.lean`); see Part 1. The Herglotz theorem on
$\mathbb Z$ (`TauCeti.isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq`,
`TauCeti/Analysis/Bochner/Herglotz.lean`) and its version for discrete abelian groups
(`TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq`,
`TauCeti/Analysis/Bochner/DiscreteGroup.lean`) are the spectral representation that item 54
uses on $\mathbb Z^d$.

**Synopsis entries.** Not covered: 52 (ingredients only: Gaussian density and conditioning),
53 (ingredients only: the affine-image theorem), 54 (ingredients only: positive-definite
functions and the spectral representation on discrete abelian groups).

### Gaussian Markov random fields

[Mathematical scope](SYNOPSIS.md#gaussian-markov-random-fields).

#### Mathlib

**Supporting (items 55–59).** In addition to the Gaussian and Schur-complement material above:
the $LDL^\top$ decomposition (`LDL.lower`, `LDL.diag`, `LDL.lowerInv`,
`Analysis/Matrix/LDL.lean`), and the Laplacian of a simple graph with its kernel and positive
semidefiniteness (`SimpleGraph.lapMatrix`, `SimpleGraph.lapMatrix_mulVec_one_eq_zero`,
`SimpleGraph.posSemidef_lapMatrix`,
`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`,
`Combinatorics/SimpleGraph/LapMatrix.lean`). The precision matrix of the first-order random
walk of item 59 is a multiple of the Laplacian of a path, so its rank-one null space is an
instance of the last theorem. Graph separation is expressible through walks and their supports
(`SimpleGraph.Walk.support`), but no separation predicate is defined.

#### TauCeti

**Gaussian conditioning in covariance form (items 55, 57).** For $N(m,S)$ on
$\mathbb R^{\iota\sqcup\kappa}$ with $S$ positive semidefinite, the conditional law of the
first block given the second is Gaussian with mean $m_1+S_{12}S_{22}^+(x_2-m_2)$ and covariance
$S_{11}-S_{12}S_{22}^+S_{21}$, which take their classical form when $S_{22}$ is positive definite
(`TauCeti.Probability.condDistrib_multivariateGaussian`,
`EuclideanSpace.gaussianCondMean_of_posDef`, `Matrix.gaussianCondCov_of_posDef`,
`TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean`). Jointly Gaussian blocks
are independent if and only if their cross-covariance vanishes
(`TauCeti.Probability.indepFun_sumEquivProd_multivariateGaussian_iff`,
`.../Gaussian/Multivariate.lean`; `indepFun_matrix_multivariateGaussian_iff`,
`.../Gaussian/Independence.lean`). For positive definite $\Sigma$ with $Q=\Sigma^{-1}$, the
identity $1/Q_{ii}=\Sigma_{ii}-\Sigma_{i,-i}\Sigma_{-i,-i}^{-1}\Sigma_{-i,i}$ is
`Matrix.PosDef.inv_inv_apply_self_eq_sub` (`TauCeti/LinearAlgebra/Matrix/SchurComplement.lean`).
Combined with the conditioning theorem this gives $\mathop{\mathrm V}(x_i\mid x_{-i})=1/Q_{ii}$,
which is not stated; the canonical parametrisation $N_C(b,Q)$, the conditional mean
$\mu_i-Q_{ii}^{-1}\sum_{j\ne i}Q_{ij}(x_j-\mu_j)$, and the equivalence of $Q_{ij}=0$ with
conditional independence are absent.

**Vertex separators (supporting, item 56).** Menger's theorem with separators written as
vertex sets meeting every walk from $A$ to $B$
(`SimpleGraph.exists_paths_setSeparator_sum_eq`,
`SimpleGraph.card_le_sum_of_forall_exists_mem_support`,
`TauCeti/Combinatorics/SimpleGraph/Connectivity/Menger.lean`). This is the separation notion
of the global Markov property; no probabilistic statement uses it.

**Cholesky factorisation (item 58).** Existence and uniqueness of the Cholesky factor of a
positive definite matrix (`Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq`,
`LDL.diagEntries_pos`, `TauCeti/Analysis/Matrix/LDL.lean`; `TauCeti.Matrix.cholesky`,
`TauCeti.Matrix.cholesky_mul_transpose`, `TauCeti.Matrix.cholesky_injective`,
`TauCeti/LinearAlgebra/Matrix/Cholesky/Basic.lean`). Nothing relates zeros of the factor to
conditional independence. No improper Gaussian law or generalised determinant is defined.

**Synopsis entries.** Not covered: 55 (ingredients only: conditioning in covariance form, the
diagonal Schur identity for $\Sigma^{-1}$, and block independence), 56 (ingredients only:
vertex separators; no global Markov property, and TauCeti lacks the intersection property of
conditional independence), 57 (ingredients only: conditioning in covariance form), 58
(ingredients only: the Cholesky factor and the affine-image theorem), 59 (ingredients only:
the kernel and rank of graph Laplacians).

### Gibbs measures on infinite lattices

[Mathematical scope](SYNOPSIS.md#gibbs-measures-on-infinite-lattices).

#### Mathlib

**Supporting (items 60–62).** The σ-algebras generated by the coordinates in a set
(`MeasureTheory.cylinderEvents`, `MeasureTheory/Constructions/Cylinders.lean`) and their
decreasing family over complements of finite sets
(`MeasureTheory.Filtration.cylinderEventsCompl`, `Probability/Process/Filtration.lean`), whose
infimum is the tail σ-algebra $\mathcal T$; proper kernels for a pair of σ-algebras
(`ProbabilityTheory.Kernel.IsProper`, `Probability/Kernel/Proper.lean`); exponential tilting
of a measure, which forms the Boltzmann weights of a finite-volume kernel
(`MeasureTheory.Measure.tilted`, `MeasureTheory/Measure/Tilted.lean`). The Kolmogorov
zero–one law for independent sequences
(`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup`,
`Probability/Independence/ZeroOne.lean`), total variation distance (`MeasureTheory.tvDist`,
`MeasureTheory/Measure/TotalVariation/Defs.lean`), product measures on arbitrary index sets
(`MeasureTheory.Measure.infinitePi`, `Probability/ProductMeasure.lean`), Prokhorov compactness
of probability measures (`MeasureTheory/Measure/Prokhorov.lean`), and the equivalence of
ergodicity with extremality among invariant measures of a single map
(`Ergodic.iff_mem_extremePoints`, `Dynamics/Ergodic/Extreme.lean`). No specification, Gibbs
measure, DLR equation, potential, or quasilocality is defined.

#### TauCeti

**Tail fields and extremality (supporting, item 61).** The tail $\sigma$-algebra of a process
indexed by $\mathbb N$ (`TauCeti.Probability.tailProcess`, `TauCeti.Probability.tailFamily`,
`TauCeti/Probability/Process/Tail/Basic.lean`); extremal invariant measures of a countable
group action are the ergodic ones (`ErgodicSMul.iff_mem_extremePoints`,
`TauCeti/MeasureTheory/Group/ErgodicExtreme.lean`); and the extremal exchangeable laws are the
i.i.d. laws (`TauCeti.Probability.exchangeable_extreme_iff_iid`,
`TauCeti/Probability/Exchangeability/PathSpace/Law/Extreme.lean`). These are analogues of
item 61 for other convex sets of measures. The finite-volume Gibbs variational identity
$\mathrm{KL}(\mu\,\|\,Z^{-1}e^{-f}\nu)-\log Z=\int f\,d\mu+\mathrm{KL}(\mu\,\|\,\nu)$ for
$f\ge0$ is `TauCeti.klDiv_tilted_neg_add_ofReal_neg_log`
(`TauCeti/InformationTheory/KullbackLeibler/Tilted.lean`); no lattice statement uses it.

**Perron–Frobenius and Markov chains (supporting, item 63).** A strictly positive real matrix
has a positive eigenvector for its spectral radius, unique up to scaling
(`Matrix.exists_mulVec_eq_smul_of_pos`, `Matrix.eq_of_mulVec_eq_smul_of_nonneg`,
`Matrix.spectralRadius_eq_of_mulVec_eq_smul`,
`TauCeti/LinearAlgebra/Matrix/PerronFrobenius/Positive.lean`, with irreducible and primitive
versions in the same directory). A finite irreducible chain has a unique invariant law
(`ProbabilityTheory.Kernel.existsUnique_invariant_probability`,
`TauCeti/Probability/MarkovChain/Invariant.lean`), and its stationary path law on $\mathbb N$
is shift invariant
(`ProbabilityTheory.Kernel.Invariant.measurePreserving_shift_markovChainLaw`,
`TauCeti/Probability/MarkovChain/Stationary.lean`). The transfer-matrix construction of the
one-dimensional Gibbs measure on a nonempty finite state space and the two-sided stationary
chain on $\mathbb Z$ are not formed.

**Synopsis entries.** Not covered: 60 (ingredients only: cylinder σ-algebras, proper kernels,
tilting, and Prokhorov compactness; existence for absolutely summable potentials and positive
finite a priori mass is absent), 61 (ingredients only: tail $\sigma$-algebras and extremality
theorems for group actions and exchangeability; the Gibbs criterion for probability measures
with a tail density is absent), 62 (ingredients only: total variation; uniqueness and
existence on nonempty standard Borel state spaces are absent), 63 (ingredients only:
Perron–Frobenius and stationary Markov path laws), 64 (absent).

### Estimation by coding and pseudolikelihood

[Mathematical scope](SYNOPSIS.md#estimation-by-coding-and-pseudolikelihood).

No coding set, conditional likelihood, or pseudolikelihood is defined in Mathlib or TauCeti.
The asymptotic tools that a proof would use are present in other forms: convergence in
probability and in distribution (`MeasureTheory.TendstoInMeasure`,
`MeasureTheory.TendstoInDistribution`), the i.i.d. central limit theorem
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`,
`Probability/CentralLimitTheorem.lean`), TauCeti's Lindeberg theorem for triangular arrays of
independent variables (`TauCeti/Probability/CentralLimitTheorem/Lindeberg.lean`), and the
chi-squared law (`TauCeti/Probability/Distributions/ChiSquared/Basic.lean`). No central limit
theorem for conditionally independent or martingale-difference arrays is present.

**Synopsis entries.** Not covered: 65 (absent).

### Finite Gibbs sampling

[Mathematical scope](SYNOPSIS.md#finite-gibbs-sampling).

#### Mathlib

**Supporting (item 123).** Finite conditional probabilities are given by
`ProbabilityTheory.condDistrib_apply_of_ne_zero` (`Probability/Kernel/CondDistrib.lean`).
Reversibility implies invariance and invariant kernels preserve the law under composition
(`ProbabilityTheory.Kernel.IsReversible.invariant`, `ProbabilityTheory.Kernel.Invariant.comp`,
`Probability/Kernel/Invariance.lean`).

#### TauCeti

**Heat-bath dynamics (part of item 123).** The uniform random-site heat bath of the hard-core
law satisfies detailed balance and converges from each initial probability at positive
activity (`TauCeti.Probability.HardCore.detailed_balance`,
`TauCeti.Probability.HardCore.isReversible`, `TauCeti.Probability.HardCore.tendsto_tvDist`,
`TauCeti/Probability/MarkovChain/Examples/HardCore/Equilibrium.lean`). An edgeless graph gives
the positive binary product-law example of item 123 by identifying subsets with binary
configurations. Generic convergence from an initial probability is available for an
irreducible aperiodic chain with an invariant probability
(`ProbabilityTheory.Kernel.Invariant.tendsto_tvDist_pow_comp`,
`TauCeti/Probability/MarkovChain/Equilibrium.lean`). General full-conditional updates,
deterministic sweeps, and uniform convergence of the finite Gibbs sampler are absent.

**Synopsis entries.** Partly covered: 123 (hard-core random-scan special case).

### Matérn fields and the stochastic partial differential equation

[Mathematical scope](SYNOPSIS.md#matérn-fields-and-the-stochastic-partial-differential-equation).

#### Mathlib

**Fourier multipliers and Bessel potentials (supporting, item 66).** Fourier multipliers on
Schwartz space and tempered distributions (`SchwartzMap.fourierMultiplierCLM`,
`TemperedDistribution.fourierMultiplierCLM`, `Analysis/Distribution/FourierMultiplier.lean`),
the Bessel potential with multiplier $(1+\|\xi\|^2)^{s/2}$
(`TemperedDistribution.besselPotential`, `Analysis/Distribution/Sobolev.lean`,
`Analysis/FunctionalSpaces/BesselPotentialSpace.lean`), and Gaussian processes
(`ProbabilityTheory.IsGaussianProcess`,
`Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`). The operator
$(\kappa^2-\Delta)^{\alpha/2}$ is a rescaled Bessel potential. No white noise and no Matérn
covariance are defined.

#### TauCeti

**Sobolev theory (supporting, items 66, 67).** $L^2$ Fourier multipliers
(`MeasureTheory.Lp.fourierMultiplierCLM`, `TauCeti/Analysis/Fourier/L2Multiplier.lean`), Bessel
potential spaces and their identification with $W^{k,p}$
(`TauCeti/Analysis/Sobolev/BesselPotential/`), and Sobolev spaces with the Rellich theorem
(`TauCeti/Analysis/Sobolev/`). `TauCeti.PDE.existsUnique_galerkinSolution` gives a
finite-dimensional Galerkin solution for a deterministic parabolic equation
(`TauCeti/Analysis/PDE/Parabolic/Galerkin.lean`). The Neumann SPDE's finite-element
precisions, convergence of means and covariances on $L^2$ test functions, and low-frequency
lattice approximation for $a>4$ are absent.

**Synopsis entries.** Not covered: 66 (ingredients only: Fourier multipliers and Bessel
potentials), 67 (ingredients only: Sobolev spaces and deterministic Galerkin equations).

## 4. Point processes and random measures

TauCeti has a substantial theory of Poisson random measures on an arbitrary measurable space,
following Last and Penrose. A random measure is a measurable map $\xi:\Omega\to\mathcal M(X)$
into all measures with the evaluation $\sigma$-algebra, and its intensity measure is the
Giry-monad bind $\mathbb P\mathbin{>\!\!>=}\xi$, so $\Lambda(B)=\mathbb E\xi(B)$. Neither library
defines a stationary point process, a Palm distribution, a Cox process, or a determinantal
process.

### General theory

[Mathematical scope](SYNOPSIS.md#general-theory).

#### Mathlib

**Campbell's formula, nonnegative case (item 68).** For a kernel $\xi$ and measurable
$u\ge0$, $\int u\,d(\mathbb P\mathbin{>\!\!>=}\xi)=\int\!\!\int u\,d\xi(\omega)\,\mathbb P(d\omega)$, and
$(\mathbb P\mathbin{>\!\!>=}\xi)(B)=\int\xi(\omega)(B)\,\mathbb P(d\omega)$
(`MeasureTheory.Measure.lintegral_bind`, `MeasureTheory.Measure.bind_apply`,
`MeasureTheory/Measure/GiryMonad.lean`; almost-everywhere measurability hypotheses). With
$\Lambda=\mathbb P\mathbin{>\!\!>=}\xi$ this is Campbell's formula for $u\ge0$.

#### TauCeti

**Campbell's formula, integrable case (item 68).** If $u$ is integrable with respect to
$\mathbb P\mathbin{>\!\!>=}\xi$, the Bochner version of the same identity holds, and integrability
is equivalent to almost-sure integrability of $u$ against $\xi(\omega)$ together with
integrability of $\omega\mapsto\int|u|\,d\xi(\omega)$ (`MeasureTheory.Measure.integral_bind`,
`MeasureTheory.Measure.integrable_bind_iff`, `MeasureTheory.Measure.integrable_integral_bind`,
`TauCeti/MeasureTheory/Integral/Bind.lean`).

**Determination of the law (items 69, 70).** For a finite measure $\mathbb P$ and almost
everywhere measurable random measures, possibly on different probability spaces, the laws
agree if and only if the finite-dimensional distributions agree on finite families, if and
only if they agree on pairwise disjoint families, if and only if the Laplace functionals agree
on $[0,\infty]$-valued measurable functions
(`MeasureTheory.Measure.map_eq_iff_forall_finset_map_eval_eq`,
`map_eq_iff_forall_map_eval_eq_of_pairwise_disjoint`,
`TauCeti/Probability/RandomMeasure/Law.lean`; `map_eq_iff_laplaceFunctional_eq`,
`map_eq_of_laplaceFunctional_sum_indicator_eq`,
`TauCeti/Probability/RandomMeasure/Determination.lean`; `Measure.laplaceFunctional`,
`TauCeti/Probability/RandomMeasure/LaplaceFunctional.lean`). The void probability
$\mathbb P(\xi(B)=0)$ is the Laplace functional at $\infty\cdot\mathbf 1_B$
(`laplaceFunctional_indicator_top`). Independence of random measures is characterised by
finite evaluation vectors (`iIndepFun_measure_iff`,
`TauCeti/Probability/RandomMeasure/Independence.lean`), and local finiteness follows from a
locally finite intensity (`ae_isLocallyFiniteMeasure_of_bind`,
`TauCeti/Probability/RandomMeasure/LocalFiniteness.lean`). Integer-valued measures are
`Measure.IsIntegerValued` (`TauCeti/MeasureTheory/Measure/IntegerValued/Basic.lean`). On a
standard Borel space a σ-finite integer-valued measure is a countable sum of Dirac masses
(`IsIntegerValued.exists_eq_sum_dirac`, `IntegerValued/Atomic.lean`), and a measurable family of
integer-valued measures with a common countable finite-mass cover has a measurable enumeration of
its atoms (`Measurable.exists_occurrence_enumeration_of_cover`,
`IntegerValued/Enumeration/LocallyFinite.lean`). No factorial measure, factorial moment measure,
product density, or pair correlation function is defined.

**Synopsis entries.** Covered: 68 (Campbell's formula with $\Lambda=\mathbb P\mathbin{>\!\!>=}\xi$:
the nonnegative case in Mathlib, the integrable case and the integrability criterion in
TauCeti; neither is named as Campbell's formula). Partly covered: 69 (the law is determined by
the finite-dimensional distributions on disjoint sets and by the Laplace functional, in
TauCeti; the characterisation by the laws of all $\int u\,d\xi$ and the refinement to
continuous functions of bounded support on a complete separable metric space are absent). Not
covered: 70 (ingredients only: void probabilities as Laplace values and determination by
finite-dimensional distributions; the Rényi-type uniqueness for simple processes is absent),
71 (ingredients only: integer-valued measures as sums of Dirac masses and measurable enumeration
of atoms; factorial measures are absent).

### The Poisson process

[Mathematical scope](SYNOPSIS.md#the-poisson-process).

#### Mathlib

**Scalar Poisson law (supporting).** `ProbabilityTheory.poissonMeasure`
(`Probability/Distributions/Poisson/Basic.lean`) and the binomial-to-Poisson limit
(`Probability/Distributions/Poisson/PoissonLimitThm.lean`). No point process is defined.

#### TauCeti

All declarations are in namespace `TauCeti.Probability` under
`TauCeti/Probability/PointProcess/Poisson/`.

**Definition, uniqueness, and existence (item 72).** `IsPoissonRandomMeasure P N Λ`
(`Basic.lean`) requires $N$ measurable, independent Poisson counts $N(A_i)\sim\mathrm{Po}(\Lambda(A_i))$
on finite disjoint families of sets of finite intensity, and $N(A)=\infty$ almost surely when
$\Lambda(A)=\infty$; $\Lambda$ is an arbitrary measure on an arbitrary measurable space. This is
the definition of the synopsis with $\mathrm{Po}(\infty)=\delta_\infty$. The law is unique for
every $\Lambda$ (`IsPoissonRandomMeasure.identDistrib`, `Law.lean`). A Poisson random measure
exists for $\sigma$-finite $\Lambda$ (`Measure.poissonLaw`,
`Measure.isPoissonRandomMeasure_poissonLaw`, `isPoissonRandomMeasure_iff_hasLaw_poissonLaw`,
`Construction.lean`); the synopsis asks for $s$-finite $\Lambda$. For finite intensity $rQ$, $Q$ a
probability measure, the law of $\sum_{i<\kappa}\delta_{X_i}$ with $\kappa\sim\mathrm{Po}(r)$
independent of i.i.d. $X_i\sim Q$ is the Poisson law (`finitePoissonLaw`,
`finitePoissonLaw_eq_map_prod_infinitePi`, `isPoissonRandomMeasure_finitePoissonLaw`,
`Finite.lean`, `Sampling/Counts.lean`), with the series formula `lintegral_finitePoissonLaw`.
The converse statement, that given $\eta(X)=m$ the points are i.i.d. with law $\Lambda/\Lambda(X)$,
is not stated.

**Laplace functional (item 73).** $N$ is Poisson with intensity $\Lambda$ if and only if
$\mathbb E e^{-\int u\,dN}=\exp(-\int(1-e^{-u})\,d\Lambda)$ for all measurable
$u:X\to[0,\infty]$ (`IsPoissonRandomMeasure.laplaceFunctional_eq_expNeg`, `Laplace.lean`;
`isPoissonRandomMeasure_of_laplaceFunctional`, `LaplaceCharacterization.lean`; any $\Lambda$).

**Superposition, restriction, and mapping (item 74).** A countable sum of independent Poisson
random measures is Poisson with the summed intensity (`isPoissonRandomMeasure_sum`,
`Superposition/Countable.lean`; `isPoissonRandomMeasure_finsetSum`, `Superposition/Basic.lean`);
restrictions are Poisson (`IsPoissonRandomMeasure.restrict`) and restrictions to disjoint sets
are independent (`IsPoissonRandomMeasure.iIndepFun_restrict`, `indepFun_restrict`,
`Independence.lean`); measurable images are Poisson with the image intensity
(`IsPoissonRandomMeasure.map`, `Basic.lean`).

**Marking and thinning (items 75, 76).** For a Poisson random measure on $X\times Y$ with
intensity $\Lambda\otimes Q$ and a measurable region $A$, the projection of the restriction to
$A$ is Poisson with intensity $\Lambda$ weighted by $x\mapsto Q(A_x)$
(`IsPoissonRandomMeasure.acceptance`, `Acceptance.lean`); for $Q$ Bernoulli$(p)$ the two colour
classes are independent Poisson random measures with intensities $p\Lambda$ and $(1-p)\Lambda$
(`acceptance_univ_prod_singleton_of_bernoulliMeasure`, `iIndepFun_map_fst_restrict_univ_prod`,
`indepFun_map_fst_restrict_univ_prod`, `Independence.lean`). These start from a Poisson
measure that is already marked. Independent marking kernels are constructed with their
Laplace formulas (`Kernel.tupleMarking`, `Kernel.optionalTupleMarking`,
`TauCeti/Probability/PointProcess/Marking/`), but the marking theorem, that independent marking
of a Poisson process gives a Poisson process on the product, is not stated, so the passage
from independent retention of points to the colour-splitting theorem is missing.

**Simplicity (item 77).** On a countably separated space, a Poisson random measure with
$\sigma$-finite diffuse intensity is almost surely simple
(`IsPoissonRandomMeasure.ae_forall_singleton_le_one`, `Simplicity.lean`). The converse is not
stated. The realisations are almost surely integer-valued and $\sigma$-finite
(`ae_isIntegerValued`, `ae_sigmaFinite`, `IntegerValued.lean`).

**Mecke equation (items 79, 80).** For $\kappa\sim\mathrm{Po}(r)$ independent of i.i.d.
$Z_i\sim Q$, $Q$ a probability measure, and $\eta=\sum_{i<\kappa}\delta_{Z_i}$,
$\mathbb E\int g(y,\eta)\,\eta(dy)=r\int\mathbb E\,g(y,\eta+\delta_y)\,Q(dy)$ for measurable
$g\ge0$ (`ProbabilityTheory.IndepFun.mecke_poissonMeasure_sample`,
`MeasureTheory.Measure.lintegral_finsetSum_dirac_poissonMeasure_pi`, `Sampling/Mecke.lean`).
This is the forward Mecke equation for finite intensity. The fixed-sample-size identity
`lintegral_finsetSum_dirac_pi_succ` is the combinatorial step towards the multivariate
equation. The general case, the converse characterisation, and the multivariate equation are
absent.

**Temporal material (supporting).** Count processes on the half-line, the characterisation of
the homogeneous Poisson process by i.i.d. exponential gaps
(`isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_occurrenceGap`, `Interarrival.lean`), and
the strong law $N(0,t]/t\to r$ (`IsPoissonRandomMeasure.ae_tendsto_nat_count_div`,
`StrongLaw.lean`). The Gaussian Poincaré inequality
(`TauCeti.Probability.variance_le_sum_integral_fderiv_sq_pi`,
`TauCeti/Probability/Distributions/Gaussian/Poincare.lean`) is not the Poisson one.

**Synopsis entries.** Covered: 73, 74. Partly covered: 72 (uniqueness for every intensity,
existence for $\sigma$-finite intensity, and the mixture representation for finite intensity;
existence for $s$-finite intensity and the conditional i.i.d. structure given $\eta(X)=m$ are
absent), 77 (diffuse intensity implies simplicity; the converse is absent), 79 (the forward
equation for finite intensity; the general case and the converse are absent). Not covered: 75
(ingredients only: marking kernels and their Laplace formulas), 76 (ingredients only: colour
splitting of a Poisson measure with Bernoulli marks; the marking theorem and the
product-density statement are missing), 78 (ingredients only: simplicity and determination by
finite-dimensional distributions), 80 (ingredients only: the fixed-sample-size identity), 81
(absent).

### Temporal counting processes

[Mathematical scope](SYNOPSIS.md#temporal-counting-processes).

#### Mathlib

**Supporting (items 124–126).** Martingales and filtrations
(`MeasureTheory.Martingale`, `Probability/Martingale/Basic.lean`), the predictable
$\sigma$-algebra (`MeasureTheory.Filtration.predictable`, `Probability/Process/Predictable.lean`),
and stopping times (`MeasureTheory.IsStoppingTime`, `Probability/Process/Stopping.lean`).
The optional-sampling theorem `Martingale.stoppedValue_ae_eq_condExp_of_le_of_countable_range`
is for stopping times with countable ranges (`Probability/Martingale/OptionalSampling.lean`).
Change of density of a measure is defined by `Measure.withDensity`
(`MeasureTheory/Measure/WithDensity.lean`).

#### TauCeti

**Temporal Poisson random measures from their counts (supporting, items 124, 125).** A
measurable random measure $M$ on $[0,\infty)$ whose cumulative counts are almost surely
$M[0,t]=N_t$ for a natural-valued process $N$ is Poisson with a locally finite intensity
$\Lambda$, $\Lambda\{0\}=0$, if and only if $N_0=0$ almost surely and $N$ has independent
increments with $N_t-N_s\sim\mathrm{Po}(\Lambda(s,t])$; atoms of $\Lambda$ at positive times are
allowed (`TauCeti.Probability.isPoissonRandomMeasure_iff_count_increments`,
`isPoissonRandomMeasure_smul_nnvolume_iff_count_increments`,
`TauCeti/Probability/PointProcess/Poisson/Temporal.lean`; the forward count properties in
`Poisson/Count.lean`). For count processes with stationary independent increments the Poisson
laws are characterised by $P(N_h=1)/h\to r$ and $P(N_h\ge2)/h\to0$
(`ProbabilityTheory.HasIndepIncrements.hasLaw_sub_poissonMeasure_iff_stationary_small_time`,
`TauCeti/Probability/Process/Poisson/Microscopic.lean`). Ordered occurrence times are stopping
times for an adapted cumulative-mass process and determine the measure and its law
(`TauCeti/Probability/PointProcess/OccurrenceTime/Stopping.lean`, `Reconstruction.lean`).
These are characterisations by independent increments, not by a martingale condition.

**Compensated homogeneous Poisson counts (part of item 124).**
`TauCeti.Probability.IsFilteredPoissonProcess` specifies independent Poisson increments of
parameter $r(t-s)$ relative to a filtration (`TauCeti/Probability/Process/Poisson/Filtered.lean`).
`IsFilteredPoissonProcess.martingale_compensated` proves that $N_t-rt$ is a martingale
(`TauCeti/Probability/Process/Poisson/Martingale.lean`). This is the forward martingale
implication from known Poisson increments with linear compensator. Conversely, a process
with independent Poisson increments starting at $0$ is a filtered Poisson process for its
natural filtration
(`ProbabilityTheory.HasIndepIncrements.isFilteredPoissonProcess_natural`, `Filtered.lean`). The
mapping theorem and exponential-gap law in the preceding section support item 125. They provide
deterministic pushforward of intensities and the gap law once the rescaled process is
shown to be Poisson. The stochastic-intensity change of law of item 126 is absent.

**Synopsis entries.** Partly covered: 124 (the implication from independent Poisson increments
to the martingale for homogeneous intensity; the converse and inhomogeneous $\nu$ are absent).
Not covered: 125 (ingredients only: stopping times, occurrence times, deterministic mappings,
exponential Poisson gaps, and recognition of Poisson random measures from count increments;
local martingales and random time changes are absent), 126 (ingredients only: predictability,
martingales, and change of density).

### Stationarity and Palm theory

[Mathematical scope](SYNOPSIS.md#stationarity-and-palm-theory).

#### Mathlib

**Supporting (items 82, 83).** Uniqueness of Haar measure up to a scalar
(`MeasureTheory.Measure.haarMeasure_unique`, `addHaarMeasure_unique`,
`MeasureTheory/Measure/Haar/Basic.lean`), which gives $\Lambda=\lambda\,|\cdot|$ for a
translation-invariant locally finite intensity; ergodic theory in `Dynamics/Ergodic/` and the
mean ergodic theorem (`Analysis/InnerProductSpace/MeanErgodic.lean`).

#### TauCeti

**Disintegration (supporting, item 83).** Disintegration of a measure on a product whose first
marginal is $\sigma$-finite, with uniqueness
(`ProbabilityTheory.sigmaFiniteCondKernel`, `compProd_fst_sigmaFiniteCondKernel`,
`eq_sigmaFiniteCondKernel_of_measure_eq_compProd`,
`TauCeti/Probability/Kernel/Disintegration/SigmaFinite.lean`; the second space is a nonempty
standard Borel space). Its documentation names Campbell measures and Palm kernels as the
intended application. For an s-finite kernel $\kappa$ and a measurable location $f$, the map
$a\mapsto\kappa(a)-\delta_{f(a)}$, erasing one atom, is measurable
(`ProbabilityTheory.Kernel.measurable_sub_dirac`, `TauCeti/Probability/Kernel/Sub.lean`); this
is the input for reduced Palm kernels. One-sided Bernoulli shifts are ergodic
(`ergodic_shift_of_iIndepFun`, `TauCeti/Probability/Ergodic/BernoulliShift.lean`), and
Birkhoff averages of a measure-preserving map converge in $L^2$ to the conditional expectation
on the invariant $\sigma$-algebra (`tendsto_eLpNorm_birkhoffAverage_sub_condExp`,
`TauCeti/Probability/Ergodic/CondExpProjection.lean`); these concern iterates of one map, not
$\mathbb Z^d$- or $\mathbb R^d$-actions. No stationary point process, reduced moment
measure, Campbell measure, or Palm distribution is formed.

**Synopsis entries.** Not covered: 82 (ingredients only: uniqueness of Haar measure and ergodic
theorems; mixing and ergodicity of Poisson processes on $\mathbb R^d$ with $d\ge1$ are absent),
83 (ingredients only: $\sigma$-finite disintegration and measurability of atom
erasure), 84 (absent; the finite-intensity Mecke equation of item 79 is present),
127 (ingredients only: disintegration and integration along a measurable translation action).

### Cox processes

[Mathematical scope](SYNOPSIS.md#cox-processes).

No Cox, mixed Poisson, log-Gaussian Cox, shot-noise, or Neyman–Scott process is defined in
either library. The ingredients are the Poisson Laplace functional and the integration of
mixtures by `Measure.bind` (Mathlib `lintegral_bind`, `MeasureTheory/Measure/GiryMonad.lean`;
TauCeti `integral_bind`, `memLp_two_bind_iff`,
`TauCeti/MeasureTheory/Integral/Bind.lean`), Gaussian processes (Mathlib `IsGaussianProcess`),
and the Gaussian moment generating function. The Cox void probability with extended intensity
uses the Poisson count law on finite-intensity sets (`IsPoissonRandomMeasure.hasLaw`) and
almost surely infinite counts on infinite-intensity sets (`IsPoissonRandomMeasure.ae_eq_top`,
`TauCeti/Probability/PointProcess/Poisson/Basic.lean`).

**Synopsis entries.** Not covered: 85 (ingredients only: integration of mixtures and the
Poisson count laws and Laplace functional), 86 (ingredients only: Gaussian processes and the
Gaussian moment generating function; the continuous-version stationarity criterion and parameter
identification are absent), 87 (absent).

### Determinantal point processes

[Mathematical scope](SYNOPSIS.md#determinantal-point-processes).

#### Mathlib

**Supporting (items 89, 90).** The spectral theorem for compact self-adjoint operators on a
Hilbert space (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`,
`Analysis/InnerProductSpace/Spectrum.lean`) and the variance of a sum of independent variables
(`ProbabilityTheory.IndepFun.variance_sum`, `Probability/Moments/Variance.lean`). No
trace-class operator or Fredholm determinant is defined.

#### TauCeti

**Supporting (items 88–91).** A Hilbert basis of eigenvectors for compact self-adjoint
operators (`TauCeti/Analysis/InnerProductSpace/Spectrum.lean`) and Bochner's theorem
(`TauCeti/Analysis/Bochner/BochnerTheorem.lean`). Operator ideals on Hilbert spaces: the
Hilbert–Schmidt energy and norm (`ContinuousLinearMap.hilbertSchmidtEnergy`,
`ContinuousLinearMap.hilbertSchmidtNorm`,
`TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Basic.lean`), the nuclear gauge
$\nu(T)=\sum_n a_n(T)\in[0,\infty]$ of approximation numbers, finite gauge implying compactness
(`ContinuousLinearMap.nuclearENorm`, `isCompactOperator_of_nuclearENorm_ne_top`,
`TauCeti/Analysis/OperatorIdeal/Nuclear/Basic.lean`), and the trace-class operator ideal
(`TauCeti.OperatorIdealFamily.traceClass`, `mem_finiteSubmodule_traceClass_iff`,
`TauCeti/Analysis/OperatorIdeal/Family/TraceClass.lean`). The trace of a trace-class operator,
integral operators of kernels on $L^2(\Lambda,\mu)$, local trace class, and Fredholm determinants
are not defined.

**Synopsis entries.** Not covered: 88 (ingredients only: the trace-class ideal; no
determinantal correlation function is defined), 89 (ingredients only: the spectral theorem for
compact self-adjoint operators and the trace-class ideal), 90 (ingredients only: eigenbasis
expansions and the variance of independent sums), 91 (ingredients only: Bochner's theorem).

## 5. Gibbs point processes and statistics of point patterns

Neither library defines a configuration space of finite point sets with its Poisson reference
measure, a Papangelou conditional intensity, a Gibbs point process, a summary statistic of a
point pattern, or a Markov chain Monte Carlo algorithm on a general state space. The Poisson
theory of Part 4 and abstract relative-entropy identities are the main ingredients.

### Densities, conditional intensities, and Markov point processes

[Mathematical scope](SYNOPSIS.md#densities-conditional-intensities-and-markov-point-processes).

#### Mathlib

**Supporting (items 92, 97).** Densities and Radon–Nikodým derivatives
(`MeasureTheory/Measure/WithDensity.lean`, `MeasureTheory/Measure/Decomposition/RadonNikodym.lean`),
mutual singularity (`MeasureTheory.Measure.MutuallySingular`), product measures, and the
Möbius inversion and inclusion–exclusion of Part 3.

#### TauCeti

**Poisson sampling series and the Mecke equation (items 92, 94, 95).** The finite Poisson law
$\Pi$ of intensity $rQ$ satisfies
$\int g\,d\Pi=\sum_n e^{-r}\frac{r^n}{n!}\int g(\sum_{i<n}\delta_{x_i})\,Q^{\otimes n}(dx)$
(`lintegral_finitePoissonLaw`, `TauCeti/Probability/PointProcess/Poisson/Finite.lean`), with
its Laplace functional (`laplaceFunctional_finitePoissonLaw`). The density of one Poisson law
with respect to another, item 92, and the bound $\int\beta^{n}\,d\Pi_W=e^{(\beta-1)|W|}$ used in
item 94 follow from this series by a computation that is not stated. The Mecke equation for
finite intensity (Part 4, item 79; `ProbabilityTheory.IndepFun.mecke_poissonMeasure_sample`,
`TauCeti/Probability/PointProcess/Poisson/Sampling/Mecke.lean`) is the case
$\lambda^\ast=\rho$ of the Georgii–Nguyen–Zessin formula, in the form
$\mathbb E\sum_{y}g(y,\eta)=r\int\mathbb E\,g(y,\eta+\delta_y)\,Q(dy)$, which is equivalent to the
form of item 95 with $h(y,\mu)=g(y,\mu+\delta_y)$; configurations are counting measures that
may have multiple points. No hereditary function, conditional intensity, or Markov function
is defined, and neither library puts a measurable structure on the finite subsets of a
window. The strong law for the counts of a homogeneous Poisson random measure on the
half-line (`TauCeti.Probability.IsPoissonRandomMeasure.ae_tendsto_nat_count_div`,
`TauCeti/Probability/PointProcess/Poisson/StrongLaw.lean`) is the ingredient of the mutual
singularity in item 92 for $d=1$; no strong law for counts in $\mathbb R^d$ is stated. The
hard-core law on a finite graph (Part 3) is a discrete model, not the continuum hard-core
process.

**Synopsis entries.** Partly covered: 95 (the Poisson case, the Mecke equation for finite
intensity, in TauCeti; the formula for hereditary densities and the converse characterisation
of finite-volume Gibbs measures are absent). Not covered: 92 (ingredients only: the Poisson
sampling series, Radon–Nikodým derivatives, and the temporal strong law; mutual singularity
of Poisson laws with distinct constant intensities on $\mathbb R^d$, $d\ge1$, is absent),
93 (absent), 94 (ingredients only: the Poisson sampling series and Laplace functional),
96 (absent),
97 (ingredients only: Möbius inversion), 98 (absent, including fixed-count integrability and
the normalisation criterion for the continuum hard-core model).

### Gibbs point processes

[Mathematical scope](SYNOPSIS.md#gibbs-point-processes).

#### Mathlib

**Relative entropy and exponential tilting (supporting, item 99).** The Kullback–Leibler
divergence with Gibbs' inequality and its equality case (`InformationTheory.klDiv`,
`InformationTheory.integral_llr_add_sub_measure_univ_nonneg`,
`InformationTheory.klDiv_eq_zero_iff`, `InformationTheory/KullbackLeibler/Basic.lean`), tilted
measures with the change-of-reference identity (`Measure.tilted`,
`MeasureTheory.integral_llr_tilted_right`, `MeasureTheory/Measure/LogLikelihoodRatio.lean`),
and the first two derivatives of the cumulant generating function as tilted mean and variance
(`ProbabilityTheory.deriv_cgf`, `ProbabilityTheory.iteratedDeriv_two_cgf`,
`Probability/Moments/MGFAnalytic.lean`; `variance_tilted_mul`,
`Probability/Moments/Tilted.lean`). For a finite-valued stable energy, deriving the activity
identity for $z>0$ and $\beta\ge0$ and the inverse-temperature identity for $z>0$ and $\beta>0$
also requires the integrability of the Poisson tilt in each parameter.

#### TauCeti

**Gibbs variational principle in abstract form (supporting, item 99).** For probability
measures $\mu,\nu$ and an almost everywhere nonnegative potential $f$,
$\mathrm{KL}(\mu\,\|\,Z^{-1}e^{-f}\nu)-\log Z=\int f\,d\mu+\mathrm{KL}(\mu\,\|\,\nu)$ in
$[0,\infty]$ (`TauCeti.klDiv_tilted_neg_add_ofReal_neg_log`,
`TauCeti/InformationTheory/KullbackLeibler/Tilted.lean`), with a real-valued version
(`TauCeti.klDiv_tilted_eq_boltzmannEntropy`,
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/InternalEnergy/Basic.lean`) and the
Donsker–Varadhan formula (`TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`,
`TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one`,
`TauCeti/InformationTheory/KullbackLeibler/Variational.lean`). With $\mathrm{KL}=0$ only at
equality, this is the variational characterisation of a Gibbs measure for a real-valued
potential. Item 99 needs energies with the value $+\infty$, the weighting $z^{n}$ against the
Poisson process on $\Lambda$, finiteness of $Z$ under stability, and the DLR equation, none of
which is formed. No infinite-volume configuration space, topology of local convergence,
tightness argument, or percolation threshold is present.

**Synopsis entries.** Not covered: 99 (ingredients only: the abstract variational identity,
Gibbs' inequality, and the cumulant derivatives), 100 (absent), 101 (absent).

### Summary statistics

[Mathematical scope](SYNOPSIS.md#summary-statistics).

#### Mathlib

**Supporting (items 102, 104).** The volume of Euclidean balls
(`EuclideanSpace.volume_ball`, `InnerProductSpace.volume_ball`,
`MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`).

#### TauCeti

**Poisson counts (supporting, items 102–104).** The count of a Poisson random measure on a set
is Poisson (`IsPoissonRandomMeasure.hasLaw`), with mean, variance, and factorial moments
(`TauCeti.Probability.integral_natCast_poissonMeasure`, `variance_natCast_poissonMeasure`,
`TauCeti/Probability/Distributions/Poisson/Basic.lean`;
`integral_prod_descFactorial_pi_poissonMeasure`,
`TauCeti/Probability/Distributions/Poisson/FactorialMoments.lean`). With the ball volume, the
first gives $1-F(r)=e^{-\lambda\omega_dr^d}$ for a homogeneous Poisson process, and the second
the variance of $\hat\lambda$ when $g\equiv1$, both by a further argument. For the
positive-dimensional Poisson process of item 104, $F=G$ additionally needs Palm theory. No
second-order moment measure, $K$ function, edge-corrected estimator, or $J$ function is defined.

**Ergodic averages (supporting, items 103, 108).** The von Neumann mean ergodic theorem for a
single measure-preserving map, with the limit identified as the conditional expectation on the
invariant σ-algebra (`TauCeti.Probability.birkhoffAverage_tendsto_metProjection`,
`TauCeti/Probability/Ergodic/MeanErgodic.lean`;
`TauCeti.Probability.tendsto_eLpNorm_birkhoffAverage_sub_condExp`,
`TauCeti/Probability/Ergodic/CondExpProjection.lean`), on top of Mathlib's abstract form
(`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`,
`Analysis/InnerProductSpace/MeanErgodic.lean`) and its definition of ergodicity
(`Ergodic`, `Dynamics/Ergodic/Ergodic.lean`). The almost-sure convergence of items 103 and 108
needs a pointwise ergodic theorem for averages over growing windows in $\mathbb R^d$ or
$\mathbb Z^d$, which is absent.

**Synopsis entries.** Not covered: 102 (ingredients only: the Mecke equation for finite
intensity and ball volumes), 103 (ingredients only: Poisson count laws with mean and variance,
and the single-map mean ergodic theorem),
104 (ingredients only: Poisson void probabilities and ball volumes), 128 (ingredients only:
marking kernels, integration against product kernels, and the finite-intensity Mecke equation),
129 (ingredients only: Poisson factorial moments, product integration, and ball volumes).

### Likelihood and estimating equations

[Mathematical scope](SYNOPSIS.md#likelihood-and-estimating-equations).

#### Mathlib

**Supporting (item 105).** Log-likelihood ratios (`MeasureTheory.llr`), the Kullback–Leibler
divergence, convexity of the exponential (`convexOn_exp`), and the central limit theorem for
i.i.d. real variables (`Probability/CentralLimitTheorem.lean`). No Fisher information, local
asymptotic normality, contiguity, or Hájek–Le Cam theory is present.

#### TauCeti

**Supporting (item 105).** Statistical experiments with densities and countable mixtures
(`TauCeti.HasDensity`, `TauCeti/Statistics/Experiments/Density.lean`,
`TauCeti/Statistics/Experiments/Mixture.lean`), as definitions. The Poisson sampling series and
the finite-intensity Mecke equation give the Poisson likelihood and the zero mean of its
score by a further argument. They also supply ingredients for the Poisson pseudolikelihood
normalisation relative to the unit-rate reference law and for the pseudolikelihood score
identity. The pseudolikelihood and its partition limit on positive-density configurations
are absent, as are Takacs–Fiksel estimation, minimum contrast, and Kutoyants' asymptotic theory.

**Synopsis entries.** Not covered: 105 (ingredients only: the Poisson sampling series and the
Mecke equation), 106 (absent), 107 (ingredients only: the Poisson sampling series and the
finite-intensity Mecke equation), 108 (ingredients only: the single-map mean ergodic
theorem), 109 (absent).

### Simulation

[Mathematical scope](SYNOPSIS.md#simulation).

#### Mathlib

**Kernels (supporting, item 110).** Detailed balance implies invariance
(`ProbabilityTheory.Kernel.IsReversible.invariant`, `Probability/Kernel/Invariance.lean`), and
$\varphi$-irreducibility is defined (`Kernel.IsIrreducible`, `Probability/Kernel/Irreducible.lean`;
definition and monotonicity in $\varphi$ only).

#### TauCeti

**Discrete Markov chains (supporting, item 110).** Singleton criteria for reversibility and
invariance (`Kernel.isReversible_iff_singleton`, `invariant_iff_singleton`,
`TauCeti/Probability/Kernel/Invariance.lean`), convergence in total variation for
positive recurrent chains irreducible with respect to counting measure
(`Kernel.IsPositiveRecurrent.tendsto_tvDist_pow_comp`,
`TauCeti/Probability/MarkovChain/Convergence.lean`), and convergence to an invariant law for
aperiodic chains of that kind (`Kernel.Invariant.tendsto_tvDist_pow_comp`,
`TauCeti/Probability/MarkovChain/Equilibrium.lean`), with aperiodicity defined through return
times (`Kernel.IsAperiodic`, `TauCeti/Probability/MarkovChain/Period.lean`). These require a
countable state space and do not apply to the continuous configuration space. The heat-bath
chain for the hard-core law on a finite graph is reversible and converges
(`TauCeti.Probability.HardCore.isReversible`, `HardCore.tendsto_tvDist`,
`TauCeti/Probability/MarkovChain/Examples/HardCore/Equilibrium.lean`), a discrete analogue of
item 110. No Metropolis–Hastings kernel, drift or minorisation condition, geometric or uniform
ergodicity, or continuous-time jump process other than the Poisson counting process is
present.

**Synopsis entries.** Not covered: 110 (ingredients only: reversibility implies invariance, and
the definition of $\varphi$-irreducibility), 111 (absent).

## 6. Stochastic and integral geometry

Mathlib has convex bodies with the Hausdorff metric and the Vietoris topology on compact sets,
and TauCeti adds Brunn–Minkowski, parallel-volume, and isoperimetric results. Neither library
defines a random closed set, intrinsic or mixed volumes, an invariant measure on affine flats,
or a random tessellation.

### Random closed sets and the Boolean model

[Mathematical scope](SYNOPSIS.md#random-closed-sets-and-the-boolean-model).

#### Mathlib

**Hyperspaces (supporting, item 112).** The Vietoris topology on compact and nonempty compact
subsets (`Topology/Sets/VietorisTopology.lean`; `NonemptyCompacts.isCompact_subsets_of_isCompact`),
the Hausdorff extended metric on closed, compact, and nonempty compact subsets with
completeness (`Closeds.edist_eq`, `Closeds.instCompleteSpace`,
`Topology/MetricSpace/Closeds.lean`), compactness of the space of closed subsets for the
Hausdorff uniformity (`Closeds.compactSpace_iff`, `Topology/UniformSpace/Closeds.lean`), and the
agreement of Hausdorff and Vietoris neighbourhoods at compact sets
(`IsCompact.nhds_hausdorff_eq_nhds_vietoris`). The Fell topology on the closed subsets of a
locally compact space is not defined. Continuity of measures along decreasing sequences
(`MeasureTheory.tendsto_measure_iInter_atTop`) gives the upper semicontinuity of a capacity
functional once it is defined.

#### TauCeti

**Choquet capacities (supporting, item 112).** Choquet capacities in the sense of descriptive
set theory, monotone set functions continuous along increasing sequences and along decreasing
sequences of closed sets, with the capacitability of analytic sets
(`TauCeti.IsChoquetCapacity`, `IsChoquetCapacity.analyticSet_eq_biSup_isCompact`,
`IsChoquetCapacity.measure`, `TauCeti/MeasureTheory/Constructions/Polish/Capacitability.lean`).
Complete alternation, the capacity functional of a random set, and the Choquet–Matheron
existence theorem are absent. For the Boolean model, the Poisson mapping and restriction
theorems and the marking kernels of Part 4 are present; the marking theorem and the germ–grain
construction are not.

**Measurable selections (supporting, item 130).** The Kuratowski–Ryll-Nardzewski theorem
`TauCeti.exists_measurable_forall_mem` gives a selection for nonempty closed values in a
Polish space when the hit events of all open sets are measurable
(`TauCeti/MeasureTheory/MeasurableSpace/Selection.lean`). Mathlib's
`geometric_hahn_banach_closed_point` separates closed convex sets from exterior points
(`Analysis/LocallyConvex/Separation.lean`). These support constructing selections and
identifying the expected convex set. No selection expectation or support-function identity
for it is defined.

**Synopsis entries.** Not covered: 112 (ingredients only: hyperspace topologies, continuity of
measures from above, and abstract Choquet capacities), 113 (ingredients only: Poisson count
laws, mapping and restriction, marking kernels, Minkowski sums, and Lebesgue measure),
130 (ingredients only: measurable selection, integration, and convex separation).

### Integral geometry of convex bodies

[Mathematical scope](SYNOPSIS.md#integral-geometry-of-convex-bodies).

#### Mathlib

**Convex bodies (supporting, items 114–117).** Nonempty compact convex sets with Minkowski
addition, nonnegative scaling, and the Hausdorff metric (`ConvexBody`,
`ConvexBody.hausdorffDist_coe`, `ConvexBody.hausdorffEDist_coe`, `Analysis/Convex/Body.lean`).
Lebesgue measure is homogeneous of degree $d$ (`MeasureTheory.Measure.addHaar_smul`), invariant
under linear isometries (`LinearIsometryEquiv.measurePreserving`,
`MeasureTheory/Measure/Haar/InnerProductSpace.lean`) and translations, and additive in the form
$|A\cup B|+|A\cap B|=|A|+|B|$ (`measure_union_add_inter`); these are the properties listed in
item 114 for $V_d$, but $V_d$ is introduced there through the Steiner formula, which is
absent, and continuity of volume on convex bodies in the Hausdorff metric was not found. Haar
measure exists on every locally compact group (`MeasureTheory.Measure.haarMeasure`), and
`MeasureTheory.Measure.haarMeasure_self` normalises it to mass $1$ on a chosen positive
compact set, the whole group when the group is compact. Support
functions, mixed and intrinsic volumes, valuations, and an affine Grassmannian with an
invariant measure are absent; Mathlib's `Grassmannian` is the algebro-geometric one.

**Surface measure (supporting, item 114).** `MeasureTheory.Measure.euclideanHausdorffMeasure`
is the Hausdorff measure normalised to agree with Lebesgue measure in the corresponding
Euclidean dimension (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`,
`Geometry/Euclidean/Volume/Measure.lean`). It gives the boundary measure in the surface-area
identity for convex bodies with nonempty interior.

#### TauCeti

**Parallel volumes and Brunn–Minkowski (supporting, item 114).** For convex bodies $K,L$,
$t\mapsto|K+tL|^{1/d}$ is concave and bounded below by $|K|^{1/d}+t|L|^{1/d}$
(`ConvexBody.concaveOn_volume_real_add_smul_rpow`,
`ConvexBody.volume_real_rpow_le_of_hasDerivWithinAt`,
`TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Parallel.lean`). For a compact convex set
with nonempty interior, the right derivative at $0$ of $t\mapsto|K+tB^d|$ is the perimeter
(`Convex.hasDerivWithinAt_measureReal_add_smul_closedBall`), and the volume of a shell is the
integral of perimeters (`TauCeti.measure_thickening_sdiff_closure_eq_setLIntegral_perimeter`,
`TauCeti/Analysis/BoundedVariation/ParallelVolume.lean`); the first gives the coefficient
$2V_{d-1}$ of the Steiner polynomial without its polynomiality. The isoperimetric inequality for
convex bodies holds with equality only for balls
(`ConvexBody.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`,
`ConvexBody.perimeter_pow_eq_iff_exists_eq_closedBall`,
`TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Isoperimetric.lean`). For a compact set
in an affine subspace of dimension $k$, the parallel volume divided by the volume of the
$(d-k)$-ball of radius $t$ tends to its $k$-dimensional Euclidean Hausdorff measure
(`TauCeti.tendsto_volume_real_add_smul_closedBall_div`), so in codimension one the right
derivative of the parallel volume at $0$ is twice the area
(`TauCeti.hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_one_eq`,
`TauCeti/Geometry/Euclidean/Volume/Parallel.lean`); this is $2V_{d-1}$ for lower-dimensional
convex bodies.

**Rigid motions (supporting, items 116–117).** The matrix orthogonal group is compact
(`TauCeti.Matrix.isCompact_unitaryGroup` with its `CompactSpace` instance,
`TauCeti/Topology/Algebra/UnitaryGroup.lean`), so it carries a Haar probability, and affine
isometries preserve volume (`AffineIsometryEquiv.measurePreserving`,
`TauCeti/MeasureTheory/Measure/Haar/InnerProductSpace.lean`). The motion group as a measure
space and the invariant measures on linear and affine flats are not formed. The files under
`TauCeti/MeasureTheory/Measure/Lebesgue/Steiner/` concern Steiner symmetrisation, not the Steiner
formula.

**Synopsis entries.** Not covered: 114 (ingredients only: convex bodies with the Hausdorff
metric, the properties of Lebesgue measure, normalised Hausdorff measure, and the derivative of
the parallel volume at $0$), 115 (absent), 116–117 (ingredients only: Haar probability on the
orthogonal group and volume preservation by affine isometries).

### Mean values for Boolean models and tessellations

[Mathematical scope](SYNOPSIS.md#mean-values-for-boolean-models-and-tessellations).

No relevant declarations were found in Mathlib, whose geometry-of-numbers file lists Voronoi
diagrams only as a future task. TauCeti has a deterministic nearest-point quantizer
(`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Quantization.lean`), unrelated to random
tessellations. A Poisson process of flats could be carried by TauCeti's Poisson law on a
parameter space of flats, which is not formed.

Haar measure and disintegration support the marked Palm description of a typical cell. Poisson
counts and Euclidean ball volumes support the containment law. In particular,
`TauCeti.Probability.IsPoissonRandomMeasure.hasLaw` gives the count on a measurable
finite-intensity set, including the event of no points. The Palm construction of the typical
Poisson–Voronoi cell and its flower are absent.

Specific intrinsic volumes of standard random sets need the intrinsic volumes of item 114 and
their additive extension to finite unions; neither library has them, nor the convex ring.

**Synopsis entries.** Not covered: 118–122 (absent), 168 (absent), 131 (ingredients only: Haar
measure and $\sigma$-finite disintegration), 132 (ingredients only: Poisson counts, ball
volumes, and deterministic nearest-point geometry).

## Missing from both libraries

The principal results of the synopsis that neither library provides, with the infrastructure
from which they would be developed:

* **Second-order random fields.** Stationarity, the realisation of positive definite functions
  as covariances of Gaussian fields, the spectral representation, mean-square calculus, and the
  isotropic classes $\Phi_d$ with Schoenberg's theorem. Bochner's theorem, the Kolmogorov
  extension theorem, and Gaussian laws are present.
* **Special functions.** The modified Bessel function $K_\nu$, hence the Matérn family;
  Gegenbauer polynomials, hence Schoenberg's theorem on spheres.
* **Gaussian process theory.** The Kolmogorov–Chentsov theorem, Dudley's bound, the
  Borell–TIS inequality, the Rice formula, the Gaussian kinematic formula, and the
  Feldman–Hájek dichotomy with its consequences for prediction under a misspecified
  covariance. Fernique's theorem, covering numbers, and finite-dimensional Gaussian densities
  are present, along with Euler characteristic for spaces of finite CW type.
* **Kriging and covariance estimation.** Universal and ordinary kriging, generalised least
  squares, restricted likelihood, and the asymptotics of maximum likelihood. Projection,
  Gaussian conditioning, and pseudoinverse block identities are present.
* **Markov random fields.** The Hammersley–Clifford theorem, Gaussian Markov random fields in
  precision form, Gibbs specifications on infinite lattices, Dobrushin's uniqueness theorem,
  the Ising phase transition, and the general finite Gibbs sampler. Möbius inversion,
  conditional independence, Gaussian conditioning, and a hard-core sampler are present.
* **Temporal counting processes.** The converse Poisson martingale characterisation,
  rescaling by a stochastic intensity, and the likelihood ratio for a predictable
  intensity. Martingales, predictability, and compensated homogeneous counts are present.
* **Point processes beyond the Poisson case.** The marking theorem, the general and
  multivariate Mecke equations, Palm theory, Cox and determinantal processes, Gibbs point
  processes with the Georgii–Nguyen–Zessin formula, summary statistics, and estimating
  equations. This includes Palm inversion and the mark-weighted and space–time $K$-functions.
  TauCeti's Poisson random measures and $\sigma$-finite disintegration are present.
* **Stochastic geometry.** Random closed sets with the Choquet–Matheron theorem, intrinsic
  volumes with the Steiner formula, Hadwiger's theorem, the Crofton and kinematic formulas,
  the Boolean model, selection expectations, and typical-cell laws for random tessellations.
  Convex bodies with the Hausdorff metric, the Vietoris topology, measurable selection, and
  Brunn–Minkowski are present.
