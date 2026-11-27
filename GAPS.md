# Principal gaps in spatial statistics

This file belongs to the project *Mathematical Statistics – Spatial Statistics*, which
describes the core mathematics of spatial statistics and compares it with the results proved
in the Lean libraries Mathlib and TauCeti. It follows the gap inventory of the sibling
statistics project, [CKSD GAPS.md](../lean-CKSD/GAPS.md). The [synopsis](SYNOPSIS.md)
describes the mathematical content in 133 numbered entries, drawn from the
[bibliography](MSSS-bib.md), and the [coverage inventory](STRUCTURE.md) records how far
Mathlib and TauCeti cover those entries, with declarations, source locations, and hypotheses.

This catalogue selects **91 principal theorem statements and theorem families** from the 129
synopsis entries that the libraries do not fully cover. The emphasis is on the central
theorems of each part, the results that organise its theory, and the results on which many
others depend. Corollaries that follow from selected statements by a short argument, routine
specialisations, and statements that are mainly definitions are not selected.

The comparison uses Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (16 November 2026)
and TauCeti at `d91980bdc255e6e50506be147ad9bcb88eb9fcc0` (19 November 2026), the dependency
pins of this project, and rests on the source inspection in the coverage inventory. Only completed proofs count as library results. Library results are
described here in words; STRUCTURE.md gives the declaration names and full hypotheses.

Each statement is restated verbatim from the synopsis, with the notation of its part and the
definitions that precede it under its heading, and keeps its synopsis number; numbers are
therefore nonconsecutive, and a reference to an item is a reference to the synopsis entry.
The conventions of the synopsis, on positive definiteness, the Fourier transform, $\Omega_d$,
$\omega_d$, and $|A|$, apply throughout. Each statement is followed by an assessment of what
the libraries supply towards it; entries that are partly covered in the sense of
STRUCTURE.md say so and are selected because the missing part is substantial. Each heading
links to its synopsis section, which supplies the reference guide, and to its coverage
section.

A *Lean target* paragraph after each assessment makes the statement actionable: it names
the library carriers to build on, the definitions the statement needs, the split into
Lean-statable conjuncts with every hypothesis explicit, the infrastructure no library has, and
the declaration of this project that states the result, with its status.

## Where the largest gaps lie

The two libraries together cover 4 of the 133 synopsis entries and partly cover 15. The
foundation on which a formalization would build is nevertheless substantial:

* Mathlib contributes the Kolmogorov extension theorem, multivariate Gaussian laws and
  Gaussian processes as a predicate, Fernique's theorem, characteristic functions with their
  differentiability, Hilbert-space projection and conditional expectation in $L^2$,
  conditional independence, Möbius inversion, graph Laplacians, Fourier multipliers and Bessel
  potentials on tempered distributions, Giry-monad integration, Haar measure, Markov kernels
  with reversibility, and convex bodies with the Hausdorff metric and the Vietoris topology.
* TauCeti adds positive definite functions with Bochner's theorem on $\mathbb R^d$ and
  Herglotz's theorem on discrete abelian groups, Bernstein's theorem for completely monotone
  functions, Schoenberg's theorem for conditionally negative definite kernels, Gaussian
  conditioning with pseudoinverses, Gaussian densities and quadratic forms, Cholesky
  factorisation, Perron–Frobenius, Sobolev spaces, Euler characteristic for spaces of finite CW
  type, a theory of random measures and Poisson random measures following Last and Penrose,
  relative-entropy variational identities, and Brunn–Minkowski, parallel-volume, and
  isoperimetric results for convex bodies.

The largest missing blocks are the theory of second-order and Gaussian random fields beyond
existence (spectral representation, isotropy, the Matérn family, sample-path regularity and
excursion sets, and equivalence of Gaussian measures), Markov random fields and Gibbs
measures, point processes other than the Poisson process, temporal intensity and Palm theory, and
stochastic and integral geometry. The special functions $\mathcal K_\nu$ and the
Gegenbauer polynomials are prerequisites for several of them.

The selected statements are distributed by part as follows:

* [1. Random fields and covariance functions](#1-random-fields-and-covariance-functions): 17 statements.
* [2. Geostatistics: spatial prediction and covariance-parameter inference](#2-geostatistics-spatial-prediction-and-covariance-parameter-inference): 13 statements.
* [3. Lattice models, Markov random fields, and Gibbs measures](#3-lattice-models-markov-random-fields-and-gibbs-measures): 16 statements.
* [4. Point processes and random measures](#4-point-processes-and-random-measures): 17 statements.
* [5. Gibbs point processes and statistics of point patterns](#5-gibbs-point-processes-and-statistics-of-point-patterns): 15 statements.
* [6. Stochastic and integral geometry](#6-stochastic-and-integral-geometry): 13 statements.

## 1. Random fields and covariance functions

Selected: 17 statements. [Synopsis part](SYNOPSIS.md#1-random-fields-and-covariance-functions) ·
[Coverage part](STRUCTURE.md#1-random-fields-and-covariance-functions).

### Existence and stationarity

[Synopsis](SYNOPSIS.md#existence-and-stationarity) ·
[Coverage](STRUCTURE.md#existence-and-stationarity).

* **2. Gaussian fields with given mean and covariance.** Let $T$ be a set,
  $m:T\to\mathbb R$ a function and $C:T\times T\to\mathbb R$ symmetric and positive
  definite. There is a Gaussian random field $Z$ on $T$, that is, one whose finite linear
  combinations are Gaussian, with $\mathbb E Z(t)=m(t)$ and
  $\mathop{\mathrm{Cov}}(Z(s),Z(t))=C(s,t)$. Its law is determined by $(m,C)$. Conversely,
  the covariance function of every second-order field is symmetric and positive definite.

  *Assessment.* Partly covered. Positive semidefiniteness of finite-dimensional covariances is
  necessary by TauCeti's covariance-matrix theorem and Mathlib's covariance bilinear form. Mathlib
  constructs the Gaussian field only for the covariance $\min(s,t)$ on $[0,\infty)$, but it has the
  multivariate Gaussian law for every positive semidefinite matrix, with its covariance and its
  consistency under restriction of coordinates. Missing are the assembly of these laws into a
  projective family indexed by finite subsets of $T$, the field it gives through the projective
  limit, and uniqueness of the law of a Gaussian field.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IsGaussianProcess`,
  `ProbabilityTheory.covariance` with its notation, `Matrix.PosSemidef` applied to `Matrix.of C`,
  which for an infinite index type quantifies over finitely supported coefficient vectors,
  `ProbabilityTheory.multivariateGaussian` with
  `ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian`, and
  `MeasureTheory.projectiveLimit`. No new definition is needed. Conjuncts: (i) for any type $T$,
  $m:T\to\mathbb R$ and $C$ with `(Matrix.of C).PosSemidef`, there is a probability measure on
  $T\to\mathbb R$ under which the coordinate process is Gaussian with mean $m$ and covariance $C$;
  (ii) two Gaussian processes, each with measurable coordinates and with the same means and
  covariances, have the same law on $T\to\mathbb R$; (iii) the covariance kernel of a family of
  square-integrable variables is positive semidefinite. Symmetry is part of `Matrix.PosSemidef`
  (Hermitian), so it need not be a separate hypothesis. Pitfall: Mathlib's `multivariateGaussian`
  returns a fallback law when the matrix is not positive semidefinite, so (i) must keep the
  hypothesis even though the definition typechecks without it. Everything is statable and provable
  at the pins; no dependency on another entry. MSSS: `MSSS.exists_isGaussianProcess_coord`,
  `MSSS.map_eq_of_isGaussianProcess`, `MSSS.posSemidef_covariance` (`MSSS/RandomFields/Basic.lean`),
  all proved.

### Spectral theory

[Synopsis](SYNOPSIS.md#spectral-theory) ·
[Coverage](STRUCTURE.md#spectral-theory).

* **5. Spectral representation of a stationary field.** Let $Z$ be a centred,
  mean-square continuous, second-order stationary field on $\mathbb R^d$ with spectral
  measure $F$. There is a complex random measure $W$ on $\mathbb R^d$ with orthogonal
  increments and $\mathbb E|W(A)|^2=F(A)$ such that
  $Z(t)=\int e^{i\langle t,\omega\rangle}W(d\omega)$ in $L^2$ for every $t$; then
  $W(-A)=\overline{W(A)}$ for every Borel set $A$. Conversely, let $F$ be a finite measure
  and $W$ a complex random measure with orthogonal increments, $\mathbb E W(A)=0$ and
  $\mathbb E|W(A)|^2=F(A)$. Then $Z(t)=\int e^{i\langle t,\omega\rangle}W(d\omega)$ is a
  centred, mean-square continuous, second-order stationary complex field with
  $\mathbb E Z(s)\overline{Z(t)}=\int e^{i\langle s-t,\omega\rangle}F(d\omega)$, and it is real
  when $W(-A)=\overline{W(A)}$ for every $A$.

  *Assessment.* TauCeti has Bochner's theorem and a Hilbert-space realisation of a positive definite
  function with a unitary representation of translations. Missing are orthogonally scattered random
  measures, the stochastic integral against them, the isometry of $L^2(F)$ onto the closed span of
  the field, and the symmetry $W(-A)=\overline{W(A)}$ for a real field.

  *Lean target.* Carriers at the pins: `MeasureTheory.charFun`, `MeasureTheory.Lp` with exponent 2
  and the inner product of `MeasureTheory.L2`, and linear isometries `Lp ℂ 2 F →ₗᵢ[ℂ] Lp ℂ 2 P`. A
  random measure with orthogonal increments and control measure $F$ is encoded as such an isometry
  $I$, with $W(A)=I(\mathbf 1_A)$, which avoids a separate definition of orthogonally scattered
  measures. New definitions: second-order field (every $Z(t)$ square-integrable), second-order
  stationarity on an additive group (constant mean and translation-invariant covariance), the
  stationary covariance $h\mapsto\mathop{\mathrm{Cov}}(Z(h),Z(0))$, mean-square continuity, and the
  plane wave $\omega\mapsto e^{i\langle t,\omega\rangle}$ as an element of $L^2(F)$. Conjuncts: (i)
  for a centred, mean-square continuous, second-order stationary real field on a finite-dimensional
  real inner-product space whose covariance is the characteristic function of a finite measure $F$,
  there is a linear isometry $I$ with centred values and $I(e^{i\langle t,\cdot\rangle})=Z(t)$
  almost surely for each $t$; (ii) for such an $I$,
  $\mathbb E\,I(e_s)\overline{I(e_t)}=\int e^{i\langle s-t,\omega\rangle}F(d\omega)$; (iii) the
  symmetry $I(\mathbf 1_{-A})=\overline{I(\mathbf 1_A)}$, and conversely reality of $I(e_t)$ under
  that symmetry. Pitfall: $F$ is supplied by hypothesis rather than produced by Bochner's theorem,
  so the statement depends on item 4's identification only through `hF`. Conjuncts (i) and (ii) are
  statable and provable at the pins; (iii) is statable. MSSS: `MSSS.exists_spectralRepresentation`
  and `MSSS.integral_spectralIntegral_mul_conj` (`MSSS/RandomFields/Spectral.lean`), both proved;
  conjunct (iii) and the mean-square continuity and centredness of the converse are not stated.

* **7. Mean-square differentiability.** Let $Z$ be a centred second-order stationary
  process on $\mathbb R$ with covariance $K$ and spectral measure $F$, and let $m\ge1$. The
  following are equivalent: $Z$ is $m$ times mean-square differentiable;
  $\int\omega^{2m}F(d\omega)<\infty$; $K^{(2m)}(0)$ exists and is finite. In that case $K$
  is $2m$ times differentiable on $\mathbb R$, and $Z^{(m)}$ is second-order stationary with
  covariance $(-1)^mK^{(2m)}$. A process may have analytic sample paths without being
  mean-square differentiable: $Z(t)=\cos(Xt+Y)$ with $X$ standard Cauchy and $Y$ uniform on
  $[0,2\pi)$ independent of $X$.

  *Assessment.* Mathlib proves that a finite moment of order $2m$ makes a characteristic function
  $2m$ times continuously differentiable. Missing are mean-square derivatives of a field, the
  converse from a finite derivative of order $2m$ at $0$ to a finite spectral moment, and the
  covariance of the derivative field.

  *Lean target.* Carriers at the pins: `MeasureTheory.charFun`,
  `MeasureTheory.iteratedDeriv_charFun`, `MeasureTheory.contDiff_charFun`, `iteratedDeriv`,
  `ContDiffOn`, and `MeasureTheory.Integrable` for the spectral moment. New definitions, beyond
  those of entry 5: the mean-square derivative (a process $Z'$ with
  $\mathbb E((Z(t+h)-Z(t))/h-Z'(t))^2\to0$ as $h\to0$, $h\ne0$, for every $t$), $m$-fold mean-square
  differentiability (a chain of square-integrable processes, each the mean-square derivative of the
  previous one), and "the derivative of order $n$ exists and is finite at $x$" ($K$ is $C^{n-1}$
  near $x$ and its derivative of order $n-1$ is differentiable at $x$). Conjuncts: (i) for $m\ge1$,
  the three conditions are equivalent; (ii) under them $K$ is $C^{2m}$ on $\mathbb R$ and the $m$th
  derivative process is second-order stationary with covariance $(-1)^mK^{(2m)}$; (iii) the Cauchy
  example is not mean-square differentiable while its paths are analytic. Pitfalls: Mathlib's
  `iteratedDeriv` returns $0$ where the derivative does not exist, so "$K^{(2m)}(0)$ exists and is
  finite" cannot be written as a value of `iteratedDeriv`; the spectral moment must be integrability
  of $\omega^{2m}$ or a `∫⁻` that is finite, not a Bochner integral. Everything is statable at the
  pins; the converse direction of (i) needs a Taylor-type second-difference argument for
  characteristic functions, which is absent. MSSS: `MSSS.isMeanSquareDifferentiable_tfae` (sorry);
  `MSSS.IsMeanSquareDifferentiable.derivative` and `MSSS.not_isMeanSquareDifferentiable_cos_cauchy`
  (`MSSS/RandomFields/Spectral.lean`), proved.

### Isotropic covariances

[Synopsis](SYNOPSIS.md#isotropic-covariances) ·
[Coverage](STRUCTURE.md#isotropic-covariances).

Let $\Phi_d$ denote the class of continuous $\varphi:[0,\infty)\to\mathbb R$ with
$\varphi(0)=1$ such that $(x,y)\mapsto\varphi(\|x-y\|)$ is positive definite on
$\mathbb R^d$, and $\Phi_\infty=\bigcap_d\Phi_d$. A continuous function
$\phi:[0,\infty)\to\mathbb R$ is **completely monotone** when it is infinitely
differentiable on $(0,\infty)$ and $(-1)^n\phi^{(n)}(t)\ge0$ for all $n\ge0$ and $t>0$.
Continuity at $0$ is part of the definition. By Bernstein's theorem, $\phi$ is completely
monotone if and only if $\phi(t)=\int_{[0,\infty)}e^{-rt}F(dr)$ for a finite nonnegative
measure $F$.

* **8. Schoenberg's theorem on isotropic covariances in $\mathbb R^d$.** Let $d\ge1$. A
  function $\varphi$ belongs to $\Phi_d$ if and only if
  $$\varphi(t)=\int_{[0,\infty)}\Omega_d(rt)\,F_0(dr),\qquad t\ge0,$$
  for a probability measure $F_0$ on $[0,\infty)$, which is then unique; $F_0$ is the image
  of the spectral measure under $\omega\mapsto\|\omega\|$. If
  $\int_0^\infty r^{d-1}|\varphi(r)|\,dr<\infty$, the spectral density is the radial function
  $$f(u)=(2\pi)^{-d/2}\int_0^\infty(ur)^{-(d-2)/2}J_{(d-2)/2}(ur)\,r^{d-1}\varphi(r)\,dr .$$
  The classes are nested and strictly decreasing,
  $\Phi_1\supsetneq\Phi_2\supsetneq\cdots\supsetneq\Phi_\infty$. For $d\ge2$, every
  non-constant member of $\Phi_d$ is strictly positive definite on $\mathbb R^d$.

  *Assessment.* TauCeti's Bochner theorem with linear pullbacks shows that the spectral measure of a
  radial function is rotation invariant, and Mathlib defines $J_\nu$. TauCeti defines the uniform
  law on the sphere, proves its invariance under linear isometries, factorises a radial density into
  an independent uniform direction and a radius, and computes the exponential moment of the uniform
  law through $I_\nu$. Missing are the characteristic function $\Omega_d$ of the uniform law on the
  sphere, the polar decomposition of rotation-invariant measures without density, the radial
  representation, the strict nesting of the classes, and strict positive definiteness.

  *Lean target.* Carriers at the pins: `TauCeti.IsPositiveDefiniteSub` on
  `EuclideanSpace ℝ (Fin d)`, `MeasureTheory.charFun`, `Complex.besselJ`,
  `TauCeti.Probability.uniformSphereMeasure`, and `MeasureTheory.Measure.withDensity`. New
  definitions: $\Omega_d(t)$, either as $\Gamma(d/2)(2/t)^{(d-2)/2}J_{(d-2)/2}(t)$ with the value
  $1$ at $t=0$ or as the characteristic function of `uniformSphereMeasure` evaluated in a fixed
  direction (the two must be proved equal); $\Phi_d$ as the set of $\varphi:\mathbb R\to\mathbb R$
  continuous on $[0,\infty)$ with $\varphi(0)=1$ and $x\mapsto\varphi(\|x\|)$ positive definite on
  `EuclideanSpace ℝ (Fin d)`; and strict positive definiteness (positive quadratic form for distinct
  points and nonzero coefficients). Conjuncts: (i) for $d\ge1$, $\varphi\in\Phi_d$ if and only if
  $\varphi(t)=\int\Omega_d(rt)F_0(dr)$ for $t\ge0$ with a probability measure $F_0$ on $\mathbb R$
  with $F_0((-\infty,0))=0$; (ii) uniqueness of $F_0$; (iii) $F_0$ is the image of the spectral
  measure under the norm; (iv) the density formula when $r^{d-1}\varphi(r)$ is integrable on
  $(0,\infty)$; (v) $\Phi_{d+1}\subsetneq\Phi_d$ and $\Phi_\infty\subsetneq\Phi_d$; (vi) for
  $d\ge2$, strict positive definiteness of non-constant members. Pitfalls: the density must be
  stated through `ENNReal.ofReal` of the radial integral, which is harmless because the integral is
  nonnegative; the factor $(ur)^{-(d-2)/2}$ at $u=0$ is a junk value on a null set; $J_{-1/2}$ for
  $d=1$ is singular at $0$, so the $d=1$ case of $\Omega_d$ must be checked against $\cos t$.
  Everything is statable at the pins; missing infrastructure is the identification of the
  characteristic function of the uniform law with $\Omega_d$ (owned on the open MotionGroupsBessel
  roadmap as the Bessel zonal function) and the polar decomposition of rotation-invariant finite
  measures. Entries 10, 11, 12 and 19 depend on this entry. MSSS: `MSSS.sphereCharFun`,
  `MSSS.isotropicClass`; `MSSS.mem_isotropicClass_iff`, `MSSS.eq_of_integral_sphereCharFun_eq`,
  `MSSS.integral_sphereCharFun_map_norm`, `MSSS.eq_withDensity_of_mem_isotropicClass`,
  `MSSS.isotropicClass_succ_ssubset`, `MSSS.isotropicClassInf_ssubset`,
  `MSSS.isStrictlyPositiveDefiniteSub_of_mem_isotropicClass` (`MSSS/RandomFields/Isotropic.lean`),
  all sorry.

* **10. Covariances valid in every dimension.** A function $\varphi$ belongs to
  $\Phi_\infty$ if and only if
  $$\varphi(t)=\int_{[0,\infty)}e^{-r^2t^2}F(dr),\qquad t\ge0,$$
  for a probability measure $F$ on $[0,\infty)$; equivalently, if and only if
  $t\mapsto\varphi(\sqrt t)$ is completely monotone. Every member of $\Phi_\infty$ is
  positive, nonincreasing, strictly decreasing unless it is constant, and infinitely
  differentiable on $(0,\infty)$. The key analytic fact is that
  $\Omega_d\bigl((2d)^{1/2}t\bigr)\to e^{-t^2}$ uniformly in $t\ge0$ as $d\to\infty$. Every
  completely monotone $\phi$ with $\phi(0)=1$ gives a member $\phi$ of $\Phi_\infty$; examples
  are $e^{-ct^\alpha}$ with $c\ge0$, $0<\alpha\le1$, and the Cauchy-type functions
  $(1+t^\alpha)^{-\beta/\alpha}$ with $0<\alpha\le1$, $\beta>0$. By the criterion through
  $\varphi(\sqrt t)$, both families belong to $\Phi_\infty$ for every $0<\alpha\le2$.

  *Assessment.* Partly covered. TauCeti proves that $e^{-c\|a-b\|^2}$ is a positive semidefinite
  kernel on every real inner-product space, so the Gaussian functions lie in every $\Phi_d$, and it
  has Bernstein's theorem and closure of positive definite functions under pointwise limits. Missing
  are closure under integral mixtures, the limit $\Omega_d((2d)^{1/2}t)\to e^{-t^2}$, and the
  characterisation of $\Phi_\infty$.

  *Lean target.* Carriers at the pins: those of entry 8, with
  `TauCeti.IsContinuousCompletelyMonotoneOnIoi`, `TauCeti.posSemidef_cexp_neg_mul_sq_norm`, and
  `TendstoUniformlyOn`. New definition: $\Phi_\infty$ as the intersection of $\Phi_d$ over $d\ge1$.
  Conjuncts: (i) $\varphi\in\Phi_\infty$ if and only if $\varphi$ is a Gaussian scale mixture with a
  probability measure on $[0,\infty)$; (ii) if and only if $\varphi(0)=1$ and
  $t\mapsto\varphi(\sqrt t)$ is continuous completely monotone; (iii) positivity on $[0,\infty)$,
  antitonicity, strict antitonicity unless constant, smoothness on $(0,\infty)$; (iv) uniform
  convergence of $\Omega_d(\sqrt{2d}\,t)$ to $e^{-t^2}$ on $[0,\infty)$; (v) continuous completely
  monotone $\varphi$ with $\varphi(0)=1$ lie in $\Phi_\infty$; (vi) the two families for
  $0<\alpha\le2$. Pitfalls: `Real.sqrt` of a negative argument is $0$, so (ii) concerns only
  $t\ge0$, which matches the definition of complete monotonicity on $(0,\infty)$ with continuity on
  $[0,\infty)$; `Real.rpow` with base $0$ and exponent $\alpha$ gives $0$, so $e^{-c\,0^\alpha}=1$
  as required. Conjuncts (i), (ii), (v) and (vi) are statable at the pins and depend only on
  Bernstein's theorem, the Gaussian kernel and closure under mixtures; (iii) follows from (i); (iv)
  depends on entry 8's $\Omega_d$. MSSS: `MSSS.mem_isotropicClassInf_of_completelyMonotone`,
  `MSSS.exp_neg_rpow_mem_isotropicClassInf`, `MSSS.cauchyType_mem_isotropicClassInf` and
  `MSSS.isPositiveDefiniteSub_sq_norm_of_completelyMonotone`, proved, but only for $0<\alpha\le1$;
  `MSSS.mem_isotropicClassInf_iff_gaussianMixture`,
  `MSSS.mem_isotropicClassInf_iff_completelyMonotone`, `MSSS.properties_of_mem_isotropicClassInf`
  and `MSSS.tendstoUniformlyOn_sphereCharFun` (`MSSS/RandomFields/Isotropic.lean`), sorry. The range
  $1<\alpha\le2$ of (vi) is not stated.

* **11. Pólya-type criteria and compact support.** (a) If $\varphi:[0,\infty)\to\mathbb R$
  is continuous and convex with $\varphi(0)=1$ and $\varphi(t)\to0$ as $t\to\infty$, then
  $\varphi\in\Phi_1$. (b) For $a>0$ and $\nu>0$, the truncated power function
  $(1-t/a)_+^{\nu}$ belongs to $\Phi_n$ if $\nu\ge(n+1)/2$, and only then. In particular the
  triangular function $(1-t/a)_+$ belongs to $\Phi_1$ but not to $\Phi_2$.

  *Assessment.* Absent from both libraries. Pólya's criterion requires that the triangular function
  be a characteristic function on $\mathbb R$ and a mixture argument; the truncated power functions
  require the radial Fourier transform of entry 8, and the "only then" clause requires the sign of
  that transform.

  *Lean target.* Carriers at the pins: those of entry 8, with `ConvexOn` and `Filter.Tendsto` at
  `Filter.atTop`. No new definition beyond $\Phi_d$. Conjuncts: (a) for $\varphi$ continuous on
  $[0,\infty)$, convex there, with $\varphi(0)=1$ and limit $0$ at infinity, $\varphi\in\Phi_1$; (b)
  for $a>0$, $\nu>0$, $n\ge1$, $(1-t/a)_+^\nu\in\Phi_n$ if and only if $\nu\ge(n+1)/2$; (c) the
  triangular function lies in $\Phi_1$ and not in $\Phi_2$. Pitfall: $(1-t/a)_+^\nu$ must be written
  as `max (1 - t / a) 0 ^ ν` with `Real.rpow`, whose value $0^\nu=0$ for $\nu>0$ is the intended
  one; the function is evaluated only at $t\ge0$ through the norm. Conjunct (a) is statable and
  provable at the pins from the triangular characteristic function and closure under mixtures; (b)
  and (c) are statable and depend on entry 8 (the radial Fourier transform) and on the Fourier
  transform of the truncated power. MSSS: `MSSS.triangular_mem_isotropicClass_one`,
  `MSSS.triangular_not_mem_isotropicClass_two`, proved; `MSSS.mem_isotropicClass_one_of_convexOn`,
  `MSSS.truncatedPower_mem_isotropicClass_iff` (`MSSS/RandomFields/Isotropic.lean`, both halves
  of (b)), sorry.

### The Matérn family

[Synopsis](SYNOPSIS.md#the-matérn-family) ·
[Coverage](STRUCTURE.md#the-matérn-family).

* **12. Matérn covariance and spectral density.** For $\nu>0$ and $\theta>0$ put
  $$\varphi_{\nu,\theta}(t)=\frac{2^{1-\nu}}{\Gamma(\nu)}\Bigl(\frac t\theta\Bigr)^{\nu}
  \mathcal K_\nu\Bigl(\frac t\theta\Bigr)\quad(t>0),\qquad \varphi_{\nu,\theta}(0)=1 .$$
  For every $d\ge1$, $\varphi_{\nu,\theta}(\|h\|)$ is an isotropic correlation function on
  $\mathbb R^d$ with spectral density
  $$f(\omega)=\frac{\Gamma(\nu+d/2)}{\Gamma(\nu)\,\pi^{d/2}}\,
  \theta^{d}\bigl(1+\theta^2\|\omega\|^2\bigr)^{-\nu-d/2},$$
  so $\varphi_{\nu,\theta}\in\Phi_\infty$. For $\nu=\tfrac12$ it is $e^{-t/\theta}$; for
  $\nu=m+\tfrac12$ with $m\in\mathbb N$ it is $e^{-t/\theta}$ times a polynomial of degree $m$
  in $t/\theta$, for instance $(1+t/\theta)e^{-t/\theta}$ for $\nu=\tfrac32$. With
  $\theta=1/(2\sqrt\nu)$, $\varphi_{\nu,\theta}(t)\to e^{-t^2}$ as $\nu\to\infty$. The Matérn
  correlation is completely monotone, as a function of $t$, exactly when $0<\nu\le\tfrac12$.

  *Assessment.* Partly covered. The case $\nu=\tfrac12$, $d=1$ is TauCeti's characteristic function
  of the Cauchy law. Neither library defines $\mathcal K_\nu$ at the pins. The general spectral
  density follows from Mathlib's Fourier transform of the Gaussian by Gamma-function subordination
  once $\mathcal K_\nu$ is defined by its integral representation.

  *Lean target.* Carriers at the pins: `MeasureTheory.charFun`, `Real.Gamma`,
  `MeasureTheory.Measure.withDensity`, `TauCeti.IsContinuousCompletelyMonotoneOnIoi`, and the
  classes of entries 8 and 10. New definitions: $\mathcal K_\nu(x)$ for $x>0$, as
  $\int_0^\infty e^{-x\cosh u}\cosh(\nu u)\,du$; the Matérn correlation, with the value $1$ at $t=0$
  and $\varphi(|t|)$ for negative arguments; and the Matérn spectral measure on
  `EuclideanSpace ℝ (Fin d)` as the measure with the density above. Conjuncts: (i) for
  $\nu,\theta>0$ and $d\ge1$, the spectral measure is a probability measure whose characteristic
  function is $\varphi_{\nu,\theta}(\|h\|)$; (ii) $\varphi_{\nu,\theta}\in\Phi_\infty$; (iii) the
  closed forms for $\nu=\tfrac12$, $\tfrac32$ and $m+\tfrac12$; (iv) convergence to $e^{-t^2}$ under
  $\theta=1/(2\sqrt\nu)$, pointwise in $t\ge0$; (v) complete monotonicity exactly for
  $0<\nu\le\tfrac12$. Pitfalls: the definition of $\mathcal K_\nu$ must not be evaluated at $x\le0$,
  where the integral diverges and a Bochner integral returns $0$; the spectral density must use
  `ENNReal.ofReal` of a positive real or an `ℝ≥0∞` density. Everything is statable at the pins; the
  TauCeti head defines the same integral as `Complex.positiveAxisBesselK`, and the
  SpecialFunctionsBessel roadmap owns `Real.besselK` with its agreement with that integral (its
  §5.1), so the Matérn definition should be stated through the TauCeti function when the pin moves.
  Entry 13 depends on this entry. MSSS: `MSSS.besselK`, `MSSS.maternCorrelation`,
  `MSSS.charFun_maternSpectralMeasure`, `MSSS.maternCorrelation_mem_isotropicClassInf`,
  `MSSS.maternCorrelation_half`, `MSSS.maternCorrelation_threeHalves`,
  `MSSS.maternCorrelation_halfInteger`, `MSSS.tendsto_maternCorrelation_gaussian`,
  `MSSS.maternCorrelation_completelyMonotone_iff` (`MSSS/RandomFields/Matern/Basic.lean`), all
  proved.

* **13. Smoothness of Matérn fields.** A second-order stationary process on $\mathbb R$
  with Matérn covariance of smoothness $\nu$ is $m$ times mean-square differentiable if and
  only if $\nu>m$. For fixed $\theta>0$, the small-lag orders of
  $1-\varphi_{\nu,\theta}(t)$ as $t\downarrow0$ are $t^{2\nu}$ for $0<\nu<1$,
  $t^2\log(1/t)$ for $\nu=1$, and $t^2$ for $\nu>1$, in each case up to positive
  multiplicative constants. The principal irregular term of $\varphi_{\nu,\theta}$ is a
  multiple of $t^{2\nu}$ when $\nu\notin\mathbb N$ and of $t^{2\nu}\log t$ when
  $\nu\in\mathbb N$.

  *Assessment.* Absent from both libraries. It needs entries 7 and 12 and the small-argument
  expansion of $\mathcal K_\nu$.

  *Lean target.* Carriers at the pins: `Asymptotics.IsBigO` and `Asymptotics.IsLittleO` at
  `nhdsWithin 0 (Set.Ioi 0)`, with the definitions of entries 7 and 12. A new definition is needed
  for the principal irregular term: a function $c\,t^{2\nu}$ or $c\,t^{2\nu}\log t$ with $c\ne0$
  such that $\varphi_{\nu,\theta}$ minus an even polynomial of degree less than $2\nu$ is that term
  plus $o(t^{2\nu})$, respectively $o(t^{2\nu}\log t)$. Conjuncts: (i) for a centred second-order
  stationary process with covariance $\sigma^2\varphi_{\nu,\theta}(|h|)$, $\sigma^2>0$, it is $m$
  times mean-square differentiable if and only if $m<\nu$, for every $m\in\mathbb N$; (ii) the upper
  and lower small-lag bounds of $1-\varphi_{\nu,\theta}(t)$ by $t^{\min(2\nu,2)}$ for $\nu\ne1$, and
  by $t^2\log(1/t)$ for $\nu=1$; (iii) the principal irregular term for $\nu\notin\mathbb N$ and for
  $\nu\in\mathbb N$. Pitfall: for $m=0$ the differentiability condition is vacuous and $0<\nu$
  holds, so (i) is consistent at $m=0$; a statement with $t^{\min(2\nu,2)}$ alone is false at
  $\nu=1$, where the order is $t^2\log(1/t)$. Conjuncts (ii) and (iii) are statable and provable at
  the pins from the gamma-mixture representation; (i) depends on entry 7. MSSS:
  `MSSS.one_sub_maternCorrelation_isBigO`, `MSSS.one_sub_maternCorrelation_not_isLittleO`,
  `MSSS.maternCorrelation_principalIrregularTerm`,
  `MSSS.maternCorrelation_principalIrregularTerm_natCast`, proved;
  `MSSS.isMeanSquareDifferentiable_matern_iff` (`MSSS/RandomFields/Matern.lean`), sorry. At $\nu=1$
  the proved upper bound is $t^2|\log t|$, but the proved lower bound only excludes $o(t^2)$, which
  is weaker than the order $t^2\log(1/t)$ of the statement.

### Variograms

[Synopsis](SYNOPSIS.md#variograms) ·
[Coverage](STRUCTURE.md#variograms).

* **15. Schoenberg–von Neumann characterisation of variograms.** Let
  $\gamma:\mathbb R^d\to\mathbb R$ be continuous and even, with $\gamma(0)=0$. The following are
  equivalent: (a) $\gamma$ is conditionally negative definite; (b) $e^{-t\gamma}$ is positive
  definite for every $t>0$; (c)
  $$\gamma(h)=Q(h)+\int_{\mathbb R^d}\frac{1-\cos\langle\omega,h\rangle}{\|\omega\|^2}\,
  \chi(d\omega),$$
  with $Q$ a positive semidefinite quadratic form and $\chi$ a symmetric nonnegative measure
  with $\chi(\{0\})=0$ and $\int(1+\|\omega\|^2)^{-1}\chi(d\omega)<\infty$. Every such
  $\gamma$ is the semivariogram of a Gaussian intrinsically stationary field. Examples:
  $\|h\|^\alpha$ with $0<\alpha\le2$ is a semivariogram on every $\mathbb R^d$.

  *Assessment.* Partly covered. For even $\gamma$, the equivalence of conditional negative
  definiteness with positive definiteness of $e^{-t\gamma}$ for all $t>0$ is a direct instance of
  TauCeti's Schoenberg theorem for kernels. TauCeti also proves conditional negative definiteness of
  $\|h\|^2$. Missing are the Lévy–Khintchine representation on $\mathbb R^d$, the realisation as a
  Gaussian intrinsically stationary field, and the power variograms $\|h\|^\alpha$ with
  $0<\alpha<2$.

  *Lean target.* Carriers at the pins: `Matrix.CondNegSemidef`,
  `condNegSemidef_iff_forall_posSemidef_cexp_neg_mul`, `TauCeti.IsPositiveDefiniteSub`,
  `ContinuousLinearMap.IsPositive` for the quadratic form, `Measure.map` with `Neg.neg` for
  symmetry, and `ProbabilityTheory.IsGaussianProcess` with `ProbabilityTheory.variance`. New
  definition: conditional negative definiteness of a function on an additive group, through
  `Matrix.CondNegSemidef` of the kernel $(x,y)\mapsto\gamma(x-y)$ or directly by finite sums with
  coefficients summing to $0$. Conjuncts: (i) for continuous even $\gamma$ on
  `EuclideanSpace ℝ (Fin d)` with $\gamma(0)=0$, the three conditions are equivalent; (ii) every
  such $\gamma$ is the semivariogram of a Gaussian field with centred increments; (iii)
  $\|h\|^\alpha$ is conditionally negative definite for $0<\alpha\le2$. Pitfalls: the integrability
  of $(1+\|\omega\|^2)^{-1}$ against $\chi$ must be a finite `∫⁻`, since $\chi$ may be infinite; the
  integrand $(1-\cos\langle\omega,h\rangle)/\|\omega\|^2$ takes the junk value $0$ at $\omega=0$,
  which is harmless only because $\chi(\{0\})=0$ is a hypothesis. The Bochner integral in the
  representation needs no separate integrability conjunct, since
  $(1-\cos\langle\omega,h\rangle)/\|\omega\|^2\le(\|h\|^2/2+2)(1+\|\omega\|^2)^{-1}$ and the `∫⁻`
  hypothesis make it integrable. Conjuncts (ii) and (iii) are statable and provable at the pins; (i)
  is statable, and its implication to (c) needs the Lévy–Khintchine representation on $\mathbb R^d$
  (absent; the InfinitelyDivisibleLaws roadmap covers only the line). (ii) holds without
  continuity. MSSS: `MSSS.IsCondNegDef`; `MSSS.isCondNegDef_tfae` (sorry);
  `MSSS.exists_isGaussianProcess_semivariogram` and `MSSS.isCondNegDef_norm_rpow`
  (`MSSS/RandomFields/Variogram.lean`), proved.

### Space–time covariances and spheres

[Synopsis](SYNOPSIS.md#spacetime-covariances-and-spheres) ·
[Coverage](STRUCTURE.md#spacetime-covariances-and-spheres).

* **16. Cressie–Huang criterion.** Let $C:\mathbb R^d\times\mathbb R\to\mathbb R$ be
  continuous, bounded, integrable, and symmetric, $C(-h,-u)=C(h,u)$. Then $C$ is positive
  definite on $\mathbb R^{d+1}$ if and only if, for almost every $\omega\in\mathbb R^d$, there
  is a continuous positive definite function $F_\omega:\mathbb R\to\mathbb C$ such that
  $F_\omega(u)=\int_{\mathbb R^d}e^{-i\langle h,\omega\rangle}C(h,u)\,dh$ for almost every $u$.
  A continuous, bounded, symmetric $C$ is positive definite if and only if
  $e^{-a\|h\|-b|u|}C(h,u)$ is positive definite for all $a,b>0$.

  *Assessment.* TauCeti has Bochner's theorem on $\mathbb R^{d+1}$ and Fourier inversion for finite
  measures. The criterion in terms of continuous temporal representatives of the partial spatial
  Fourier transform is absent.

  *Lean target.* Carriers at the pins: `TauCeti.IsPositiveDefiniteSub` on
  `EuclideanSpace ℝ (Fin d) × ℝ`, `MeasureTheory.Integrable`, `Filter.EventuallyEq` at
  `MeasureTheory.ae`, and the Bochner integral. No new definition. Conjuncts: (i) for continuous,
  bounded, integrable, symmetric $C$, positive definiteness is equivalent to: for almost every
  $\omega$ there is a continuous positive definite $F_\omega$ agreeing almost everywhere with the
  partial spatial Fourier transform; (ii) for continuous, bounded, symmetric $C$, positive
  definiteness is equivalent to positive definiteness of $e^{-a\|h\|-b|u|}C(h,u)$ for all $a,b>0$.
  Pitfall: the partial Fourier transform is a Bochner integral that is junk for those $u$ where
  $C(\cdot,u)$ is not integrable; integrability of $C$ makes this a null set, which is why the
  agreement is only almost everywhere. Everything is statable and provable at the pins; no
  dependency on another entry. MSSS: `MSSS.isPositiveDefiniteSub_iff_forall_exp_mul` and
  `MSSS.isPositiveDefiniteSub_iff_ae_spatialFourier` (`MSSS/RandomFields/SpaceTime.lean`), proved.

* **17. Gneiting's nonseparable space–time covariances.** Let
  $\varphi:[0,\infty)\to\mathbb R$ be completely monotone, let
  $\psi:[0,\infty)\to(0,\infty)$ be positive with completely monotone derivative, and let
  $\sigma^2>0$. Then
  $$C(h,u)=\frac{\sigma^2}{\psi(u^2)^{d/2}}\,\varphi\Bigl(\frac{\|h\|^2}{\psi(u^2)}\Bigr),
  \qquad(h,u)\in\mathbb R^d\times\mathbb R,$$
  is positive definite on $\mathbb R^{d+1}$. With $\varphi(t)=e^{-ct^\gamma}$ and
  $\psi(t)=(at^\alpha+1)^\beta$, where $a,c\ge0$, $\alpha,\gamma\in(0,1]$ and
  $\beta\in[0,1]$, this gives a family in which $\beta=0$ is separable and $\beta$ measures
  space–time interaction.

  *Assessment.* TauCeti has Bernstein's theorem, the Gaussian kernel, and products of positive
  definite functions on product groups, from which Gneiting's construction is assembled. The theorem
  is absent from the libraries, including the separable case.

  *Lean target.* Carriers at the pins: `TauCeti.IsContinuousCompletelyMonotoneOnIoi` for $\varphi$,
  `TauCeti.IsCompletelyMonotoneOnIoi` for $\psi'$, `DifferentiableOn` on $(0,\infty)$, and
  `TauCeti.IsPositiveDefiniteSub` on `EuclideanSpace ℝ (Fin d) × ℝ`. No new definition. Conjuncts:
  (i) for continuous completely monotone $\varphi$, $\psi$ continuous and positive on $[0,\infty)$
  and differentiable on $(0,\infty)$ with completely monotone derivative, and $\sigma^2>0$, the
  function is positive definite on $\mathbb R^{d+1}$; (ii) the same for the parametric family with
  $a,c\ge0$, $\alpha,\gamma\in(0,1]$, $\beta\in[0,1]$. Pitfalls: `deriv ψ` is junk at $0$, which the
  hypothesis on $(0,\infty)$ avoids; $\psi$ must be continuous at $0$, which complete monotonicity
  of $\psi'$ on $(0,\infty)$ does not give; $\psi(u^2)^{d/2}$ is a `Real.rpow` of a positive base.
  Everything is statable and provable at the pins; no dependency. MSSS:
  `MSSS.isPositiveDefiniteSub_gneiting`, `MSSS.isPositiveDefiniteSub_gneiting_family` and
  `MSSS.isPositiveDefiniteSub_integral` (`MSSS/RandomFields/SpaceTime.lean`), proved.

Let $S^d$ be the unit sphere of $\mathbb R^{d+1}$ with geodesic distance
$\theta(x,y)=\arccos\langle x,y\rangle\in[0,\pi]$. Let $\Psi_d$ be the class of continuous
$\psi:[0,\pi]\to\mathbb R$ with $\psi(0)=1$ such that $\psi(\theta(x,y))$ is positive
definite on $S^d$, $\Psi_d^+$ its strictly positive definite members, and
$\Psi_\infty=\bigcap_d\Psi_d$, $\Psi_\infty^+=\bigcap_d\Psi_d^+$. $C_n^\lambda$ denotes the
Gegenbauer polynomial, with $C_n^0(\cos\theta)=\cos n\theta$.

* **18. Schoenberg's theorem on spheres.** (a) $\psi\in\Psi_d$ if and only if
  $$\psi(\theta)=\sum_{n\ge0}b_{n,d}\,\frac{C_n^{(d-1)/2}(\cos\theta)}{C_n^{(d-1)/2}(1)}$$
  with uniquely determined $b_{n,d}\ge0$ and $\sum_nb_{n,d}=1$. For $d=1$ this is the cosine
  series $\sum_nb_{n,1}\cos n\theta$, and for $d=2$ the Legendre series
  $\sum_nb_{n,2}P_n(\cos\theta)$. (b) $\psi\in\Psi_\infty$ if and only if
  $\psi(\theta)=\sum_{n\ge0}b_n(\cos\theta)^n$ with $b_n\ge0$ and $\sum_nb_n=1$. (c) For
  $d\ge2$, $\psi\in\Psi_d^+$ if and only if moreover $b_{n,d}>0$ for infinitely many even and
  infinitely many odd $n$; the same criterion with the $b_n$ characterises $\Psi_\infty^+$.
  For $d=1$, $\psi\in\Psi_1^+$ if and only if, for any two integers $0\le j<n$, some
  $b_{j+kn,1}$ with $k\ge0$ is positive.
  (d) $\Psi_d$ and $\Psi_\infty$ are convex and closed under products and under pointwise
  limits with continuous limit.

  *Assessment.* Mathlib has positive semidefinite Gram matrices and the Schur product theorem, which
  make $\langle x,y\rangle^n$ positive definite on the sphere, and Chebyshev and shifted Legendre
  polynomials. TauCeti has harmonic polynomials with the Fischer decomposition and the dimension of
  each harmonic space. Gegenbauer polynomials, restriction of harmonic polynomials to the sphere,
  the addition theorem for spherical harmonics, and the characterisation are absent at the pins.

  *Lean target.* Carriers at the pins: `Matrix.PosSemidef` and `Matrix.PosDef` of a kernel indexed
  by the subtype `Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1`, `Real.arccos`, `HasSum`,
  `Polynomial.Chebyshev.T`, `Polynomial.shiftedLegendre`, `Matrix.PosSemidef.hadamard` and
  `MvPolynomial.harmonicSubmodule`. New definitions: the Gegenbauer polynomial $C_n^\lambda$ by its
  three-term recurrence; the normalised Gegenbauer function $C_n^\lambda(x)/C_n^\lambda(1)$,
  replaced by $T_n(x)$ at $\lambda=0$, where $C_n^0=0$ for $n\ge1$; the kernel
  $\psi(\arccos\langle x,y\rangle)$ on the sphere; $\Psi_d$, $\Psi_d^+$, $\Psi_\infty$ and
  $\Psi_\infty^+$. Conjuncts: (a) for $d\ge1$ the series characterisation, the uniqueness of the
  coefficients, and the identification with $\cos n\theta$ for $d=1$ and with $P_n$ for $d=2$; (b)
  the power-series characterisation of $\Psi_\infty$; (c) for $d\ge2$ the even/odd criterion, for
  $\Psi_\infty^+$ the same, and for $d=1$ the residue-class criterion; (d) convexity, products and
  pointwise limits. Pitfalls: `Real.arccos` clamps its argument, so values outside $[-1,1]$ do not
  arise on the sphere but do arise if the kernel is evaluated off it; $\psi$ is a function on
  $\mathbb R$, so the classes must constrain only $[0,\pi]$; `Matrix.PosDef` over an infinite index
  type quantifies over finitely supported vectors, which matches strict positive definiteness.
  Everything is statable at the pins; missing infrastructure is the addition theorem for spherical
  harmonics in all dimensions (owned on the open HigherSpheres roadmap, §4.1, with Funk–Hecke in
  §4.3), and the Gegenbauer polynomials (owned on main by LaguerreJacobi, §6.2). Entry 19 depends on
  this entry. MSSS: `MSSS.gegenbauer`, `MSSS.normalizedGegenbauer`, `MSSS.sphereClass`,
  `MSSS.strictSphereClass`; `MSSS.normalizedGegenbauer_half_eq_shiftedLegendre`,
  `MSSS.convex_sphereClass`, `MSSS.mul_mem_sphereClass`, `MSSS.mem_sphereClass_of_tendsto` and their
  $\Psi_\infty$ versions, proved; `MSSS.mem_sphereClass_iff`,
  `MSSS.eq_of_hasSum_normalizedGegenbauer`, `MSSS.mem_sphereClassInf_iff`,
  `MSSS.mem_strictSphereClass_iff`, `MSSS.mem_strictSphereClassInf_iff`
  (`MSSS/RandomFields/Sphere.lean`), sorry. The $d=1$ criterion of (c) is not stated.

* **19. From Euclidean space to the sphere.** (a) If $k\ge2$ and $\varphi\in\Phi_k$, then
  $\theta\mapsto\varphi(2\sin(\theta/2))$, the correlation in chordal distance, belongs to
  $\Psi_{k-1}$, and to $\Psi_{k-1}^+$ if $\varphi$ is not constant. (b) If $\varphi\in\Phi_3$
  and $\varphi(t)=0$ for $t\ge\pi$, then $\varphi|_{[0,\pi]}\in\Psi_3^+$, as a function of
  great-circle distance. (c) If $\varphi$ is completely monotone, non-constant, and
  $\varphi(0)=1$, then $\theta\mapsto\varphi(\theta/c)$ belongs to $\Psi_\infty^+$ for every
  $c>0$. (d) $e^{-(\theta/c)^\alpha}$ belongs to $\Psi_\infty^+$ for $\alpha\in(0,1]$ and to
  no $\Psi_d$ for $\alpha>1$; the Matérn correlation in great-circle distance belongs to
  $\Psi_\infty^+$ for $\nu\in(0,\tfrac12]$ and to no $\Psi_d$ for $\nu>\tfrac12$.

  *Assessment.* Absent from both libraries. The non-strict half of (a) is elementary: for
  $x,y\in S^{k-1}$, $\|x-y\|=2\sin(\theta(x,y)/2)$, so the kernel is the restriction of a positive
  definite function on $\mathbb R^k$. The strict half needs entry 8's strict positive definiteness;
  (b) needs Gneiting's Theorem 3 on restriction of compactly supported members of $\Phi_3$; (c) and
  (d) need entry 18's characterisation and the Schoenberg coefficients of completely monotone
  functions.

  *Lean target.* Carriers at the pins: those of entries 8 and 18, with `Real.sin`. No new definition
  beyond $\Phi_k$, $\Psi_d$, $\Psi_d^+$ and $\Psi_\infty^+$. Conjuncts: (a) for $k\ge2$ and
  $\varphi\in\Phi_k$, $\theta\mapsto\varphi(2\sin(\theta/2))$ lies in $\Psi_{k-1}$, and in
  $\Psi_{k-1}^+$ if $\varphi$ is not constant on $[0,\infty)$; (b) for $\varphi\in\Phi_3$ vanishing
  on $[\pi,\infty)$, $\varphi\in\Psi_3^+$; (c) for continuous completely monotone, non-constant
  $\varphi$ with $\varphi(0)=1$ and $c>0$, $\theta\mapsto\varphi(\theta/c)$ lies in $\Psi_\infty^+$;
  (d) the powered exponential for $\alpha\in(0,1]$ and the Matérn correlation for
  $\nu\in(0,\frac12]$ lie in $\Psi_\infty^+$, and for $\alpha>1$, $\nu>\frac12$ in no $\Psi_d$,
  $d\ge1$. Pitfalls: (b) needs $\varphi$ itself as a function of $\theta$ on $[0,\pi]$, so the class
  membership constrains only that interval; "not constant" must be stated on $[0,\infty)$, since
  $\varphi$ on negative arguments is arbitrary. The non-strict half of (a) is statable and provable
  at the pins; the rest is statable, with (a) depending on entry 8, (b) on entry 8, and (c)–(d) on
  entries 12 and 18. MSSS: no declaration.

### Gaussian fields: continuity, suprema, and excursion sets

[Synopsis](SYNOPSIS.md#gaussian-fields-continuity-suprema-and-excursion-sets) ·
[Coverage](STRUCTURE.md#gaussian-fields-continuity-suprema-and-excursion-sets).

For a centred Gaussian field $f$ on $T$, the **canonical pseudometric** is
$d(s,t)=\bigl(\mathbb E(f(s)-f(t))^2\bigr)^{1/2}$, and $N(\varepsilon)$ is the least number
of closed $d$-balls of radius $\varepsilon$ that cover $T$.

* **20. Dudley's entropy bound.** Let $f$ be a centred Gaussian field on a set $T$ that is
  compact for $d$, and $H(\varepsilon)=\log N(\varepsilon)$. There is a universal constant
  $K$ such that
  $$\mathbb E\sup_{t\in T}f(t)\le
  K\int_0^{\mathop{\mathrm{diam}}(T)/2}H(\varepsilon)^{1/2}d\varepsilon,
  \qquad \mathbb E\sup_{d(s,t)\le\delta}|f(t)-f(s)|\le
  K\int_0^\delta H(\varepsilon)^{1/2}d\varepsilon .$$
  If the entropy integral is finite, a separable version of $f$ has, almost surely, bounded
  sample paths that are uniformly continuous for $d$. For a centred, mean-square continuous
  stationary Gaussian process on a compact abelian group, sample continuity, sample
  boundedness, and finiteness of the entropy integral are equivalent. Consequently, a centred
  Gaussian field on a compact $T\subset\mathbb R^N$ with
  $\mathbb E|f(s)-f(t)|^2\le C|\log|s-t||^{-1-\alpha}$ for $|s-t|<\eta$, for some
  $C,\alpha,\eta>0$, has a version with continuous bounded sample paths.

  *Assessment.* Mathlib has covering numbers, polynomial covering bounds, the pair-reduction lemma
  used in chaining, and the definition of the Kolmogorov moment condition; TauCeti has the moment
  bounds for Gaussian increments and chaining edge estimates. Missing are a continuity theorem of
  Kolmogorov–Chentsov type, Dudley's entropy bound, and Fernique's converse for stationary fields.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IsGaussianProcess`, `Finset.sup'` for
  maxima over finite sets, `ENNReal` and `MeasureTheory.lintegral` for the entropy integral, and
  `Metric.coveringNumber`. New definitions: the canonical pseudometric
  $d(s,t)=(\mathbb E(f(s)-f(t))^2)^{1/2}$; the covering number for $d$ with values in `ℕ∞`; the
  square root of the metric entropy with values in `ℝ≥0∞`, equal to $\infty$ when the covering
  number is infinite; the canonical diameter in `ℝ≥0∞`; and the entropy integral
  $\int_{0<\varepsilon\le\delta}H(\varepsilon)^{1/2}d\varepsilon$ as a `∫⁻`. Conjuncts: (i) a
  universal $K>0$ with $\mathbb E\max_{t\in F}f(t)\le K\cdot$ entropy integral at half the diameter
  for every finite nonempty $F\subseteq T$, and the analogous modulus bound over finite sets of
  pairs at distance at most $\delta$; (ii) finite entropy integral gives a modification whose paths
  are bounded and uniformly continuous for $d$; (iii) for a centred, mean-square continuous Gaussian
  process on a compact abelian group, with covariance invariant under translation, the three
  conditions are equivalent; (iv) the logarithmic modulus criterion on a compact subset of
  `EuclideanSpace ℝ (Fin N)`. Pitfalls: the expected supremum over an uncountable $T$ is not
  measurable without separability, which (i) avoids by taking maxima over finite sets;
  $\log N(\varepsilon)$ with $N(\varepsilon)=\infty$ must not pass through `ENat.toNat`, which
  returns $0$; the bound must be in `ℝ≥0∞`, since the entropy integral may be infinite;
  $|\log r|^{-1-\alpha}$ is a `Real.rpow` of a nonnegative base and takes the value $0$ at $r=1$, so
  the hypothesis must restrict to $r<\eta$ with $\eta\le1$ or accept that $r=1$ forces $f(s)=f(t)$.
  Everything is statable at the pins; missing infrastructure is chaining itself. Entry 21 does not
  depend on this entry. MSSS: `MSSS.canonicalDist`, `MSSS.canonicalCoveringNumber`,
  `MSSS.sqrtEntropy`, `MSSS.canonicalDiam`, `MSSS.entropyIntegral`; `MSSS.dudley_entropy_bound`,
  `MSSS.exists_continuous_modification_of_entropyIntegral`, `MSSS.fernique_stationary_tfae`,
  `MSSS.exists_continuous_modification_of_logModulus` (`MSSS/RandomFields/GaussianSuprema.lean`),
  all sorry. `MSSS.fernique_stationary_tfae` is stated for a compact `CommGroup`;
  `MSSS.exists_continuous_modification_of_logModulus` does not bound $\eta$ by $1$.

* **21. Borell–TIS inequality.** Let $f$ be a centred Gaussian field, almost surely bounded
  on $T$, and separable. Put $\|f\|=\sup_{t\in T}f(t)$ and
  $\sigma_T^2=\sup_{t\in T}\mathbb E f(t)^2$. Then $\mathbb E\|f\|<\infty$ and for every $u>0$
  $$\mathbb P\{\|f\|-\mathbb E\|f\|>u\}\le e^{-u^2/(2\sigma_T^2)} .$$

  *Assessment.* Mathlib has Fernique's theorem, and TauCeti Gaussian concentration for continuously
  differentiable functions with a non-sharp constant. The Borell–TIS inequality, which needs the
  Gaussian isoperimetric inequality or the sharp concentration constant for Lipschitz functions, is
  absent.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IsGaussianProcess`, `iSup` over a
  countable index type, `BddAbove`, `MeasureTheory.Integrable`, and `ENNReal.ofReal`. No new
  definition. Conjuncts, for a centred Gaussian process on a countable nonempty $T$ with paths
  almost surely bounded above: (i) $\sup_tf(t)$ is integrable; (ii) the variances are bounded; (iii)
  for every $u>0$, the tail bound with $\sigma_T^2=\sup_t\mathbb Ef(t)^2$. Countability replaces
  separability. Pitfalls: the real `iSup` of a family that is not bounded above is $0$, so the
  supremum is meaningful only on the almost-sure event, and the variance supremum only after (ii);
  for $\sigma_T^2=0$ the exponent $-u^2/0$ is $0$ in Lean, so the bound is the trivial $1$, which is
  true; a statement with an uncountable $T$ and no separability would assert integrability of a
  non-measurable function. Everything is statable at the pins; missing is the Gaussian isoperimetric
  inequality or sharp Lipschitz concentration, owned on main by GaussianIsoperimetryAndClusters
  (§8.1, §8.4, with the finite median form of Borell–TIS in §8.5). No dependency on entry 20. MSSS:
  `MSSS.borell_tis` (`MSSS/RandomFields/GaussianSuprema.lean`), sorry.

* **22. Rice formula.** Let $f$ be a centred stationary Gaussian process on $\mathbb R$ with
  unit variance, continuously differentiable sample paths, and second spectral moment
  $\lambda_2=\mathop{\mathrm{Var}}f'(0)$. The expected number of upcrossings of the level $u$
  in $[0,T]$ is
  $$\mathbb E N_u^+(0,T)=\frac{T\lambda_2^{1/2}}{2\pi}e^{-u^2/2} .$$
  More generally (Kac–Rice), under non-degeneracy and regularity conditions, the expected
  number of zeros of $f-u$ in a compact $T\subset\mathbb R^N$, for a random field
  $f:\mathbb R^N\to\mathbb R^N$, is
  $\int_T\mathbb E\bigl\{|\det\nabla f(t)|\,\big|\,f(t)=u\bigr\}\,p_t(u)\,dt$, with $p_t$ the
  density of $f(t)$.

  *Assessment.* Absent from both libraries.

  *Lean target.* Carriers at the pins: `ProbabilityTheory.IsGaussianProcess`,
  `ProbabilityTheory.variance`, `ContDiff`, `Set.encard`, `MeasureTheory.lintegral`,
  `ProbabilityTheory.HasLaw`, `LinearMap.det` and `fderiv`. New definitions: the set of upcrossings
  of $u$ by $g$ in $[0,T]$, as points $t\in[0,T]$ with $g(t)=u$, $g<u$ on a left neighbourhood and
  $g>u$ on a right neighbourhood. Conjuncts: (i) for a centred, unit-variance, second-order
  stationary Gaussian process with $C^1$ paths, $\mathbb E N_u^+(0,T)$ as a `∫⁻` of `encard` equals
  `ENNReal.ofReal` of the right-hand side, with $\lambda_2=\mathop{\mathrm{Var}}f'(0)$; (ii) the
  Kac–Rice formula in joint-density form on a compact $T\subset\mathbb R^N$, with the regularity
  hypotheses that every solution of $f(t)=u$ lies in the interior with nonsingular derivative, and a
  jointly measurable density of $(f(t),\nabla f(t))$. Pitfalls: the count must be `encard` with a
  `∫⁻`, since it may be infinite; the "expected value conditional on $f(t)=u$" must be written
  through a joint density, not a conditional expectation, which is defined only almost everywhere;
  with $\lambda_2=0$ the paths are constant and both sides are $0$. Everything is statable at the
  pins; the proof needs the area formula, absent from Mathlib. Entry 23 for $N=1$ depends on (i).
  MSSS: `MSSS.upcrossings`; `MSSS.rice_formula` and `MSSS.lintegral_encard_levelSet`
  (`MSSS/RandomFields/Excursion.lean`), sorry.

* **23. Expected Euler characteristic of excursion sets.** Let $f$ be a centred,
  stationary, isotropic Gaussian field on $T=[0,L]^N$ with variance $\sigma^2$ and second
  spectral moment $\lambda_2$, satisfying the non-degeneracy and regularity conditions of
  Adler and Taylor. For the excursion set $A_u=\{t\in T:f(t)\ge u\}$,
  $$\mathbb E\,\chi(A_u)=\Psi\Bigl(\frac u\sigma\Bigr)+e^{-u^2/2\sigma^2}\sum_{k=1}^N
  \binom Nk\frac{L^k\lambda_2^{k/2}}{(2\pi)^{(k+1)/2}\sigma^k}H_{k-1}\Bigl(\frac u\sigma\Bigr),$$
  where $\chi$ is the Euler characteristic, $\Psi$ the standard Gaussian tail, and $H_n$ the
  probabilists' Hermite polynomials. For $N=1$ this is the probability that $f(0)\ge u$ plus
  the expected number of upcrossings of $u$ in $[0,L]$, which is item 22 applied to $f/\sigma$
  at the level $u/\sigma$. On a compact regular stratified manifold $M$, the **Gaussian
  kinematic formula** expresses the mean Lipschitz–Killing curvatures of
  $M\cap y^{-1}(D)$, for a vector $y$ of independent copies of a centred unit-variance field
  satisfying the regularity conditions of Adler and Taylor, with the curvatures of $M$
  computed in the metric that the field induces, as
  $\mathbb E\mathcal L_i(M\cap y^{-1}(D))=\sum_{j=0}^{N-i}\bigl[{i+j\atop j}\bigr]
  (2\pi)^{-j/2}\mathcal L_{i+j}(M)\mathcal M_j^\gamma(D)$, with flag coefficients and the
  Gaussian Minkowski functionals $\mathcal M_j^\gamma$ of $D$.

  *Assessment.* Mathlib has the probabilists' Hermite polynomials. TauCeti defines Euler
  characteristic for spaces of finite CW type. The expected Euler characteristic of excursion sets,
  the Lipschitz–Killing curvatures, and the Gaussian kinematic formula are absent. Item 114
  describes the Euclidean intrinsic volumes needed for the isotropic case.

  *Lean target.* Carriers at the pins: `TauCeti.eulerChar` and `TauCeti.FiniteCWType`,
  `Polynomial.hermite`, `ProbabilityTheory.gaussianReal` for the tail $\Psi$, and the carriers of
  entry 22. New definitions: the coordinate derivative and the joint vector of first and second
  derivatives at a point (for the non-degeneracy hypothesis), and the connected components of an
  excursion set for $N=1$. Conjuncts: (i) on $[0,L]^N$, for a centred isotropic Gaussian field with
  $C^2$ paths, variance $\sigma^2>0$, coordinate derivative variance $\lambda_2$, a non-degenerate
  joint law of first and second derivatives at each point, and a Hölder bound on the second
  derivatives in mean square, the expected Euler characteristic of $A_u$ equals the formula; (ii)
  for $N=1$, the expected number of components of $A_u$ equals $\Psi(u/\sigma)$ plus entry 22's
  formula for $f/\sigma$ at $u/\sigma$. The Gaussian kinematic formula on stratified manifolds is
  not statable at the pins. Pitfalls: the Euler characteristic is defined only for spaces of finite
  CW type, so the excursion set is assumed of finite CW type almost surely, as in the source, and the
  Euler characteristic is set to $0$ off that event; the Bochner integral is $0$ when the integrand
  is not integrable, so integrability is a conjunct, as in
  `MSSS.integral_eulerChar_excursion_cube`. Conjunct (i) is statable at
  the pins; (ii) is statable and depends on entry 22. MSSS: `MSSS.coordDeriv`,
  `MSSS.gradientHessian`, `MSSS.excursionComponents`; `MSSS.integral_eulerChar_excursion_cube` and
  `MSSS.lintegral_encard_excursionComponents` (`MSSS/RandomFields/Excursion.lean`), sorry.

## 2. Geostatistics: spatial prediction and covariance-parameter inference

Selected: 13 statements. [Synopsis part](SYNOPSIS.md#2-geostatistics-spatial-prediction-and-covariance-parameter-inference) · [Coverage part](STRUCTURE.md#2-geostatistics-spatial-prediction-and-covariance-parameter-inference).

Throughout, $Z=\{Z(x):x\in D\}$, $D\subseteq\mathbb R^d$, is a second-order field with mean
$m(x)$ and covariance $K(x,y)$. The observations are
$\mathbf Z=(Z(x_1),\dots,Z(x_n))^\top$ and the predictand is $Z(x_0)$. Write
$\mathbf K=(K(x_i,x_j))_{i,j\le n}$, $\mathbf k=(K(x_i,x_0))_{i\le n}$, $k_0=K(x_0,x_0)$,
and $\mathbf m=(m(x_i))_{i\le n}$.

### Linear prediction

[Synopsis](SYNOPSIS.md#linear-prediction) · [Coverage](STRUCTURE.md#linear-prediction).

* **24. Simple kriging (best linear prediction).** Let $m$ and $K$ be known. For every
  affine predictor $\lambda_0+\lambda^\top\mathbf Z$,
  $$\mathbb E\bigl(Z(x_0)-\lambda_0-\lambda^\top\mathbf Z\bigr)^2
  =\bigl(m(x_0)-\lambda_0-\lambda^\top\mathbf m\bigr)^2+k_0-2\lambda^\top\mathbf k
  +\lambda^\top\mathbf K\lambda .$$
  The vector $\mathbf k$ lies in the column space of $\mathbf K$, and the minimisers are
  exactly the pairs with $\mathbf K\lambda=\mathbf k$ and
  $\lambda_0=m(x_0)-\lambda^\top\mathbf m$. A best linear predictor therefore always exists,
  and any two agree almost surely. If $\mathbf K$ is nonsingular, the predictor is
  $$\hat Z(x_0)=m(x_0)+\mathbf k^\top\mathbf K^{-1}(\mathbf Z-\mathbf m),$$
  and its mean squared error, the **simple kriging variance**, is
  $k_0-\mathbf k^\top\mathbf K^{-1}\mathbf k\le k_0$.

  *Assessment.* Partly covered. The column-space claim follows from TauCeti's range
  inclusion for positive semidefinite block matrices
  (`Matrix.PosSemidef.range_toEuclideanLin_toBlocks₂₁_le`), equivalently
  $S_{12}S_{22}^+S_{22}=S_{12}$, applied to the joint covariance of $(Z(x_0),\mathbf Z)$.
  Missing are the expansion of the mean squared error, the characterisation of its
  minimisers, and the predictor and kriging variance. This is finite matrix algebra with the
  libraries' covariance and pseudoinverse results, selected because the rest of Part 2 rests
  on it.

  *Lean target.* Carriers: a probability measure `P`, a field `Z : T → Ω → ℝ` with
  `MemLp (Z t) 2 P` for every `t`, sites `x : ι → T` with `[Fintype ι]`, covariances
  `ProbabilityTheory.covariance` and matrices `Matrix ι ι ℝ` with `Matrix.mulVec`. New
  definitions: the mean squared error of an affine predictor (from the measure, the
  observations, the predictand, an intercept and a weight vector, to a real number); the
  predicate that an affine predictor minimises it; the observation covariance matrix and the
  cross-covariance vector. Conjuncts: the expansion; the existence of `v` with
  $\mathbf Kv=\mathbf k$; minimisers if and only if $\mathbf K\lambda=\mathbf k$ and the
  intercept identity; existence; almost-sure uniqueness; and, under `IsUnit K.det`, the
  predictor and the variance identity with its bound. Pitfalls: the matrix inverse
  `Matrix.inv` is junk zero for singular $\mathbf K$, so the closed forms need nonsingularity
  as a hypothesis; the Bochner integral of a non-integrable square is zero, so the
  second-moment hypothesis must be stated. Statable and provable at the pins with no further
  infrastructure. MSSS: `MSSS.affineMSE_eq`, `MSSS.exists_obsCov_mulVec_eq_crossCov`,
  `MSSS.isBestAffinePredictor_iff`, `MSSS.exists_isBestAffinePredictor`,
  `MSSS.IsBestAffinePredictor.ae_eq`, `MSSS.isBestAffinePredictor_simpleKriging`, and
  `MSSS.affineMSE_simpleKriging` in `MSSS/Geostatistics/Kriging.lean`, all proved.

Suppose now that $m(x)=f(x)^\top\beta$ with known $f:D\to\mathbb R^p$ and unknown
$\beta\in\mathbb R^p$, and that $K$ is known. Let $\mathbf F=(f(x_1),\dots,f(x_n))^\top$
and $f_0=f(x_0)$. A predictor $\lambda_0+\lambda^\top\mathbf Z$ is **unbiased** when its
error has mean zero for every $\beta$; a **best linear unbiased predictor** minimises the
mean squared error among unbiased linear predictors.

* **27. Universal kriging.** (a) $\lambda_0+\lambda^\top\mathbf Z$ is unbiased if and only
  if $\lambda_0=0$ and $\mathbf F^\top\lambda=f_0$; an unbiased linear predictor exists if
  and only if $f_0$ lies in the column space of $\mathbf F^\top$. (b) $\lambda^\top\mathbf Z$
  is a best linear unbiased predictor if and only if there is $\mu\in\mathbb R^p$ with
  $$\begin{pmatrix}\mathbf K&\mathbf F\\ \mathbf F^\top&0\end{pmatrix}
  \begin{pmatrix}\lambda\\ \mu\end{pmatrix}=\begin{pmatrix}\mathbf k\\ f_0\end{pmatrix};$$
  this system is solvable whenever an unbiased predictor exists, and the best linear
  unbiased predictor is then unique almost surely. (c) The bordered matrix is nonsingular
  if and only if $\mathbf F$ has full column rank and
  $\ker\mathbf K\cap\ker\mathbf F^\top=\{0\}$; in particular, if $\mathbf K$ is positive
  definite and $\mathbf F$ has full column rank. (d) If $\mathbf K$ is nonsingular and
  $\mathbf F$ has full column rank, the predictor is
  $$\hat Z(x_0)=f_0^\top\hat\beta+\mathbf k^\top\mathbf K^{-1}(\mathbf Z-\mathbf F\hat\beta),\qquad
  \hat\beta=(\mathbf F^\top\mathbf K^{-1}\mathbf F)^{-1}\mathbf F^\top\mathbf K^{-1}\mathbf Z,$$
  with mean squared error
  $k_0-\mathbf k^\top\mathbf K^{-1}\mathbf k+g^\top(\mathbf F^\top\mathbf K^{-1}\mathbf F)^{-1}g$,
  $g=f_0-\mathbf F^\top\mathbf K^{-1}\mathbf k$. The generalised least-squares estimator
  $\hat\beta$ is the best linear unbiased estimator of $\beta$, with covariance
  $(\mathbf F^\top\mathbf K^{-1}\mathbf F)^{-1}$, and it is the maximum-likelihood estimator
  of $\beta$ when $\mathbf Z$ is Gaussian. (e) The error of the best linear unbiased
  predictor is a contrast, that is, a linear combination with mean zero for every $\beta$,
  and it is uncorrelated with every contrast of the observations; the predictor and its
  mean squared error depend on $K$ only through the covariances of contrasts.

  *Assessment.* TauCeti has Moore–Penrose inverses, Schur complements, and the Gaussian
  density. Unbiased prediction, the bordered kriging system with its nonsingularity
  criterion, the generalised least squares estimator, and the kriging variance are absent.
  The best-linear-unbiased-estimator part of (d) is the Aitken theorem that the
  GaussianLinearModels roadmap owns (§2.4).

  *Lean target.* Carriers: as in item 24, with a centred residual field
  `ε : T → Ω → ℝ`, a regressor map `f : T → Fin p → ℝ`, and the bordered matrix as
  `Matrix.fromBlocks K F Fᵀ 0`. New definitions: the design matrix (from `f` and the sites to
  `Matrix ι (Fin p) ℝ`); the mean squared error at parameter `β` of an affine predictor of
  $Z_\beta(x_0)$; the predicates "unbiased for every `β`" and "best linear unbiased
  predictor"; the generalised least-squares matrix (from `K` and `F` to
  `Matrix (Fin p) ι ℝ`). Conjuncts: (a) two equivalences; (b) the solvability of the system
  under the existence of an unbiased predictor, the characterisation of best linear unbiased
  predictors by the system, and almost-sure uniqueness for each `β`; (c) the determinant
  criterion for positive semidefinite `K` and the positive definite corollary; (d) under
  `IsUnit K.det` and injectivity of `F.mulVec`, the predictor identity, the variance formula,
  unbiasedness and covariance of `β̂`, its minimal variance among linear unbiased estimators
  `C 𝐙` with `C * F = 1` in every direction `a`, and its minimisation of the generalised
  residual sum of squares; (e) the contrast and uncorrelatedness claims, and invariance under
  residual fields with equal contrast variances. Pitfalls: `Matrix.inv` of a singular
  `Fᵀ K⁻¹ F` is zero, so full column rank is a hypothesis; "best" must quantify over all
  `β` simultaneously; the maximum-likelihood claim should be stated as minimisation of the
  quadratic form, since no likelihood maximiser carrier exists. Statable and provable at the
  pins. MSSS: `MSSS.isUnbiasedPredictor_iff`, `MSSS.exists_isUnbiasedPredictor_iff`,
  `MSSS.isBLUP_iff`, `MSSS.exists_krigingSystem`, `MSSS.IsBLUP.ae_eq`,
  `MSSS.det_borderedMatrix_ne_zero_iff`, `MSSS.det_borderedMatrix_ne_zero_of_posDef`,
  `MSSS.isBLUP_universalKriging`, `MSSS.gls_isBLUE`, `MSSS.gls_isMinOn_gaussianLikelihood`,
  `MSSS.IsBLUP.error_contrast`, and `MSSS.isBLUP_iff_of_contrastVariance_eq` in
  `MSSS/Geostatistics/Kriging.lean`, all proved.

### Misspecified covariances and equivalence of Gaussian measures

[Synopsis](SYNOPSIS.md#misspecified-covariances-and-equivalence-of-gaussian-measures) · [Coverage](STRUCTURE.md#misspecified-covariances-and-equivalence-of-gaussian-measures).

Two probability measures are **equivalent** when they are mutually absolutely continuous
and **orthogonal** when they are mutually singular. For a mean function $m$ and covariance
$K$ on $D$, let $G_D(m,K)$ be the law of the Gaussian field on $D$ with these moments.

* **34. Effect of a misspecified covariance in finite samples.** Let $(0,K_0)$ be the true
  and $(0,K_1)$ a presumed second-order structure, both with mean zero. Suppose
  that on the linear span of the observations and the predictand
  $0<a\le\mathbb E_1h^2/\mathbb E_0h^2\le b<\infty$ for every $h$ with $\mathbb E_0h^2>0$.
  Let $e_j$ be the error of the best linear predictor computed under $K_j$, and assume
  $\mathbb E_0e_0^2>0$. Then
  $$1\le\frac{\mathbb E_0e_1^2}{\mathbb E_0e_0^2}=1+\frac{\mathbb E_0(e_1-e_0)^2}{\mathbb E_0e_0^2}
  \le1+\frac{(b-a)^2}{4ab},$$
  and $a\le\mathbb E_1e_1^2/\mathbb E_0e_1^2\le b$.

  *Assessment.* Mathlib has Hilbert-space projection, which gives the orthogonality of
  $e_0$ to $e_1-e_0$ and hence the equality and the lower bound. The upper bound rests on the
  Kantorovich inequality, which is absent from both libraries, as are the relative bounds.

  *Lean target.* Carriers: two probability measures `P₀`, `P₁` on one sample space, finitely
  many observations `Y : ι → Ω → ℝ` and a predictand `ψ`, all in `MemLp · 2` and centred
  under both measures. New definitions: the error of a chosen best affine predictor (item
  24's predicate with a choice of minimiser). Hypotheses: `0 < a`, the two-sided comparison
  of second moments under `P₀` and `P₁` for every linear combination
  $c_0\psi+\sum_ic_iY_i$ with positive `P₀`-second moment, and $\mathbb E_0e_0^2>0$.
  Conjuncts: the lower bound, the Pythagorean identity, the Kantorovich upper bound, and the
  two bounds on the presumed-to-true ratio. Pitfalls: real division by zero is zero, so the
  positivity of $\mathbb E_0e_0^2$ (and of $\mathbb E_0e_1^2$, which follows) must be in the
  hypotheses; a chosen minimiser defined by `Classical.epsilon` is junk unless existence is
  proved, which item 24 supplies. Statable and provable at the pins once the Kantorovich
  inequality for a positive definite matrix with spectrum in $[a,b]$ is proved locally.
  MSSS: `MSSS.misspecified_prediction_bounds` in `MSSS/Geostatistics/Equivalence.lean`,
  proved.

* **35. Feldman–Hájek dichotomy.** Two Gaussian measures $G_D(m_0,K_0)$ and
  $G_D(m_1,K_1)$, with continuous means and continuous covariances on a closed set $D$, are
  either equivalent or orthogonal. They are equivalent if and only if
  $G_D(m_0,K_0)\equiv G_D(m_1,K_0)$ and $G_D(m_0,K_0)\equiv G_D(m_0,K_1)$. Suppose the
  variances $\mathop{\mathrm{Var}}_0h$ and $\mathop{\mathrm{Var}}_1h$ are comparable on the
  linear span, let $(\psi_j)$ be an orthonormal basis of the Gaussian space for $K_0$, and put
  $b_{jk}=K_1(\psi_j,\psi_k)-\delta_{jk}$ and $\mu_j=\mathbb E_1\psi_j-\mathbb E_0\psi_j$.
  Then the measures are equivalent if and only if $\sum_{j,k}b_{jk}^2<\infty$ and
  $\sum_j\mu_j^2<\infty$. Two Gaussian laws on $\mathbb R^n$ are equivalent if and only if
  they are supported by the same affine subspace.

  *Assessment.* TauCeti proves that a finite-dimensional Gaussian law has a positive
  Lebesgue density when its covariance is positive definite, is singular to Lebesgue measure
  otherwise, and is supported on its affine range, from which the finite-dimensional case
  follows. The dichotomy on infinite-dimensional spaces and the Hilbert–Schmidt criterion are
  absent. Mathlib's reproducing kernel Hilbert space of $K_0$ is the Cameron–Martin space,
  but no Gaussian measure is attached to it, and Kakutani's theorem on infinite products is
  absent.

  *Lean target.* Carriers: measures on `D → ℝ` with the product σ-algebra, the coordinate
  process, `ProbabilityTheory.IsGaussianProcess`, `MeasureTheory.Measure.AbsolutelyContinuous`
  and `MeasureTheory.Measure.MutuallySingular`; in finite dimension,
  `ProbabilityTheory.multivariateGaussian` and `LinearMap.range` of
  `Matrix.toEuclideanLin`. New definitions: the predicate that a measure on `D → ℝ` makes the
  coordinates a Gaussian field with mean `m` and covariance `K`, and a chosen such law
  $G_D(m,K)$ (from `m` and `K` to a probability measure). Hypotheses: `K₀` and `K₁`
  positive semidefinite as kernels (`(Matrix.of K).PosSemidef`); for the criterion, a
  countable orthonormal family in $L^2(G_D(m_0,K_0))$ of centred finite linear combinations
  whose span is dense in the Gaussian space, and comparability constants `0 < a ≤ b`.
  Conjuncts: the dichotomy; the reduction to a mean shift and a covariance change; the
  criterion as two `Summable` statements; the finite-dimensional range criterion. On the
  product σ-algebra the continuity of $m$, $K$ and the closedness of $D$ are not needed,
  since every event depends on countably many coordinates. Pitfalls: a chosen law with a
  Dirac fallback when $K$ is not positive semidefinite makes the statements false without
  the positive-semidefiniteness hypotheses; `Summable` of a non-summable real family is
  merely false, not junk, so the criterion is safe. Statable at the pins. Missing
  infrastructure: Kakutani's dichotomy for infinite products of equivalent measures, the
  likelihood ratio of Gaussian measures on separable spaces, and the Cameron–Martin theorem
  for general Gaussian measures (TauCeti has it for Brownian motion only, through Girsanov).
  MSSS: `MSSS.multivariateGaussian_equiv_iff`, proved;
  `MSSS.gaussianFieldLaw_equiv_or_mutuallySingular`, `MSSS.gaussianFieldLaw_equiv_iff`, and
  `MSSS.gaussianFieldLaw_equiv_iff_summable` in `MSSS/Geostatistics/Equivalence.lean`, sorry.

* **36. Spectral criteria for equivalence.** Let $Z$ be centred and stationary on
  $\mathbb R^d$ under two spectral densities $f_0,f_1$. Suppose $f_0(\omega)\|\omega\|^\alpha$
  is bounded away from $0$ and $\infty$ for large $\|\omega\|$ and some $\alpha>0$
  (necessarily $\alpha>d$, since $f_0$ is integrable), and that
  for some $C<\infty$
  $$\int_{\|\omega\|>C}\Bigl(\frac{f_1(\omega)-f_0(\omega)}{f_0(\omega)}\Bigr)^2d\omega<\infty .$$
  Then $G_D(0,K_0)\equiv G_D(0,K_1)$ for every bounded $D$. On an interval, the exponential
  covariances $\sigma_i^2e^{-\alpha_i|t|}$ give equivalent laws if
  $\sigma_0^2\alpha_0=\sigma_1^2\alpha_1$ and orthogonal laws otherwise.

  *Assessment.* Absent. It needs item 35 and the spectral theory of item 5.

  *Lean target.* Carriers: `EuclideanSpace ℝ (Fin d)`, nonnegative integrable spectral
  densities, `Bornology.IsBounded D`, and $G_D$ of item 35 on the subtype `D`. New
  definitions: the stationary covariance of a spectral density,
  $K(h)=\int\cos\langle h,\omega\rangle f(\omega)\,d\omega$ (from a density to a function on
  $\mathbb R^d$). Hypotheses: `0 ≤ f₀`, `0 ≤ f₁`, `Integrable f₀`, `Integrable f₁`,
  `0 < α`, two-sided bounds on $f_0(\omega)\|\omega\|^\alpha$ outside a ball, and
  `IntegrableOn` of the squared relative difference outside a ball. Conjuncts: equivalence on
  every bounded $D$; for the exponential example on $[0,L]$ with all parameters positive,
  equivalence when $\sigma_0^2\alpha_0=\sigma_1^2\alpha_1$ and orthogonality otherwise.
  Pitfalls: $(f_1-f_0)/f_0$ is junk zero where $f_0=0$, which is harmless only because the
  lower bound on $f_0$ holds outside a ball; the Bochner integral defining $K$ is junk zero
  for a non-integrable density, so integrability is a hypothesis; the spectral convention
  ($\cos\langle h,\omega\rangle$ against $e^{-2\pi i\langle h,\omega\rangle}$) changes the
  constant in the exponential example's spectral density but not the criterion. Statable at
  the pins; missing infrastructure is item 35, the identification of the Gaussian space with
  a space of Fourier transforms on bounded sets (Stein, §4.2), and the extension of
  covariance operators from a bounded set. The orthogonality half of the exponential example
  follows from item 39. MSSS: `MSSS.gaussianFieldLaw_equiv_of_spectralDensity` and
  `MSSS.gaussianFieldLaw_exponential` in `MSSS/Geostatistics/Equivalence.lean`, sorry.

* **37. Stein's asymptotic optimality of pseudo-best linear prediction.** Let
  $h_1,h_2,\dots$ be observations whose span is dense in the Gaussian space of the field,
  let $e_j(\psi,n)$ be the error of the best linear predictor of $\psi$ from
  $h_1,\dots,h_n$ computed under $(m_j,K_j)$, and suppose
  $G(m_0,K_0)\equiv G(m_1,K_1)$. Then, uniformly over predictands $\psi$ with
  $\mathbb E_0e_0(\psi,n)^2>0$,
  $$\frac{\mathbb E_0e_1^2}{\mathbb E_0e_0^2}\to1,\qquad
  \frac{\mathbb E_1e_1^2}{\mathbb E_0e_1^2}\to1\qquad(n\to\infty).$$
  The predictor computed under the wrong covariance is asymptotically efficient, and its
  presumed mean squared error is asymptotically correct. For universal kriging, let
  $e_j(x_0,n)$ be the error of the best linear unbiased predictor of $Z(x_0)$ from
  $Z(x_1),\dots,Z(x_n)$ computed under $K_j$. If $G_D(0,K_0)\equiv G_D(0,K_1)$ and the design
  is such that $0<\mathbb E_0e_0(x_0,n)^2\to0$ (for instance, the field is mean-square
  continuous and $x_0$ is a limit point of the design), then the same two ratios tend to $1$.

  *Assessment.* Absent. It needs the Hilbert–Schmidt criterion of item 35 and best linear
  prediction in $L^2$, for which Mathlib's projection theorems are present.

  *Lean target.* Carriers: two Gaussian probability measures on `ℕ → ℝ` for which the
  coordinates are a Gaussian process (`ProbabilityTheory.IsGaussianProcess`), equivalent in
  the sense of mutual absolute continuity; predictands in the closure in $L^2$ of the affine
  span of the coordinates; for universal kriging, $G_T(0,K_j)$ of item 35 and item 27's
  best linear unbiased predictor. New definitions: item 24's chosen prediction error from
  the first $n$ coordinates, and item 27's chosen best linear unbiased weights. Hypotheses:
  equivalence; for universal kriging, eventual existence of an unbiased predictor, eventual
  positivity of $\mathbb E_0e_0(x_0,n)^2$, and its convergence to zero. Conjuncts: the two
  uniform limits, written as "for every $\varepsilon>0$, eventually in $n$, for every
  predictand with positive error", and the two limits for universal kriging. Pitfalls: the
  ratios are junk where a denominator vanishes, so the uniformity must range only over
  predictands with positive error; under $\mu_1$ a predictand from the $\mu_0$ Gaussian space
  must be shown square integrable before the chosen predictor under $\mu_1$ is meaningful,
  which equivalence supplies but which needs a lemma; the mean-square continuity example is
  a separate claim and not a conjunct. Statable at the pins; missing infrastructure is item
  35's criterion. MSSS: `MSSS.stein_asymptotic_efficiency` and
  `MSSS.stein_asymptotic_efficiency_universalKriging` in
  `MSSS/Geostatistics/Equivalence.lean`, sorry.

* **38. Matching high-frequency behaviour on a lattice.** Let $Z$ be centred and stationary
  on $\mathbb R^d$, observed on $\delta\mathbb Z^d$, with spectral densities $f_0,f_1$ such
  that $f_0/f_1$ is bounded away from $0$ and $\infty$ on $\mathbb R^d$,
  $f_1/f_0\to c\in(0,\infty)$ as $\|\omega\|\to\infty$, $f_1$ is bounded away from $0$ on
  bounded sets, and $f_1(\omega)\to0$ as $\|\omega\|\to\infty$. Then, as $\delta\downarrow0$,
  uniformly over predictands with positive error variance,
  $\mathbb E_1e_1^2/\mathbb E_0e_1^2\to c$ and $\mathbb E_0(e_0-e_1)^2/\mathbb E_0e_0^2\to0$.
  Here equivalence of the measures is not required.

  *Assessment.* Absent. Stein, §3.8, Theorem 10, p. 102, proves it from the spectral
  description of prediction from an infinite lattice and the bound of Theorem 9 there, p. 100,
  which neither library has. Selected because it is the principal asymptotic result on
  misspecified prediction that does not rest on equivalence of Gaussian measures, and it
  needs only second-order theory.

  *Lean target.* Carriers: the Hilbert space $L^2(f\,d\omega)$ on `EuclideanSpace ℝ (Fin d)`
  with complex values (`MeasureTheory.Lp ℂ 2 (volume.withDensity f)`), its closed subspace
  spanned by $e^{i\langle x,\cdot\rangle}$, $x\in\delta\mathbb Z^d$, and orthogonal projection
  (`Submodule.starProjection`). New definitions: the Hilbert space of a spectral
  density (the closed span of $e^{i\langle x,\cdot\rangle}$, $x\in\mathbb R^d$, in
  $L^2(f)$); the error of the best linear predictor of a predictand $H$ from the lattice
  $\delta\mathbb Z^d$ under $f_j$ (from a density, a mesh and a predictand to an element of
  the space); and the error of the pseudo-predictor computed under $f_1$ and measured under
  $f_0$. Hypotheses: $f_0,f_1$ nonnegative and integrable; $f_0\asymp f_1$ on all of
  $\mathbb R^d$, so that the two Hilbert spaces coincide as sets; $f_1/f_0\to c>0$ at
  infinity; $f_1$ bounded below on bounded sets; $f_1\to0$ at infinity. Conjuncts: the two
  limits, uniform over predictands with positive error under $f_0$.
  Pitfalls: the ratios are junk where $\mathbb E_0e_0^2=0$, which happens for predictands in
  the lattice span, so they are excluded; without $f_0\asymp f_1$ the pseudo-predictor need
  not lie in the space of $f_0$ and the statement is false. Statable at the pins; missing
  infrastructure is the spectral theory of prediction from an infinite lattice, Stein, §3.8,
  pp. 97–100, with the bound of Theorem 9, (49)–(51), p. 100. MSSS: no declaration.

* **39. Microergodicity and non-consistency.** For a family $\{P_\theta\}$ of laws of a
  field on a bounded set, a function $h(\theta)$ is **microergodic** when
  $h(\theta)\ne h(\theta')$ implies $P_\theta\perp P_{\theta'}$. If
  $P_{\theta_0}\equiv P_{\theta_1}$ and $h(\theta_0)\ne h(\theta_1)$, then no sequence of
  estimators based on observations of the field on that set is weakly consistent for
  $h(\theta)$ at both $\theta_0$ and $\theta_1$. Let $Z$ be a centred stationary Gaussian
  process on $[0,1]$ whose autocovariance satisfies $K(t)=C-D|t|+o(|t|)$ near $0$ with
  $D>0$ and has a bounded second derivative on $(0,1]$. Then the halved quadratic
  variations $U_n=\tfrac12\sum_{j\le n}(Z(j/n)-Z((j-1)/n))^2$ satisfy
  $\mathbb EU_n=D+O(n^{-1})$ and $\mathop{\mathrm{Var}}U_n=2D^2n^{-1}+O(n^{-2})$, so $U_n\to D$
  in $L^2$. Hence two such autocovariances with different values of $D$ give orthogonal
  laws on $[0,1]$.

  *Assessment.* TauCeti proves that the quadratic variation of Brownian motion converges in
  $L^2$, an analogue without stationarity, and the Gaussian fourth-moment formula on which the
  variance of $U_n$ rests. Microergodicity, the non-consistency argument, and the stationary
  quadratic-variation theorem are absent.

  *Lean target.* Carriers: a family `P : Θ → Measure Ω` of probability measures,
  estimators `ℕ → Ω → α` into a metric space, `MeasureTheory.TendstoInMeasure`; for the
  quadratic variation, a process `Z : ℝ → Ω → ℝ` with `ProbabilityTheory.IsGaussianProcess`,
  stationarity and centring, and the little-o `Asymptotics.IsLittleO` at `𝓝 0`. New
  definitions: the predicate that `h : Θ → α` is microergodic; the halved quadratic variation
  on the uniform mesh of $[0,1]$. Hypotheses: for non-consistency, equivalence and
  $h(\theta_0)\ne h(\theta_1)$; for the quadratic variation, `0 < D`, the expansion
  $K(t)-(C-D|t|)=o(t)$, `ContDiffOn ℝ 2 K (Ioc 0 1)` and a bound on the second derivative
  there. Conjuncts: non-consistency; $\mathbb EU_n-D=O(n^{-1})$;
  $\mathop{\mathrm{Var}}U_n-2D^2/n=O(n^{-2})$; $L^2$ convergence; orthogonality of the
  laws on $[0,1]$ for $D_0\ne D_1$, as measures on `Icc 0 1 → ℝ`. Pitfalls: the second
  derivative on $(0,1]$ must be taken with `iteratedDerivWithin`, since $K$ is not
  differentiable at $0$; the bound $O(n^{-1})$ for the mean and the sharp variance asymptotic
  are separate conjuncts from $L^2$ convergence and are not stated in MSSS; orthogonality is
  a statement about the laws on path space, so the field must be realised as coordinates.
  Statable and provable at the pins. MSSS: `MSSS.IsMicroergodic`,
  `MSSS.not_consistent_of_equiv`, `MSSS.tendsto_quadraticVariation` (the $L^2$ limit only),
  and `MSSS.gaussianFieldLaw_mutuallySingular_of_slope_ne` in
  `MSSS/Geostatistics/Equivalence.lean`, all proved; the rates for the mean and the variance
  have no declaration.

* **40. Zhang's theorem on the Matérn family.** For $\sigma^2,\alpha,\nu>0$ let
  $K(x)=\sigma^2\,\frac{2^{1-\nu}}{\Gamma(\nu)}(\alpha x)^\nu\mathcal K_\nu(\alpha x)$, $K(0)=\sigma^2$. Let
  $d\in\{1,2,3\}$ and let $P_i$ make $Z$ a centred stationary Gaussian field on
  $\mathbb R^d$ with isotropic Matérn covariance of parameters $(\sigma_i^2,\alpha_i,\nu)$,
  with the same $\nu$. For every bounded infinite $T\subset\mathbb R^d$, $P_1$ and $P_2$ are
  equivalent on $\{Z(s):s\in T\}$ if $\sigma_1^2\alpha_1^{2\nu}=\sigma_2^2\alpha_2^{2\nu}$ and
  orthogonal otherwise. Consequently, under infill sampling in a bounded infinite set,
  neither $\sigma^2$ nor $\alpha$ has a weakly consistent estimator, while predictive
  conditional laws under two equivalent parameters merge: for observations
  $s_1,s_2,\dots\in T$,
  $\sup_A|P_1(A\mid Z(s_1),\dots,Z(s_n))-P_2(A\mid Z(s_1),\dots,Z(s_n))|\to0$ almost surely
  under $P_1$ (equivalently, under $P_2$), the supremum over events $A$ of the future
  observations $Z(s_{n+1}),Z(s_{n+2}),\dots$.

  *Assessment.* Absent. It needs $\mathcal K_\nu$ (item 12), item 36, and the
  Blackwell–Dubins merging theorem. TauCeti's Bessel kernel gives the Matérn covariance
  through its spectral density $(1+\|\xi\|^2)^{-\delta/2}$, but not its closed form.

  *Lean target.* Carriers: $G_T$ of item 35 on the subtype `T` of
  `EuclideanSpace ℝ (Fin d)`, `MeasureTheory.TendstoInMeasure`, `ProbabilityTheory.condDistrib`
  and `MeasureTheory.tvDist`; $\mathcal K_\nu$ either as the cosh integral or as
  the Bessel roadmap's `Real.besselK` (SpecialFunctionsBessel, §1.3). New definitions: the
  Matérn correlation (from $\nu$, a range and a distance to a real number, equal to $1$ at
  distance $0$); the Matérn law on a set (from $\nu$, $\sigma^2$, $\alpha$ and $T$ to a
  probability measure on `T → ℝ`). Hypotheses: `1 ≤ d ≤ 3`, `0 < ν`, all variances and inverse
  ranges positive, `Bornology.IsBounded T`, `T.Infinite`. Conjuncts: equivalence under equal
  microergodic parameter; orthogonality otherwise; non-consistency of $\sigma^2$ and of
  $\alpha$; almost-sure merging in total variation under $P_1$ of the conditional laws of the
  future observations on `ℕ → ℝ`. Pitfalls: $\mathcal K_\nu(0)$ is infinite and its
  integral form is junk there, so the value at $0$ must be set by cases; for $T$ finite the
  laws are equivalent whatever the parameters, so infiniteness is essential; the
  parametrisation by $\alpha$ against the range $1/\alpha$ moves the exponent between
  $\alpha^{2\nu}$ and $\phi^{-2\nu}$; "equivalently, under $P_2$" follows from equivalence
  and is not a separate hypothesis. Statable at the pins with a local $\mathcal K_\nu$;
  missing infrastructure is item 36, the closed-form spectral density of the Matérn
  covariance, and Blackwell–Dubins merging. MSSS: `MSSS.maternLaw_equiv_iff`,
  `MSSS.not_consistent_maternVariance`, `MSSS.not_consistent_maternInverseRange`, and
  `MSSS.tendsto_tvDist_condDistrib_maternLaw` in `MSSS/Geostatistics/MaternInference.lean`,
  sorry.

* **41. Consistency of the microergodic parameter.** In item 40 let $\nu$ be known, let
  $D_n$ be an increasing sequence of finite sets whose union is bounded and infinite, and
  fix $\alpha_1>0$. Let $\hat\sigma_n^2$ maximise the Gaussian likelihood of
  $Z|_{D_n}$ over $\sigma^2$ with $\alpha=\alpha_1$. Then
  $\hat\sigma_n^2\alpha_1^{2\nu}\to\sigma_0^2\alpha_0^{2\nu}$ almost surely under the true
  parameters $(\sigma_0^2,\alpha_0)$.

  *Assessment.* Absent. It needs item 40 and a strong law for quadratic forms in Gaussian
  vectors.

  *Lean target.* Carriers: the Matérn law of item 40 on all of $\mathbb R^d$, finite sets
  `D : ℕ → Finset (EuclideanSpace ℝ (Fin d))`, and the Gaussian log-likelihood
  $-\frac12\log\det S-\frac12r^\top S^{-1}r$ with `Matrix.det` and `Matrix.inv`. New
  definitions: the Gaussian log-likelihood up to a constant (from a covariance matrix and a
  residual to a real number). Hypotheses: `1 ≤ d ≤ 3`, `0 < ν`, positive true parameters and
  `0 < α₁`; `Monotone D`; bounded, infinite union; a family of estimators that maximise the
  likelihood over $\sigma^2>0$ whenever the data on $D_n$ are not all zero. Conjunct:
  almost-sure convergence of $\hat\sigma_n^2\alpha_1^{2\nu}$. Pitfalls: for zero data the
  likelihood in $\sigma^2$ is unbounded, so the maximising property is required only off
  that null set; `Real.log` of a nonpositive determinant is junk, which is harmless because
  the Matérn matrix at distinct sites is positive definite, a fact that must be proved;
  the closed form $\hat\sigma_n^2=\mathbf Z^\top R_n^{-1}\mathbf Z/|D_n|$ is a separate
  lemma. Statable at the pins; missing infrastructure is item 40 and the martingale argument
  of Zhang, p. 253, or a strong law for $\mathbf Z^\top R_n^{-1}\mathbf Z/n$. MSSS:
  `MSSS.tendsto_maternMLE_microergodic` in `MSSS/Geostatistics/MaternInference.lean`, sorry.

### Likelihood inference under increasing-domain asymptotics

[Synopsis](SYNOPSIS.md#likelihood-inference-under-increasing-domain-asymptotics) · [Coverage](STRUCTURE.md#likelihood-inference-under-increasing-domain-asymptotics).

Let $\mathbf Y\sim N(\mathbf X\beta,V(\theta))$, with $\mathbf X$ an $n\times q$ matrix of
rank $q$, $\beta$ in an open subset of $\mathbb R^q$, $\theta$ in an open subset of
$\mathbb R^p$, and $V(\theta)$ positive definite and twice continuously differentiable in
$\theta$. The log-likelihood is
$-\tfrac12\log\det V-\tfrac12(\mathbf Y-\mathbf X\beta)^\top V^{-1}(\mathbf Y-\mathbf X\beta)$
up to a constant, and the Fisher information is block diagonal with blocks
$B_\beta=\mathbf X^\top V^{-1}\mathbf X$ and
$(B_\theta)_{ij}=\tfrac12\mathop{\mathrm{tr}}(V^{-1}V_iV^{-1}V_j)$,
$V_i=\partial V/\partial\theta_i$.

* **42. Mardia–Marshall theorem.** Consider observation sets $T_n$ of size $n$. Suppose
  that, as $n\to\infty$: (i) the largest eigenvalues of $V$, $V_i$, and
  $V_{ij}=\partial^2V/\partial\theta_i\partial\theta_j$ in absolute value have finite
  limits; (ii) $\|V_i\|^{-2}=O(n^{-1/2-\delta})$ for some $\delta>0$ and each $i$, with
  $\|\cdot\|$ the Frobenius norm; (iii) the limits
  $a_{ij}=\lim t_{ij}/(t_{ii}t_{jj})^{1/2}$, $t_{ij}=\mathop{\mathrm{tr}}(V^{-1}V_iV^{-1}V_j)$,
  exist and form a nonsingular matrix; (iv) $(\mathbf X^\top\mathbf X)^{-1}\to0$. Then there
  is a sequence of roots $\hat\phi_n=(\hat\beta_n,\hat\theta_n)$ of the likelihood equations
  that is weakly consistent and satisfies
  $B_n^{1/2}(\hat\phi_n-\phi)\Rightarrow N(0,I_{p+q})$, $B_n=\mathop{\mathrm{diag}}(B_\beta,B_\theta)$.
  For a stationary Gaussian field observed on a growing regular lattice in $\mathbb Z^d$,
  with all side lengths tending to infinity, the conclusion holds under (iii) and (iv) when
  the covariance and its first and second $\theta$-derivatives are absolutely summable over
  $\mathbb Z^d$.

  *Assessment.* Absent. Neither library has maximum likelihood estimation or asymptotic
  normality for dependent observations; TauCeti has the multivariate Gaussian density. The
  iid theory of MathematicalStatisticsAsymptotic (§5.3) does not apply, since the
  observations are dependent and not identically distributed.

  *Lean target.* Carriers: index types `κ n` with `Fintype`, regression matrices
  `Matrix (κ n) (Fin q) ℝ`, covariance families `(Fin p → ℝ) → Matrix (κ n) (κ n) ℝ`,
  the operator norm on matrices (scope `Matrix.Norms.L2Operator`), `fderiv`, `ContDiffOn`,
  `Asymptotics.IsBigO`, and convergence in distribution either as
  `MeasureTheory.TendstoInDistribution` or by testing against
  `BoundedContinuousFunction`. New definitions: entrywise partial derivatives of a matrix
  family; the Frobenius norm; the conclusion predicate (measurable estimators that are roots
  of the likelihood equations with probability tending to one, weakly consistent, and with
  $B_n^{1/2}(\hat\phi_n-\phi)$ converging in law to the standard Gaussian on
  $\mathbb R^{q+p}$); the lattice box. Hypotheses: an open parameter set containing
  $\theta$; sizes tending to infinity; injective `X n`; $V_n$ positive definite and $C^2$ on
  it; (i)–(iv) as stated, with (i) for the operator norm. Conjuncts: the general theorem
  and the lattice corollary. Pitfalls: the Mardia–Marshall conclusion is informal in the
  source, so the target fixes "roots with probability tending to one"; `Real.sqrt` of a
  negative product in (iii) is junk zero, harmless because the traces are positive;
  `CFC.sqrt` of the information matrix needs it positive semidefinite, which holds. Statable
  at the pins. Missing infrastructure: a Sweeting-type theorem on roots of likelihood
  equations for non-identically distributed observations, central limit theorems for
  Gaussian quadratic forms with growing dimension, and a uniform law of large numbers for
  the observed information. MSSS: `MSSS.HasConsistentNormalRoots`, `MSSS.mardia_marshall`,
  and `MSSS.mardia_marshall_lattice` in `MSSS/Geostatistics/Likelihood.lean`, the two
  theorems sorry.

* **44. Restricted maximum likelihood.** Let $\mathbf Y\sim N(\mathbf X\beta,\Sigma(\theta))$
  with $\mathbf X$ of rank $q<n$ and $\Sigma(\theta)$ positive definite. Let $A$ be any
  $n\times(n-q)$ matrix of rank $n-q$ with $A^\top\mathbf X=0$. The law of $A^\top\mathbf Y$
  does not depend on $\beta$, and its log-density equals, up to an additive constant that
  depends on $A$ and $\mathbf X$ but not on $\theta$,
  $$-\tfrac12\Bigl\{\log\det\Sigma+\log\det(\mathbf X^\top\Sigma^{-1}\mathbf X)
  +(\mathbf Y-\mathbf X\tilde\beta)^\top\Sigma^{-1}(\mathbf Y-\mathbf X\tilde\beta)\Bigr\},$$
  with $\tilde\beta$ the generalised least-squares estimator for $\Sigma(\theta)$. The
  restricted maximum-likelihood estimator therefore does not depend on the choice of $A$.
  For independent errors with constant mean, $\Sigma=\sigma^2I$ and $\mathbf X=\mathbf 1$ with
  $n\ge2$, the restricted likelihood has, when the $Y_i$ are not all equal, the unique
  maximiser $\sigma^2=(n-1)^{-1}\sum_i(Y_i-\bar Y)^2$; when they are all equal it is
  unbounded as $\sigma^2\downarrow0$.

  *Assessment.* TauCeti has the Gaussian density and affine images of Gaussian laws, and
  Mathlib has block determinants. The restricted likelihood, its independence of the mean
  parameters, and its invariance under the choice of contrasts are absent.

  *Lean target.* Carriers: `Matrix ι (Fin q) ℝ` with injective `mulVec`, a contrast matrix
  `Matrix ι κ ℝ` with `Fintype.card κ + q = Fintype.card ι`, the Gaussian law on `ι → ℝ` as
  the image of `ProbabilityTheory.multivariateGaussian`, and
  `TauCeti.Probability.multivariateGaussianPDFReal`. New definitions: the restricted
  log-likelihood (from a covariance matrix, a design and data to a real number), using item
  27's generalised least-squares matrix. Hypotheses: `S.PosDef`; `Aᵀ * X = 0`; `A` injective;
  for the iid case `2 ≤ n` and $\sigma^2>0$. Conjuncts: the law of $A^\top\mathbf Y$ is
  $N(0,A^\top SA)$ for every $\beta$; there is a constant $c(A,\mathbf X)$ with log-density
  equal to $c$ plus the restricted log-likelihood for every positive definite $S$ and every
  data vector; two admissible contrast matrices give log-densities that differ by a constant;
  in the iid case, strict maximality of $S/(n-1)$ for data not all equal, and divergence to
  $+\infty$ as $\sigma^2\downarrow0$ for constant data. Pitfalls: `Real.log` of a
  nonpositive determinant is junk, so positive definiteness of $S$ is a hypothesis; with
  $q=n$ the contrast space is trivial and the density is that of a point mass, so $q<n$
  is needed; the GLS matrix uses `Matrix.inv` and is junk without full column rank. Statable
  and provable at the pins. MSSS: `MSSS.remlLogLik`, `MSSS.map_mulVec_gaussianLaw_eq`,
  `MSSS.log_pdf_eq_remlLogLik`, `MSSS.log_pdf_sub_log_pdf_eq_const`, and
  `MSSS.remlLogLik_iid_lt` in `MSSS/Geostatistics/Likelihood.lean`, all proved; the
  unboundedness for constant data has no declaration.

### Variogram estimation and generalised linear models

[Synopsis](SYNOPSIS.md#variogram-estimation-and-generalised-linear-models) · [Coverage](STRUCTURE.md#variogram-estimation-and-generalised-linear-models).

* **45. Matheron's variogram estimator.** For a lag $h$ let $N(h)$ be the set of pairs of
  data sites $(s_i,s_j)$ with $s_i-s_j=h$. For $N(h)\ne\emptyset$ put
  $2\hat\gamma(h)=|N(h)|^{-1}\sum_{N(h)}(Z(s_i)-Z(s_j))^2$. (a) If $Z$ is intrinsically
  stationary with constant mean and semivariogram $\gamma$, then
  $\mathbb E\,2\hat\gamma(h)=2\gamma(h)$. If $Z=\mu+\varepsilon$ with deterministic trend
  $\mu$ and intrinsically stationary residual $\varepsilon$ of constant mean and
  semivariogram $\gamma$, then
  $\mathbb E(Z(s_i)-Z(s_j))^2=2\gamma(s_i-s_j)+(\mu(s_i)-\mu(s_j))^2$. (b)
  $\hat\gamma(h)=\mathbf Z^\top A(h)\mathbf Z$ with $A(h)$ symmetric positive semidefinite and
  $A(h)\mathbf 1=0$; if $\mathbf Z\sim N(\mu\mathbf 1,\Sigma)$, then $\hat\gamma(h)$ has the law
  of $\sum_i\lambda_i\chi^2_{1,i}$ with independent $\chi^2_1$ variables and $\lambda_i$ the
  nonzero eigenvalues of $A(h)\Sigma$, so $\mathbb E\hat\gamma(h)=\mathop{\mathrm{tr}}(A(h)\Sigma)$
  and $\mathop{\mathrm{Var}}\hat\gamma(h)=2\mathop{\mathrm{tr}}((A(h)\Sigma)^2)$. (c) The
  estimated function need not be conditionally negative definite.

  *Assessment.* TauCeti proves
  $\mathbb E\langle B(x-m),x-m\rangle=\mathop{\mathrm{tr}}(B\Sigma)$, the moment generating
  function of a Gaussian quadratic form, and that of a weighted sum of squared independent
  standard Gaussians. The mean and weighted $\chi^2_1$ law at observed lags follow by a
  further argument using the estimator's quadratic form. Neither library states the
  estimator, its variance formula, or the other claims about it.

  *Lean target.* Carriers: sites `s : ι → E` in an additive group with decidable equality,
  data `ι → ℝ`, `Matrix.PosSemidef`, the Gaussian law on `ι → ℝ` of item 44,
  `ProbabilityTheory.stdGaussian`, and `ProbabilityTheory.variance`. New definitions: the
  set of site pairs at lag $h$ (a `Finset (ι × ι)`); the estimator $\hat\gamma(h)$ (from sites,
  a lag and data to a real number); its matrix $A(h)$. Hypotheses: for (a), square
  integrability, constant mean, and the increment variance $2\gamma$; $N(h)\ne\emptyset$;
  for (b), $\Sigma$ positive semidefinite. Conjuncts: (a) the two expectation identities;
  (b) positive semidefiniteness, $A(h)\mathbf 1=0$ and the quadratic-form identity; the law
  of $\hat\gamma(h)$ as the image of the standard Gaussian under
  $u\mapsto\sum_i\lambda_iu_i^2$ with $\lambda_i$ the eigenvalues of
  $\Sigma^{1/2}A(h)\Sigma^{1/2}$; mean and variance; (c) an explicit configuration with
  $\sum_kc_k=0$, all lags observed, and a positive quadratic sum. Pitfalls: for
  $N(h)=\emptyset$ the estimator is $0/0$, junk zero, so (a) needs nonemptiness; the
  eigenvalues of $A(h)\Sigma$ are not those of a symmetric matrix, so the law is stated
  through $\Sigma^{1/2}A(h)\Sigma^{1/2}$, whose nonzero eigenvalues agree; for (c) every
  difference $x_k-x_l$ must be an observed lag, or the counterexample is vacuous. Statable
  and provable at the pins; TauCeti's later weighted-$\chi^2$ law
  (`TauCeti.Probability.map_norm_sq_multivariateGaussian_eq_map_sum_eigenvalues_mul_sq` at
  its latest head)
  would shorten (b). MSSS: `MSSS.integral_matheronEstimator`, `MSSS.integral_sq_sub_of_mean`,
  `MSSS.matheronMatrix_properties`, `MSSS.map_matheronEstimator_gaussianLaw`,
  `MSSS.moments_matheronEstimator_gaussianLaw`, and
  `MSSS.exists_matheronEstimator_not_condNegDef` in
  `MSSS/Geostatistics/VariogramEstimation.lean`, all proved.

## 3. Lattice models, Markov random fields, and Gibbs measures

Selected: 16 statements. [Synopsis part](SYNOPSIS.md#3-lattice-models-markov-random-fields-and-gibbs-measures) · [Coverage part](STRUCTURE.md#3-lattice-models-markov-random-fields-and-gibbs-measures).

For a finite site set $S=\{1,\dots,n\}$ and state spaces $E_i$, put
$\Omega=\prod_iE_i$. A **density** is a probability mass function or a density with
respect to a product reference measure. For $x\in\Omega$, $x_{-i}=(x_j)_{j\ne i}$, and
$\pi_i(\cdot\mid x_{-i})$ is the **full conditional** at site $i$. A density $\pi$
satisfies the **positivity condition** when its support is the product of its marginal
supports. Given an undirected graph on $S$, write $j\sim i$ for neighbours,
$\partial i$ for the neighbours of $i$, and call $C\subseteq S$ a **clique** when its
distinct elements are pairwise neighbours; singletons are cliques. $X$ is a **Markov random
field** for the graph when, for each $i$, the full conditional law depends on $x_{-i}$ only
through $x_{\partial i}$ for almost every $x_{-i}$ under its marginal law. For countable
state spaces this means every conditioning configuration of positive marginal mass.

The *Lean target* paragraphs name declarations at the project pins and, where the statement
is already formalised, the declaration in `MSSS/Lattice/` that states it. Unless stated
otherwise, the finite-site carriers are a site type `S` with `[Fintype S] [DecidableEq S]`,
state spaces `E : S → Type*` with `[∀ i, Countable (E i)]`, and a mass function
`π : (∀ i, E i) → ℝ` with `MSSS.IsDensity π` (nonnegative with `HasSum π 1`). The full
conditional `MSSS.fullConditional π i x y` is the ratio
`π (update x i y) / ∑' z, π (update x i z)`, whose junk value `0` off the support of the
conditioning configuration is harmless only because each statement assumes positivity or
restricts to positive-mass configurations.

### Conditional specification and the Hammersley–Clifford theorem

[Synopsis](SYNOPSIS.md#conditional-specification-and-the-hammersleyclifford-theorem) · [Coverage](STRUCTURE.md#conditional-specification-and-the-hammersleyclifford-theorem).

* **47. Brook's factorisation lemma.** Let $\pi$ satisfy the positivity condition and let
  $x,y$ lie in its support. Then
  $$\frac{\pi(x)}{\pi(y)}=\prod_{i=1}^n
  \frac{\pi_i(x_i\mid x_1,\dots,x_{i-1},y_{i+1},\dots,y_n)}
  {\pi_i(y_i\mid x_1,\dots,x_{i-1},y_{i+1},\dots,y_n)} .$$
  Consequently two densities satisfying the positivity condition, with the same support and
  the same full conditionals on it, coincide.

  *Assessment.* Absent from both libraries. It is a finite telescoping identity under the
  positivity condition.

  *Lean target.* Positivity is `MSSS.SatisfiesPositivity π` (a configuration whose
  coordinates all have positive marginal mass `MSSS.marginal π i (x i)` has positive mass).
  The identity is one theorem over `S = Fin n`, with `0 < π x` and `0 < π y` and the
  intermediate configurations `j ↦ if j < i then x j else y j`; the uniqueness is a second
  theorem for two densities with the positivity condition whose full conditionals agree at
  every `(i, x, y)`, which under the junk convention includes agreement of the supports.
  Both are stated and proved, as `MSSS.brook_factorization` and
  `MSSS.eq_of_fullConditional_eq` (`MSSS/Lattice/MarkovField.lean`). The density form with
  respect to a product reference measure `Measure.pi ρ` needs a full conditional density,
  which no library defines; it is statable at the pins as the Radon–Nikodym derivative of
  Mathlib's `ProbabilityTheory.condDistrib` of the coordinate `i` given the restriction to
  `{i}ᶜ`, with respect to `ρ i`, and is a prerequisite for the converse half of item 52.

* **49. Hammersley–Clifford theorem.** Let $S$ be finite with a graph, and let $\pi>0$ on
  $\Omega$, with $E_i$ countable or $\pi$ a density on $\mathbb R^S$. Then $X$ is a Markov
  random field for the graph if and only if
  $$\pi(x)=\prod_{C\text{ clique}}\varphi_C(x_C)$$
  for positive functions $\varphi_C$; equivalently, the canonical potential of item 48
  vanishes on every non-clique. More generally, a product of nonnegative clique functions
  with positive finite total mass defines a Markov random field after normalisation, with
  the conditional-law identities understood almost surely. For a positive Markov random
  field, $\pi(x_A\mid x_{S\setminus A})=\pi(x_A\mid x_{\partial A})$ for every nonempty
  $A$. Without strict positivity a Markov random field need not factorise over cliques: the
  binary field on the $2\times2$ grid (the four-cycle) whose law is uniform on the eight
  configurations that are monotone along the cycle is Markov and has no clique factorisation.

  *Assessment.* Mathlib has cliques of graphs, Möbius inversion on locally finite orders,
  and conditional independence. TauCeti has weak union, decomposition, and the alternating
  interval sum. The positive equivalence and the almost-sure Markov implication for
  normalised nonnegative clique products are absent.

  *Lean target.* The graph is a Mathlib `SimpleGraph S` with cliques
  `SimpleGraph.IsClique`; the Markov property is `MSSS.IsMarkovRandomField G π` (full
  conditionals at `i` agree on any two conditioning configurations of positive mass that agree
  on the neighbours of `i`), the canonical potential is `MSSS.canonicalPotential π a A x`, and
  the conditional mass of a block is `MSSS.setConditional π A x z`. A clique factorisation
  is a family `φ : Finset S → (∀ i, E i) → ℝ` with `φ C` depending only on the coordinates in
  `C` and `φ C = 1` on non-cliques. The conjuncts are five theorems, all stated and proved in
  `MSSS/Lattice/MarkovField.lean`: the equivalence for `π > 0`
  (`MSSS.isMarkovRandomField_iff_factorization`), its canonical-potential form for any
  reference configuration `a` (`MSSS.isMarkovRandomField_iff_canonicalPotential`), the
  implication for nonnegative factors with the normalised product a density when it is
  summable with positive sum (`MSSS.isMarkovRandomField_of_factorization`), the block form
  (`MSSS.setConditional_eq_of_eqOn_boundary`), and the counterexample on
  `SimpleGraph.cycleGraph 4` (`MSSS.exists_markovRandomField_not_factorization`). Two parts
  remain: the case of a density on $\mathbb R^S$, which needs the conditional densities of
  item 47; and a bridge from `MSSS.IsMarkovRandomField` to Mathlib's
  `ProbabilityTheory.CondIndepFun` for the law
  `∑' x, ENNReal.ofReal (π x) • Measure.dirac x`, so that the local Markov property is stated
  in the measure-theoretic language used by items 55–56.

* **50. Besag's auto-models.** Let $0\in E_i$ for every $i$, and let $\pi>0$ be a Markov
  random field whose canonical potential relative to the configuration $0$ vanishes on
  cliques of more than two sites. Suppose each full conditional
  is a one-parameter exponential family,
  $\log\pi_i(x_i\mid x_{-i})=A_i(x_{-i})B_i(x_i)+C_i(x_i)+D_i(x_{-i})$ with
  $B_i(0)=C_i(0)=0$ and $B_i\not\equiv0$ for every $i$. Then there are constants $\alpha_i$
  and $\beta_{ij}=\beta_{ji}$, with
  $\beta_{ij}=0$ unless $i\sim j$, such that
  $$A_i(x_{-i})=\alpha_i+\sum_{j\ne i}\beta_{ij}B_j(x_j),\qquad
  \pi(x)\propto\exp\Bigl\{\sum_i\bigl(\alpha_iB_i(x_i)+C_i(x_i)\bigr)
  +\sum_{i<j}\beta_{ij}B_i(x_i)B_j(x_j)\Bigr\}.$$
  Conversely, such conditionals with symmetric $\beta$ come from this joint law whenever it
  is normalisable. The **auto-logistic** model, $E_i=\{0,1\}$ and
  $\pi_i(1\mid x_{-i})=e^{\eta_i}/(1+e^{\eta_i})$ with
  $\eta_i=\alpha_i+\sum_{j\ne i}\beta_{ij}x_j$ and $\beta_{ij}=\beta_{ji}$, is always
  normalisable.

  *Assessment.* Absent from both libraries. It needs item 49 and exponential families on a
  single site.

  *Lean target.* Each `E i` carries `[Zero (E i)]` for the reference value; the hypotheses
  are `π > 0`, `MSSS.IsMarkovRandomField G π`, vanishing of
  `MSSS.canonicalPotential π 0 A` for `2 < A.card`, functions `A D : S → (∀ i, E i) → ℝ`
  unchanged by `Function.update x i`, `B C : ∀ i, E i → ℝ` with `B i 0 = C i 0 = 0` and
  `∃ e, B i e ≠ 0`, and the exponential-family identity for
  `Real.log (MSSS.fullConditional π i x (x i))`, whose argument is positive, so the junk value
  of `Real.log 0` does not arise. The exponent is `MSSS.autoModel α β B C x`, the pair sum
  written as half the sum over ordered pairs. The direct statement, the converse for summable
  `exp ∘ MSSS.autoModel α β B C` with symmetric `β`, and the auto-logistic case on
  `S → Bool` are `MSSS.exists_autoModel`, `MSSS.fullConditional_autoModelDensity`, and
  `MSSS.fullConditional_autoLogistic`, all proved (`MSSS/Lattice/MarkovField.lean`). The
  auto-models with continuous states, of which item 52 is the Gaussian case, need the density
  form of item 47.

### Conditional and simultaneous autoregressions

[Synopsis](SYNOPSIS.md#conditional-and-simultaneous-autoregressions) · [Coverage](STRUCTURE.md#conditional-and-simultaneous-autoregressions).

* **52. Gaussian conditional specification.** Let the full conditionals be
  $X_i\mid x_{-i}\sim N\bigl(\mu_i+\sum_{j\ne i}c_{ij}(x_j-\mu_j),\ \kappa_i\bigr)$ with
  $\kappa_i>0$. Put $C=(c_{ij})$ with zero diagonal and $M=\mathop{\mathrm{diag}}(\kappa_i)$.
  These are the full conditionals of a joint law if and only if $M^{-1}(I-C)$ is symmetric
  and positive definite, that is, $c_{ij}\kappa_j=c_{ji}\kappa_i$ and $I-C$ has positive
  eigenvalues; the joint law is then $N\bigl(\mu,(I-C)^{-1}M\bigr)$, a **conditional
  autoregression**. If $C=\phi N$ with $N$ the adjacency matrix and $\phi\ne0$, symmetry
  forces $\kappa_i$ to be constant on each connected component of the graph, and then
  $|\phi|\,|\partial i|<1$ for every $i$ suffices.

  *Assessment.* Mathlib has multivariate Gaussian laws, positive definite matrices, Schur
  complements, and Gershgorin's theorem; TauCeti has Gaussian densities and conditioning. The
  characterisation of Gaussian conditional specifications that admit a joint law is absent.

  *Lean target.* Carriers: `MSSS.gaussianLaw μ S`, the image of Mathlib's
  `ProbabilityTheory.multivariateGaussian` on `ι → ℝ` with `[Fintype ι] [DecidableEq ι]`;
  `Matrix.PosDef`; `Matrix.diagonal κ` with `∀ i, 0 < κ i`; a matrix `C` with `C i i = 0`.
  New definition: `MSSS.HasGaussianFullConditionals P μ C κ : Prop` for a probability measure
  `P` on `ι → ℝ`, saying that for every `i` the conditional law
  `ProbabilityTheory.condDistrib (fun x ↦ x i) (fun x (j : {j // j ≠ i}) ↦ x j) P` is
  `P`-almost everywhere Mathlib's `gaussianReal m v` with mean
  `m = μ i + ∑ j ∈ univ.erase i, C i j * (x j - μ j)` and variance `v = κ i` as an `ℝ≥0`.
  Conjuncts: (a) if `(Matrix.diagonal κ)⁻¹ * (1 - C)` is positive definite then
  `MSSS.gaussianLaw μ ((1 - C)⁻¹ * Matrix.diagonal κ)` has these full conditionals; (b) if a
  probability measure with a positive continuous Lebesgue density has these full conditionals
  then `C i j * κ j = C j i * κ i` and `(Matrix.diagonal κ)⁻¹ * (1 - C)` is positive definite,
  and the measure is that Gaussian law; (c) for the symmetric case, positive definiteness is
  equivalent to positivity of the eigenvalues of `1 - C`; (d) the sufficient condition, with
  `C = φ • G.adjMatrix ℝ`, `φ ≠ 0`, `κ` constant on each `G.ConnectedComponent`, and
  `|φ| * G.degree i < 1`, by Mathlib's Gershgorin theorem `eigenvalue_mem_ball`. Part (a)
  follows from the conditional moments of item 55 (`MSSS.condExp_gaussianLaw_coord`,
  `MSSS.condVar_gaussianLaw_coord`) and TauCeti's Gaussian conditioning; (b) needs the density
  form of item 47, which is the infrastructure no library has. The inverse `(1 - C)⁻¹` is the
  junk value `0` when `1 - C` is singular, which the hypothesis of (a) excludes.

* **54. Stationary autoregressions on $\mathbb Z^d$.** Let $L\subset\mathbb Z^d\setminus\{0\}$
  be finite and symmetric and $c_s=c_{-s}$ for $s\in L$. If
  $P^\ast(u)=1-\sum_{s\in L}c_s\cos\langle s,u\rangle$ has no zero on $[-\pi,\pi]^d$, there is a
  centred stationary Gaussian field with
  $X_t=\sum_{s\in L}c_sX_{t-s}+e_t$ and $\mathop{\mathrm{Cov}}(e_t,X_s)=0$ for $s\ne t$, with
  spectral density $\sigma_e^2(2\pi)^{-d}P^\ast(u)^{-1}$, where $\sigma_e^2>0$ is the variance
  of $e_t$; the conditional residuals satisfy
  $\mathop{\mathrm{Cov}}(e_t,e_{t+s})=-\sigma_e^2c_s$ for $s\in L$. Every stationary
  simultaneous autoregression on $\mathbb Z^d$ is such a conditional autoregression; for
  $d=1$ the two classes coincide, and for $d\ge2$ the inclusion is strict, as the isotropic
  four-nearest-neighbour conditional autoregression with $0<|c|<1/4$ shows.

  *Assessment.* TauCeti has Bochner's theorem and the Herglotz theorem on $\mathbb Z$ and on
  discrete abelian groups. No spectral density of a field on $\mathbb Z^d$, no stationary
  autoregression, and no comparison of the two classes is present.

  *Lean target.* Carriers: sites `Fin d → ℤ` with `1 ≤ d`; a real field
  `X : (Fin d → ℤ) → Ω → ℝ` on a probability space, Gaussian in Mathlib's sense
  (`ProbabilityTheory.IsGaussianProcess X P`), centred and stationary; the symbol
  `P*(u) = 1 - ∑ s ∈ L, c s * Real.cos ⟪s, u⟫` on the torus `Fin d → ℝ` restricted to
  `[-π, π]^d`, for a finite symmetric `L : Finset (Fin d → ℤ)` with `0 ∉ L` and `c (-s) = c s`.
  New definitions: the spectral density of a stationary field on `ℤ^d`, as a nonnegative
  integrable `f` with `cov[X t, X (t + h)] = ∫ u in [-π, π]^d, Real.cos ⟪h, u⟫ * f u`; the
  conditional and simultaneous autoregressive classes as sets of spectral densities,
  `σ² (2π)^{-d} / P*(u)` and `σ² (2π)^{-d} / |1 - ∑_s b_s e^{i⟨s,u⟩}|²`. Conjuncts: (a)
  existence of `X` with that covariance when `P*` has no zero, by the Gaussian-field existence
  of item 2 (`MSSS.exists_isGaussianProcess_coord`, proved) and positive definiteness of the
  Fourier transform of a nonnegative integrable density; (b) the residual identities
  `cov[e t, X s] = 0` for `s ≠ t` and `cov[e t, e (t + s)] = -σ² c s`; (c) inclusion of the
  simultaneous class in the conditional class; (d) equality for `d = 1`, which needs the
  Fejér–Riesz factorisation of a positive trigonometric polynomial, absent from both
  libraries; (e) strictness for `d ≥ 2` with the four-neighbour symbol and `0 < |c| < 1/4`.
  The variance `σ²` must be positive, or the spectral density is the junk zero density.
  Depends on items 2 and 5.

### Gaussian Markov random fields

[Synopsis](SYNOPSIS.md#gaussian-markov-random-fields) · [Coverage](STRUCTURE.md#gaussian-markov-random-fields).

A random vector $x\in\mathbb R^n$ is a **Gaussian Markov random field** for a graph $G$ on
$\{1,\dots,n\}$, with mean $\mu$ and symmetric positive definite precision $Q$, when
$x\sim N(\mu,Q^{-1})$ and, for $i\ne j$, $Q_{ij}\ne0$ exactly when $i\sim j$. The
**canonical parametrisation** $N_C(b,Q)$ is the law with density proportional to
$\exp(-\tfrac12x^\top Qx+b^\top x)$, so $N(\mu,Q^{-1})=N_C(Q\mu,Q)$.

* **55. Precision and conditional independence.** If $x\sim N(\mu,Q^{-1})$ with $Q$
  positive definite, then for $i\ne j$, $x_i$ and $x_j$ are conditionally independent given
  $x_{-ij}$ if and only if $Q_{ij}=0$. Moreover
  $$\mathbb E(x_i\mid x_{-i})=\mu_i-\frac1{Q_{ii}}\sum_{j\ne i}Q_{ij}(x_j-\mu_j),\qquad
  \mathop{\mathrm{Var}}(x_i\mid x_{-i})=Q_{ii}^{-1},\qquad
  \mathop{\mathrm{Corr}}(x_i,x_j\mid x_{-ij})=-\frac{Q_{ij}}{\sqrt{Q_{ii}Q_{jj}}} .$$

  *Assessment.* TauCeti has Gaussian conditioning in covariance form, the identity
  $1/Q_{ii}=\Sigma_{ii}-\Sigma_{i,-i}\Sigma_{-i,-i}^{-1}\Sigma_{-i,i}$, and independence of
  jointly Gaussian blocks with zero cross-covariance. The precision form of the conditional
  law and the equivalence of $Q_{ij}=0$ with conditional independence are absent.

  *Lean target.* Carriers: `MSSS.gaussianLaw μ Q⁻¹` on `ι → ℝ` with `Q.PosDef`, so that the
  inverse is not the junk value; conditioning on a set of coordinates is conditioning on the
  σ-algebra `MSSS.coordSigma A` they generate. The four conclusions are four theorems:
  conditional independence of `x i` and `x j` given `coordSigma {i, j}ᶜ` in Mathlib's
  `ProbabilityTheory.CondIndepFun`, if and only if `Q i j = 0`
  (`MSSS.condIndepFun_iff_precision_eq_zero`); the conditional mean as an almost-everywhere
  equality of Mathlib's conditional expectation (`MSSS.condExp_gaussianLaw_coord`); the
  conditional variance as the conditional expectation of the squared residual
  (`MSSS.condVar_gaussianLaw_coord`); and the partial correlation from the conditional
  moments of the residuals (`MSSS.condCorr_gaussianLaw_coord`), all proved
  (`MSSS/Lattice/GaussianMarkov.lean`). The canonical parametrisation $N_C(b,Q)$ and item 57
  are not stated; they need a definition `MSSS.gaussianCanonical b Q`, equal to
  `MSSS.gaussianLaw (Q⁻¹ *ᵥ b) Q⁻¹`, with the conditioning identity derived from TauCeti's
  `TauCeti.Probability.condDistrib_multivariateGaussian`.

* **56. Markov properties.** Let $x\sim N(\mu,Q^{-1})$ with $Q$ positive definite, and let
  $G$ be a graph on $\{1,\dots,n\}$. The pairwise property ($x_i$ and $x_j$ conditionally
  independent given $x_{-ij}$ for non-adjacent $i\ne j$), the local property ($x_i$
  conditionally independent of the coordinates outside $\{i\}\cup\partial i$ given
  $x_{\partial i}$, for every $i$), and the global property with respect to $G$ are
  equivalent, and each holds exactly when $Q_{ij}=0$ for all non-adjacent $i\ne j$. In
  particular a Gaussian Markov random field for $G$ has all three. The global property states
  that $x_A$ and $x_B$
  are conditionally independent given $x_C$ whenever $A,B,C$ are disjoint, $A,B$ nonempty,
  and $C$ separates $A$ from $B$ in $G$; for $C=\emptyset$ this is independence.

  *Assessment.* Neither library defines the global Markov property, and TauCeti lacks the
  intersection property of conditional independence. TauCeti has vertex separators in the
  form used by Menger's theorem.

  *Lean target.* Definitions: `MSSS.Separates G A B C` (every walk from `A` to `B` meets
  `C`, through `SimpleGraph.Walk.support`) and the three properties `MSSS.PairwiseMarkov`,
  `MSSS.LocalMarkov`, `MSSS.GlobalMarkov` of a finite measure on `ι → ℝ`, each a family of
  `ProbabilityTheory.CondIndepFun` statements for coordinate σ-algebras. The equivalence for
  `MSSS.gaussianLaw μ S` with `S.PosDef` and any graph is `MSSS.gaussianLaw_markov_tfae`, and
  the global property of a Gaussian Markov random field is `MSSS.globalMarkov_gaussianLaw`,
  both proved (`MSSS/Lattice/GaussianMarkov.lean`). The characterisation by zeros of the
  precision for non-adjacent pairs is `MSSS.pairwiseMarkov_gaussianLaw_inv_iff`, proved. The general equivalence for positive densities needs the
  intersection property, which is a target of the open roadmap PR
  GraphicalModelsAndConditionalIndependence (§1.4) for finite state spaces only.

### Gibbs measures on infinite lattices

[Synopsis](SYNOPSIS.md#gibbs-measures-on-infinite-lattices) · [Coverage](STRUCTURE.md#gibbs-measures-on-infinite-lattices).

Let $S$ be countably infinite, $(E,\mathcal E)$ a measurable space, $\Omega=E^S$, and for
finite $\Lambda\subset S$ let $\mathcal T_\Lambda$ be the $\sigma$-algebra generated by the
coordinates outside $\Lambda$; the **tail $\sigma$-algebra** is
$\mathcal T=\bigcap_\Lambda\mathcal T_\Lambda$. A **specification** is a family
$\gamma=(\gamma_\Lambda)$ of probability kernels from $(\Omega,\mathcal T_\Lambda)$ to
$\Omega$ that are proper, $\gamma_\Lambda(B\mid\cdot)=\mathbf 1_B$ for
$B\in\mathcal T_\Lambda$, and consistent, $\gamma_\Delta\gamma_\Lambda=\gamma_\Delta$ for
$\Lambda\subseteq\Delta$. The set $\mathcal G(\gamma)$ of **Gibbs measures** consists of the
probability measures $\mu$ satisfying the **DLR equations** $\mu\gamma_\Lambda=\mu$ for every
finite $\Lambda$, equivalently $\mu(A\mid\mathcal T_\Lambda)=\gamma_\Lambda(A\mid\cdot)$
almost surely. For a potential $\Phi=(\Phi_A)$, $A$ finite, $\Phi_A$ depending only on the
coordinates in $A$, and an a priori measure $\lambda$ on $E$, the Gibbsian specification is
$$\gamma^\Phi_\Lambda(A\mid\omega)=Z_\Lambda(\omega)^{-1}\int\mathbf 1_A(\zeta\omega_{S\setminus\Lambda})
e^{-H_\Lambda(\zeta\omega_{S\setminus\Lambda})}\lambda^\Lambda(d\zeta),\qquad
H_\Lambda=\sum_{A\cap\Lambda\ne\emptyset}\Phi_A,$$
when the sums converge and $0<Z_\Lambda<\infty$. $\Phi$ is **absolutely summable** when
$\sum_{A\ni i}\sup|\Phi_A|<\infty$ for every $i$, and there is a **phase transition** when
$|\mathcal G(\gamma^\Phi)|>1$.

In the *Lean target* paragraphs below the configuration space is `S → E` with
`[MeasurableSpace E]`; `MSSS.outsideSigma Λ` is the σ-algebra of the coordinates outside
`Λ` (Mathlib's `MeasureTheory.cylinderEvents Λᶜ` would serve) and `MSSS.tailSigma` is its
infimum over finite `Λ`. A specification is a raw family
`γ : Finset S → (S → E) → Measure (S → E)` with the predicate `MSSS.IsSpecification γ`
(probability measures, `outsideSigma`-measurability, properness, consistency in the
integrated form), and `MSSS.IsGibbs γ μ` is the integrated DLR equation
`μ A = ∫⁻ ω, γ Λ ω A ∂μ`, which avoids the junk value of `Measure.bind` along a
non-measurable map. A potential is `Φ : Finset S → (S → E) → ℝ` with `MSSS.IsPotential Φ`
(measurable, depending only on the coordinates in `A`), absolute summability
`MSSS.IsAbsolutelySummable Φ` takes the supremum in `ℝ≥0∞`, so the junk value of a real
`⨆` over an unbounded set does not arise, and the Gibbsian specification is
`MSSS.gibbsKernel Φ ρ`.

* **60. Existence of Gibbs measures.** If $(E,\mathcal E)$ is a standard Borel space,
  $0<\lambda(E)<\infty$, and $\Phi$ is absolutely summable, then $\mathcal G(\gamma^\Phi)$ is
  nonempty, convex, and compact in the topology of local convergence. This covers every
  nonempty finite state space with counting measure and an absolutely summable potential,
  such as the Ising model on $\mathbb Z^d$ and the auto-logistic models with
  $\sum_j|\beta_{ij}|<\infty$ for every $i$.

  *Assessment.* Mathlib has cylinder σ-algebras, proper kernels, exponential tilting, and
  Prokhorov compactness. Neither library defines a specification, a potential, or the DLR
  equations.

  *Lean target.* Hypotheses: `[Countable S] [DecidableEq S] [StandardBorelSpace E]`,
  `MSSS.IsPotential Φ`, `MSSS.IsAbsolutelySummable Φ`, and `ρ` with `[IsFiniteMeasure ρ]`
  and `[NeZero ρ]`, which is $0<\lambda(E)<\infty$. Conclusions, as conjuncts of one theorem:
  `MSSS.IsSpecification (MSSS.gibbsKernel Φ ρ)`; nonemptiness of
  `MSSS.gibbsSet (MSSS.gibbsKernel Φ ρ)`; closure under convex combinations with weights
  `ENNReal.ofReal t`, `ENNReal.ofReal (1 - t)`, `t ∈ [0, 1]`; and compactness for local
  convergence (`MSSS.TendstoLocally`, convergence of integrals of bounded measurable local
  functions), stated as convergence along every ultrafilter containing the Gibbs set. It is
  `MSSS.gibbsSet_nonempty_convex_compact`, proved (`MSSS/Lattice/Gibbs/Existence.lean`). The
  topology of local convergence is not a Mathlib topology; stating compactness as
  `IsCompact` needs that topology on `Measure (S → E)` or on Mathlib's
  `MeasureTheory.ProbabilityMeasure`. The roadmap GibbsMeasuresAndTheIsingModel (§2.1) owns
  existence for quasilocal specifications on a finite spin space, a special case.

* **61. Extreme Gibbs measures.** Let $\gamma$ be a specification. A measure
  $\mu\in\mathcal G(\gamma)$ is extreme in $\mathcal G(\gamma)$ if and only if it is trivial
  on $\mathcal T$. If $\mu\in\mathcal G(\gamma)$ and $\nu$ is a probability measure with
  $\nu\ll\mu$, then $\nu\in\mathcal G(\gamma)$ if and only if $d\nu/d\mu$ has a
  $\mathcal T$-measurable version. Each element of
  $\mathcal G(\gamma)$ is determined within $\mathcal G(\gamma)$ by its restriction to
  $\mathcal T$, and distinct extreme elements are mutually singular on $\mathcal T$.

  *Assessment.* TauCeti has tail $\sigma$-algebras and the correspondence between
  extremality and ergodicity for group actions and exchangeable laws, analogous results for
  other convex sets of measures. The theorem for Gibbs measures is absent.

  *Lean target.* For a specification `γ` (`MSSS.IsSpecification γ`) and `MSSS.IsGibbs γ μ`,
  extremality is `MSSS.IsExtremeGibbs γ μ` (no proper convex combination of two Gibbs
  measures with real weight in `(0, 1)`). The four conclusions are four theorems: extreme if
  and only if every `tailSigma`-measurable set has measure `0` or `1`
  (`MSSS.isExtremeGibbs_iff_tail_trivial`); for a probability measure `ν ≪ μ`, `ν` is Gibbs
  if and only if `ν = μ.withDensity g` for a `tailSigma`-measurable `g : (S → E) → ℝ≥0∞`
  (`MSSS.isGibbs_iff_tail_density`); determination by the restriction to the tail
  (`MSSS.eq_of_isGibbs_of_tail_eq`); and a tail set of measure `1` and `0` for two distinct
  extreme measures (`MSSS.exists_tail_mutuallySingular`). All are proved
  (`MSSS/Lattice/Gibbs/Basic.lean`). The roadmap GibbsMeasuresAndTheIsingModel (§§1.1–1.2)
  owns the same results for a countable site set, with its specifications taken from
  DimerModelsAndLozengeTilings (Layer 4), on a full shift over a finite alphabet.

* **62. Dobrushin's uniqueness theorem.** For a specification $\gamma$ let $\gamma_i^0$ be the
  single-site conditional law at $i$ and
  $C_{ij}=\sup\{\|\gamma_i^0(\cdot\mid\zeta)-\gamma_i^0(\cdot\mid\eta)\|:\zeta=\eta\text{ off }j\}$,
  with the total-variation distance $\|\alpha-\beta\|=\sup_A|\alpha(A)-\beta(A)|$. If $\gamma$
  is quasilocal and $\sup_i\sum_jC_{ij}<1$, then $|\mathcal G(\gamma)|\le1$, with equality
  when $E$ is nonempty and standard Borel. For the Gibbsian specification of a potential for
  which the specification is defined, with $\lambda$ $\sigma$-finite, the condition holds when
  $\sup_i\sum_{A\ni i}(|A|-1)\,(\sup\Phi_A-\inf\Phi_A)<2$, and the constant $2$ cannot be
  enlarged. Hence $\beta\Phi$ has at most one Gibbs measure for all small $\beta>0$ when the
  left side is finite for $\Phi$.

  *Assessment.* Absent from both libraries. Mathlib has total variation distance.

  *Lean target.* Definitions: the single-site law `MSSS.singleSiteLaw γ i ω`, the image of
  `γ {i} ω` under the coordinate `i`; the total variation `MSSS.tvSup α β = ⨆ A, |α A - β A|`
  in `ℝ≥0∞`; Dobrushin's coefficient `MSSS.dobrushinCoeff γ i j` in `ℝ≥0∞`, so that the sum
  `∑' j` is never a junk value; quasilocality `MSSS.IsQuasilocal γ`. Conjuncts: at most one
  Gibbs measure under `[Countable S]`, quasilocality, and `∃ c < 1, ∀ i, ∑' j, C i j ≤ c`
  (`MSSS.gibbsSet_subsingleton_of_dobrushin`); exactly one under `[Nonempty E]`
  `[StandardBorelSpace E]` (`MSSS.existsUnique_gibbs_of_dobrushin`); and the oscillation
  criterion for `MSSS.gibbsKernel Φ ρ` with the oscillation
  `⨆ ω ω', ENNReal.ofReal (Φ A ω - Φ A ω')` and `((A.card : ℝ≥0∞) - 1)`, which is `0` for
  `A = ∅` by truncated subtraction (`MSSS.gibbsSet_subsingleton_of_oscillation`). All are
  proved (`MSSS/Lattice/Gibbs/Dobrushin.lean`). The oscillation theorem assumes a finite
  nonzero `ρ` and absolute summability, narrower than Georgii's $\lambda$-admissible potential
  with $\sigma$-finite $\lambda$; the sharpness of the constant $2$ is not stated. The roadmap
  GibbsMeasuresAndTheIsingModel (§3.1) owns Dobrushin's theorem for a finite spin space, with
  the oscillation bound in the form $c_{ij}\le\tfrac12\sum_{A\ni i,j}\delta(\Phi_A)$.

* **63. No phase transition in one dimension.** Let $S=\mathbb Z$, $E$ finite and nonempty,
  and $\lambda$ counting measure. Call $\gamma$ a positive homogeneous Markov specification when
  $\gamma_{\{i\}}(\sigma_i=y\mid\omega)=g(\omega_{i-1},y,\omega_{i+1})$ with $g>0$. Such a
  specification has exactly one Gibbs measure, the stationary Markov chain with a transition
  matrix $P$ with positive entries, and $\gamma\mapsto P$ is a bijection onto these
  matrices. Explicitly, fix $a\in E$, put $Q(x,y)=g(a,x,y)/g(a,a,y)$, let $q$ be the Perron
  eigenvalue of $Q$ and $r$ a positive right eigenvector; then $P(x,y)=Q(x,y)r(y)/(q\,r(x))$.

  *Assessment.* TauCeti has the Perron–Frobenius theorem for positive matrices and
  stationary Markov chains on $\mathbb N$. The transfer-matrix construction and the
  uniqueness of the Gibbs measure are absent.

  *Lean target.* Carriers: `[Fintype E] [Nonempty E] [MeasurableSingletonClass E]`, sites
  `ℤ`, a specification `γ` whose singleton kernels are
  `γ {i} ω {σ | σ i = y} = ENNReal.ofReal (g (ω (i - 1)) y (ω (i + 1)))` with `g > 0`, and
  `MSSS.IsMarkovChainLaw P μ`, the cylinder probabilities of a stationary chain on `ℤ`.
  Conjuncts: (a) `∃! μ, MSSS.IsGibbs γ μ`, and that measure is the chain with
  `P x y = g a x y / g a a y * r y / (q * r x)` for every positive eigenpair `(q, r)` of
  `Q x y = g a x y / g a a y`; (b) every positive stochastic `P` arises, with
  `g x y z = P x y * P y z / ∑ w, P x w * P w z`; (c) injectivity of `P ↦ g`. These are
  `MSSS.existsUnique_gibbs_markovSpecification` and `MSSS.markovSpecification_of_transition`,
  both admitted with `sorry`, and `MSSS.transition_injective`, proved
  (`MSSS/Lattice/Gibbs.lean`). The proof needs TauCeti's Perron–Frobenius theorem
  (`Matrix.exists_mulVec_eq_smul_of_pos`) for the eigenpair and the two-sided stationary
  chain on `ℤ`, which neither library constructs (Mathlib's Ionescu-Tulcea construction and
  TauCeti's chain law live on `ℕ`); uniqueness also uses item 62 or the boundary-uniformity
  argument of GibbsMeasuresAndTheIsingModel §3.2, which owns uniqueness for finite-range
  potentials on `ℤ` but not the identification with a Markov chain.

* **64. Phase transition of the two-dimensional Ising model.** Let $S=\mathbb Z^2$,
  $E=\{-1,1\}$, $\lambda$ counting measure, and $\Phi_{\{i,j\}}=-\sigma_i\sigma_j$ for
  nearest neighbours $i,j$, with all other $\Phi_A=0$. For all sufficiently large $\beta$
  there are two shift-invariant Gibbs measures $\mu_\pm^\beta\in\mathcal G(\beta\Phi)$, each
  the spin-flip image of the other, with $\mu_-^\beta(\sigma_0)<0<\mu_+^\beta(\sigma_0)$, and
  they can be chosen so that they converge locally to the point masses on the all-plus and
  all-minus configurations as $\beta\to\infty$. Hence $|\mathcal G(\beta\Phi)|>1$ for large
  $\beta$. The critical value in this normalisation is $\beta_c=\tfrac12\log(1+\sqrt2)$,
  with uniqueness for $\beta<\beta_c$ and a phase transition for $\beta>\beta_c$.

  *Assessment.* Absent from both libraries.

  *Lean target.* Carriers: sites `ℤ × ℤ`, spins `Bool` with `MSSS.spin true = -1` and
  `MSSS.spin false = 1`, the potential `MSSS.isingPotential` ($-\sigma_i\sigma_j$ on nearest-neighbour pairs), and
  `MSSS.gibbsSet (MSSS.gibbsKernel (fun A ω ↦ β * MSSS.isingPotential A ω) Measure.count)`.
  Conjuncts: (a) for `β` beyond some `β₀`, two Gibbs measures invariant under every
  translation, each the image of the other under the spin flip, with opposite signs of
  `∫ ω, MSSS.spin (ω 0)`, and the plus measure of every finite all-plus cylinder tending to
  `1` as `β → ∞` (`MSSS.ising_phaseTransition`); (b) uniqueness for `0 ≤ β < β_c` and
  non-uniqueness for `β > β_c` with `β_c = ½ log (1 + √2)` (`MSSS.ising_critical`). Both are
  admitted with `sorry` (`MSSS/Lattice/Gibbs.lean`). Part (a) needs Peierls' contour bound,
  owned by GibbsMeasuresAndTheIsingModel (§5.2), which imports the dual-cycle geometry of
  BernoulliPercolation (§5.1, Layer 6). Part (b) is Onsager's value, which that roadmap lists
  beyond its scope; its uniqueness half needs the sharpness of the transition and is not
  within reach at the pins. `MSSS.spin` follows the convention of that roadmap, `Bool` with `true` the
  spin $-1$, so the all-plus configuration is the constant `false`.

### Estimation by coding and pseudolikelihood

[Synopsis](SYNOPSIS.md#estimation-by-coding-and-pseudolikelihood) · [Coverage](STRUCTURE.md#estimation-by-coding-and-pseudolikelihood).

* **65. Coding and pseudolikelihood.** A set $C$ of sites is a **coding set** when no two
  of its points are neighbours. For a Markov random field, the variables $X_i$, $i\in C$,
  are conditionally independent given $X_{S\setminus C}$, with laws
  $\pi_i(\cdot\mid x_{\partial i})$; hence $\prod_{i\in C\cap D_n}\pi_i(x_i\mid x_{\partial i};\theta)$
  is a conditional likelihood, the **coding likelihood**. The **pseudolikelihood** is
  $\prod_{i\in D_n}\pi_i(x_i\mid x_{\partial i};\theta)$. Let $X$ be a Markov random field on
  a countable graph with specification $\pi_\theta$, $\theta$ in the interior of a compact
  $\Theta\subset\mathbb R^p$, observed on $D_n\cup\partial D_n$ with $D_n$ strictly
  increasing. Under conditions that ensure a positive density of strong coding sites, uniform
  positivity and continuity of the conditional laws, and identifiability through the
  conditional Kullback–Leibler contrast, the maximum pseudolikelihood and coding estimators
  are consistent. Under further smoothness and a lower bound on the conditional
  information, the coding estimator satisfies
  $I_n^C(\theta)^{1/2}(\hat\theta_n^C-\theta)\Rightarrow N(0,I_p)$, where
  $I_n^C(\theta)=\sum_{i\in C\cap D_n}\mathop{\mathrm{Var}}_\theta\bigl(\partial_\theta\log
  \pi_i(X_i\mid x_{\partial i};\theta)\mid x_{\partial i}\bigr)$ is the conditional
  information of the coding sites, and the coding
  likelihood-ratio statistic for a smooth hypothesis of dimension $q$ is asymptotically
  $\chi^2_{p-q}$.

  *Assessment.* Absent from both libraries. The i.i.d. and Lindeberg central limit theorems
  and the chi-squared law are present; no central limit theorem for conditionally independent
  or martingale-difference arrays is.

  *Lean target.* The exact part (conditional independence of the coding variables, with laws
  the full conditionals) is `MSSS.setConditional_codingSet` for finite `S`, positive `π`, and
  `C : Finset S` with no two sites adjacent, proved (`MSSS/Lattice/MarkovField.lean`). The
  asymptotic part needs new carriers: a parametric family of specifications
  `γ : Θ → Finset S → (S → E) → Measure (S → E)` on a countable graph, `Θ ⊆ Fin p → ℝ`
  compact with `θ₀ ∈ interior Θ`; a nested sequence of finite windows `D : ℕ → Finset S`; the
  contrasts `U_n θ ω = -∑ i ∈ D n, Real.log (q θ i ω)` with `q θ i ω` the single-site
  density, positive by hypothesis so that `Real.log` has no junk value, and the coding
  contrast on `C ∩ D n`; and an estimator as any measurable selection of minimisers. The
  conjuncts are three theorems under the conditions (C1)–(C3), (N1)–(N2) written out as
  hypotheses: consistency of both estimators in probability under every Gibbs measure of
  `γ θ₀` (`MeasureTheory.TendstoInMeasure`); asymptotic normality
  `I_n^C(θ₀)^{1/2} (θ̂_n - θ₀) → N(0, I_p)` in distribution
  (`MeasureTheory.TendstoInDistribution`), with `I_n^C` the conditional information summed
  over the coding sites; and the chi-squared limit of the coding likelihood-ratio statistic
  for a smooth sub-model of dimension `q`. The central limit step needs a central limit
  theorem for sums that are independent conditionally on the complement of the coding set, or
  a martingale central limit theorem, which neither library has. Depends on items 60–61.

### Finite Gibbs sampling

[Synopsis](SYNOPSIS.md#finite-gibbs-sampling) · [Coverage](STRUCTURE.md#finite-gibbs-sampling).

* **123. Finite Gibbs sampler.** Let $S$ be a nonempty finite set of sites with nonempty
  finite state spaces $E_i$, and let $\pi$ be a strictly positive probability law on
  $\prod_{i\in S}E_i$. Let $P_i$ resample coordinate $i$ from its full conditional
  $\pi_i(\cdot\mid x_{-i})$, keeping all other coordinates fixed. Each $P_i$ is reversible
  for $\pi$. A sweep applying each $P_i$ once in a fixed order preserves $\pi$, and
  the random-scan kernel $\sum_{i\in S}q_iP_i$ is reversible for $\pi$ when the $q_i$
  are fixed positive probabilities summing to one. For either kernel $P$, the iterates $\nu P^n$
  converge in total variation to $\pi$ uniformly over initial laws $\nu$.

  *Assessment.* Partly covered. TauCeti proves reversibility and convergence from each
  initial law for the hard-core heat bath. Its edgeless case gives uniform random-site
  updates for a positive binary product law. Mathlib supplies conditional distributions and
  invariance under kernel composition. The general finite Gibbs updates, fixed sweeps, and
  uniform convergence remain open in the libraries.

  *Lean target.* Carriers: `[Fintype S] [Nonempty S]`, `E i` finite and nonempty with the
  discrete σ-algebra, `π : Measure (∀ i, E i)` a probability measure with
  `∀ x, 0 < π {x}`; Mathlib's `ProbabilityTheory.Kernel`, `Kernel.IsReversible`,
  `Kernel.Invariant`, and `MeasureTheory.tvDist`. New definitions: the single-site kernel
  `MSSS.gibbsUpdate π i`, whose row at `x` is the conditional law of `π` on the configurations that
  agree with `x` off `i` (positive by hypothesis, so no junk conditioning on a null set); the
  sweep as the composition of these kernels along a list enumerating `S`; and the random scan
  `∑ i, q i • MSSS.gibbsUpdate π i` for `q : S → ℝ≥0∞` positive with sum `1`. Conjuncts:
  reversibility of each update; invariance of the sweep (not reversibility); reversibility of
  the random scan; and `⨆ ν, tvDist (ν.bind (P ^ n)) π → 0` over probability measures `ν`,
  for both kernels. Uniformity follows from a Doeblin minorisation `P^N x ≥ ε π`, which no
  library states; TauCeti's `ProbabilityTheory.Kernel.Invariant.tendsto_tvDist_pow_comp`
  gives convergence for each initial law. No MSSS declaration states this entry. The roadmap
  MarkovChainMixing (§6.1) owns reversibility of the uniform random-scan Glauber kernel for
  countable values.

### Matérn fields and the stochastic partial differential equation

[Synopsis](SYNOPSIS.md#matérn-fields-and-the-stochastic-partial-differential-equation) · [Coverage](STRUCTURE.md#matérn-fields-and-the-stochastic-partial-differential-equation).

* **66. Whittle's equation.** Let $\nu>0$, $\kappa>0$, $\alpha=\nu+d/2$, and let $\mathcal W$
  be Gaussian white noise of unit variance on $\mathbb R^d$. Define
  $(\kappa^2-\Delta)^{\alpha/2}$ by the
  Fourier multiplier $(\kappa^2+\|k\|^2)^{\alpha/2}$. The stationary solutions of
  $(\kappa^2-\Delta)^{\alpha/2}x=\mathcal W$ are exactly the centred Gaussian fields with
  spectral density $(2\pi)^{-d}(\kappa^2+\|k\|^2)^{-\alpha}$, that is, the Matérn fields
  with smoothness $\nu$, inverse scale $\kappa$, and variance
  $$\sigma^2=\frac{\Gamma(\nu)}{\Gamma(\nu+d/2)\,(4\pi)^{d/2}\kappa^{2\nu}} .$$
  The equation $(\kappa^2-\Delta)^{\alpha/2}(\tau x)=\mathcal W$ with a constant $\tau>0$
  gives variance $\sigma^2/\tau^2$. The Fourier multiplier never vanishes, so the operator
  is injective on tempered distributions. For an even integer $\alpha$ the differential
  operator $(\kappa^2-\Delta)^{\alpha/2}$ acting on smooth functions has a nontrivial null
  space, containing $u\mapsto e^{\kappa\langle e,u\rangle}$ for every unit vector $e$; these
  functions are not tempered, and stationarity on $\mathbb R^d$, or boundary conditions on a
  bounded domain, single out the Matérn solution.

  *Assessment.* Mathlib has Fourier multipliers on tempered distributions and Bessel
  potentials, and TauCeti Bessel-potential spaces. White noise, the generalised-function
  solution of the equation, and the identification of its covariance as Matérn are absent;
  the last needs item 12.

  *Lean target.* In the spectral formulation: a stationary field with finite spectral
  measure `F` on `EuclideanSpace ℝ (Fin d)` solves the equation when
  `F.withDensity (fun k ↦ ENNReal.ofReal ((κ ^ 2 + ‖k‖ ^ 2) ^ α))` is
  `ENNReal.ofReal ((2π)^{-d}) • volume`, the spectral measure of unit white noise. The
  conjuncts are: the characterisation of the solutions by the density
  `MSSS.whittleDensity d ν κ` (`MSSS.whittle_spectral_iff`); the covariance as
  `σ² * MSSS.maternCorrelation ν (1 / κ) ‖h‖` with the stated `σ²`, and `σ² / τ²` for `τ x`
  with `τ ≠ 0` (`MSSS.spectralCov_whittleDensity`, with `1 ≤ d`, `0 < ν`, `0 < κ`); and the
  exponential null solution of the differential operator `κ² - Δ`
  (`MSSS.exp_mem_null_helmholtz`, Mathlib's Laplacian `Δ`). All three are proved
  (`MSSS/Lattice/SPDE.lean`). The generalised-function form, with white noise as an isonormal
  Gaussian process on `L²(ℝ^d)` and `(κ² - Δ)^{α/2}` as Mathlib's
  `TemperedDistribution.fourierMultiplierCLM`, needs a Gaussian measure on tempered
  distributions, which no library has.

* **67. Finite-element Gaussian Markov random fields.** Let a bounded domain carry a
  triangulation with piecewise-linear basis functions $\psi_1,\dots,\psi_n$ and Neumann
  boundary conditions, and put $C_{ij}=\langle\psi_i,\psi_j\rangle$,
  $G_{ij}=\langle\nabla\psi_i,\nabla\psi_j\rangle$, $K=\kappa^2C+G$, and assume
  $\partial_n\psi_k=0$ on the boundary. For integer $\alpha\ge1$, the finite-element
  approximations $\sum_k\psi_kw_k$ to the Neumann problem for Whittle's equation in item 66
  (the weak least-squares solution for $\alpha=1$, the weak Galerkin solution for $\alpha=2$,
  and the recursive Galerkin solution for $\alpha\ge3$) have $w\sim N(0,Q_\alpha^{-1})$ with
  $$Q_1=K,\qquad Q_2=KC^{-1}K,\qquad Q_\alpha=KC^{-1}Q_{\alpha-2}C^{-1}K\quad(\alpha\ge3).$$
  In dimension two, $\alpha=1$ is the limiting case $\nu=0$, outside item 66.
  Replacing $C$ by the diagonal matrix $\tilde C_{ii}=\langle\psi_i,1\rangle$ makes every
  $Q_\alpha$ sparse for fixed $\alpha$, so the approximation is a Gaussian Markov random
  field. For the approximations with the exact mass matrix, assume that every $H^1$ function
  is the $H^1$-limit of a sequence with one function from each successive finite-element
  space. The approximations then converge weakly to the Neumann solution, for $\alpha=1,2$
  and iteratively for larger integers. For each pair of $L^2$ test functions $f,g$, the mean
  of $\langle f,x_m\rangle$ and the covariance of $\langle f,x_m\rangle$ and
  $\langle g,x_m\rangle$ converge to those for the Neumann solution, where $x_m$ denotes the
  approximation in the $m$th space. On the unit lattice $\mathbb Z^2$, take the model with
  full conditional mean $a^{-1}(x_{i-1,j}+x_{i+1,j}+x_{i,j-1}+x_{i,j+1})$ and variance $1/a$
  for $a>4$. Its precision symbol is
  $a-2\cos\omega_1-2\cos\omega_2=\kappa^2+\|\omega\|^2+O(\|\omega\|^4)$ with $\kappa^2=a-4$.
  Taking the $(\nu+1)$-fold convolution of the precision stencil gives the low-frequency
  Matérn approximation for positive integer $\nu$ in dimension two.

  *Assessment.* TauCeti has Sobolev spaces and finite-dimensional Galerkin equations for
  deterministic parabolic problems. The finite-element mass and stiffness matrices for the
  Neumann SPDE, the weak convergence of its tested means and covariances, and the lattice
  approximation are absent.

  *Lean target.* The precisions are `MSSS.femPrecision K C α` (`Q_0 = C`, `Q_1 = K`,
  `Q_{α+2} = K C⁻¹ Q_α C⁻¹ K`); positive definiteness for `C.PosDef`, `G.PosSemidef`,
  `0 < κ` is `MSSS.femPrecision_posDef`, and sparsity with a lumped diagonal `C̃` and `K`
  supported on the edges of a graph, `Q_α i j = 0` beyond graph distance `α`, is
  `MSSS.femPrecision_eq_zero_of_lt_edist`. The weak convergence is stated abstractly: for an
  energy space `V`, `L²` space `H`, inclusion `J : V →L[ℝ] H`, and subspaces `U n` whose
  union is dense, `⟪f, (J P_n J†)^α g⟫ → ⟪f, (J J†)^α g⟫`
  (`MSSS.tendsto_inner_galerkinCovariance`). The lattice symbol is
  `MSSS.latticeSymbol_isBigO` and `MSSS.tendsto_latticeSymbol_div` (`4 < a`). All are proved
  (`MSSS/Lattice/SPDE.lean`). Not yet stated: the identification of the covariance of the
  finite-element weights with `Q_α⁻¹`, which needs the triangulation and the hat functions
  $\psi_k$ on a polygonal domain (no library has finite-element spaces), and the
  instantiation of the abstract theorem with TauCeti's Sobolev space `H¹` and the weak Neumann
  form, which needs the energy inner product `κ² ⟪u, v⟫ + ⟪∇u, ∇v⟫` as an inner-product
  structure on `H¹`. Depends on item 66.

## 4. Point processes and random measures

Selected: 17 statements. [Synopsis part](SYNOPSIS.md#4-point-processes-and-random-measures) · [Coverage part](STRUCTURE.md#4-point-processes-and-random-measures).

Two frameworks occur in the sources. Last and Penrose work on an arbitrary measurable
space $(\mathbb X,\mathcal X)$ with s-finite intensity measures, and point processes need
not be locally finite. Daley–Vere-Jones, Kallenberg, Baccelli–Błaszczyszyn–Karray, and the
spatial texts work on a complete separable metric space or a localized Borel space and build
local finiteness into the definitions. The entries are stated in the first framework unless
they say otherwise; the reference guide records where the second needs extra hypotheses.

Let $\mathbf N$ be the set of measures on $\mathbb X$ that are countable sums of finite
measures with values in $\mathbb N_0$, with the $\sigma$-algebra generated by the maps
$\mu\mapsto\mu(B)$. A measure is **s-finite** when it is a countable sum of finite measures.
A **point process** is a random element $\eta$ of $\mathbf N$, and a **random measure** is a
random element $\xi$ of the space of s-finite measures with the analogous $\sigma$-algebra.
The **intensity measure** is $\Lambda(B)=\mathbb E\eta(B)$. $\eta$ is **simple** when almost
surely $\eta\{x\}\le1$ for every $x$. The **Laplace functional** is
$L_\xi(u)=\mathbb E\exp(-\int u\,d\xi)$ for measurable $u\ge0$. $\mathrm{Po}(\infty)$ is the
point mass at $\infty$.

*Lean carriers for this part.* A random measure is a map `N : Ω → Measure X`, measurable for the
evaluation σ-algebra `MeasureTheory.Measure.instMeasurableSpace`; a point process has in addition `∀
ω, (N ω).IsIntegerValued` (TauCeti `MeasureTheory.Measure.IsIntegerValued`) and `∀ ω, SFinite (N
ω)`. The intensity measure is the Giry bind `P.bind N`, the Laplace functional
`MeasureTheory.Measure.laplaceFunctional P N f` for `f : X → ℝ≥0∞`, and the Poisson property
`TauCeti.Probability.IsPoissonRandomMeasure P N Λ`, which forces `IsProbabilityMeasure P` and treats
`Po(∞)` as the point mass at `∞`. The local code `MSSS/PointProcesses/` also presents a point
process by its points, `MSSS.pointSum I x` with `I : ℕ → Bool` and `x : ℕ → X`, with factorial
measures `MSSS.factorialPointSum m I x : Measure (Fin m → X)`, and stationarity on `EuclideanSpace ℝ
(Fin d)` as `MSSS.IsStationary P η` with `MSSS.translate y μ = μ.map (· - y)`. Moments and
identities are stated with `∫⁻` in `ℝ≥0∞`; a Bochner integral or a `toReal` appears only with an
explicit integrability or finiteness hypothesis. A local declaration is called proved when neither
it nor anything it uses contains `sorry` and it depends only on the standard axioms.

### The Poisson process

[Synopsis](SYNOPSIS.md#the-poisson-process) · [Coverage](STRUCTURE.md#the-poisson-process).

Let $\lambda$ be an s-finite measure. A point process $\eta$ is a **Poisson process with
intensity measure $\lambda$** when $\eta(B)\sim\mathrm{Po}(\lambda(B))$ for every $B$ and
$\eta(B_1),\dots,\eta(B_m)$ are independent for pairwise disjoint $B_1,\dots,B_m$.

* **75. Marking theorem.** Let $K$ be a probability kernel from $\mathbb X$ to $\mathbb Y$
  and $\eta=\sum_{n\le\kappa}\delta_{X_n}$ a Poisson process with intensity $\lambda$. If,
  given $\kappa$ and $X_1,X_2,\dots$, the marks $Y_n$ are independent with laws $K(X_n,\cdot)$,
  then
  $\sum_{n\le\kappa}\delta_{(X_n,Y_n)}$ is a Poisson process on $\mathbb X\times\mathbb Y$
  with intensity measure $(\lambda\otimes K)(C)=\iint\mathbf 1_C(x,y)K(x,dy)\lambda(dx)$.

  *Assessment.* TauCeti constructs independent marking kernels with their Laplace formulas and proves colour splitting for a Poisson measure that already has product intensity. The marking theorem itself is absent; with TauCeti's Laplace characterisation of item 73 it is a moderate argument.

  *Lean target.* Carriers: `TauCeti.Probability.IsPoissonRandomMeasure P η Λ` with `η : Ω → Measure
  X`, a Markov kernel `K : ProbabilityTheory.Kernel X Y` with `[IsMarkovKernel K]`, and the
  intensity `Λ ⊗ₘ K` (`MeasureTheory.Measure.compProd`). The points are presented as `η ω =
  MSSS.pointSum (MSSS.finiteMask (κ ω)) (Xs ω)` with `κ : Ω → ℕ∞` and `Xs : Ω → ℕ → X`, the marks as
  `Ys : Ω → ℕ → Y`. The marking hypothesis is conditional on `(κ, Xs)`: for `P`-almost every `ω`,
  `ProbabilityTheory.condDistrib Ys (fun ω ↦ (κ ω, Xs ω)) P (κ ω, Xs ω) = Measure.infinitePi fun n ↦
  K (Xs ω n)`, which needs `[StandardBorelSpace Y] [Nonempty Y]`; for a general mark space, state it
  as a joint law `P.map (fun ω ↦ ((κ ω, Xs ω), Ys ω)) = (P.map fun ω ↦ (κ ω, Xs ω)) ⊗ₘ L` for an
  s-finite kernel `L` with that almost-sure value. Further hypotheses: `[IsProbabilityMeasure P]`,
  `[SFinite Λ]`, measurability of `ω ↦ (κ ω, Xs ω)` and of `Ys`. Conclusion: `IsPoissonRandomMeasure
  P (fun ω ↦ pointSum (finiteMask (κ ω)) fun n ↦ (Xs ω n, Ys ω n)) (Λ ⊗ₘ K)`. Statable and provable
  at the pins from `ProbabilityTheory.Kernel.optionalTupleMarking`, the Poisson Laplace functional
  `IsPoissonRandomMeasure.laplaceFunctional_eq_expNeg` and its converse
  `isPoissonRandomMeasure_of_laplaceFunctional`. Stated and proved locally as
  `MSSS.isPoissonRandomMeasure_marking` and `MSSS.isPoissonRandomMeasure_marking_of_map_eq_compProd`
  (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`). Item 76 follows by marking with
  `Y = Bool` and the colour-splitting results
  `IsPoissonRandomMeasure.iIndepFun_map_fst_restrict_univ_prod` and
  `acceptance_univ_prod_singleton_of_bernoulliMeasure`.

* **78. Rényi's theorem.** Let $\mathbb X$ be a Borel space, $\lambda$ a diffuse s-finite
  measure, and $\eta$ a simple point process with $\mathbb P(\eta(B)=0)=e^{-\lambda(B)}$ for
  every $B\in\mathcal X$. Then $\eta$ is Poisson with intensity $\lambda$. Likewise, a random
  measure on a localized Borel space with no fixed atoms is a Poisson process if and only if
  $\xi(U)$ is Poisson distributed for every $U$ in a generating ring of bounded sets.

  *Assessment.* TauCeti has simplicity of Poisson random measures with diffuse intensity and determination of laws by finite-dimensional distributions. Rényi's theorem, that void probabilities determine a simple point process, is absent.

  *Lean target.* Two theorems. (i) Rényi's theorem: `[StandardBorelSpace X]`, `[SFinite Λ]`,
  `[NoAtoms Λ]`, `[IsProbabilityMeasure P]`, a measurable `η : Ω → Measure X` with `∀ ω, (η
  ω).IsIntegerValued` and `∀ ω, SFinite (η ω)` (TauCeti `MeasureTheory.Measure.IsIntegerValued`),
  simplicity `∀ᵐ ω ∂P, ∀ x, η ω {x} ≤ 1`, and void probabilities `P {ω | η ω B = 0} = ENNReal.ofReal
  (Real.exp (-(Λ B).toReal))` when `Λ B < ∞` and `= 0` when `Λ B = ∞`, for every measurable `B`;
  conclusion `IsPoissonRandomMeasure P η Λ`. The case split is needed: `(Λ B).toReal` is the junk
  value `0` at `∞`. The core is uniqueness of the law of a simple point process given its void
  probabilities (Last–Penrose, Theorem 6.11; Kallenberg, Theorem 3.8), which needs a predicate
  `Measure.IsSimple μ : Prop := ∀ x, μ {x} ≤ 1` and the measurability of the set of simple
  integer-valued measures; neither library has them. (ii) Kallenberg's criterion: `[MetricSpace X]
  [ProperSpace X] [BorelSpace X]`, a ring `R` of bounded measurable sets (`IsSetRing R`) with
  `MeasurableSpace.generateFrom R` the Borel σ-algebra, `ξ` almost surely locally finite
  (`IsLocallyFiniteMeasure (ξ ω)`) without fixed atoms (`∀ x, P {ω | 0 < ξ ω {x}} = 0`); conclusion
  `IsPoissonRandomMeasure P ξ (P.bind ξ) ↔ ∀ U ∈ R, ∃ c : ℝ≥0, HasLaw (fun ω ↦ ξ ω U)
  ((poissonMeasure c).map (Nat.cast : ℕ → ℝ≥0∞)) P`. Both are statable at the pins; they use item 77
  in the direction proved by TauCeti (`IsPoissonRandomMeasure.ae_forall_singleton_le_one`) and
  determination by finite-dimensional distributions (`map_eq_iff_forall_finset_map_eval_eq`). Local
  statements: `MSSS.isPoissonRandomMeasure_of_void` and
  `MSSS.isPoissonRandomMeasure_iff_poisson_counts`, both `sorry`.

* **79. Mecke equation.** Let $\lambda$ be s-finite. A point process $\eta$ is Poisson with
  intensity $\lambda$ if and only if
  $$\mathbb E\int f(x,\eta)\,\eta(dx)=\int\mathbb E f(x,\eta+\delta_x)\,\lambda(dx)$$
  for every measurable $f:\mathbb X\times\mathbf N\to[0,\infty]$.

  *Assessment.* Partly covered. TauCeti proves the forward equation for finite intensity, in the representation by a Poisson number of independent points. Missing are the equation for $s$-finite intensity and the converse characterisation of the Poisson process.

  *Lean target.* `[IsProbabilityMeasure P]`, `[SFinite Λ]`, a measurable `η : Ω → Measure X` with
  `∀ ω, (η ω).IsIntegerValued` and `∀ ω, SFinite (η ω)`; conclusion
  `IsPoissonRandomMeasure P η Λ ↔ ∀ f : X → Measure X → ℝ≥0∞, Measurable (Function.uncurry f) →
  ∫⁻ ω, ∫⁻ x, f x (η ω) ∂η ω ∂P = ∫⁻ x, ∫⁻ ω, f x (η ω + Measure.dirac x) ∂P ∂Λ`. The lower
  integrals keep the identity meaningful when both sides are infinite. Forward direction: both
  sides depend only on the law `P.map η` (`IsPoissonRandomMeasure.identDistrib`), the finite case
  is `ProbabilityTheory.IndepFun.mecke_poissonMeasure_sample` with `finitePoissonLaw`, and the
  s-finite case follows by countable independent superposition (`isPoissonRandomMeasure_sum`);
  existence of a Poisson random measure for s-finite, not σ-finite, intensity (item 72) is not at
  the pins and is needed to realise that superposition. Converse: test functions
  `f x μ = 1_B x · h (μ B)` give the factorial moments of `η B` and the Laplace functional, then
  `isPoissonRandomMeasure_of_laplaceFunctional`. Local statement:
  `MSSS.isPoissonRandomMeasure_iff_mecke` (`sorry`); the forward identity for finite intensity is
  proved locally as `MSSS.lintegral_finitePoissonRandomMeasure_mecke`.

* **80. Multivariate Mecke equation.** If $\eta$ is Poisson with s-finite intensity
  $\lambda$ and $m\ge1$, then for every measurable $f\ge0$
  $$\mathbb E\int f(x_1,\dots,x_m,\eta)\,\eta^{(m)}(d(x_1,\dots,x_m))
  =\int\mathbb E f\bigl(x_1,\dots,x_m,\eta+\delta_{x_1}+\dots+\delta_{x_m}\bigr)\,
  \lambda^m(d(x_1,\dots,x_m)).$$
  In particular $\alpha_m=\lambda^m$; on $\mathbb R^d$ with intensity function $\rho$,
  $\rho^{(m)}(x_1,\dots,x_m)=\prod_i\rho(x_i)$, and $g(x,y)=1$ where $\rho(x)\rho(y)>0$.

  *Assessment.* TauCeti proves the combinatorial fixed-sample-size identity. The multivariate equation and the factorial moment measures are absent.

  *Lean target.* New definition: the factorial measure of an integer-valued s-finite measure,
  `Measure.factorialPower (μ : Measure X) (m : ℕ) : Measure (Fin m → X)`, the sum of Dirac masses at
  injectively indexed tuples of atoms counted with multiplicity, with its measurability in `μ`
  (Last–Penrose, Proposition 4.3). On a standard Borel space it can be built from TauCeti's
  measurable enumeration of atoms (`Measurable.exists_occurrence_enumeration_of_cover`,
  `IsIntegerValued.exists_eq_sum_dirac`), but no library defines it. At the pins the statement is
  made for the point presentation `η ω = MSSS.pointSum (I ω) (x ω)` with `MSSS.factorialPointSum m
  (I ω) (x ω)`. Hypotheses: `[IsProbabilityMeasure P]`, `[SFinite Λ]` (the local statement assumes
  `[SigmaFinite Λ]`, which is weaker than the source), `IsPoissonRandomMeasure P (fun ω ↦ pointSum
  (I ω) (x ω)) Λ`, `1 ≤ m`, `f : (Fin m → X) → Measure X → ℝ≥0∞` with `Measurable (Function.uncurry
  f)`; conclusion `∫⁻ ω, ∫⁻ y, f y (η ω) ∂factorialPointSum m (I ω) (x ω) ∂P = ∫⁻ y, ∫⁻ ω, f y (η ω
  + ∑ i, Measure.dirac (y i)) ∂P ∂Measure.pi (fun _ ↦ Λ)`. Corollary: `P.bind (fun ω ↦
  factorialPointSum m (I ω) (x ω)) = Measure.pi fun _ ↦ Λ` for every `m`, including `m = 0` (both
  sides are a Dirac mass). The product-density clause on `ℝ^d` is a separate statement with `Λ =
  volume.withDensity ρ`; the pair-correlation clause needs a definition of `g` with the convention
  `a/0 = 0` and is true only where `ρ x * ρ y ≠ 0`. Depends on item 79 (induction on `m`,
  Last–Penrose Theorem 4.4). TauCeti's `lintegral_finsetSum_dirac_pi_succ` is the fixed-sample-size
  step. Local statements: `MSSS.mecke_multivariate` and `MSSS.factorialMoment_poisson`, both
  `sorry`.

* **81. Poincaré inequality.** Let $\eta$ be Poisson with $\sigma$-finite intensity
  $\lambda$, and put $D_xf(\mu)=f(\mu+\delta_x)-f(\mu)$. If $\mathbb E f(\eta)^2<\infty$, then
  $$\mathop{\mathrm{Var}}f(\eta)\le\int\mathbb E\bigl(D_xf(\eta)\bigr)^2\lambda(dx),$$
  with equality for $f(\mu)=\mu(B)$, $\lambda(B)<\infty$.

  *Assessment.* Absent. The Gaussian Poincaré inequality in TauCeti is a different statement.

  *Lean target.* `[IsProbabilityMeasure P]`, `[SigmaFinite Λ]`, `IsPoissonRandomMeasure P η Λ`,
  measurable `f : Measure X → ℝ` with `MemLp (fun ω ↦ f (η ω)) 2 P`; conclusion `ENNReal.ofReal
  Var[fun ω ↦ f (η ω); P] ≤ ∫⁻ x, ∫⁻ ω, ENNReal.ofReal ((f (η ω + Measure.dirac x) - f (η ω)) ^ 2)
  ∂P ∂Λ`. The right side must be a lower integral: the difference operator need not be square
  integrable. New infrastructure: the difference operator `D x f μ = f (μ + δ_x) - f μ` and its
  iterates, and either the Fock-space isometry `E f(η)² = ∑ₙ ‖E Dⁿ f(η)‖²/n!` (Last–Penrose, Theorem
  18.6, p. 189), which rests on item 80; no library has either. The equality case for `f μ = μ B`,
  `Λ B < ∞`, is the Poisson variance; state it with `(η ω B).toReal`, which is almost surely finite.
  Local statements: `MSSS.poincare_poisson` (`sorry`) and the equality case
  `MSSS.variance_count_poisson` (proved).

### Temporal counting processes

[Synopsis](SYNOPSIS.md#temporal-counting-processes) · [Coverage](STRUCTURE.md#temporal-counting-processes).

Let $N$ be a simple locally finite point process on $(0,\infty)$, with
$N_t=N((0,t])$ finite at finite times and adapted to a right-continuous filtration
$(\mathcal F_t)_{t\ge0}$. A
**stochastic intensity** is a nonnegative predictable process $\lambda_t$ for which
$A_t=\int_0^t\lambda_s\,ds$ is finite at finite times almost surely and $N_t-A_t$ is a
local martingale. Here predictability means measurability for the $\sigma$-algebra
generated by the left-continuous adapted processes.

* **124. Martingale characterisation of Poisson counting processes.** Let $N$ be a
  simple locally finite point process on $(0,\infty)$ with $(\mathcal F_t)$-adapted
  counts $N_t=N((0,t])$ and $\mathbb E N_t<\infty$ at every finite $t$. Let $\nu$ be
  a diffuse locally finite measure on $[0,\infty)$. Then $N_t-\nu((0,t])$ is an
  $(\mathcal F_t)$-martingale if and only if each increment $N_t-N_s$, $0\le s<t$, is
  Poisson with parameter $\nu((s,t])$ and independent of $\mathcal F_s$. In particular
  a deterministic continuous compensator characterises a Poisson process.

  *Assessment.* Partly covered. TauCeti proves the martingale implication from independent
  Poisson increments of constant rate, and recognises a Poisson random measure on the half-line
  from independent Poisson count increments with a general locally finite intensity. The
  converse from the martingale condition and the martingale implication for a general
  deterministic diffuse mean measure are absent.

  *Lean target.* Carriers: a filtration `ℱ : MeasureTheory.Filtration ℝ≥0 mΩ`, a natural-valued
  count process `N : ℝ≥0 → Ω → ℕ` adapted to `ℱ` (`MeasureTheory.Adapted`), with every path
  nondecreasing, right-continuous, `N 0 = 0` and jumps of size at most one (simplicity), and
  `∀ t, Integrable (fun ω ↦ (N t ω : ℝ)) P`; a measure `ν` on `ℝ≥0` with
  `[IsLocallyFiniteMeasure ν]` and `[NoAtoms ν]`. Statement: `MeasureTheory.Martingale (fun t ω ↦
  (N t ω : ℝ) - (ν (Set.Ioc 0 t)).toReal) ℱ P ↔ ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
  (poissonMeasure (ν (Set.Ioc s t)).toNNReal) P ∧ ProbabilityTheory.Indep (MeasurableSpace.comap
  (fun ω ↦ N t ω - N s ω) inferInstance) (ℱ s) P`.
  The `toReal` and `toNNReal` are safe because `ν` is locally finite. The forward direction for
  `ν = r • volume` is TauCeti's `IsFilteredPoissonProcess.martingale_compensated`; the general
  forward direction is a short extension. The converse (Watanabe) needs the exponential formula
  for a counting process with continuous compensator, i.e. a pathwise Stieltjes calculus for
  `exp (i u N_t)` against the counting measure and optional stopping in continuous time; TauCeti
  has Stieltjes integrals (`TauCeti/Probability/Process/Stieltjes/`) but not this argument.
  Diffuseness of `ν` is essential: at an atom the jump of the compensator would have to be matched
  by jumps of size larger than one. TauCeti's `isPoissonRandomMeasure_iff_count_increments`
  converts the conclusion into `IsPoissonRandomMeasure` for the random measure of the path. No
  local declaration.

* **125. Time rescaling by a stochastic intensity.** Let $N$ be a simple locally finite
  point process on $(0,\infty)$ with adapted counts $N_t=N((0,t])$ and nonnegative
  predictable intensity $\lambda_t$ for a right-continuous filtration $(\mathcal F_t)$.
  Suppose $N_t-A_t$ is a local martingale and $A_t=\int_0^t\lambda_s\,ds$ is almost
  surely finite at finite times, strictly increasing and unbounded. For
  $\tau(u)=A^{-1}(u)$, the rescaled count $N_{\tau(u)}$ is a rate-one Poisson process
  relative to $(\mathcal F_{\tau(u)})_{u\ge0}$. If $T_n$ are the arrival times and
  $T_0=0$, the transformed gaps $A_{T_n}-A_{T_{n-1}}$ are independent standard
  exponential variables.

  *Assessment.* Mathlib supplies predictable processes and stopping times. TauCeti has the deterministic Poisson mapping and exponential interarrival laws. Rescaling by a random compensator and obtaining independence relative to the time-changed filtration are absent.

  *Lean target.* Carriers as for item 124, with a right-continuous filtration
  (`ℱ.rightCont = ℱ`, `MeasureTheory.Filtration.rightCont`) and an intensity
  `λ : ℝ≥0 → Ω → ℝ≥0` that is predictable (`MeasureTheory.IsStronglyPredictable ℱ λ`, measurable
  for `MeasureTheory.Filtration.predictable ℱ`). New definitions: the compensator
  `A t ω = ∫⁻ s in Set.Ioc 0 t, λ s ω` in `ℝ≥0∞`, and a predicate `IsLocalMartingale ℱ M P`
  (a sequence of stopping times `τₙ ↑ ∞` with every stopped process `MeasureTheory.stoppedProcess
  M τₙ` a martingale); neither library defines local martingales. Hypotheses: almost surely
  `A t ω < ∞` for all `t`, `t ↦ A t ω` strictly increasing with `A t ω → ∞`, and
  `IsLocalMartingale ℱ (fun t ω ↦ (N t ω : ℝ) - (A t ω).toReal) P`. With `τ u ω` the inverse of
  `A · ω` (each `τ u` an `ℱ`-stopping time, `MeasureTheory.IsStoppingTime`), conclusions:
  (a) the process `u ↦ N (τ u ω) ω` is a rate-one `TauCeti.Probability.IsFilteredPoissonProcess`
  for the time-changed filtration `u ↦ ℱ_{τ u}` (`MeasureTheory.IsStoppingTime.measurableSpace`);
  (b) the gaps `A_{T_n} - A_{T_{n-1}}` of the arrival times are i.i.d. `ProbabilityTheory.expMeasure
  1`. Part (b) follows from (a) and TauCeti's
  `isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_occurrenceGap`. Part (a) needs item 124
  (Watanabe) and optional sampling at continuous-time stopping times; Mathlib's optional sampling
  is for countable ranges only. No local declaration.

* **126. Likelihood of a counting process with predictable intensity.** For $0<T<\infty$
  let $P_0$ be the rate-one Poisson law on finite simple configurations in $(0,T]$ with
  their natural filtration. Let $\lambda_t$ be a predictable function of the
  configuration up to time $t$, with deterministic bounds $0<c\le\lambda_t\le C<\infty$.
  There is a unique law $P$ on this configuration space under which
  $N_t-\int_0^t\lambda_s\,ds$ is a martingale. Its likelihood relative to $P_0$ is
  $$\frac{dP}{dP_0}
    =\exp\!\left(\int_0^T(1-\lambda_t)\,dt\right)
       \prod_{t\in N\cap(0,T]}\lambda_t.$$

  *Assessment.* Mathlib supplies predictable processes, martingales, and changing the density of a measure. The predictable-intensity likelihood formula and its normalisation and uniqueness as a law on finite configurations are absent.

  *Lean target.* Carriers: the space of finite configurations in `(0,T]`, as `Measure ℝ≥0` with
  support in `Set.Ioc 0 T`, `IsIntegerValued` and finite, or as the canonical count paths; the
  rate-one Poisson law `P₀ = Measure.poissonLaw (volume.restrict (Set.Ioc 0 T))`; its natural
  filtration generated by `μ ↦ μ (Set.Ioc 0 s)`, `s ≤ t`. The intensity is a function `λ : ℝ≥0 →
  Measure ℝ≥0 → ℝ≥0`, predictable for that filtration, with constants `0 < c ≤ C` and `∀ t μ, c ≤ λ
  t μ ≤ C`. New definition: the likelihood `L μ`, the product of `ENNReal.ofReal (Real.exp (∫ t in
  Set.Ioc 0 T, (1 - λ t μ)))` and of `λ t μ` over the atoms `t` of `μ`, the latter written as `exp
  (∫ log (λ t μ) ∂μ)` or through a measurable enumeration of atoms
  (`Measurable.exists_occurrence_enumeration_of_cover`). Conclusions: (a) `∫⁻ μ, L μ ∂P₀ = 1`; (b)
  under `P = P₀.withDensity L`, the compensated count `μ (Set.Ioc 0 t) - ∫ s in Set.Ioc 0 t, λ s μ`
  is a martingale; (c) any probability measure on the configuration space with that martingale
  property equals `P₀.withDensity L`. The bounds make `L` bounded on configurations with a bounded
  number of points and keep `log λ` finite. (a)–(b) need the exponential martingale of a counting
  process (Stieltjes calculus, item 124's infrastructure); (c) needs uniqueness of the law given the
  compensator. Depends on item 124. No local declaration.

### Stationarity and Palm theory

[Synopsis](SYNOPSIS.md#stationarity-and-palm-theory) · [Coverage](STRUCTURE.md#stationarity-and-palm-theory).

For $y\in\mathbb R^d$ let $\theta_y\mu(B)=\mu(B+y)$. A point process $\eta$ on
$\mathbb R^d$ is **stationary** when $\theta_y\eta$ has the law of $\eta$ for every $y$; its
**intensity** is $\gamma=\mathbb E\eta([0,1]^d)$.

* **82. Stationary point processes.** (a) If $\eta$ is stationary with $\gamma<\infty$, its
  intensity measure is $\gamma$ times Lebesgue measure. (b) If moreover $\eta$ is locally
  square integrable, the reduced second factorial moment measure
  $\alpha_2^!(B)=\int\mathbf 1\{x\in[0,1]^d,\ y-x\in B\}\,\alpha_2(d(x,y))$ is locally finite
  and $\int f\,d\alpha_2=\iint f(x,x+y)\,\alpha_2^!(dy)\,dx$ for measurable $f\ge0$. (c) On
  $\mathbb R^d$ with $d\ge1$, a stationary Poisson process with finite intensity is mixing,
  hence ergodic. (d) If $\eta$ is stationary with finite intensity, $W$ is a compact convex
  set with nonempty interior, and $a_n\to\infty$, then $\eta(a_nW)/|a_nW|$ converges in
  $L^1$ to the conditional expectation
  of $\eta([0,1]^d)$ given the invariant $\sigma$-algebra, which is $\gamma$ when $\eta$ is
  ergodic.

  *Assessment.* Mathlib has uniqueness of Haar measure, which gives the form of a
  translation-invariant intensity, and general ergodic theorems. The reduced moment measure
  and the mixing and ergodicity theorem for Poisson processes on $\mathbb R^d$ with $d\ge1$
  are absent.

  *Lean target.* Carriers: `X = EuclideanSpace ℝ (Fin d)`, `η : Ω → Measure X` measurable,
  `MSSS.IsStationary P η`, `MSSS.intensity P η = ∫⁻ ω, η ω (MSSS.unitCube d) ∂P`, and
  `MSSS.reducedSecondMoment`. Four theorems. (a) `[IsProbabilityMeasure P]`, `MSSS.intensity P η <
  ∞`; conclusion `P.bind η = intensity P η • volume`, from Mathlib's
  `MeasureTheory.Measure.addHaarMeasure_unique` (the additive form of `haarMeasure_unique`); proved
  locally as `MSSS.intensityMeasure_stationary`. (b) For the point presentation `η ω = MSSS.pointSum
  (I ω) (x ω)` with `∫⁻ ω, η ω B ^ 2 ∂P < ∞` for bounded `B`: local finiteness of the reduced
  measure and the disintegration identity in `∫⁻`; proved locally as
  `MSSS.reducedSecondMoment_spec`. (c) `1 ≤ d` (essential: for `d = 0` every set of measures is
  shift-invariant and a Poisson count with positive mean is not almost surely constant), `γ < ∞`,
  `IsPoissonRandomMeasure P η (γ • volume)`; conclusions: mixing, `Tendsto (fun y ↦ P.map η (A ∩
  translate y ⁻¹' B)) (cocompact X) (𝓝 (P.map η A * P.map η B))` for measurable `A`, `B`, and
  ergodicity, every shift-invariant measurable `A` has `P.map η A ∈ {0, 1}`. A predicate for mixing
  or ergodicity of an `ℝ^d`-action is absent from both libraries (Mathlib's `Ergodic` is for a
  single map). (d) Mean ergodic theorem: `W` compact, convex, `(interior W).Nonempty`, `a n → ∞`; `η
  (a n • W) / volume (a n • W)` (as `toReal`, harmless since both are finite and the volume is
  positive for large `n`) converges in `L¹(P)` to `P[fun ω ↦ (η ω (unitCube d)).toReal |
  invariantSigma.comap η]`. This needs a multiparameter (`ℤ^d`) mean ergodic theorem, which neither
  library has; TauCeti's `tendsto_eLpNorm_birkhoffAverage_sub_condExp` is for one map. Local
  statements: `MSSS.poisson_mixing` (with `1 ≤ d`) and `MSSS.tendsto_count_div_volume` (`sorry`).

* **83. Palm distributions and the refined Campbell theorem.** Let $\eta$ be a stationary
  point process on $\mathbb R^d$ with intensity $\gamma\in(0,\infty)$. There is a unique
  probability measure $P^0$ on $\mathbf N$, the **Palm distribution**, such that
  $$\mathbb E\int f(x,\theta_x\eta)\,\eta(dx)=\gamma\int\!\!\int f(x,\mu)\,P^0(d\mu)\,dx$$
  for every measurable $f\ge0$, and $P^0(\mu\{0\}>0)=1$. In general, for a random measure
  with $\sigma$-finite intensity measure $M$ on a complete separable metric space there is a
  kernel $x\mapsto P_x$ of local Palm distributions, unique up to $M$-null sets, with
  $\mathbb E\int g(x,\xi)\,\xi(dx)=\iint g(x,\mu)\,P_x(d\mu)\,M(dx)$.

  *Assessment.* TauCeti has disintegration with a $\sigma$-finite first marginal, documented for Campbell measures and Palm kernels, and measurability of atom erasure. Campbell measures, Palm distributions, and the refined Campbell theorem are absent.

  *Lean target.* Two theorems. (i) Stationary Palm distribution: `η` measurable on
  `EuclideanSpace ℝ (Fin d)` with integer-valued realisations, `MSSS.IsStationary P η`,
  `0 < MSSS.intensity P η < ∞`; conclusion `∃! P₀ : Measure (Measure X), IsProbabilityMeasure P₀ ∧
  (∀ f, Measurable (Function.uncurry f) → ∫⁻ ω, ∫⁻ x, f x (MSSS.translate x (η ω)) ∂η ω ∂P =
  intensity P η * ∫⁻ x, ∫⁻ μ, f x μ ∂P₀ ∂volume) ∧ P₀ {μ | 0 < μ {0}} = 1`. Existence: define
  `P₀ A = (γ)⁻¹ ∫⁻ ω, ∫⁻ x in unitCube d, 1_A (translate x (η ω)) ∂η ω ∂P` and prove the identity
  by stationarity and the uniqueness of translation-invariant measures (as in item 82(a));
  measurability of `(x, μ) ↦ translate x μ` is needed. (ii) Local Palm kernel on a Polish space
  (`[PolishSpace X] [BorelSpace X]`), `[SigmaFinite (P.bind ξ)]`: a Markov kernel
  `Px : ProbabilityTheory.Kernel X (Measure X)` with `∫⁻ ω, ∫⁻ x, g x (ξ ω) ∂ξ ω ∂P =
  ∫⁻ x, ∫⁻ μ, g x μ ∂Px x ∂P.bind ξ`, unique `P.bind ξ`-a.e. TauCeti's
  `ProbabilityTheory.sigmaFiniteCondKernel` disintegrates the Campbell measure
  `C = P.bind (fun ω ↦ (ξ ω).map (fun x ↦ (x, ξ ω)))` on `X × Measure X`; since `Measure X` with the
  evaluation σ-algebra is not a standard Borel space, the local proof first codes the finite
  pieces of each realisation into one. Proved locally as
  `MSSS.exists_palmKernel` and `MSSS.palmKernel_ae_eq`; (i) is `MSSS.existsUnique_palm`
  (`sorry`). A Campbell-measure definition, `campbellMeasure P ξ : Measure (X × Measure X)`, would
  serve both parts and items 84, 127 and the Palm–Cox results.

* **84. Slivnyak–Mecke theorem.** A stationary point process $\eta$ on $\mathbb R^d$ with
  intensity in $(0,\infty)$ is Poisson if and only if its Palm distribution is the law of
  $\eta+\delta_0$. More generally, a point process with locally finite intensity measure $M$
  is Poisson if and only if $P_x$ is the law of $\eta+\delta_x$ for $M$-almost every $x$.

  *Assessment.* Absent. It needs item 83 and item 79 for $s$-finite intensity.

  *Lean target.* (i) Stationary form: hypotheses of item 83(i) and a probability `P₀` satisfying the
  refined Campbell identity; conclusion `IsPoissonRandomMeasure P η (intensity P η • volume) ↔ P₀ =
  P.map fun ω ↦ η ω + Measure.dirac 0`. (ii) General form: `[PolishSpace X] [BorelSpace X]`,
  integer-valued realisations, `[IsLocallyFiniteMeasure (P.bind η)]`, a Markov kernel `Px`
  satisfying the Campbell identity of item 83(ii); conclusion `IsPoissonRandomMeasure P η (P.bind η)
  ↔ ∀ᵐ x ∂P.bind η, Px x = P.map fun ω ↦ η ω + Measure.dirac x`. Both are statable at the pins.
  Proof route: (ii) is the Mecke characterisation of item 79 rewritten through the Palm kernel
  (uniqueness from 83(ii)); (i) follows from (ii) by stationarity. Depends on items 79, 83. Local
  statements: `MSSS.isPoissonRandomMeasure_iff_palm` and
  `MSSS.isPoissonRandomMeasure_iff_palmKernel` (`sorry`).

* **127. Palm inversion on the line.** Let $N$ be an almost surely nonempty stationary
  simple point process on $\mathbb R$ with intensity $\gamma\in(0,\infty)$ and Palm law
  $P^0$. Under $P^0$, let $T_1$ be the first point strictly to the right of $0$. Then
  $\mathbb E^0T_1=1/\gamma$ and for every nonnegative measurable function $f$ of the
  configuration,
  $$\mathbb E f(N)=\gamma\,\mathbb E^0\int_0^{T_1} f(\theta_tN)\,dt.$$
  Equivalently, bias the Palm law by the length of the next gap and shift the origin
  to a uniform location in that gap to obtain the stationary law.

  *Assessment.* TauCeti supplies sigma-finite disintegration for a Palm kernel. The Palm inversion formula and the gap-length-biased recovery of the stationary law are absent.

  *Lean target.* Carriers: `η : Ω → Measure ℝ` measurable, integer-valued, simple (`∀ x, η ω {x} ≤
  1`), locally finite, almost surely nonzero, stationary under `μ ↦ μ.map (· - t)`, with intensity
  `γ = ∫⁻ ω, η ω (Set.Ioc 0 1) ∂P ∈ (0, ∞)`, and its Palm law `P₀` from item 83(i) (for `d = 1`,
  transported from `EuclideanSpace ℝ (Fin 1)` or restated on `ℝ`). New definition: the first point
  after `0`, `T₁ μ = sInf {t | 0 < t ∧ 0 < μ {t}}` valued in `ℝ≥0∞` (or `WithTop ℝ`) so that the
  empty configuration does not give the junk value `0`; TauCeti's `Measure.occurrenceTime` on `ℝ≥0`
  is the model. Conclusions: `∫⁻ μ, T₁ μ ∂P₀ = γ⁻¹` and, for measurable `f : Measure ℝ → ℝ≥0∞`, `∫⁻
  ω, f (η ω) ∂P = γ * ∫⁻ μ, ∫⁻ t in Set.Ioo 0 (T₁ μ), f (μ.map (· - t)) ∂P₀`. The gap-length-biased
  recovery is a restatement and need not be a separate theorem. Needs item 83(i) and measurability
  of `T₁` and of the shift action; the proof is the refined Campbell identity applied to `f(x, θ_x
  μ) 1{x is the last point before 0}`-type tests, as in Brémaud, Theorem 7.3.4. No local
  declaration.

### Cox processes

[Synopsis](SYNOPSIS.md#cox-processes) · [Coverage](STRUCTURE.md#cox-processes).

A point process $\eta$ is a **Cox process directed by the random measure $\xi$** when,
conditionally on $\xi$, it is a Poisson process with intensity measure $\xi$.

* **85. Moments of Cox processes.** Let $\eta$ be a Cox process directed by $\xi$. (a) The
  factorial moment measures of $\eta$ are the moment measures of $\xi$,
  $\mathbb E\eta^{(m)}=\mathbb E\xi^m$; in particular $\eta$ and $\xi$ have the same intensity
  measure $\nu$. (b) For $u\in L^1(\nu)$, $\mathbb E\eta(u)^2<\infty$ if and only if
  $\mathbb E\xi(u)^2<\infty$ and $u\in L^2(\nu)$, and then
  $\mathop{\mathrm{Var}}\eta(u)=\nu(u^2)+\mathop{\mathrm{Var}}\xi(u)$. (c) Two Cox processes
  have the same law if and only if their directing measures do. (d) $\eta$ is a Cox
  process directed by $\xi$ if and only if
  $\mathbb E\int f(x,\eta,\xi)\,\eta(dx)=\mathbb E\int f(x,\eta+\delta_x,\xi)\,\xi(dx)$ for all
  measurable $f\ge0$. (e) On a Borel space, $\eta$ is almost surely simple if and only if
  $\xi$ is almost surely diffuse. (f) On $\mathbb R^d$ with $\xi(dx)=Z(x)\,dx$ and $Z(x)$
  square integrable, $\rho(x)=\mathbb E Z(x)$,
  $g(x,y)=\mathbb E[Z(x)Z(y)]/(\rho(x)\rho(y))$, and the void
  probability for a measurable set $B$ is $\mathbb E\exp(-\xi(B))$, where
  $\xi(B)=\int_B Z(x)\,dx$ is the extended nonnegative integral and $\exp(-\infty)=0$.

  *Assessment.* Mathlib and TauCeti supply integration of mixtures for nonnegative and
  integrable functions, respectively. TauCeti has the Poisson Laplace functional, a Poisson
  count law for sets of finite intensity, and almost surely infinite counts on sets of infinite
  intensity. The Cox process moment formulas and the void probability identity with random
  directing measure are absent.

  *Lean target.* Carrier: a predicate `IsCoxProcess P η ξ` for measurable `η ξ : Ω → Measure X`,
  saying that the joint law of `ξ` and the counts of `η` on finitely many disjoint measurable sets
  is the `ξ`-mixture of independent Poisson laws, with `Po(∞)` assigning mass `0` to every natural
  number; equivalently `P.map (fun ω ↦ (ξ ω, η ω)) = (P.map ξ) ⊗ₘ Πκ` for the kernel
  `Πκ μ = Measure.poissonLaw μ` (σ-finite `μ`), which is the cleaner form once the Poisson law is
  a measurable kernel in `μ`. Local definition: `MSSS.IsCoxProcess` (count form). Conjuncts as
  separate theorems, all with `[IsProbabilityMeasure P]`: (a) factorial moment measures,
  `P.bind (fun ω ↦ factorialPointSum m (I ω) (x ω)) = P.bind (fun ω ↦ Measure.pi fun _ : Fin m ↦
  ξ ω)` for the point presentation, with `∀ ω, SigmaFinite (ξ ω)`; (b) with `ν = P.bind ξ` and
  `Integrable u ν`, `MemLp (fun ω ↦ ∫ y, u y ∂η ω) 2 P ↔ MemLp (fun ω ↦ ∫ y, u y ∂ξ ω) 2 P ∧
  MemLp u 2 ν`, and then `Var[η(u)] = ∫ u² dν + Var[ξ(u)]` (the Bochner integrals `∫ y, u y ∂η ω`
  are almost surely of integrable functions, since `u ∈ L¹(ν)` and Campbell's formula); (c) equality
  of laws of `η`, `η'` iff equality of laws of `ξ`, `ξ'`, with integer-valued `η`, `η'` almost
  surely; (d) the Cox–Mecke characterisation with test functions `X → Measure X → Measure X →
  ℝ≥0∞`; (e) `[StandardBorelSpace X]`, `ξ` almost surely σ-finite: simplicity of `η` almost surely
  iff `ξ` almost surely has no atoms; (f) on `ℝ^d` with directing density
  `ξ ω = volume.withDensity fun y ↦ ENNReal.ofReal (Z y ω)`, `Z` jointly measurable, nonnegative,
  `MemLp (Z y) 2 P` for every `y`: the intensity, second factorial moment, and void probability
  `P {ω | η ω B = 0} = ∫⁻ ω, ENNReal.expNeg (∫⁻ y in B, ENNReal.ofReal (Z y ω)) ∂P` (an extended
  integral, so `exp(-∞) = 0` is built in). Ingredients at the pins: `Measure.bind`,
  `lintegral_bind`, `integral_bind`, `memLp_two_bind_iff`, `IsPoissonRandomMeasure.hasLaw`,
  `ae_eq_top`, and item 80 for (a). Local statements: `MSSS.factorialMoment_cox`,
  `MSSS.variance_cox`, `MSSS.map_eq_iff_cox`, `MSSS.isCoxProcess_iff_mecke`,
  `MSSS.simple_iff_diffuse_cox` (`sorry`), and `MSSS.moments_cox_density` (proved).

* **86. Log-Gaussian Cox processes.** Let $Y$ be a jointly measurable Gaussian field on
  $\mathbb R^d$ with mean $m$ and covariance $c$ such that $e^{Y}$ is almost surely locally
  integrable. An almost surely continuous modification can be used when it exists. The Cox
  process directed by $e^{Y(x)}dx$ has product densities
  $$\rho^{(n)}(x_1,\dots,x_n)=\exp\Bigl(\sum_im(x_i)+\tfrac12\sum_{i,j}c(x_i,x_j)\Bigr),$$
  so $\rho(x)=\exp(m(x)+c(x,x)/2)$ and $g(x,y)=\exp(c(x,y))$. Stationarity of $Y$ implies
  stationarity of the Cox process. If $Y$ has an almost surely continuous modification,
  stationarity of the process conversely implies stationarity of that modification.
  In the stationary continuous case with mean $\mu$, variance $\sigma^2>0$, and correlation
  $r$, one has $\rho=e^{\mu+\sigma^2/2}$ and $g(h)=e^{\sigma^2r(h)}$. The map
  $(\mu,\sigma^2,r)\mapsto(\rho,g)$ is injective, with $g(0)$ given by continuous extension.

  *Assessment.* The Gaussian moment generating function is available. The product-density
  formulas, the stationarity criterion for a continuous modification, and the identification
  of the parameters from the intensity and pair correlation are absent. They also use the Cox
  process theory in item 85 and Gaussian random fields in item 2.

  *Lean target.* Carriers: `Y : EuclideanSpace ℝ (Fin d) → Ω → ℝ` with
  `Measurable (Function.uncurry Y)` and `ProbabilityTheory.IsGaussianProcess Y P`, mean
  `m y = P[Y y]` and covariance `c y z = cov[Y y, Y z; P]`, local integrability
  `∀ᵐ ω ∂P, MeasureTheory.LocallyIntegrable (fun y ↦ Real.exp (Y y ω))`, and a Cox process `η`
  directed by `volume.withDensity fun y ↦ ENNReal.ofReal (Real.exp (Y y ω))` (item 85). Three
  theorems. (a) For every `n`, `P.bind (fun ω ↦ factorialPointSum n (I ω) (x ω)) =
  volume.withDensity fun z ↦ ENNReal.ofReal (Real.exp (∑ i, m (z i) + (1 / 2) * ∑ i, ∑ j,
  c (z i) (z j)))`; from (85a) and the Gaussian moment generating function. (b) Stationarity:
  constant mean and translation-invariant covariance imply `MSSS.IsStationary P η`; conversely,
  if `η` is stationary and `Y` has continuous sample paths (or `m`, `c` continuous), then `m` is
  constant and `c` translation invariant. Without continuity the converse is false: changing `Y`
  at one location to an independent Gaussian of another variance leaves the directing measure,
  hence the law of `η`, unchanged. (c) Injectivity of `(μ, σ², r) ↦ (e^{μ+σ²/2}, e^{σ² r})` for
  `σ² > 0`, `r 0 = 1`; elementary, proved locally as `MSSS.logGaussianCox_parameters_injective`.
  Depends on items 2 (Gaussian fields) and 85. Local statements:
  `MSSS.factorialMoment_logGaussianCox` and `MSSS.isStationary_logGaussianCox_iff` (`sorry`); the
  latter is stated as an equivalence under almost surely continuous sample paths of `Y`.

### Determinantal point processes

[Synopsis](SYNOPSIS.md#determinantal-point-processes) · [Coverage](STRUCTURE.md#determinantal-point-processes).

Let $\Lambda$ be a locally compact Polish space with a Radon measure $\mu$, and
$K:\Lambda^2\to\mathbb C$ measurable. A simple point process is **determinantal** with
kernel $K$ when its product densities with respect to $\mu$ are
$\rho^{(k)}(x_1,\dots,x_k)=\det(K(x_i,x_j))_{i,j\le k}$ for every $k\ge1$.

* **88. Basic properties.** Suppose $K$ is locally square integrable and its integral
  operator is Hermitian, nonnegative, and locally of trace class. Then there is at most one
  determinantal point process with kernel $K$; its counts on compact sets have exponential
  tails; its intensity is $K(x,x)$; and where $K(x,x)K(y,y)>0$ its pair correlation is
  $g(x,y)=1-|K(x,y)|^2/(K(x,x)K(y,y))\le1$. Independent $p$-thinning gives the determinantal
  process with kernel $\sqrt{p(x)}K(x,y)\sqrt{p(y)}$.

  *Assessment.* Absent. TauCeti defines the trace-class operator ideal on Hilbert spaces, but
  neither library defines integral operators of kernels, local trace class, or determinantal
  correlation functions.

  *Lean target.* Carriers: `X` with `[TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X]
  [BorelSpace X]`, `μ` with `[SigmaFinite μ] [IsLocallyFiniteMeasure μ]`, a kernel
  `K : X → X → ℂ`, and the point presentation `(I, x)`. Definition: `IsDeterminantal P I x K μ`,
  almost-sure simplicity together with `P.bind (fun ω ↦ factorialPointSum k (I ω) (x ω)) =
  (Measure.pi fun _ : Fin k ↦ μ).withDensity fun z ↦ ENNReal.ofReal (Matrix.det (Matrix.of
  fun i j ↦ K (z i) (z j))).re` for every `k ≥ 1` (local `MSSS.IsDeterminantal`). The operator
  hypotheses are best expressed through the integral operator `T_K : L²(μ) →L[ℂ] L²(μ)`, which no
  library defines: Hermitian, nonnegative, and `T_{1_D K 1_D}` trace class for compact `D`
  (`TauCeti.OperatorIdealFamily.traceClass`, or `ContinuousLinearMap.nuclearENorm (T_{K,D}) < ∞`);
  the local `MSSS.IsAdmissibleKernel` replaces these by quadratic-form conditions on bounded
  compactly supported test functions and `∫⁻ y in D, ‖K y y‖ₑ ∂μ < ∞`. Conjuncts: uniqueness of the
  law (`MSSS.map_eq_determinantalLaw`, `sorry`; it needs determination of a law by factorial
  moment measures under a growth bound, Last–Penrose Proposition 4.12, absent); exponential
  moments `∫⁻ ω, ENNReal.ofReal (Real.exp (c * (η ω D).toReal)) ∂P < ∞` for compact `D` and some
  `c > 0` (`MSSS.exponential_tail_determinantal`, `sorry`; it needs Hadamard's inequality for the
  determinants); intensity `μ.withDensity fun y ↦ ENNReal.ofReal (K y y).re`
  (`MSSS.intensity_determinantal`, proved); the pair-correlation identity where
  `0 < (K y y).re * (K z z).re` (`MSSS.pairCorrelation_determinantal`, proved); and `p`-thinning
  with uniform marks independent of the points (`MSSS.isDeterminantal_thinning`, proved).

* **89. Macchi–Soshnikov theorem.** Let $K$ be a kernel whose integral operator on
  $L^2(\Lambda,\mu)$ is Hermitian and locally of trace class, with $K$ equal on the diagonal to
  the version given by the spectral expansion. A determinantal point process with kernel $K$
  exists if and only if the spectrum of the operator is contained in $[0,1]$.

  *Assessment.* Mathlib and TauCeti have the spectral theorem for compact self-adjoint
  operators, and TauCeti has the trace-class ideal. Integral operators of kernels, the trace
  functional, and the Macchi–Soshnikov theorem are absent.

  *Lean target.* Carriers as for item 88, with the integral operator `T_K` on
  `MeasureTheory.Lp ℂ 2 μ` (new: a bounded operator built from a locally square-integrable kernel,
  with its restrictions `T_{K,D}` to compact `D`), self-adjointness (`IsSelfAdjoint`), and local
  trace class through `TauCeti.OperatorIdealFamily.traceClass`. Statement: if `T_K` is
  self-adjoint and locally trace class and `K` agrees on the diagonal with the spectral version
  (for example, `K` continuous), then `(∃ Q : Measure ((ℕ → Bool) × (ℕ → X)), IsProbabilityMeasure
  Q ∧ IsDeterminantal Q Prod.fst Prod.snd K μ) ↔ spectrum ℂ T_K ⊆ Set.Icc 0 1` (Mathlib
  `spectrum`). The local `MSSS.exists_determinantal_iff` (`sorry`) states the spectral condition as
  `0 ≤ Re⟨f, T_K f⟩ ≤ ‖f‖²` on bounded measurable compactly supported `f`, which is equivalent
  because such `f` are dense in `L²(μ)`. Infrastructure needed: integral operators of kernels,
  Mercer's theorem for continuous nonnegative kernels on compact sets (the spectral version of the
  diagonal), the trace of a trace-class operator (not at the pins), and the construction of the
  process for finite-rank projection kernels; the "only if" direction uses item 90's eigenvalue
  representation. Depends on items 88, 90.

* **90. Number of points.** Let the kernel be Hermitian of trace class,
  $K(x,y)=\sum_k\lambda_k\varphi_k(x)\overline{\varphi_k(y)}$ with orthonormal $\varphi_k$ and
  $\lambda_k\in[0,1]$, and let $I_k$ be independent Bernoulli($\lambda_k$) variables. The
  process is a mixture over $I$ of the determinantal projection processes with kernels
  $\sum_kI_k\varphi_k(x)\overline{\varphi_k(y)}$. In particular the total number of points has
  the law of $\sum_kI_k$, with mean $\sum_k\lambda_k$, variance $\sum_k\lambda_k(1-\lambda_k)$,
  and void probability $\prod_k(1-\lambda_k)$. Applied to the restriction to a compact $D$,
  this gives the law of $X(D)$ in terms of the eigenvalues of $K$ on $D$.

  *Assessment.* Mathlib and TauCeti have eigenbasis expansions and variances of sums of independent variables. The representation of the number of points as a sum of independent Bernoulli variables is absent.

  *Lean target.* Carriers: an orthonormal family `φ : ℕ → X → ℂ` in `L²(μ)` (`MemLp (φ k) 2 μ` and
  `∫ y, conj (φ k y) * φ l y ∂μ = if k = l then 1 else 0`), eigenvalues `ls : ℕ → ℝ` in `[0, 1]`
  with `Summable ls`, and `K y z = ∑' k, ls k * φ k y * conj (φ k z)`; the series converges
  absolutely for `μ ⊗ μ`-almost every `(y, z)`, and `tsum` gives the junk value `0` elsewhere, which
  is harmless because only densities enter. Independent Bernoulli variables are realised as `I k =
  1{U k < ls k}` with `U` distributed as `Measure.infinitePi fun _ ↦ (volume : Measure
  unitInterval)`. Statements: the law of the process is the mixture over `U` of the projection laws
  with kernels `∑' k, I k * φ k y * conj (φ k z)`; the total count `η ω Set.univ` has the law of `∑'
  k, (I k : ℝ≥0∞)`, mean `∑' k, ls k`, variance `∑' k, ls k * (1 - ls k)`, and void probability
  `ENNReal.ofReal (∏' k, (1 - ls k))`. The count is almost surely finite (Borel–Cantelli, since `∑
  ls k < ∞`), so `toReal` in the mean and variance is safe. Infrastructure: existence and the point
  count of determinantal projection processes of finite rank (Hough–Krishnapur–Peres–Virág, Lemma
  4.5.1), the Cauchy–Binet expansion (TauCeti `Matrix.det_mul_eq_sum_prod_mul_det_submatrix`), and
  uniqueness from item 88. Local statements: `MSSS.determinantal_mixture` and
  `MSSS.count_determinantal` (`sorry`).

## 5. Gibbs point processes and statistics of point patterns

Selected: 15 statements. [Synopsis part](SYNOPSIS.md#5-gibbs-point-processes-and-statistics-of-point-patterns) · [Coverage part](STRUCTURE.md#5-gibbs-point-processes-and-statistics-of-point-patterns).

Let $d\ge1$ and let $W\subset\mathbb R^d$ be a bounded Borel set with $0<|W|<\infty$, $N_f$ the
set of finite subsets of $W$, $\Pi_W$ the law of the unit-rate Poisson process on $W$, and
$n(\mathbf x)$ the number of points of $\mathbf x\in N_f$. A point process $X$ on $W$ has
**density** $f:N_f\to[0,\infty)$ when
$$\mathbb P(X\in F)=\sum_{n\ge0}\frac{e^{-|W|}}{n!}\int_{W^n}\mathbf 1[\{x_1,\dots,x_n\}\in F]\,
f(\{x_1,\dots,x_n\})\,dx_1\cdots dx_n$$
for measurable $F\subseteq N_f$. A function $h:N_f\to[0,\infty)$ is **hereditary** when
$h(\mathbf x)>0$ and $\mathbf y\subseteq\mathbf x$ imply $h(\mathbf y)>0$. The **Papangelou
conditional intensity** of $f$ is $\lambda^\ast(\mathbf x,\xi)=f(\mathbf x\cup\{\xi\})/f(\mathbf x)$
for $\xi\notin\mathbf x$, with $\lambda^\ast=0$ when $f(\mathbf x)=0$.

### Densities, conditional intensities, and Markov point processes

[Synopsis](SYNOPSIS.md#densities-conditional-intensities-and-markov-point-processes) · [Coverage](STRUCTURE.md#densities-conditional-intensities-and-markov-point-processes).

* **94. Stability and normalisability.** Let $\phi^\ast:W\to[0,\infty)$ be integrable. A
  function $h$ is **locally stable** when $h(\mathbf x\cup\{\xi\})\le\phi^\ast(\xi)h(\mathbf x)$
  for all $\mathbf x$ and $\xi\notin\mathbf x$, and **Ruelle stable** when
  $h(\mathbf x)\le\alpha\prod_{\xi\in\mathbf x}\phi^\ast(\xi)$ for some $\alpha>0$. Local
  stability implies Ruelle stability and heredity, and gives $\lambda^\ast\le\phi^\ast$.
  Ruelle stability implies $\int h\,d\Pi_W<\infty$; for $\phi^\ast\equiv\beta$ the bound is
  $\int h\,d\Pi_W\le h(\emptyset)e^{(\beta-1)|W|}$ when $h$ is locally stable. A locally stable
  $h$ with $h(\emptyset)>0$ is therefore proportional to a probability density.

  *Assessment.* TauCeti's series for the finite Poisson law and its Laplace functional give the bound $\int\beta^{n}\,d\Pi_W=e^{(\beta-1)|W|}$ by a computation. Local and Ruelle stability and the resulting normalisability are absent, as is the configuration space of finite subsets of $W$.

  *Lean target.* Configurations are `Finset E` over a measure space `E` (in practice
  `EuclideanSpace ℝ (Fin d)` with `volume`), and the window is `W : Set E` with `MeasurableSet W`
  and `volume W < ∞`. The reference integral is the `ℝ≥0∞`-valued series
  `∫ h dΠ_W = ∑' n, e^{-|W|}/n! ∫⁻_{W^n} h({x_1,…,x_n})`, a definition `poissonIntegral W h` with
  `h : Finset E → ℝ≥0∞`, together with a predicate `IsConfigMeasurable h` (measurability of
  `x ↦ h(toConfig x)` on `Fin n → E` for every `n`); neither library has a measurable space on
  `Finset E`. The upstream bridge is TauCeti's `TauCeti.Probability.finitePoissonLaw` with `r = |W|`
  and `Q` the normalised restriction of `volume` to `W`, via `lintegral_finitePoissonLaw`, after
  sending a tuple to its counting measure; this needs the diagonal to be null,
  `[NoAtoms (volume.restrict W)]`. New definitions: `IsLocallyStable W φ h`
  (`h(x ∪ {ξ}) ≤ φ ξ * h x` for `x ⊆ W`, `ξ ∈ W \ x`) and `IsRuelleStable W φ h`
  (`∃ α > 0, ∀ x ⊆ W, h x ≤ α * ∏ ξ ∈ x, φ ξ`), for `φ : E → ℝ` with `0 ≤ φ` and `IntegrableOn φ W`.
  Separate theorems: (a) local stability implies heredity and `papangelou h x ξ ≤ φ ξ` on `W`; (b)
  local stability implies Ruelle stability, with no condition on `h ∅` (take `α = max (h ∅) 1`); (c)
  Ruelle stability gives `poissonIntegral W (ofReal ∘ h) < ∞`; (d) for `φ ≡ β` the bound
  `poissonIntegral W (ofReal ∘ h) ≤ ofReal (h ∅) * ofReal (exp ((β - 1) * (volume W).toReal))`; (e)
  `0 < h ∅` gives `0 < poissonIntegral W (ofReal ∘ h)`. The Papangelou quotient needs the explicit
  branch `λ* = 0` where `h x = 0`, not Lean's `x / 0 = 0` alone, so that the definition is readable.
  Everything is statable at the pins, with no dependency on other entries. In
  `MSSS/GibbsPointProcesses/Finite/Reference.lean`, `MSSS.isLocallyStable_consequences` ((a) and
  (b)), `MSSS.poissonIntegral_lt_top_of_ruelle`,
  `MSSS.poissonIntegral_le_of_locallyStable_const`, and `MSSS.normalisable_of_locallyStable` are
  proved.

* **95. Georgii–Nguyen–Zessin formula.** If $X$ has a hereditary density with conditional
  intensity $\lambda^\ast$, then for every measurable $h\ge0$
  $$\mathbb E\sum_{\xi\in X}h(\xi,X\setminus\{\xi\})=\int_W\mathbb E\bigl[h(\xi,X)\,\lambda^\ast(X,\xi)\bigr]\,d\xi .$$
  Conversely, let $H$ be a non-degenerate, hereditary, stable energy (item 99), $z>0$,
  $\beta\ge0$, and $\Lambda$ bounded with $|\Lambda|>0$. A probability measure $P$ on finite
  configurations in $\Lambda$ satisfies the formula with
  $\lambda^\ast(\mathbf x,\xi)=ze^{-\beta(H(\mathbf x\cup\{\xi\})-H(\mathbf x))}$ for all $h$
  if and only if $P$ is the Gibbs measure $P^{z,\beta}_\Lambda$ of item 99. For
  $\lambda^\ast=\rho$ the formula is the Mecke equation, item 79.

  *Assessment.* Partly covered. The Poisson case is TauCeti's Mecke equation for finite intensity. The formula for hereditary densities and the converse characterisation of finite-volume Gibbs measures are absent.

  *Lean target.* Carriers as in item 94, with a random configuration `X : Ω → Finset E` on a
  probability space `(Ω, P)`. The density statement is a predicate `HasConfigDensity P X W f`:
  `X ω ⊆ W` for all `ω`, and `∫⁻ ω, h (X ω) ∂P = poissonIntegral W (h · ofReal ∘ f)` for every
  configuration-measurable `h : Finset E → ℝ≥0∞`. The forward formula is stated with `∫⁻` and
  `h : E → Finset E → ℝ≥0∞` jointly measurable on `E × (Fin n → E)` for each `n`:
  `∫⁻ ω, ∑ ξ ∈ X ω, h ξ ((X ω).erase ξ) ∂P` equals
  `∫⁻ ξ in W, ∫⁻ ω, h ξ (X ω) * ofReal (papangelou f (X ω) ξ) ∂P`, under `0 ≤ f`,
  `IsConfigMeasurable f`, `IsHereditary f`, `volume W < ∞`, and a diffuse `volume.restrict W`
  (tuples with a repeated point are null). The converse needs energies `H : Finset E → WithTop ℝ`
  with predicates `IsNonDegenerate`, `IsHereditaryEnergy`, `IsStableEnergy`
  (`∃ A, ∀ x, A * x.card ≤ H x`), a measurability predicate for `H` and for `{H = ⊤}`, the local
  energy with `⊤ - ⊤ = 0`, and the weight `e^{-β H}` of the convention preceding item 99, which must
  read `1` at `β = 0` also where `H = ⊤`. It is then an `↔` between
  `HasConfigDensity P X Λ (gibbsDensity Λ z β H)` and the formula for all `h`, with `0 < z`,
  `0 ≤ β`, `0 < volume Λ < ∞`, and `X` measurable in the sense that `ω ↦ h (X ω)` is measurable for
  configuration-measurable `h`. The Poisson case should be derived from TauCeti's
  `ProbabilityTheory.IndepFun.mecke_poissonMeasure_sample`, which works with counting measures and
  multiplicities, through an almost-sure simplicity lemma for diffuse `Q`. Statable at the pins; the
  converse depends on item 99 for `0 < Z < ∞`. In `MSSS/GibbsPointProcesses/`,
  `MSSS.georgii_nguyen_zessin` (`Finite/Reference.lean`) is proved, and
  `MSSS.hasConfigDensity_gibbs_iff_gnz` (`Finite.lean`) is `sorry`. Its weight `MSSS.gibbsWeight`
  follows the convention: `0` on `{H = ⊤}` for `β ≠ 0` and `1` at `β = 0`.

Let $\sim$ be a reflexive symmetric relation on $W$. A **clique** is a configuration whose
points are pairwise related; $\emptyset$ and singletons are cliques. A hereditary
$h:N_f\to[0,\infty)$ is a **Markov function** when, for $h(\mathbf x)>0$ and
$\xi\notin\mathbf x$, the ratio $h(\mathbf x\cup\{\xi\})/h(\mathbf x)$ depends on $\mathbf x$
only through $\{\eta\in\mathbf x:\eta\sim\xi\}$.

* **97. Hammersley–Clifford–Ripley–Kelly theorem.** A hereditary $h$ is a Markov function if
  and only if there is $\phi:N_f\to[0,\infty)$ with $\phi(\mathbf y)=1$ whenever $\mathbf y$
  is not a clique, such that
  $$h(\mathbf x)=\prod_{\mathbf y\subseteq\mathbf x}\phi(\mathbf y)\qquad(\mathbf x\in N_f).$$
  Then $\lambda^\ast(\mathbf x,\xi)=\prod_{\mathbf y\subseteq\mathbf x}\phi(\mathbf y\cup\{\xi\})$ for
  $h(\mathbf x)>0$. If $X$ has a Markov density and $A,B\subseteq W$ are Borel sets such that
  no point of $A$ is related to a point of $B$, then $X_A$ and $X_B$ are conditionally independent
  given $X_{W\setminus(A\cup B)}$. The theorem uses no structure of $W$ beyond the
  relation.

  *Assessment.* Mathlib has Möbius inversion. Markov functions, the clique factorisation, and the spatial Markov property are absent.

  *Lean target.* The theorem is combinatorial: a type `W` (the window as a subtype, or any type, by
  Remark 6.3 of Møller–Waagepetersen), a relation `r : W → W → Prop` with `[DecidableRel r]`,
  reflexive and symmetric, and `h : Finset W → ℝ` with `0 ≤ h`. New definitions:
  `IsConfigClique r y` (`∀ ξ ∈ y, ∀ η ∈ y, r ξ η`) and `IsMarkovFunction r h` (hereditary, and for
  `h x > 0`, `h x' > 0`, `ξ ∉ x ∪ x'` with `x.filter (r ξ) = x'.filter (r ξ)` the ratios
  `h (insert ξ x) / h x` and `h (insert ξ x') / h x'` agree). Conjuncts: (a) `IsMarkovFunction r h`
  holds if and only if there is `φ : Finset W → ℝ` with `0 ≤ φ`, `φ y = 1` whenever
  `¬ IsConfigClique r y`, and `h x = ∏ y ∈ x.powerset, φ y` for all `x`; (b) for `h x > 0` and
  `ξ ∉ x`, `papangelou h x ξ = ∏ y ∈ x.powerset, φ (insert ξ y)`; (c) uniqueness of `φ` on
  `{h > 0}`; (d) the spatial Markov property for Borel `A, B ⊆ W` with no related pair: first the
  factorisation `f x = g (x ∩ (A ∪ C)) * k (x ∩ (B ∪ C))`, `C = W \ (A ∪ B)`, then
  `ProbabilityTheory.CondIndepFun` of `X ∩ A` and `X ∩ B` given `X ∩ C`. (a)–(c) need no measure
  theory and are statable at the pins. (d) needs a measurable space on finite configurations, which
  neither library has; the counting σ-algebra generated by `x ↦ #(x ∩ B)`, or TauCeti's
  random-measure carrier `Ω → Measure E`, with Mathlib's measurable space on `Measure E`, supplies
  one. It also needs the independence of the restrictions of the unit-rate Poisson process to
  disjoint sets (Part 4). In `MSSS/GibbsPointProcesses/Finite.lean`, `MSSS.isMarkovFunction_iff`,
  `MSSS.papangelou_markov`, and `MSSS.markov_density_factorization` (the factorisation form of (d))
  are proved; the conditional-independence form and (c) are not stated.

* **98. Strauss process.** For $\beta>0$, $R>0$, $\gamma\ge0$, and
  $s_R(\mathbf x)=\#\{\{\xi,\eta\}\subseteq\mathbf x:\|\xi-\eta\|\le R\}$, let
  $h(\mathbf x)=\beta^{n(\mathbf x)}\gamma^{s_R(\mathbf x)}$ with $0^0=1$. If $\gamma\le1$, $h$ is
  locally stable with $\phi^\ast\equiv\beta$, hence normalisable, and Markov for the relation
  $\|\xi-\eta\|\le R$. For $h(\mathbf x)>0$ and $\xi\notin\mathbf x$, the conditional intensity
  is $\lambda^\ast(\mathbf x,\xi)=\beta\gamma^{\#\{\eta\in\mathbf x:\|\xi-\eta\|\le R\}}$.
  The case $\gamma=1$ gives the Poisson process of intensity $\beta$ on $W$ and $\gamma=0$
  gives a hard-core process. If $\gamma>1$, then $\int h\,d\Pi_W=\infty$. For a fixed number
  $n$ of points, the Strauss weight on $W^n$ is integrable for every $\gamma\ge0$. It can be
  normalised for $\gamma>0$, and for $\gamma=0$ exactly when the set of $n$-tuples in $W^n$
  with all pairwise distances greater than $R$ has positive Lebesgue measure.

  *Assessment.* Absent, including fixed-count integrability and the normalisation
  criterion for the continuum hard-core case. TauCeti has a discrete hard-core law on a
  finite graph.

  *Lean target.* Carriers as in items 94 and 97, with `E` a real normed space (in practice
  `EuclideanSpace ℝ (Fin d)`), `[SeparableSpace E]`, `[BorelSpace E]`. New definition:
  `straussDensity β γ R x = β ^ x.card * γ ^ s_R x`, with `s_R x` the number of unordered pairs of
  `x` at distance `≤ R` (`(x.offDiag.filter …).card / 2`); Lean's `0 ^ 0 = 1` is the convention of
  the entry. Separate theorems, with `0 < β`, `0 < R`, `0 ≤ γ`, and `volume W < ∞`: (a) for `γ ≤ 1`,
  `IsLocallyStable W (fun _ ↦ β) (straussDensity β γ R)`, `poissonIntegral W … < ∞`,
  `IsMarkovFunction (fun ξ η ↦ ‖ξ - η‖ ≤ R) …`, and
  `papangelou (straussDensity β γ R) x ξ = β * γ ^ #{η ∈ x | ‖ξ - η‖ ≤ R}` for `h x > 0`, `ξ ∉ x`;
  (b) for `γ = 1`, `straussDensity β 1 R` is the Poisson density of item 92 up to the constant
  `e^{|W| - β|W|}`; (c) for `1 < γ`, `MeasurableSet W`, `0 < volume W`, and diffuse
  `volume.restrict W`, `poissonIntegral W … = ⊤` (an `ℝ≥0∞` statement); (d) for each `n`,
  `∫⁻ x in Set.pi univ (fun _ : Fin n ↦ W), ofReal (straussDensity β γ R (toConfig x)) < ⊤`; (e) for
  `0 < γ` that integral is positive when `0 < volume W`, and for `γ = 0` it is positive if and only
  if `volume {x ∈ W^n | ∀ i ≠ j, R < ‖x i - x j‖} > 0`. Note that `toConfig` collapses repeated
  coordinates, which is harmless only on a diffuse window. Statable at the pins; depends on items 94
  and 97. In `MSSS/GibbsPointProcesses/Finite.lean`, `MSSS.strauss_properties` ((a)),
  `MSSS.strauss_not_normalisable` ((c)), and `MSSS.strauss_fixed_number_integrable` ((d)) are
  proved; (b) and (e) are not stated.

### Gibbs point processes

[Synopsis](SYNOPSIS.md#gibbs-point-processes) · [Coverage](STRUCTURE.md#gibbs-point-processes).

An **energy** is a function $H:N_f\to\mathbb R\cup\{+\infty\}$. It is **non-degenerate** when
$H(\emptyset)<\infty$, **hereditary** when $H(\mathbf x)<\infty$ implies
$H(\mathbf x\setminus\{\xi\})<\infty$, and **stable** when $H(\mathbf x)\ge A\,n(\mathbf x)$
for a constant $A$. For bounded $\Lambda$, $z>0$, and $\beta\ge0$, the **finite-volume Gibbs
measure** is $P^{z,\beta}_\Lambda=Z^{-1}z^{n(\cdot)}e^{-\beta H}\Pi_\Lambda$; its conditional
intensity is $z\,e^{-\beta h(\xi,\mathbf x)}$ with local energy
$h(\xi,\mathbf x)=H(\mathbf x\cup\{\xi\})-H(\mathbf x)$, using $(+\infty)-(+\infty)=0$.
The weight $e^{-\beta H}$ is $0$ where $H=+\infty$ and $\beta>0$, and $e^{-0\cdot H}=1$, so
that $P^{z,0}_\Lambda$ is the Poisson process of intensity $z$ on $\Lambda$.

* **99. Finite-volume Gibbs measures.** For a non-degenerate, hereditary, stable energy,
  $0<Z<\infty$. For $\Delta\subseteq\Lambda$ with $|\Delta|>0$ and
  $H_\Delta(\mathbf x)=H(\mathbf x)-H(\mathbf x\cap\Delta^c)$, the DLR equation
  $$P^{z,\beta}_\Lambda(d\mathbf x_\Delta\mid\mathbf x_{\Delta^c})
  =Z_\Delta(\mathbf x_{\Delta^c})^{-1}z^{n(\mathbf x_\Delta)}e^{-\beta H_\Delta(\mathbf x)}\,
  \Pi_\Delta(d\mathbf x_\Delta)$$
  holds almost surely. $P^{z,\beta}_\Lambda$ is the unique minimiser of
  $\beta\,\mathbb E_PH-\log z\,\mathbb E_Pn(\cdot)+I(P\mid\Pi_\Lambda)$ among probability measures
  with finite intensity, $I$ the relative entropy, and the minimum is
  $-\log Z$. For finite-valued stable $H$ and $z>0$,
  $\frac{d}{dz}\mathbb E\,n=\mathop{\mathrm{Var}}(n)/z$ at $\beta\ge0$, and
  $\frac{d}{d\beta}\mathbb E H=-\mathop{\mathrm{Var}}(H)$ at $\beta>0$.

  *Assessment.* TauCeti proves the abstract identity $\mathrm{KL}(\mu\,\|\,Z^{-1}e^{-f}\nu)-\log Z=\int f\,d\mu+\mathrm{KL}(\mu\,\|\,\nu)$ for nonnegative $f$, and Mathlib the derivatives of cumulant generating functions. Missing are energies with the value $+\infty$, finiteness of $Z$ under stability, the DLR equation, and the setting of finite configurations with the Poisson reference measure.

  *Lean target.* Carriers as in item 95. New definitions: `partitionFunction Λ z β H : ℝ≥0∞` (the
  `poissonIntegral` of `z ^ x.card * e^{-β H x}`), `gibbsDensity Λ z β H` (its normalisation, a real
  function used only when `0 < Z < ⊤`, since `toReal ⊤ = 0`), and the local Hamiltonian
  `H_Δ x = H x - H (x.filter (· ∉ Δ))` with `⊤ - ⊤ = 0`. Separate theorems: (a)
  `0 < partitionFunction Λ z β H ∧ partitionFunction Λ z β H < ⊤` for `0 < z`, `0 ≤ β`,
  `volume Λ < ∞` and a non-degenerate, hereditary, stable `H`; (b) the DLR equation for measurable
  `Δ ⊆ Λ` with `0 < volume Δ`, stated as an identity of iterated `∫⁻`: for configuration-measurable
  `F ≥ 0`, `∫⁻ F dP^{z,β}_Λ` equals the integral over the exterior configuration of the normalised
  integral against `poissonIntegral Δ` of `F(y ∪ x_{Λ\Δ}) z^{#y} e^{-β H_Δ(y ∪ x_{Λ\Δ})}`; this
  avoids conditional distributions on configuration spaces, which have no measurable structure
  upstream, and needs the product decomposition `Π_Λ = Π_Δ ⊗ Π_{Λ\Δ}` of the Poisson series; (c) the
  variational principle with TauCeti's `TauCeti.klDiv_tilted_neg_add_ofReal_neg_log` and Mathlib's
  `InformationTheory.klDiv` and `InformationTheory.klDiv_eq_zero_iff` once the laws are measures on
  a measurable carrier (TauCeti's counting-measure configurations):
  `β E_P H - log z E_P n + I(P | Π_Λ) ≥ -log Z` among `P` with `E_P n < ∞`, equality iff
  `P = P^{z,β}_Λ`, stated in `EReal` or with `I` in `ℝ≥0∞` and the convention of item 95 at `β = 0`,
  because `E_P H` can be `+∞`; (d) for finite-valued stable `H`,
  `HasDerivAt (fun z ↦ E n) (Var n / z) z` for `0 < z` and `HasDerivAt (fun β ↦ E H) (-Var H) β` for
  `0 < β`, from Mathlib's `ProbabilityTheory.deriv_cgf` and
  `ProbabilityTheory.iteratedDeriv_two_cgf` after writing the Gibbs law as a tilted Poisson law
  (`MeasureTheory.Measure.tilted`). Statable at the pins except that (c) needs the bridge between
  finite-set densities and laws on a measurable configuration space. In
  `MSSS/GibbsPointProcesses/Finite.lean`, `MSSS.partitionFunction_pos_lt_top`,
  `MSSS.hasDerivAt_gibbs_meanCount`, and `MSSS.hasDerivAt_gibbs_meanEnergy` (for nonnegative `H`)
  are proved; `MSSS.gibbs_dlr` and `MSSS.gibbs_variational` (for real-valued `H`) are `sorry`.

* **100. Infinite-volume Gibbs point processes.** Let $H$ be a non-degenerate, hereditary,
  stable, translation-invariant energy of finite range $R$. A stationary probability measure
  on locally finite configurations in $\mathbb R^d$ is an **infinite-volume Gibbs measure**
  when the DLR equations of item 99 hold for every bounded $\Delta$ with $|\Delta|>0$. For all
  $z>0$ and $\beta\ge0$ an infinite-volume Gibbs measure exists: the stationarised measures
  $\bar P^{z,\beta}_{[-n,n]^d}$ are tight in the topology of local convergence, and each of
  their accumulation points is one. A stationary probability measure $P$ is an
  infinite-volume Gibbs measure for $(z,\beta,H)$ if and only if
  $$\int\sum_{\xi\in\mathbf x}f(\xi,\mathbf x\setminus\{\xi\})\,P(d\mathbf x)
  =z\int\!\!\int_{\mathbb R^d}f(\xi,\mathbf x)e^{-\beta h(\xi,\mathbf x)}\,d\xi\,P(d\mathbf x)$$
  for every measurable $f\ge0$.

  *Assessment.* Absent. Neither library has the space of locally finite configurations with the topology of local convergence.

  *Lean target.* Carriers: locally finite configurations as TauCeti random-measure values
  `Measure (EuclideanSpace ℝ (Fin d))` (counting measures; simplicity is an extra predicate), laws
  `P : Measure (Measure (EuclideanSpace ℝ (Fin d)))` with the measurable structure TauCeti uses for
  random measures, translations by `Measure.map (· + u)`, and stationarity as invariance of `P`
  under all translations. New definitions: the restriction of a configuration to a set and the
  finite set of its atoms there; finite range `IsFiniteRange H R` (`H_Δ x` depends only on `x` in
  `Δ ⊕ B(0, R)`); translation invariance of `H`; the infinite-volume DLR predicate
  `IsInfiniteGibbs P z β R H` (probability, stationary, a.s. simple, and for every bounded
  measurable `Δ` with `0 < volume Δ` and measurable `F ≥ 0`,
  `∫⁻ F dP = ∫⁻ (normalised ∫ over Π_Δ of F) dP` as in item 99(b)); the stationarised measures
  `P̄_n = (2n)^{-d} ∫_{[-n,n]^d} (P^{z,β}_{[-n,n]^d} ∘ τ_u^{-1}) du`; and the topology of local
  convergence as the coarsest topology making `P ↦ ∫ F dP` continuous for bounded local `F`, a
  `TopologicalSpace` on probability measures on configurations, not Mathlib's weak topology.
  Theorems: (a) tightness of `(P̄_n)` in that topology, via the specific-entropy bound; (b) every
  cluster point satisfies `IsInfiniteGibbs`, hence existence for `0 < z`, `0 ≤ β`; (c) for
  stationary `P`, `IsInfiniteGibbs P z β R H ↔` the GNZ identity in `∫⁻` form, with
  `h(ξ, x) = h(ξ, x ∩ B(ξ, R))` making the local energy defined on infinite configurations.
  Infrastructure that no library has: the local-convergence topology with its compactness criterion
  (Georgii's level-set tightness of specific entropy), specific relative entropy, and the product
  decomposition of the Poisson process into a window and its exterior on `ℝ^d`. Depends on items 95
  and 99 and on the stationary Poisson process of Part 4. In
  `MSSS/GibbsPointProcesses/InfiniteVolume.lean`, `MSSS.IsInfiniteGibbs` is defined and
  `MSSS.exists_isInfiniteGibbs` and `MSSS.isInfiniteGibbs_iff_gnz` are `sorry`; the tightness
  statement (a) is not stated separately.

* **101. Uniqueness and phase transition.** Let $H$ be an energy as in item 100, of finite
  range $R$, with local energy bounded below, $h\ge C$. There is $z_d\in(0,\infty]$, the
  percolation threshold of the Poisson Boolean model with balls of radius $\tfrac12$, finite
  for $d\ge2$, such that for every $\beta\ge0$ and $z<z_de^{C\beta}/R^d$ the infinite-volume
  Gibbs measure is unique. For $d\ge2$ and the Widom–Rowlinson energy
  $H(\mathbf x)=|\bigcup_{\xi\in\mathbf x}B(\xi,R)|$ there are at least two infinite-volume
  Gibbs measures when $z=\beta$ is large enough.

  *Assessment.* Absent. It needs the percolation threshold of the Poisson Boolean model.

  *Lean target.* Carriers as in item 100. New definitions: the Boolean model
  `L_r(x) = ⋃ ξ ∈ x, ball ξ r` of a configuration, percolation as the existence of an unbounded
  connected component of `L_{1/2}(x)` (Mathlib's `connectedComponentIn` and `Bornology.IsBounded`),
  and the threshold `z_d = sSup {z | Poisson(z)(percolates) = 0} : ℝ≥0∞`; the set contains `0`, so
  the supremum in `ℝ≥0∞` carries no junk value, while a real `sSup` would be `0` when unbounded.
  Theorems: (a) `0 < z_d` for `d ≥ 1` and `z_d < ⊤` for `d ≥ 2`; (b) uniqueness: for `H` as in item
  100 with `∀ ξ x, C ≤ h(ξ, x)` (in `WithTop ℝ`) and `(z : ℝ≥0∞) < z_d * exp (C β) / R ^ d`, any two
  `P, Q` with `IsInfiniteGibbs` are equal; (c) for the Widom–Rowlinson energy `H x = volume (L_R x)`
  (finite range `2R`, stable with `A = 0`) and `d ≥ 2`, there is `z₀` such that for `z = β ≥ z₀` two
  distinct infinite-volume Gibbs measures exist. Infrastructure that no library has: continuum
  percolation (Poisson Boolean model, Kolmogorov 0–1 law for percolation, the threshold bounds),
  stochastic domination of Gibbs specifications by Poisson processes, disagreement percolation, and
  the Ruelle-type estimates of item 100. Depends on items 100 and 99. In
  `MSSS/GibbsPointProcesses/InfiniteVolume.lean`, `MSSS.criticalIntensity_pos`,
  `MSSS.criticalIntensity_lt_top`, `MSSS.isInfiniteGibbs_unique`, and
  `MSSS.widomRowlinson_phase_transition` are `sorry`.

### Summary statistics

[Synopsis](SYNOPSIS.md#summary-statistics) · [Coverage](STRUCTURE.md#summary-statistics).

For a point process with intensity function $\rho$, consider
$$\mathcal K(B)=\frac1{|A|}\mathbb E\sum^{\neq}_{\xi,\eta\in X}
\frac{\mathbf 1[\xi\in A,\ \eta-\xi\in B]}{\rho(\xi)\rho(\eta)},\qquad 0<|A|<\infty,$$
with $a/0=0$. The process is **second-order intensity-reweighted stationary** when
$\mathcal K$ does not depend on $A$; stationary processes are. Ripley's **$K$-function** is
$K(r)=\mathcal K(B(0,r))$ and the **$L$-function** is $L(r)=(K(r)/\omega_d)^{1/d}$. For a
stationary process with intensity $\rho>0$, the **empty-space function** is
$F(r)=\mathbb P(X\cap B(0,r)\ne\emptyset)$, the **nearest-neighbour function** $G(r)$ is the
Palm probability that the typical point has another point within distance $r$, and
$J(r)=(1-G(r))/(1-F(r))$ for $F(r)<1$.

* **103. Estimation of intensity and $K$.** Let $X$ be stationary with intensity $\lambda$
  and locally integrable pair correlation $g$. The estimator $\hat\lambda=X(W)/|W|$ is unbiased with
  $$\mathop{\mathrm{Var}}\hat\lambda=\frac{\lambda}{|W|}+\frac{\lambda^2}{|W|^2}
  \int_W\int_W\bigl(g(x,y)-1\bigr)\,dx\,dy .$$
  If $X$ is second-order intensity-reweighted stationary with known $\rho$, and
  $|W\cap(W+\xi)|>0$ for $\xi\in B$, the translation-corrected estimator
  $$\widehat{\mathcal K}(B)=\sum^{\neq}_{\xi,\eta\in X\cap W}
  \frac{\mathbf 1[\eta-\xi\in B]}{\rho(\xi)\rho(\eta)\,|W\cap(W+\eta-\xi)|}$$
  is unbiased. When the intensity of a stationary process is estimated by $\hat\lambda$, the
  ratio estimator of $K$ is biased; for a Poisson process with Ripley's isotropic edge
  correction its conditional mean given $X(W)=N\ge1$ is $\pi t^2(N-1)/N$ in the plane, for
  every $t>0$ such that each circle of radius at most $t$ centred at a point of $W$ meets $W$
  in an arc of positive length. For an ergodic process
  and increasing convex windows whose inradius tends to infinity, the edge-corrected
  estimators converge to $K$ almost surely, uniformly on compact intervals.

  *Assessment.* TauCeti gives the Poisson count law with its mean and variance, from which the variance of $\hat\lambda$ for a Poisson process follows, and the mean ergodic theorem for a single measure-preserving map. Second-order moment measures, edge-corrected estimators, and their consistency are absent.

  *Lean target.* Carriers: a point process as TauCeti's `X : Ω → Measure (EuclideanSpace ℝ (Fin d))`
  with `[IsProbabilityMeasure P]`; the intensity measure, and the second factorial moment measure on
  `Fin 2 → ℝ^d` (or `ℝ^d × ℝ^d`) as `∫⁻` of the factorial point sum, with a pair correlation `g` a
  density of it relative to `ρ ⊗ ρ · volume ⊗ volume`; stationarity as invariance of the law under
  translations. New definitions: the reduced measure `𝒦(B)` (an `ℝ≥0∞`-valued `∫⁻`, with `a/0 = 0`
  made explicit by an indicator of `ρ > 0`), second-order intensity-reweighted stationarity (`𝒦`
  independent of `A`, equivalently the reweighted second factorial measure is `volume ⊗ 𝒦` after the
  shear `(ξ, η) ↦ (ξ, η - ξ)`), the translation-corrected estimator as a `∑` over ordered pairs of
  distinct atoms in `W`, and Ripley's isotropic weight in the plane. Separate theorems: (a)
  `∫ X(W)/|W| = λ` and `Var (X(W)/|W|) = λ/|W| + λ²/|W|² ∫∫_{W×W} (g - 1)`, with `MeasurableSet W`,
  `0 < volume W < ∞`, `Integrable (X(W))^2`, and `g` locally integrable; (b) `∫ 𝒦̂(B) = 𝒦(B)` for
  measurable `B` with `0 < volume (W ∩ (W + ξ))` on `B`, an `ℝ≥0∞` identity; (c) for `N ≥ 1` i.i.d.
  uniform points on `W ⊆ ℝ²` (the Poisson process conditioned on `X(W) = N`), the mean of Ripley's
  ratio estimator is `π t² (N - 1) / N` when every circle of radius `r ∈ (0, t]` about a point of
  `W` meets `W` in positive length; (d) for an ergodic stationary process (ergodic under the
  `ℝ^d`-action of translations) and increasing convex bodies `W_n` with inradius `→ ∞`,
  `TendstoUniformlyOn` on `[0, r₀]` of the edge-corrected ratio estimators to `K`, almost surely.
  (a)–(c) are statable at the pins; (d) needs a pointwise ergodic theorem for averages over growing
  convex sets in `ℝ^d`, which no library has (TauCeti has the mean ergodic theorem for a single
  map), and Palm theory to identify `K`. Depends on items 102 and 83 (Palm). In
  `MSSS/GibbsPointProcesses/SummaryStatistics.lean`, `MSSS.intensity_estimator` ((a)) is proved, and
  `MSSS.integral_translationK` ((b), for `ρ > 0`), `MSSS.integral_ripleyK` ((c), for `N ≥ 1`), and
  `MSSS.tendstoUniformlyOn_translationK` ((d)) are `sorry`.

* **104. $F$, $G$, and $J$.** For a stationary Poisson process of intensity $\lambda>0$
  on $\mathbb R^d$ with $d\ge1$, $1-F(r)=e^{-\lambda\omega_dr^d}$ and $F=G$, so $J\equiv1$.
  For a stationary Gibbs process with translation-invariant interaction function and
  intensity $\rho>0$,
  $J(r)=\mathbb E[\lambda^\ast(X,0)\mid X\cap B(0,r)=\emptyset]/\rho$; if the interaction has
  finite range $R$, then $J(r)=\lambda^\ast(\emptyset,0)/\rho$ for $r\ge R$ with $F(r)<1$.

  *Assessment.* TauCeti's Poisson count law and Mathlib's ball volumes give
  $1-F(r)=e^{-\lambda\omega_dr^d}$ by a short argument. The positive-dimensional Poisson
  identity $F=G$ needs Palm theory (item 83), and the $J$-function of a Gibbs process needs item 95.

  *Lean target.* Carriers as in item 103, with the Palm distribution of a stationary process (item
  83) as a probability measure on configurations. New definitions: the empty-space function
  `F r = P(X(closedBall 0 r) ≠ 0)` (or with open balls; the two agree for a diffuse intensity but
  not in general), `G` as the Palm probability of a further point within `r`, and
  `J r = (1 - G r) / (1 - F r)`, to be used only where `F r < 1` since `x / 0 = 0`. Separate
  theorems: (a) for TauCeti's `IsPoissonRandomMeasure P X (λ • volume)` with `0 < λ` and `d ≥ 1`,
  `1 - F r = exp (-λ * volume (ball 0 r)).toReal` and `G = F`, hence `J r = 1` for `F r < 1`; the
  first part needs only `IsPoissonRandomMeasure.hasLaw` and `EuclideanSpace.volume_ball`, the second
  the Slivnyak–Mecke theorem (item 84); (b) for a stationary infinite-volume Gibbs measure of item
  100 with intensity `ρ ∈ (0, ∞)` and `λ*(x, 0) = z e^{-β h(0, x)}`,
  `J r = E[λ*(X, 0); X(B(0, r)) = 0] / (ρ (1 - F r))` for `F r < 1`; (c) if `R ≤ r` and `F r < 1`,
  `J r = λ*(∅, 0) / ρ`. (a) is statable at the pins modulo Palm distributions; (b)–(c) depend on
  items 100, 83, and 84. In `MSSS/GibbsPointProcesses/SummaryStatistics.lean`,
  `MSSS.emptySpace_poisson` ((a)) is proved, and `MSSS.jFunction_gibbs` and
  `MSSS.jFunction_gibbs_of_range_le` are `sorry`.

* **128. Mark-weighted $K$ and translation correction.** Let $(x,m_x)$ be a stationary
  simple marked point process with ground process $X$, intensity $\lambda\in(0,\infty)$,
  and typical mark distribution $\zeta$. For a nonnegative measurable weight $w$ on pairs of marks,
  suppose $c_w=\iint w(m,n)\,\zeta(dm)\zeta(dn)$ is positive and finite, and the
  weighted second factorial measure, obtained by weighting each ordered pair of
  distinct points by $w(m_x,m_y)$, has locally integrable density $b_w(y-x)$. Put
  $$K_w(r)=\frac{1}{\lambda^2c_w}\int_{B(0,r)}b_w(h)\,dh.$$
  Then $\lambda c_wK_w(r)$ is the Palm mean of the sum of $w(m_0,m_y)$ over further
  points at distance at most $r$. Under independent labelling with law $\zeta$,
  $K_w=K$. For a window $W$ of positive finite volume with $|W\cap(W+h)|>0$ for
  almost every $h\in B(0,r)$, the sum
  $$\sum_{x\ne y\in X\cap W}
    \frac{w(m_x,m_y)\,\mathbf 1[\|y-x\|\le r]}{|W\cap(W+y-x)|}$$
  is unbiased for $\lambda^2c_wK_w(r)$, with a zero summand when the overlap volume vanishes.

  *Assessment.* TauCeti supplies marking kernels and the finite-intensity Mecke equation. The weighted factorial measure, its Palm identity and invariance under independent labelling, and the unbiased translation-corrected estimator are absent.

  *Lean target.* Carriers: a marked point process as a random measure on `ℝ^d × M` for a measurable
  mark space `M` (TauCeti's marking kernels and `IsPoissonRandomMeasure` give the independently
  marked Poisson case), with stationarity of the ground process and the typical mark law
  `ζ : Measure M` as a Palm mark distribution. New definitions: the `w`-weighted second factorial
  measure on `ℝ^d × ℝ^d` for measurable `w : M → M → ℝ≥0∞`, its translation-invariant density `b_w`,
  `c_w = ∫⁻∫⁻ w dζ dζ` required in `(0, ⊤)`, and `K_w r` as a real number defined from the `ℝ≥0∞`
  integral of `b_w` over `closedBall 0 r` only where that integral is finite. Separate theorems: (a)
  the Palm identity `λ c_w K_w r = E⁰ ∑ w(m_0, m_y) 1[‖y‖ ≤ r]` over further points; (b) under
  independent labelling with law `ζ`, `K_w = K`; (c) for measurable `W` with `0 < volume W < ∞` and
  `0 < volume (W ∩ (W + h))` for almost every `h` in the ball, the translation-corrected sum, with
  summand `0` where the overlap vanishes, has `∫⁻` equal to `λ² c_w K_w r`. (c) is statable at the
  pins from the second factorial measure of `MSSS/PointProcesses/Basic.lean`; (a) and (b) need Palm
  theory for marked processes (item 83). No declaration in `MSSS/` states this entry.

### Likelihood and estimating equations

[Synopsis](SYNOPSIS.md#likelihood-and-estimating-equations) · [Coverage](STRUCTURE.md#likelihood-and-estimating-equations).

* **105. Poisson likelihood.** For a Poisson process with intensity $\lambda_\theta$ observed
  on $W$, the log-likelihood with respect to $\Pi_W$ is
  $\ell(\theta)=\sum_{x\in\mathbf x}\log\lambda_\theta(x)-\int_W\lambda_\theta+|W|$. For the
  log-linear model $\lambda_\beta(u)=\exp(\beta^\top C(u))$, $\ell$ is concave, the score
  equations are $\int_WC_j\lambda_\beta=\sum_{x\in\mathbf x}C_j(x)$, and the Fisher
  information $\int_WCC^\top\lambda_\beta$ equals the negative Hessian. For any point process
  with intensity $\rho_\theta$, positive on $W$ and differentiable in $\theta$ with
  $\int_W\|\nabla\rho_\theta\|<\infty$, the first-order composite score
  $\sum_{u\in\mathbf x}\nabla\log\rho_\theta(u)-\int_W\nabla\rho_\theta$ has mean zero at
  the true parameter.

  *Assessment.* TauCeti's Poisson sampling series and Mecke equation give the likelihood and the mean-zero score by a further argument. The likelihood, its concavity for log-linear intensities, and the composite score are not stated.

  *Lean target.* Carriers: the Poisson law on `W` as in item 94, intensities
  `λ : EuclideanSpace ℝ (Fin d) → ℝ` with `0 ≤ λ` and `IntegrableOn λ W`, a covariate map
  `C : ℝ^d → EuclideanSpace ℝ (Fin p)` with `IntegrableOn (fun u ↦ exp ⟪θ, C u⟫ * ‖C u‖²) W`. New
  definitions: the Poisson density `poissonDensity W λ x = exp (|W| - ∫_W λ) ∏ ξ ∈ x, λ ξ` and the
  log-likelihood `ℓ θ x = ∑ ξ ∈ x, log λ_θ ξ - ∫_W λ_θ + |W|`, where `Real.log 0 = 0` silently hides
  a zero intensity at an observed point; either assume `0 < λ_θ` on `W` or use `EReal`. Separate
  theorems: (a) `HasConfigDensity P X W (poissonDensity W λ)` for the Poisson process of intensity
  `λ` (item 92); (b) `ConcaveOn ℝ univ (ℓ · x)` for the log-linear model; (c) `HasFDerivAt` of `ℓ`
  with gradient `∑ C(ξ) - ∫ C λ_θ` and Hessian `-∫ C Cᵀ λ_θ`, the Fisher information, under the
  integrability above (domination for differentiation under the integral); (d) for any point process
  with intensity measure `ρ_θ · volume`, `ρ_θ > 0` on `W`, `HasFDerivAt` in `θ`, and
  `IntegrableOn ‖∇ρ_θ‖ W`, `E[∑ ξ ∈ X ∩ W, ∇ρ_θ ξ / ρ_θ ξ] = ∫_W ∇ρ_θ` at the true `θ` (Campbell's
  formula, with integrability of the sum). All statable at the pins; (a) depends on item 92. In
  `MSSS/GibbsPointProcesses/PoissonLikelihood.lean`, `MSSS.concaveOn_logLinearLogLik`,
  `MSSS.hasDerivAt_logLinearLogLik`, `MSSS.hasDerivAt_deriv_logLinearLogLik`, and
  `MSSS.integral_compositeScore` (a directional form) are proved, and
  `MSSS.hasConfigDensity_poisson` ((a), for bounded intensities) is `sorry`.

* **106. Kutoyants' asymptotic theory.** For each $n$ let a Poisson process be observed on a
  set $A_n$ with intensity measures $\Lambda^{(n)}_\vartheta$, $\vartheta$ in an open bounded
  $\Theta\subseteq\mathbb R^p$, mutually equivalent and finite on $A_n$. Put
  $\Psi_n=2\sqrt{d\Lambda^{(n)}_\vartheta/d\Lambda^{(n)}_{\vartheta_0}}$ and let
  $I_n(\vartheta)$ be the Fisher information, the Gram matrix of $\nabla_\vartheta\Psi_n$ in
  $L^2$. Under smoothness, identifiability and moment conditions, and with $I_n$ positive
  definite and $\sup\|I_n^{-1}\|\to0$, the family is locally asymptotically normal with
  normalisation $\varphi_n=I_n^{-1/2}$, the Hájek–Le Cam minimax bound holds, and the
  maximum-likelihood estimator is uniformly consistent on compacts, satisfies
  $\varphi_n^{-1}(\hat\vartheta_n-\vartheta)\Rightarrow N(0,I_p)$ with convergence of all
  moments, and is asymptotically efficient. For intensity $nS(\vartheta,x)$ on a fixed set,
  $I_n=nI$ with $I(\vartheta)=\int\nabla S\,\nabla S^\top/S\,dx$.

  *Assessment.* Absent. Neither library has local asymptotic normality, the Hájek–Le Cam bound, or asymptotics of maximum likelihood.

  *Lean target.* Carriers: for each `n` a family of finite intensity measures on a set `A_n` of a
  complete separable metric space, parameter set `Θ ⊆ EuclideanSpace ℝ (Fin p)` open and bounded,
  Poisson laws `P_{n,ϑ}` (TauCeti's `MeasureTheory.Measure.finitePoissonLawOf`), mutual absolute
  continuity `Λ_{n,ϑ} ≪ Λ_{n,ϑ₀}` both ways, and the likelihood ratio
  `exp (∫ log S d X - Λ_ϑ(A_n) + Λ_{ϑ₀}(A_n))` with `S = dΛ_ϑ/dΛ_{ϑ₀}` (Mathlib's
  `MeasureTheory.Measure.rnDeriv`, whose junk value off the support is harmless under equivalence).
  New definitions: the Fisher information `I_n(ϑ)` as the Gram matrix in `L²(Λ_{n,ϑ})` of the
  derivative of `2 √S`; local asymptotic normality of a sequence of experiments (a structure with
  the normalising matrices `φ_n`, the central sequence `Δ_n ⇒ N(0, I_p)` via Mathlib's
  `ProbabilityTheory.multivariateGaussian`, and a remainder `TendstoInMeasure` to `0`); Kutoyants'
  conditions B1–B5 as a structure. Separate theorems: (a) under A1–A3, LAN with `φ_n = I_n^{-1/2}`;
  (b) the Hájek–Le Cam bound for bowl-shaped losses, with `Tr(φ_n φ_nᵀ) → 0`; (c) under B1–B5,
  uniform consistency on compacts of measurable maximisers of the likelihood over `closure Θ`,
  `φ_n^{-1}(ϑ̂_n - ϑ) ⇒ N(0, I_p)`, convergence of all moments, and efficiency; (d) the
  specialisation `Λ_{n,ϑ} = n S(ϑ, x) dx`, `I_n = n I`. Infrastructure that no library has at the
  pins: local asymptotic normality, Le Cam's lemmas, the Hájek–Le Cam minimax theorem, Anderson's
  lemma, and the Ibragimov–Has'minskii likelihood-ratio method for maximum likelihood. Depends on
  item 105. In `MSSS/GibbsPointProcesses/PoissonLikelihood.lean`, `MSSS.poisson_lan`,
  `MSSS.poisson_hajek_leCam`, and `MSSS.poisson_mle_asymptotics` are `sorry`; they state only the
  specialisation (d) on a fixed set with `√n` normalisation.

* **107. Pseudolikelihood.** Let $f_\theta$ be a hereditary, Ruelle-stable density relative to
  the unit-rate Poisson law $\Pi_W$ on a window $W$ of finite volume, and let $A\subseteq W$ be
  measurable. The **pseudolikelihood**
  $$PL_A(\theta;\mathbf x)=\exp\Bigl(-\int_A\lambda^\ast_\theta(\mathbf x,\xi)\,d\xi\Bigr)
  \prod_{\xi\in\mathbf x\cap A}\lambda^\ast_\theta(\mathbf x\setminus\{\xi\},\xi)$$
  is the limit of $e^{-|A|}\prod_jf_\theta(\mathbf x_{A_j}\mid\mathbf x_{W\setminus A_j})$ at
  any configuration with $f_\theta(\mathbf x)>0$, along nested measurable partitions
  $\{A_j\}$ of $A$ with $m\max_j|A_j|^2\to0$, where $m$ is the number of cells and eventually
  each cell contains at most one point of $\mathbf x$. Each cell conditional density is
  obtained by fixing the exterior configuration in $f_\theta$ and normalising the resulting
  function by its integral under the unit-rate Poisson law on the cell. By item 95 its score
  $\sum_{\xi\in\mathbf x\cap A}\nabla\log\lambda^\ast_\theta(\mathbf x\setminus\{\xi\},\xi)
  -\int_A\nabla\lambda^\ast_\theta(\mathbf x,\xi)\,d\xi$ has mean zero at the true $\theta$
  when the derivatives exist and both terms are integrable. For an exponential family
  $\lambda^\ast_\theta=b\,e^{\theta^\top t}$, $\log PL_A$ is concave. For a
  Poisson process, $PL_W(\theta;\mathbf x)=e^{-|W|}f_\theta(\mathbf x)$ with the same
  reference law $\Pi_W$ as in item 105.

  *Assessment.* TauCeti's finite-intensity Mecke equation and the Poisson sampling series give
  ingredients for the score identity and the Poisson special case. Neither library defines
  the pseudolikelihood or proves the partition limit on positive-density configurations.

  *Lean target.* Carriers as in items 94–95, with a parametric family `f : Θ → Finset E → ℝ`,
  `Θ ⊆ EuclideanSpace ℝ (Fin p)`, each `f θ` hereditary, Ruelle stable, configuration- measurable,
  and a probability density relative to `Π_W`. New definitions: the pseudolikelihood
  `PL_A θ x = exp (-∫_A λ*_θ(x, ξ) dξ) * ∏ ξ ∈ x.filter (· ∈ A), λ*_θ(x.erase ξ, ξ)` (real-valued;
  the integral is a Bochner integral that needs `IntegrableOn (λ*_θ x) A`, which Ruelle stability
  alone does not give pointwise, so define the exponent as `(∫⁻ …).toReal` with a separate
  finiteness lemma, or as `exp (-∫⁻ …)` in `ℝ≥0∞`), and the cell conditional density for a
  measurable partition `A_1, …, A_m` of `A`. Separate theorems: (a) the partition limit at each
  `x ⊆ W` with `f θ x > 0`, along nested measurable partitions with `m * (max_j |A_j|)² → 0` that
  eventually separate the points of `x`; (b) the score identity at the true `θ`, as an equality of
  Bochner integrals under explicit integrability of both terms, derived from item 95 applied to the
  positive and negative parts; (c) `ConcaveOn ℝ univ (fun θ ↦ log PL_A θ x)` for
  `λ*_θ = b e^{⟪θ, t⟫}` with `b > 0`; with `b = 0` allowed, `Real.log 0 = 0` breaks concavity, so
  state it in `EReal` or assume `b > 0` on the relevant pairs; (d) `PL_W θ x = e^{-|W|} f θ x` for
  the Poisson family. All statable at the pins; depends on items 94 and 95. In
  `MSSS/GibbsPointProcesses/Finite.lean`, `MSSS.concaveOn_log_pseudolikelihood` and
  `MSSS.pseudolikelihood_poisson` are proved, and
  `MSSS.tendsto_prod_conditionalDensity_pseudolikelihood` and
  `MSSS.pseudolikelihood_score_mean_zero` are `sorry`.

* **108. Takacs–Fiksel estimation.** For test functions $f_1,\dots,f_K$, $K\ge2$, put
  $$C_\Lambda^{z,\beta}(f,\mathbf x)=\sum_{\xi\in\mathbf x\cap\Lambda}f(\xi,\mathbf x\setminus\{\xi\})
  -z\int_\Lambda e^{-\beta h(\xi,\mathbf x)}f(\xi,\mathbf x)\,d\xi,$$
  which has mean zero at the true parameters by item 100. Let $\Gamma$ be a stationary
  finite-range infinite-volume Gibbs process with parameters $(z^\ast,\beta^\ast)$ in a bounded
  domain $D\subseteq(0,\infty)\times[0,\infty)$. If
  $\mathbb E\bigl[|f_k(0,\Gamma)|(1+|h(0,\Gamma)|)\sup_De^{-\beta h(0,\Gamma)}\bigr]<\infty$ for
  each $k$, and the parameters are identifiable in the sense that
  $\sum_k\bigl(\mathbb E f_k(0,\Gamma)(ze^{-\beta h(0,\Gamma)}-z^\ast e^{-\beta^\ast h(0,\Gamma)})\bigr)^2=0$
  only at $(z^\ast,\beta^\ast)$, then every minimiser over $D$ of
  $\sum_kC_{[-n,n]^d}^{z,\beta}(f_k,\Gamma)^2$ is strongly consistent. The maximum
  pseudolikelihood estimator is the case $f_1=1$, $f_2=h$, and is consistent when
  $\mathbb E[(1+h(0,\Gamma)^2)\sup_De^{-\beta h(0,\Gamma)}]<\infty$ and
  $\mathbb P(h(0,\Gamma)=h(0,\emptyset))<1$.

  *Assessment.* Absent. It needs item 100 and a pointwise ergodic theorem for spatial averages; TauCeti has only the mean ergodic theorem for a single map.

  *Lean target.* Carriers as in item 100, with `Γ` an infinite-volume Gibbs process
  (`IsInfiniteGibbs (P.map Γ) z* β* R H`), test functions `f_k : ℝ^d → Measure ℝ^d → ℝ` measurable
  and local, `K ≥ 2`, and a bounded set `D ⊆ Ioi 0 ×ˢ Ici 0` containing `(z*, β*)`. New definitions:
  the contrast `C_Λ^{z,β}(f, x)` (a finite sum over atoms in `Λ` minus
  `z ∫_Λ e^{-β h(ξ, x)} f(ξ, x) dξ`, a Bochner integral needing integrability, else junk `0`), the
  cubes `[-n, n]^d`, and an estimator as any measurable `(ẑ_n, β̂_n)` that minimises the sum of
  squares over `D`; existence of a minimiser needs compactness of `closure D` and continuity in
  `(z, β)`, so state the theorem for every minimiser over `closure D`. Separate theorems: (a)
  `∫ C_Λ^{z*,β*}(f, Γ) dP = 0` for bounded `Λ` under integrability, from item 100; (b) under (5.38)
  and identifiability, every measurable minimiser converges `P`-almost surely to `(z*, β*)`; (c) the
  pseudolikelihood case `f_1 = 1`, `f_2 = h`, under (5.44) and `P(h(0, Γ) = h(0, ∅)) < 1`.
  Infrastructure that no library has: the pointwise ergodic theorem for averages over cubes under
  the translation action of `ℝ^d` or `ℤ^d` (TauCeti has only the mean ergodic theorem for one map),
  the ergodic decomposition of stationary Gibbs measures, and uniform laws of large numbers over
  `D`. Depends on item 100. In `MSSS/GibbsPointProcesses/InfiniteVolume.lean`,
  `MSSS.integral_takacsFiksel`, `MSSS.takacsFiksel_consistent`, and
  `MSSS.pseudolikelihood_consistent` are `sorry`.

### Simulation

[Synopsis](SYNOPSIS.md#simulation) · [Coverage](STRUCTURE.md#simulation).

* **110. Birth–death Metropolis–Hastings algorithm.** Let $h$ be an unnormalised density that
  is locally stable with integrable $\phi^\ast$, $c^\ast=\int\phi^\ast>0$, and $h(\emptyset)>0$.
  With probability $p\in(0,1)$ propose the birth of a point $\xi$ with density
  $\phi^\ast/c^\ast$, accepted with probability
  $\min\{1,\lambda^\ast(\mathbf x,\xi)(1-p)c^\ast/(\phi^\ast(\xi)p(n(\mathbf x)+1))\}$, and otherwise
  propose the death of a uniformly chosen point with the reciprocal ratio. The chain is
  reversible with respect to $h$, irreducible with respect to the point mass at $\emptyset$,
  and aperiodic. For every $\beta>1$ it is $V$-uniformly ergodic with $V(\mathbf x)=\beta^{n(\mathbf x)}$,
  hence geometrically ergodic. It is uniformly ergodic if and only if $n(\mathbf x)\le n_0$ on
  $\{h>0\}$ for some $n_0\ge1$, and then the total-variation distance to the target after $m$
  steps is at most $\bigl(1-\min\{1-p,p/c^\ast\}^{n_0}\bigr)^{\lfloor m/n_0\rfloor}$.

  *Assessment.* Mathlib proves that detailed balance implies invariance and defines $\varphi$-irreducibility. The birth–death Metropolis–Hastings kernel, aperiodicity, geometric and uniform ergodicity, and drift and minorisation conditions are absent. TauCeti's convergence theorems for Markov chains need a countable state space.

  *Lean target.* Carriers: Mathlib's `ProbabilityTheory.Kernel` on a measurable configuration space
  (TauCeti's counting-measure configurations, or the disjoint union `Σ n, Fin n → W` modulo
  permutations), `Kernel.IsReversible`, `Kernel.Invariant`, `Kernel.IsIrreducible` with
  `φ = dirac ∅`, and `MeasureTheory.tvDist`. New definitions: the birth–death Metropolis–Hastings
  kernel for a locally stable `h` with `IntegrableOn φ* W`, `0 < c* = ∫_W φ*`, `h ∅ > 0`, and
  `p ∈ (0, 1)`, with the acceptance ratios as in the entry (`min 1 r`, `r` with an explicit `λ* = 0`
  branch); the state space `{h > 0}`; aperiodicity for a general-state kernel (TauCeti's
  `Kernel.IsAperiodic` is defined through return times at points and suits only countable spaces);
  `V`-uniform ergodicity as `∃ R, ∃ r < 1, ∀ x, ∀ g, |g| ≤ V → |(κ ^ m) g x - ∫ g dπ| ≤ R V(x) r^m`,
  and uniform ergodicity. Separate theorems: (a) reversibility with respect to `h · Π_W` (Mathlib's
  `ProbabilityTheory.Kernel.IsReversible.invariant` then gives invariance); (b)
  `Kernel.IsIrreducible (dirac ∅)` and aperiodicity; (c) for every `1 < β`, `V`-uniform ergodicity
  with `V x = β ^ x.card`; (d) uniform ergodicity `↔ ∃ n₀ ≥ 1, ∀ x, h x > 0 → x.card ≤ n₀`; (e) then
  `tvDist ((κ ^ m) x) π ≤ (1 - min (1 - p) (p / c*) ^ n₀) ^ (m / n₀)` with natural-number division
  `m / n₀`, the floor; with a real exponent the bound is false. Infrastructure that no library has:
  small sets, the geometric drift condition, and the Meyn–Tweedie theorems linking drift and
  minorisation to `V`-uniform and uniform ergodicity on general state spaces. Depends on item 94. In
  `MSSS/GibbsPointProcesses/BirthDeath.lean`, the chain is modelled as an operator
  `MSSS.birthDeathStep` on functions; `MSSS.birthDeath_irreducible` and `MSSS.birthDeath_aperiodic`
  are proved, and `MSSS.birthDeath_reversible`, `MSSS.birthDeath_vUniformlyErgodic`,
  `MSSS.birthDeath_uniformlyErgodic_iff`, and `MSSS.birthDeath_tv_bound` (with the floor) are
  `sorry`.

## 6. Stochastic and integral geometry

Selected: 13 statements. [Synopsis part](SYNOPSIS.md#6-stochastic-and-integral-geometry) · [Coverage part](STRUCTURE.md#6-stochastic-and-integral-geometry).

Let $E$ be a locally compact, Hausdorff, second countable space, and let $\mathcal F$,
$\mathcal C$, and $\mathcal G$ be its closed, compact, and open subsets. The **Fell
topology** on $\mathcal F$ is generated by the sets $\{F:F\cap C=\emptyset\}$, $C\in\mathcal C$,
and $\{F:F\cap G\ne\emptyset\}$, $G\in\mathcal G$; it makes $\mathcal F$ compact with a
countable base. A **random closed set** is a random element $Z$ of $\mathcal F$ with its Borel
$\sigma$-algebra, and its **capacity functional** is $T(C)=\mathbb P(Z\cap C\ne\emptyset)$,
$C\in\mathcal C$. $\mathcal K^d$ denotes the convex bodies, the nonempty compact convex
subsets of $\mathbb R^d$; a functional $\varphi$ on $\mathcal K^d$ is extended by
$\varphi(\emptyset)=0$, and an additive one is extended by inclusion–exclusion to the convex
ring of finite unions of convex bodies whenever such an extension exists, as it does for the
intrinsic volumes of item 114. $\kappa_j=\omega_j$ is the volume of the unit ball of
$\mathbb R^j$, and $c^r_s=r!\kappa_r/(s!\kappa_s)$, with
$c^{r_1,r_2}_{s_1,s_2}=c^{r_1}_{s_1}c^{r_2}_{s_2}$.

### Random closed sets and the Boolean model

[Synopsis](SYNOPSIS.md#random-closed-sets-and-the-boolean-model) · [Coverage](STRUCTURE.md#random-closed-sets-and-the-boolean-model).

* **112. Choquet–Matheron theorem.** The capacity functional of a random closed set
  satisfies $0\le T\le1$ and $T(\emptyset)=0$; it is upper semicontinuous, $T(C_i)\to T(C)$
  when $C_i\downarrow C$; and it is completely alternating: the successive differences
  $S_0(C_0)=1-T(C_0)$ and
  $S_k(C_0;C_1,\dots,C_k)=S_{k-1}(C_0;C_1,\dots,C_{k-1})-S_{k-1}(C_0\cup C_k;C_1,\dots,C_{k-1})$
  are nonnegative, and equal
  $\mathbb P(Z\cap C_0=\emptyset,\ Z\cap C_i\ne\emptyset\ \text{for}\ i=1,\dots,k)$.
  Conversely, every functional on $\mathcal C$ with these properties is the capacity
  functional of a unique law on $\mathcal F$. In particular the capacity functional
  determines the law of a random closed set.

  *Assessment.* Mathlib has the Vietoris topology and the Hausdorff metric on compact sets, and
  TauCeti Choquet capacities in the sense of capacitability, continuous along increasing sequences
  and along decreasing sequences of closed sets. The Fell topology, complete alternation, and the
  Choquet–Matheron theorem are absent.

  *Lean target.* Carrier `TopologicalSpace.Closeds E` with
  `[TopologicalSpace E] [LocallyCompactSpace E] [T2Space E] [SecondCountableTopology E]`.
  Definitions needed: the σ-algebra on `Closeds E` generated by the miss events
  `{F | (F : Set E) ∩ C = ∅}` for compact `C` (`MeasurableSpace.generateFrom`), stated without the
  Fell topology, which no library has and which is only needed to name it Borel; the capacity
  functional of a measurable `Z : Ω → Closeds E` as a function `Set E → ℝ`, the `toReal` of
  `P {ω | ((Z ω : Set E) ∩ C).Nonempty}`, which is exact because `P` is a probability measure; and
  the successive differences by recursion on `k` with `Fin k → Set E`. Conjuncts: the bounds and
  `T ∅ = 0`; continuity along antitone sequences of compact sets; nonnegativity and the event
  formula for `S_k` with `C₀` and every `C i` compact; uniqueness of the law through
  `MeasureTheory.ext_of_generate_finite` on the miss π-system; existence, whose hypotheses
  quantify over compact sets only, so the values of the functional off compact sets are junk and
  must not be used. All of it is statable and provable at the pins. MSSS: `MSSS.fellSigma`,
  `MSSS.capacity`, `MSSS.succDiff`, `MSSS.succDiff_eq`, `MSSS.capacity_properties`,
  `MSSS.map_eq_of_capacity_eq`, and `MSSS.existsUnique_law_of_capacity`, all proved.

* **113. Boolean model.** Let $\{x_n\}$ be a stationary Poisson process of intensity
  $\lambda>0$ in $\mathbb R^d$ and let $\Xi_n$ be independent copies of a random compact set
  $\Xi_0$, independent of the germs, with $\mathbb E V_d(\Xi_0\oplus K)<\infty$ for every
  compact $K$. For $\Xi=\bigcup_n(x_n+\Xi_n)$ and compact $K$, with $\check K=-K$,
  $$T(K)=1-\exp\bigl(-\lambda\,\mathbb E V_d(\Xi_0\oplus\check K)\bigr),$$
  and the number of grains hitting $K$ is Poisson with mean
  $\lambda\mathbb E V_d(\Xi_0\oplus\check K)$. The volume fraction is
  $p=\mathbb P(0\in\Xi)=1-e^{-\lambda\mathbb E V_d(\Xi_0)}$, the covariance is
  $\mathbb P(0\in\Xi,\ r\in\Xi)=2p-1+(1-p)^2\exp\bigl(\lambda\,\mathbb E V_d(\Xi_0\cap(\Xi_0-r))\bigr)$,
  and the contact distribution function
  $H_B(r)=\mathbb P(0\in\Xi\oplus rB\mid 0\notin\Xi)$ for a convex structuring element $B$
  containing the origin is
  $H_B(r)=1-\exp\bigl(-\lambda[\mathbb E V_d(\Xi_0\oplus rB)-\mathbb E V_d(\Xi_0)]\bigr)$.
  When $\Xi_0$ is almost surely nonempty, the capacity functional determines $\lambda$ and the
  law of $\Xi_0$ up to translation: for every measurable centre map $c$ on the nonempty
  compact sets with $c(K+x)=c(K)+x$, it determines the law of $\Xi_0-c(\Xi_0)$.

  *Assessment.* TauCeti has Poisson count laws, mapping, restriction, and marking kernels, and
  Mathlib Minkowski sums and Lebesgue measure. The Boolean model and its formulas are absent; they
  need the marking theorem of item 75, which TauCeti proves only after its project pin.

  *Lean target.* Carriers: `TauCeti.Probability.IsPoissonRandomMeasure` for the germs with
  intensity `ENNReal.ofReal λ • volume` on `EuclideanSpace ℝ (Fin d)`, `Closeds` for the grains,
  and `MeasureTheory.Measure.infinitePi` for their independent copies. Definitions needed: a
  predicate `IsBooleanModel` bundling a probability `P`, `0 < λ`, the germ process, measurability
  of germs and grains, the product law of germs and grain sequence, a grain law `Q` that is a
  probability measure carried by compact sets, and `∫⁻ F, volume ((F : Set _) + K) ∂Q < ∞` for
  every compact `K`, kept in `ℝ≥0∞` until this finiteness is available; the union set; and the
  contact distribution as a real ratio, whose denominator `1 - p` is nonzero because `p < 1` under
  the finiteness hypothesis, which the statement must record or the ratio is junk. Conjuncts:
  Poisson law of the hit count through `ProbabilityTheory.HasLaw` and
  `ProbabilityTheory.poissonMeasure`; the capacity functional; the volume fraction; the
  covariance; the contact distribution for compact convex `B` containing `0` and `r ≥ 0`;
  identifiability for two models with almost surely nonempty grains, stated for events of grain
  sets that are invariant under translation, which is equivalent to the centre-map form. Depends
  on item 75 (marking). MSSS: `MSSS.IsBooleanModel`, `MSSS.booleanSet`, `MSSS.grainMeanVolume`,
  `MSSS.contactDistribution`, `MSSS.boolean_hitCount`, `MSSS.boolean_capacity`,
  `MSSS.boolean_volumeFraction`, `MSSS.boolean_covariance`, `MSSS.boolean_contactDistribution`,
  and `MSSS.boolean_identifiable`, all proved, using a marking theorem proved locally in
  `MSSS/PointProcesses/Poisson.lean`.

* **130. Selection expectation of a random compact set.** Let $X$ be an almost surely
  nonempty random compact set in $\mathbb R^d$ with
  $\mathbb E\sup_{x\in X}\|x\|<\infty$. Define the selection expectation
  $\mathbb E_{\mathrm{sel}}X$ to be the closure of the set of expectations of
  measurable selections $\xi\in X$ almost surely. If $X$ is almost surely convex
  or the probability space is nonatomic, this expectation is the unique nonempty compact
  convex set whose support function is the mean support function of $X$:
  $$h_{\mathbb E_{\mathrm{sel}}X}(u)=\mathbb E h_X(u),\qquad
    h_K(u)=\sup_{x\in K}\langle x,u\rangle,\qquad u\in\mathbb R^d.$$
  Without either hypothesis the closure need not be convex: on a one-point probability
  space with $X=\{0,1\}\subset\mathbb R$ it is $\{0,1\}$, while $\mathbb E h_X$ is the
  support function of $[0,1]$.

  *Assessment.* TauCeti supplies the measurable selection theorem for weakly measurable
  closed-valued maps into Polish spaces. Mathlib supplies Bochner integration and separation of
  closed convex sets. The selection expectation, its convexity on a nonatomic probability space,
  and its support-function identity are absent.

  *Lean target.* Carriers: `TopologicalSpace.NonemptyCompacts (EuclideanSpace ℝ (Fin d))` for the
  values and `ConvexBody` for the expectation. Definitions needed: the integrable selections of a
  measurable `X : Ω → NonemptyCompacts _`, those `ξ` with `Integrable ξ P` and
  `∀ᵐ ω ∂P, ξ ω ∈ X ω`; the selection expectation as the closure of their integrals; and the
  support function `u ↦ ⨆ x ∈ K, ⟪x, u⟫` on nonempty compact sets, where the real supremum is not
  junk because the set is nonempty and bounded. Hypotheses: `IsProbabilityMeasure P`,
  measurability of `X` for the σ-algebra of item 112, and integrability of `ω ↦ ⨆ x ∈ X ω, ‖x‖`,
  which is best stated as `∫⁻ ω, ENNReal.ofReal (⨆ x ∈ X ω, ‖x‖) ∂P < ∞`. Conjuncts: for almost
  surely convex `X`, or for `MeasureTheory.NoAtoms P`, the expectation is nonempty, compact, and
  convex; and its support function is `u ↦ ∫ ω, h (X ω) u ∂P`; uniqueness follows from separation
  (`geometric_hahn_banach_closed_point`). The example of the synopsis is a negative control: a
  statement dropping both alternative hypotheses is false. Selections exist by
  `TauCeti.exists_measurable_forall_mem`; the nonatomic case needs a Lyapunov convexity theorem
  for vector measures, which neither library has. Depends on item 112 for measurability. MSSS:
  none.

### Integral geometry of convex bodies

[Synopsis](SYNOPSIS.md#integral-geometry-of-convex-bodies) · [Coverage](STRUCTURE.md#integral-geometry-of-convex-bodies).

* **114. Steiner formula and intrinsic volumes.** For $K\in\mathcal K^d$ and
  $\varepsilon\ge0$,
  $$V_d(K+\varepsilon B^d)=\sum_{j=0}^d\varepsilon^{d-j}\kappa_{d-j}V_j(K),$$
  which defines the **intrinsic volumes** $V_0,\dots,V_d$. $V_d$ is the volume. For $d\ge1$,
  $2V_{d-1}(K)$ is the surface-area functional. If $K$ has nonempty interior, it equals
  $\mathcal H^{d-1}(\partial K)$, where Hausdorff measure is normalised to agree with
  $(d-1)$-dimensional Lebesgue measure on affine $(d-1)$-planes.
  $V_1(K)=\frac{d\kappa_d}{2\kappa_{d-1}}w(K)$, where $w(K)$ is the mean width, the mean of
  $h_K(u)+h_K(-u)$ over the uniform law on the unit sphere; $V_0$ is the Euler characteristic,
  equal to $1$ on nonempty convex bodies. $V_j$ does not depend on the dimension of the
  ambient space, $V_j(B^d)=\binom dj\kappa_d/\kappa_{d-j}$, and each $V_j$ is additive,
  continuous in the Hausdorff metric, invariant under rigid motions, and homogeneous of
  degree $j$.

  *Assessment.* Mathlib has convex bodies with the Hausdorff metric, the homogeneity, invariance,
  and additivity of Lebesgue measure, and the normalised measure
  `MeasureTheory.Measure.euclideanHausdorffMeasure` used in the surface-area identity. TauCeti
  proves that the right derivative at $0$ of $t\mapsto|K+tB^d|$ is the perimeter for a compact
  convex set with nonempty interior, and is twice the area for a compact set in a hyperplane. The
  polynomiality of the parallel volume and the intrinsic volumes are absent.

  *Lean target.* Carrier `ConvexBody (EuclideanSpace ℝ (Fin d))`, or `Set` with explicit
  `IsCompact`, `Convex ℝ`, and `Set.Nonempty` hypotheses, the latter needed for item 119 where
  intersections may be empty. Definitions needed: the unit-ball volume `κ j`; the Steiner
  polynomial, for instance as the `Lagrange.interpolate` of the real parallel volumes at
  `0, …, d`, which is junk unless the Steiner formula is proved; the intrinsic volume `V j K`, its
  coefficient of degree `d - j` divided by `κ (d - j)`, set to `0` for `j > d` and on the empty
  set. Conjuncts: the Steiner identity for `ε ≥ 0`; `V d K` is the volume; for `d ≥ 1`,
  `2 V (d - 1) K = μHE[d - 1] (frontier K)` when `(interior K).Nonempty`, with
  `MeasureTheory.Measure.euclideanHausdorffMeasure` and not the raw
  `MeasureTheory.Measure.hausdorffMeasure`, which differs by the factor of
  `TauCeti.euclideanHausdorffMeasure_eq_smul_hausdorffMeasure` (`4/π` for surfaces in space);
  `V 1 K = d κ d / (2 κ (d - 1)) * w K` with the mean width as an integral over the unit sphere
  (`MeasureTheory.Measure.toSphere`); `V 0 K = 1`; invariance under linear isometric embeddings
  into higher dimension; the ball values; additivity when `K ∪ M` is convex; continuity;
  invariance under `≃ᵃⁱ[ℝ]`; homogeneity for `t ≥ 0`. All statable at the pins; the proof of
  polynomiality needs mixed volumes or polytope approximation, which no library has. MSSS:
  `MSSS.steinerPolynomial`, `MSSS.intrinsicVolume`, `MSSS.meanWidth`; proved
  `MSSS.intrinsicVolume_top`, `MSSS.intrinsicVolume_ball`,
  `MSSS.isConvexValuation_intrinsicVolume`, `MSSS.isHausdorffContinuous_intrinsicVolume`,
  `MSSS.isMotionInvariant_intrinsicVolume`; `sorry` `MSSS.steiner_formula`, `MSSS.surfaceArea_eq`,
  `MSSS.intrinsicVolume_one_eq_meanWidth`, `MSSS.intrinsicVolume_zero`,
  `MSSS.intrinsicVolume_linearIsometry`, `MSSS.intrinsicVolume_smul`. `MSSS.surfaceArea_eq` is
  stated with `μHE[d - 1]`.

* **115. Hadwiger's characterisation theorem.** Let $\psi:\mathcal K^d\to\mathbb R$ be
  additive, $\psi(K\cup M)+\psi(K\cap M)=\psi(K)+\psi(M)$ whenever $K\cup M$ is convex,
  invariant under rigid motions, and continuous in the Hausdorff metric. Then
  $\psi=\sum_{i=0}^dc_iV_i$ for real constants $c_i$. If $\psi$ is monotone instead of
  continuous, the same holds with $c_i\ge0$.

  *Assessment.* Absent. It needs item 114 and valuations on convex bodies.

  *Lean target.* Carrier `ConvexBody (EuclideanSpace ℝ (Fin d))` or nonempty compact convex
  `Set`s. Definitions needed: predicates for a real functional to be a convex valuation (additive
  whenever `K ∪ M` is convex, with `K ∩ M` nonempty or the value at `∅` fixed to `0`), continuous
  for the Hausdorff metric, invariant under every `AffineIsometryEquiv`, and monotone for
  inclusion. Conjuncts: continuous version, `∃ c : Fin (d + 1) → ℝ, ψ = ∑ i, c i * V i`; monotone
  version with `0 ≤ c i`. Both are statable at the pins; the proof needs the Klain–Schneider
  characterisation of simple valuations or Hadwiger's polytope argument, which no library has.
  Small cases: `d = 0` gives a constant, `d = 1` gives `c₀ + c₁ · length`. Depends on item 114.
  MSSS: `MSSS.IsConvexValuation`, `MSSS.IsHausdorffContinuous`, `MSSS.IsMotionInvariant`, and
  `MSSS.hadwiger`, `MSSS.hadwiger_monotone`, both `sorry`.

* **116. Crofton formula.** Let $\mu_k$ be the motion-invariant measure on the space $A(d,k)$
  of affine $k$-flats, normalised as the integral over linear subspaces $L$, under the
  rotation-invariant probability, of Lebesgue measure on $L^\perp$. For $K\in\mathcal K^d$,
  $1\le k\le d-1$, and $0\le j\le k$,
  $$\int_{A(d,k)}V_j(K\cap F)\,\mu_k(dF)=c^{k,\,d-k+j}_{j,\,d}\,V_{d-k+j}(K).$$
  For $j=0$ this expresses $V_{d-k}(K)$ through the measure of the flats that hit $K$.

  *Assessment.* Absent. Neither library has the invariant measure on affine flats; TauCeti has a
  Haar probability on the orthogonal group through its compactness, and Mathlib's `Grassmannian`
  is the algebro-geometric one.

  *Lean target.* Carriers: `Matrix.orthogonalGroup (Fin d) ℝ` with the `CompactSpace` instance of
  `TauCeti.Matrix.isCompact_unitaryGroup` and a left-invariant probability `ν` on it (for instance
  `MeasureTheory.Measure.haarMeasure ⊤`, of mass one by `MeasureTheory.Measure.haarMeasure_self`).
  Definitions needed: the parametrisation of affine `k`-flats as `g • (L₀ + y)` with `L₀` the span
  of the first `k` coordinates, `g` in the orthogonal group, and `y` in `L₀ᗮ`; the invariant
  measure `μ_k` as the image of `ν ⊗ volume`, which avoids a quotient space. Hypotheses: `1 ≤ k`,
  `k ≤ d - 1`, `j ≤ k`, `K` nonempty compact convex. The integrand `F ↦ V j (K ∩ F)` must be shown
  measurable and integrable, or the statement written with `∫⁻` and `ENNReal.ofReal`, since
  `V j ≥ 0` and the Bochner integral of a non-integrable function is junk `0`; it vanishes off the
  flats hitting `K`, which have finite measure. Statable at the pins; the proof needs item 114 and
  a Fubini argument over flats. Small cases for the test file: `d = 2, k = 1, j = 0` gives the
  Cauchy formula `L/π`, and `d = 3, k = 1, j = 0` gives `V 2 / 2`. Depends on item 114. MSSS:
  `MSSS.IsRotationInvariant`, `MSSS.standardFlat`, `MSSS.flat`, and `MSSS.crofton`, `sorry`.

* **117. Principal kinematic formula.** Let $\mu$ be the Haar measure on the group $G_d$ of
  rigid motions of $\mathbb R^d$, the product of Lebesgue measure on translations and the
  Haar probability on rotations. For $K,M\in\mathcal K^d$ and $j=0,\dots,d$,
  $$\int_{G_d}V_j(K\cap gM)\,\mu(dg)=\sum_{k=j}^dc^{k,\,d-k+j}_{j,\,d}\,V_k(K)\,V_{d-k+j}(M).$$
  For $j=0$ the left side is the measure of the motions that bring $gM$ into contact with
  $K$. More generally, for every additive continuous $\varphi$ on $\mathcal K^d$, extended by
  $\varphi(\emptyset)=0$, $\int\varphi(K\cap gM)\,\mu(dg)=\sum_{k=0}^d\varphi_{d-k}(K)V_k(M)$,
  where $\varphi_{d-k}(K)=\int_{A(d,k)}\varphi(K\cap F)\,\mu_k(dF)$; for $k=0$ the measure
  $\mu_0$ is Lebesgue measure on the points of $\mathbb R^d$, and for $k=d$ it is the unit mass
  at $\mathbb R^d$.

  *Assessment.* Absent. Haar measure exists on the group of rigid motions only abstractly; TauCeti
  adds a Haar probability on the orthogonal group and volume preservation by affine isometries.

  *Lean target.* Carriers as in item 116, with the motion `x ↦ g x + t` for `g` in the orthogonal
  group and `t` in `EuclideanSpace ℝ (Fin d)`, and `μ = ν ⊗ volume` on pairs, so that no group
  structure on motions is needed. Conjuncts: for nonempty compact convex `K, M` and `j ≤ d`, the
  integral of `(g, t) ↦ V j (K ∩ (g • M + t))`, with `V j ∅ = 0`, equals the stated sum; the
  general form for every real `φ` that is additive, Hausdorff continuous, and satisfies `φ ∅ = 0`,
  with `φ (d - k)` defined through the measures of item 116 and with `μ_0` the volume on points
  and `μ_d` the unit mass. The integrands vanish outside the bounded set of motions with
  `K ∩ (g • M + t)` nonempty; for `V j` integrability follows from continuity, but for the general
  `φ` measurability and integrability must be proved or assumed, and the statement must not rely
  on the junk value of a non-integrable Bochner integral. Small case for the test file:
  `d = 2, j = 0` gives `A_K + A_M + L_K L_M / (2π)`. Statable at the pins; the proof needs items
  114–116. MSSS: `MSSS.kinematicConst`, `MSSS.principal_kinematic` and `MSSS.kinematic_valuation`
  (with the hypothesis `φ ∅ = 0`), both `sorry`.

### Mean values for Boolean models and tessellations

[Synopsis](SYNOPSIS.md#mean-values-for-boolean-models-and-tessellations) · [Coverage](STRUCTURE.md#mean-values-for-boolean-models-and-tessellations).

* **119. Miles' formulas.** Let $\Xi$ be a stationary Boolean model with convex grains, and
  define the densities $\overline V_j(\Xi)=\lim_{r\to\infty}\mathbb E V_j(\Xi\cap rW)/V_d(rW)$
  for a convex body $W$ with $V_d(W)>0$; the limits exist. Let
  $\overline V_j(X)=\lambda\mathbb E V_j(\Xi_0)$. Then
  $\overline V_d(\Xi)=1-e^{-\overline V_d(X)}$ and
  $\overline V_{d-1}(\Xi)=e^{-\overline V_d(X)}\overline V_{d-1}(X)$. If moreover the grains are
  isotropic, then in the plane, with area $A$, perimeter $L$, and Euler characteristic $\chi$,
  $$A_A=1-e^{-\lambda\mathbb E A},\qquad L_A=\lambda e^{-\lambda\mathbb E A}\mathbb E L,\qquad
  \chi_A=e^{-\lambda\mathbb E A}\Bigl(\lambda-\frac{\lambda^2(\mathbb E L)^2}{4\pi}\Bigr),$$
  and in space, with volume $V$, surface area $S$, integral of mean curvature $M$, and the
  grain densities $\overline V,\overline S,\overline M,\overline\chi$ equal to $\lambda$ times
  the mean grain values,
  $$V_V=1-e^{-\overline V},\quad S_V=e^{-\overline V}\overline S,\quad
  M_V=e^{-\overline V}\Bigl(\overline M-\frac{\pi^2}{32}\overline S^{\,2}\Bigr),\quad
  \chi_V=e^{-\overline V}\Bigl(\overline\chi-\frac{\overline M\,\overline S}{4\pi}
  +\frac{\pi\overline S^{\,3}}{384}\Bigr).$$

  *Assessment.* Absent. It needs items 113, 114, and 117.

  *Lean target.* Carriers: `MSSS`-style `IsBooleanModel` from item 113 and nonempty compact convex
  grains (`∀ᵐ F ∂Q, Convex ℝ (F : Set _) ∧ (F : Set _).Nonempty`). Definitions needed: the
  intrinsic volume of a finite union of convex bodies by inclusion–exclusion over the grains
  hitting the window, which needs that only finitely many grains hit a bounded set almost surely,
  otherwise the definition is junk; the specific intrinsic volume as a limit of
  `E V_j(Ξ ∩ rW) / V_d(rW)` with `rW` for real `r → ∞`. Hypotheses: compact convex `W` with
  `0 < volume W`, `1 ≤ d`, and `E V_j(Ξ_0) < ∞`, which follows from the finiteness hypothesis of
  item 113 through item 114; the Bochner expectation of `V_j(Ξ ∩ rW)` must be shown integrable,
  since `V_j` of a union can be negative for `j < d`. Isotropy: rotation invariance of the grain
  law, for example of its capacity functional. Conjuncts: existence of the densities; the volume
  and surface formulas; the planar and spatial formulas under isotropy, with `L = 2 V_1`,
  `S = 2 V_2`, `M = π V_1`, `χ = V_0`. Statable at the pins; the proof needs items 113, 114, 117
  and the additive extension of item 168. MSSS: `MSSS.unionIntrinsicVolume`, `MSSS.hitIndices`,
  `MSSS.booleanIntrinsicVolume`, `MSSS.grainMeanIntrinsicVolume`, `MSSS.IsIsotropicGrainLaw`, and
  `MSSS.miles_densities`, `MSSS.miles_plane`, `MSSS.miles_space`, all `sorry`.
  `MSSS.grainMeanIntrinsicVolume` is a Bochner integral without an integrability hypothesis in the
  theorems; it is finite under the standing hypothesis, which a proof must derive.

* **168. Specific intrinsic volumes and stereology of standard random sets.** A
  **standard random set** is a stationary random closed set $Z$ in $\mathbb R^d$ that is
  almost surely a locally finite union of convex bodies, with
  $\mathbb E\,2^{N(Z\cap[0,1]^d)}<\infty$, where $N(A)$ is the least number of convex
  bodies whose union is $A$. For such $Z$ and every convex body $W$ with $V_d(W)>0$ the
  **specific intrinsic volumes**
  $\overline V_j(Z)=\lim_{r\to\infty}\mathbb E V_j(Z\cap rW)/V_d(rW)$, $j=0,\dots,d$, exist
  and do not depend on $W$, and $\overline V_d(Z)=\mathbb P(0\in Z)$. If $Z$ is moreover
  isotropic, then for every convex body $W$
  $$\mathbb E V_j(Z\cap W)=\sum_{k=j}^dc^{k,\,d-k+j}_{j,\,d}\,\overline V_k(Z)\,V_{d-k+j}(W),$$
  and for every $k$-flat $F$, $1\le k\le d-1$, the section $Z\cap F$ is an isotropic standard
  random set in $F$ with $\overline V_j(Z\cap F)=c^{k,\,d-k+j}_{j,\,d}\,\overline V_{d-k+j}(Z)$
  for $0\le j\le k$. For $d=3$ and plane sections, with $V_V,S_V,M_V$ the specific volume,
  surface area, and integral of mean curvature and $A_A,L_A,\chi_A$ the specific area,
  boundary length, and Euler characteristic of the section,
  $$V_V=A_A,\qquad S_V=\frac4\pi L_A,\qquad M_V=2\pi\chi_A.$$

  *Assessment.* Absent. Neither library has intrinsic volumes, their additive extension to the
  convex ring, or stationary random sets beyond item 113; MSSS has inclusion–exclusion over
  finitely many grains only.

  *Lean target.* Carriers: a measurable `Z : Ω → Closeds (EuclideanSpace ℝ (Fin d))` for the
  σ-algebra of item 112. Definitions needed: the convex ring as finite unions of nonempty compact
  convex sets; the additive extension of `V j` to it, well defined by Groemer's extension theorem
  (Schneider–Weil, Theorem 14.4.2, p. 620), which no library has; the least number `N` of convex
  bodies in a representation; a predicate for a standard random set bundling stationarity (the law
  is invariant under translations), local polyconvexity almost surely, and
  `∫⁻ ω, 2 ^ N (Z ω ∩ [0,1]^d) ∂P < ∞`, kept in `ℝ≥0∞`; isotropy as rotation invariance of the
  law. Conjuncts: existence and independence of `W` of the specific intrinsic volumes for compact
  convex `W` with `0 < volume W`; `V̄ d = P (0 ∈ Z)`; under isotropy, the kinematic formula for
  `E V_j(Z ∩ W)`; the section formula for `k`-flats with `1 ≤ k ≤ d - 1` and `j ≤ k`; and the
  three stereological identities for `d = 3`. The specific values are signed reals for `j < d`;
  expectations are Bochner integrals whose integrability follows from the moment hypothesis. Small
  check for the test file: the constants `c^{2,2}_{1,3} = π/4` and `c^{2,1}_{0,3} = 1/2` give
  `4/π` and `2π`. Depends on items 112, 114, 116, and 117; item 119 is its special case for the
  Boolean model. MSSS: none.

* **121. Poisson line and hyperplane tessellations.** For a motion-invariant Poisson line
  process in the plane with length density $L_A$, put $\varrho=2L_A/\pi$, the mean number of
  lines hitting a unit segment. Almost surely every vertex has degree $4$; the intensities of
  vertices, edges, and cells are $\pi\varrho^2/4$, $\pi\varrho^2/2$, and $\pi\varrho^2/4$; the
  mean edge length is $1/\varrho$; and the typical cell has mean area $4/(\pi\varrho^2)$, mean
  perimeter $4/\varrho$, mean number of vertices $4$, and mean squared area $8/\varrho^4$. For a
  stationary Poisson hyperplane process in $\mathbb R^d$ of intensity $\gamma>0$ whose
  spherical directional distribution $\varphi$ is not concentrated on a great subsphere, let
  $\Pi$ be the associated zonoid, with support function
  $h_\Pi(u)=\frac\gamma2\int|\langle u,v\rangle|\,\varphi(dv)$. Then the intensity of
  $k$-faces of the tessellation is $\binom dkV_d(\Pi)$ for $0\le k\le d$.

  *Assessment.* Absent from both libraries. TauCeti's Poisson random measures can carry the line
  and hyperplane processes on a parameter space; the faces of an arrangement, typical faces, and
  the associated zonoid are not defined.

  *Lean target.* Carriers: `TauCeti.Probability.IsPoissonRandomMeasure` on the parameters
  `(p, θ) ∈ ℝ × ℝ` with intensity `ENNReal.ofReal (ϱ / 2) • volume.restrict (univ ×ˢ Ico 0 π)` for
  lines, and on `EuclideanSpace ℝ (Fin d) × ℝ` with a translation-invariant intensity carried by
  unit normals for hyperplanes. Definitions needed: the arrangement of the atoms; its `k`-faces as
  connected components (`connectedComponentIn`) of the points on exactly `d - k` hyperplanes; face
  intensities and typical-face means as limits of ratios over balls of radius `r → ∞`, with counts
  in `ℝ≥0∞` (`∫⁻`, `Set.encard`) and lengths through `μHE[1]`, not the raw Hausdorff measure,
  which agrees in dimension `1` only; the associated zonoid through its support function.
  Hypotheses: `0 < ϱ`; for hyperplanes, `0 < γ`, finiteness on bounded slabs, and directions not
  concentrated on a great subsphere, without which the cells are unbounded and the face
  intensities fail. Conjuncts as in the synopsis. Small check for the test file: with `L_A = 1.7`,
  vertex intensity `L_A²/π`, mean cell area `π/L_A²`, and `V_2(Π) = L_A²/π`. Typical-face means as
  Palm expectations need the Palm theory of PR #417; the ergodic-ratio form above avoids it but
  then needs an ergodic theorem for the Poisson process. Depends on items 114 and 131. MSSS:
  `MSSS.hyperplane`, `MSSS.arrangementFaces`, `MSSS.lineArrangement`,
  `MSSS.hyperplaneArrangement`, `MSSS.zonoidSupport`, `MSSS.associatedZonoid`,
  `MSSS.HasFaceIntensity`, `MSSS.HasTypicalMean`, and `MSSS.poissonLine_simple`,
  `MSSS.poissonLine_intensities`, `MSSS.poissonLine_typical`,
  `MSSS.poissonHyperplane_faceIntensity`, all `sorry`. The MSSS length functionals use the raw
  `MeasureTheory.Measure.hausdorffMeasure 1`, which is correct in dimension one.

* **122. Poisson–Voronoi tessellation.** For the Voronoi tessellation of a stationary Poisson
  process of intensity $\gamma$ in $\mathbb R^d$, the cell intensity is $\gamma$, so the
  typical cell has mean volume $1/\gamma$. In the plane, every vertex lies on three cells
  almost surely; the intensities of vertices and edges are $2\gamma$ and $3\gamma$; the
  typical cell has on average $6$ vertices and mean perimeter $4/\sqrt\gamma$; the mean
  edge length is $2/(3\sqrt\gamma)$; and the edge length per unit area is $2\sqrt\gamma$. In
  space the vertex and edge intensities are $\frac{24\pi^2}{35}\gamma$ and
  $\frac{48\pi^2}{35}\gamma$, and the face intensity is $(\frac{24\pi^2}{35}+1)\gamma$.

  *Assessment.* Absent from both libraries. TauCeti's nearest-point quantizer is deterministic.

  *Lean target.* Carriers: `TauCeti.Probability.IsPoissonRandomMeasure` with intensity
  `ENNReal.ofReal γ • volume` on `EuclideanSpace ℝ (Fin d)`, `0 < γ`, `1 ≤ d`. Definitions needed:
  the nuclei as the atoms; the nearest nuclei of a point; the `k`-faces as connected components of
  the points with exactly `d - k + 1` nearest nuclei, which is correct only after general position
  is proved; face intensities and typical means as in item 121. Conjuncts: cell intensity `γ` and
  mean typical volume `1/γ`; in the plane, general position, vertex and edge intensities, mean
  vertex number, mean perimeter, mean edge length, and edge length per unit area (lengths through
  `μHE[1]`); in space, vertex, edge, and face intensities. Small checks for the test file: `2γ`
  and `24π²/35 γ` from the general vertex formula, and `2/(3√γ)` with `4/√γ`. The planar and
  spatial constants need the Blaschke–Petkantschin formula, which no library has. Depends on items
  131 and 132. MSSS: `MSSS.voronoiNearest`, `MSSS.voronoiFaces`, `MSSS.nuclei`, and
  `MSSS.poissonVoronoi_cells`, `MSSS.poissonVoronoi_plane`, `MSSS.poissonVoronoi_space`, all
  `sorry`.

* **131. Typical cells and volume bias.** Let a stationary locally finite
  tessellation of $\mathbb R^d$ into compact convex cells with nonempty interiors
  have a measurable translation-equivariant centre $z(C)\in\mathop{\mathrm{int}}C$ for each
  cell. Suppose the centre process has intensity $\gamma\in(0,\infty)$,
  and the origin almost surely belongs to a unique cell $C_0$. The typical cell
  $C_{\mathrm{typ}}$ is the centred cell under the Palm law of the centre process
  marked with the centred cells. For nonnegative measurable translation-invariant
  $f$ and bounded Borel $W$ of positive volume,
  $$\mathbb E f(C_{\mathrm{typ}})=\frac{1}{\gamma|W|}
    \mathbb E\sum_{z(C)\in W}f(C),\qquad
    \mathbb E f(C_0)=\gamma\mathbb E[|C_{\mathrm{typ}}|f(C_{\mathrm{typ}})].$$
  Thus the typical cell has mean volume $1/\gamma$, and the zero cell has its
  volume-biased law for translation-invariant observables.

  *Assessment.* Mathlib supplies Haar measure and the disintegration of measures on standard Borel
  spaces (`MeasureTheory.Measure.condKernel`). A marked process of tessellation centres, the
  corresponding typical cell, and its volume-bias identity are absent.

  *Lean target.* Carriers: a random tessellation as a measurable map into point configurations on
  `NonemptyCompacts (EuclideanSpace ℝ (Fin d))` with convex members, through the point-process
  carriers of Part 4. Definitions needed: a measurable centre map `z` with `z (C + x) = z C + x`
  and `z C ∈ interior C`; the marked centre process; its Palm mark law, which is the typical cell;
  the zero cell, defined on the event that `0` lies in exactly one cell. Hypotheses: stationarity,
  local finiteness, cells compact convex with nonempty interior, centre intensity `γ` with `0 < γ`
  and `γ < ∞`, `0` almost surely in a unique cell. Conjuncts, for measurable translation-invariant
  `f ≥ 0` with values in `ℝ≥0∞` and Borel `W` with `0 < volume W < ∞`: the Campbell form of the
  typical mean, and the volume-bias identity `E f(C₀) = γ E[|C_typ| f(C_typ)]` with both sides in
  `ℝ≥0∞`. `f = 1` gives `E |C_typ| = 1/γ`. Depends on the stationary Palm theory and refined
  Campbell theorem of item 83, supplied by PR #417. MSSS: none; the means of items 121 and 122 are
  stated through `MSSS.HasTypicalMean` instead.

* **132. Containment probabilities for the typical Poisson–Voronoi cell.** For a
  homogeneous Poisson process $\eta$ of intensity $\gamma>0$ in $\mathbb R^d$,
  $d\ge1$, the typical cell centred at its nucleus has the law of the cell of
  $0$ in the tessellation generated by $\eta+\delta_0$. For compact $K$ containing
  $0$ define its **Voronoi flower** by $D(K)=\bigcup_{x\in K}B^\circ(x,\|x\|)$,
  using open balls. Then
  $$\mathbb P(K\subset C_{\mathrm{typ}})=e^{-\gamma|D(K)|}.$$
  The radius $R_0$ of the largest ball about the nucleus contained in the typical
  cell satisfies $\mathbb P(R_0>r)=\exp(-\gamma\omega_d(2r)^d)$ for $r\ge0$.

  *Assessment.* TauCeti supplies Poisson counts on measurable sets, and Mathlib Euclidean ball
  volumes. The typical cell through Poisson Palm conditioning, its containment criterion, and the
  distribution of the centred inradius are absent.

  *Lean target.* Carriers: `TauCeti.Probability.IsPoissonRandomMeasure` with intensity
  `ENNReal.ofReal γ • volume`, `0 < γ`, `1 ≤ d`, and
  `TauCeti.Probability.IsPoissonRandomMeasure.hasLaw` for the void probability of a measurable set
  of finite volume. Definitions needed: the Voronoi cell of `0` for the configuration `η + δ₀`;
  the flower `⋃ x ∈ K, Metric.ball x ‖x‖` for compact `K` containing `0`. Conjuncts: the Slivnyak
  description of the typical cell, which needs item 84 and the Palm theory of PR #417; the
  deterministic criterion that `K` lies in the cell of `0` exactly when the configuration misses
  the flower; `P (K ⊆ C) = exp (-γ |D(K)|)`, which follows at the pins with the cell of `0` for
  `η + δ₀` taken as the definition, the flower being measurable as an open set and bounded by
  `closedBall 0 (2 R)` when `K ⊆ closedBall 0 R`; and the inradius tail for `r ≥ 0`, from
  `D (closedBall 0 r) = ball 0 (2 r)`. The negative control `K = {0}` gives `D = ∅` and
  probability `1`. Depends on items 84 and 131 for the Palm reading. MSSS: none.
