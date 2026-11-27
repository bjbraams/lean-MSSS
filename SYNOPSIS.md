# Spatial statistics: synopsis

This synopsis describes the mathematical content of the references in
[MSSS-bib.md](MSSS-bib.md). It is addressed to mathematicians and is independent of the
library-coverage inventory. Proofs are outside its scope.

The synopsis has 133 numbered entries in six parts:

* [1. Random fields and covariance functions](#1-random-fields-and-covariance-functions), items 1–23.
* [2. Geostatistics: spatial prediction and covariance-parameter inference](#2-geostatistics-spatial-prediction-and-covariance-parameter-inference), items 24–46.
* [3. Lattice models, Markov random fields, and Gibbs measures](#3-lattice-models-markov-random-fields-and-gibbs-measures), items 47–67 and 123.
* [4. Point processes and random measures](#4-point-processes-and-random-measures), items 68–91 and 124–127.
* [5. Gibbs point processes and statistics of point patterns](#5-gibbs-point-processes-and-statistics-of-point-patterns), items 92–111 and 128–129.
* [6. Stochastic and integral geometry](#6-stochastic-and-integral-geometry), items 112–122, 130–132 and 168.

The source basis is the local copies in [References/](References/). Schoenberg's papers
(1938, 1942) are not local; their theorems are cited through Gneiting (2013), the
*Handbook of Spatial Statistics*, Stein, Matérn, Chilès–Delfiner, and Cressie, which restate
them. Cressie and Wikle's *Statistics for Spatio-Temporal Data* is not local and is not used.
Schmidt (LNM 2120) was searched and supplies only the definition cited in Part 1; Antipova's applied text was not consulted. The local
copy of Møller and Waagepetersen (2004) has no printed page numbers, so that book is cited by
definition, proposition, theorem, and equation numbers only.

Each part gives definitions and principal theorems, followed by a reference guide. The
reference guides name the source basis of each entry with printed page numbers, record
differences of convention between the sources, and note places where a source statement
needs an additional hypothesis or contains a misprint. The formulation recorded in an entry
is a standard usable one, with the hypotheses stated in full.

Numbered entries, cited as SYNOPSIS item $k$, are stable identifiers. An entry keeps its
number when its wording is revised. A removed number is not reused, and a new entry takes
the next free number.

The sibling project lean-CKSD contains an elementary account of kriging, the Matérn family,
semivariograms, and point-pattern summaries in
[CKSD SYNOPSIS106](../lean-CKSD/SYNOPSIS106.md), items 20–27. The present synopsis treats
the same topics at research-monograph level and is self-contained.

## Conventions

A **random field** on an index set $T$ is a family $Z=\{Z(t):t\in T\}$ of real random
variables on one probability space. It is **second-order** when $\mathbb E Z(t)^2<\infty$
for every $t$. A function $K:T\times T\to\mathbb C$ is **positive definite** when
$\sum_{j,k}c_j\bar c_kK(t_j,t_k)\ge0$ for all finite families of points and complex
coefficients; it is **strictly positive definite** when the sum is positive for pairwise
distinct points unless all $c_j$ vanish. A function $C$ on $\mathbb R^d$ is positive
definite when $(s,t)\mapsto C(s-t)$ is.

The Fourier convention is the angular one: a finite measure $F$ on $\mathbb R^d$ has
characteristic function $\int e^{i\langle h,\omega\rangle}F(d\omega)$, and an integrable
covariance $C$ has spectral density
$f(\omega)=(2\pi)^{-d}\int e^{-i\langle h,\omega\rangle}C(h)\,dh$.
Chilès and Delfiner use ordinary frequency $e^{2\pi i\langle u,h\rangle}$, so their
spectral densities differ by powers of $2\pi$.

$\mathcal K_\nu$ is the modified Bessel function of the second kind and $J_\mu$ the Bessel
function of the first kind. For $d\ge1$ put
$$\Omega_d(t)=\Gamma(d/2)\,(2/t)^{(d-2)/2}J_{(d-2)/2}(t),\qquad \Omega_d(0)=1,$$
so that $\Omega_1=\cos$, $\Omega_2=J_0$, and $\Omega_3(t)=\sin t/t$. The function
$\Omega_d(\|\cdot\|)$ is the characteristic function of the uniform law on the unit sphere
of $\mathbb R^d$. $\omega_d$ is the volume of the unit ball of $\mathbb R^d$ and $|A|$ the
Lebesgue measure of a Borel set $A\subseteq\mathbb R^d$.

## 1. Random fields and covariance functions

This part covers the existence of random fields, stationarity, the characterisation of
covariance and variogram functions through Bochner's and Schoenberg's theorems, the Matérn
family, positive definite functions on spheres and in space–time, and the sample-path
theory of Gaussian fields.

### Existence and stationarity

* **1. Kolmogorov existence theorem for random fields.** Let $T$ be a set and, for every
  finite tuple $(t_1,\dots,t_n)$ of points of $T$, let $P_{t_1,\dots,t_n}$ be a Borel
  probability measure on $(\mathbb R^m)^n$. Suppose the family is consistent: permuting the
  $t_j$ permutes the coordinates of $P_{t_1,\dots,t_n}$ accordingly, and the image of
  $P_{t_1,\dots,t_n}$ under deletion of the last coordinate is $P_{t_1,\dots,t_{n-1}}$.
  Then there is an $\mathbb R^m$-valued random field on $T$ whose finite-dimensional
  distributions are the $P_{t_1,\dots,t_n}$. No regularity of sample paths follows.

* **2. Gaussian fields with given mean and covariance.** Let $T$ be a set,
  $m:T\to\mathbb R$ a function and $C:T\times T\to\mathbb R$ symmetric and positive
  definite. There is a Gaussian random field $Z$ on $T$, that is, one whose finite linear
  combinations are Gaussian, with $\mathbb E Z(t)=m(t)$ and
  $\mathop{\mathrm{Cov}}(Z(s),Z(t))=C(s,t)$. Its law is determined by $(m,C)$. Conversely,
  the covariance function of every second-order field is symmetric and positive definite.

Let $Z$ be a random field on $\mathbb R^d$. It is **strictly stationary** when the law of
$(Z(t_1+h),\dots,Z(t_n+h))$ does not depend on $h$. It is **second-order stationary** when
it is second-order, $\mathbb E Z(t)=\mu$ is constant, and
$\mathop{\mathrm{Cov}}(Z(s),Z(t))=C(s-t)$; $C$ is its **stationary covariance**. It is
**isotropic** when moreover $C(h)=C_0(\|h\|)$. It is **intrinsically stationary** when
$\mathbb E(Z(s+h)-Z(s))=0$ and $\mathop{\mathrm{Var}}(Z(s+h)-Z(s))=2\gamma(h)$ depend only
on $h$; $2\gamma$ is the **variogram** and $\gamma$ the **semivariogram**. A strictly
stationary second-order field is second-order stationary, and for Gaussian fields the two
notions coincide. A second-order stationary field is intrinsically stationary with
$\gamma(h)=C(0)-C(h)$. Brownian motion on $\mathbb R$ is intrinsically stationary with
$\gamma(h)=|h|/2$ but not second-order stationary.

* **3. Elementary properties of stationary covariances.** Let $C$ be the stationary
  covariance of a second-order stationary field on $\mathbb R^d$. Then $C(0)\ge0$,
  $C(-h)=C(h)$, $|C(h)|\le C(0)$, and $C$ is positive definite. For all $s,h$,
  $$|C(s+h)-C(s)|\le\sqrt{2C(0)\bigl(C(0)-C(h)\bigr)},$$
  so $C$ is uniformly continuous on $\mathbb R^d$ if it is continuous at $0$. For every
  linear map $A$ of $\mathbb R^d$, $h\mapsto C(Ah)$ is a stationary covariance. The class of
  stationary covariances on $\mathbb R^d$ is closed under nonnegative linear combinations,
  products, pointwise limits, and mixtures $\int C(\cdot\,;u)\,\mu(du)$ against a positive
  measure, provided the limit or integral exists for every $h$.

### Spectral theory

* **4. Bochner's theorem.** A continuous function $C:\mathbb R^d\to\mathbb C$ is positive
  definite if and only if there is a finite nonnegative Borel measure $F$ on
  $\mathbb R^d$ with
  $$C(h)=\int_{\mathbb R^d}e^{i\langle h,\omega\rangle}F(d\omega),\qquad h\in\mathbb R^d .$$
  The **spectral measure** $F$ is unique and $F(\mathbb R^d)=C(0)$. $C$ is real if and only
  if $F$ is symmetric, and then $C(h)=\int\cos\langle h,\omega\rangle\,F(d\omega)$. If
  $C\in L^1(\mathbb R^d)$, then $F$ has the continuous nonnegative density
  $f(\omega)=(2\pi)^{-d}\int e^{-i\langle h,\omega\rangle}C(h)\,dh$. For a positive
  definite function, continuity everywhere is equivalent to continuity at $0$. The
  covariances of mean-square continuous second-order stationary fields on $\mathbb R^d$
  are exactly the real functions of this form. On the lattice $\mathbb Z^d$ (Herglotz) every
  positive definite function is $C(h)=\int_{[-\pi,\pi)^d}e^{i\langle h,\omega\rangle}F(d\omega)$
  with $F$ finite and nonnegative.

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

* **6. Mean-square continuity.** A second-order field $Z$ on $S\subseteq\mathbb R^d$ is
  **mean-square continuous** at $s$ when $\mathbb E(Z(s_n)-Z(s))^2\to0$ whenever $s_n\to s$.
  A centred second-order field is mean-square continuous on $S$ if and only if its
  covariance $C(s,t)$ is continuous at every diagonal point $(s,s)$; a field that is not
  centred is mean-square continuous if and only if, in addition, its mean is continuous. For a
  second-order
  stationary field, $\mathbb E(Z(x)-Z(y))^2=2(C(0)-C(x-y))$, so $Z$ is mean-square
  continuous if and only if $C$ is continuous at $0$, and then $C$ is continuous
  everywhere. Mean-square continuity does not imply continuity of sample paths.

* **7. Mean-square differentiability.** Let $Z$ be a centred second-order stationary
  process on $\mathbb R$ with covariance $K$ and spectral measure $F$, and let $m\ge1$. The
  following are equivalent: $Z$ is $m$ times mean-square differentiable;
  $\int\omega^{2m}F(d\omega)<\infty$; $K^{(2m)}(0)$ exists and is finite. In that case $K$
  is $2m$ times differentiable on $\mathbb R$, and $Z^{(m)}$ is second-order stationary with
  covariance $(-1)^mK^{(2m)}$. A process may have analytic sample paths without being
  mean-square differentiable: $Z(t)=\cos(Xt+Y)$ with $X$ standard Cauchy and $Y$ uniform on
  $[0,2\pi)$ independent of $X$.

### Isotropic covariances

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

* **9. Lower bounds for isotropic correlations.** Let $d\ge1$ and $\varphi\in\Phi_d$. Then
  $\varphi(t)\ge-1/d$ for all $t$. The sharp bound is
  $\varphi(t)\ge\inf_{s\ge0}\Omega_d(s)$, which is attained by $\varphi=\Omega_d(s_0\,\cdot)$
  for suitable $s_0$; numerically the bound is $-0.4028$ for $d=2$ (at $s_0=3.8317$),
  $-0.2172$ for $d=3$ (at $s_0=4.4934$), and $-0.1323$ for $d=4$ (at $s_0=5.1356$), to four
  places. If $d\ge2$ and $\varphi(t_0)=1$ for some $t_0>0$, then
  $\varphi\equiv1$.

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

* **11. Pólya-type criteria and compact support.** (a) If $\varphi:[0,\infty)\to\mathbb R$
  is continuous and convex with $\varphi(0)=1$ and $\varphi(t)\to0$ as $t\to\infty$, then
  $\varphi\in\Phi_1$. (b) For $a>0$ and $\nu>0$, the truncated power function
  $(1-t/a)_+^{\nu}$ belongs to $\Phi_n$ if $\nu\ge(n+1)/2$, and only then. In particular the
  triangular function $(1-t/a)_+$ belongs to $\Phi_1$ but not to $\Phi_2$.

### The Matérn family

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

* **13. Smoothness of Matérn fields.** A second-order stationary process on $\mathbb R$
  with Matérn covariance of smoothness $\nu$ is $m$ times mean-square differentiable if and
  only if $\nu>m$. For fixed $\theta>0$, the small-lag orders of
  $1-\varphi_{\nu,\theta}(t)$ as $t\downarrow0$ are $t^{2\nu}$ for $0<\nu<1$,
  $t^2\log(1/t)$ for $\nu=1$, and $t^2$ for $\nu>1$, in each case up to positive
  multiplicative constants. The principal irregular term of $\varphi_{\nu,\theta}$ is a
  multiple of $t^{2\nu}$ when $\nu\notin\mathbb N$ and of $t^{2\nu}\log t$ when
  $\nu\in\mathbb N$.

### Variograms

* **14. Properties of variograms.** Let $Z$ be intrinsically stationary on $\mathbb R^d$
  with semivariogram $\gamma$. Then:
  (a) $\gamma(0)=0$ and $\gamma(-h)=\gamma(h)\ge0$;
  (b) $\gamma$ is **conditionally negative definite**: for all points $s_1,\dots,s_n$ and
  $a\in\mathbb R^n$ with $\sum_ia_i=0$,
  $$\mathop{\mathrm{Var}}\Bigl(\sum_ia_iZ(s_i)\Bigr)=-\sum_{i,j}a_ia_j\gamma(s_i-s_j)\ge0;$$
  (c) for every linear map $A$, $h\mapsto\gamma(Ah)$ is a semivariogram, and nonnegative
  combinations, mixtures, and pointwise limits of semivariograms are semivariograms;
  (d) if $\gamma$ is continuous at $0$, it is continuous everywhere, with
  $|\gamma(s+h)-\gamma(s)|\le\sqrt{\gamma(h)}\bigl(\sqrt{\gamma(s)}+\sqrt{\gamma(s+h)}\bigr)$;
  (e) $\gamma(nh)\le n^2\gamma(h)$ for $n\in\mathbb N$, and if $\gamma$ is bounded near $0$
  there are $a,b\ge0$ with $\gamma(h)\le a\|h\|^2+b$ for all $h$.

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

### Space–time covariances and spheres

* **16. Cressie–Huang criterion.** Let $C:\mathbb R^d\times\mathbb R\to\mathbb R$ be
  continuous, bounded, integrable, and symmetric, $C(-h,-u)=C(h,u)$. Then $C$ is positive
  definite on $\mathbb R^{d+1}$ if and only if, for almost every $\omega\in\mathbb R^d$, there
  is a continuous positive definite function $F_\omega:\mathbb R\to\mathbb C$ such that
  $F_\omega(u)=\int_{\mathbb R^d}e^{-i\langle h,\omega\rangle}C(h,u)\,dh$ for almost every $u$.
  A continuous, bounded, symmetric $C$ is positive definite if and only if
  $e^{-a\|h\|-b|u|}C(h,u)$ is positive definite for all $a,b>0$.

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

* **19. From Euclidean space to the sphere.** (a) If $k\ge2$ and $\varphi\in\Phi_k$, then
  $\theta\mapsto\varphi(2\sin(\theta/2))$, the correlation in chordal distance, belongs to
  $\Psi_{k-1}$, and to $\Psi_{k-1}^+$ if $\varphi$ is not constant. (b) If $\varphi\in\Phi_3$
  and $\varphi(t)=0$ for $t\ge\pi$, then $\varphi|_{[0,\pi]}\in\Psi_3^+$, as a function of
  great-circle distance. (c) If $\varphi$ is completely monotone, non-constant, and
  $\varphi(0)=1$, then $\theta\mapsto\varphi(\theta/c)$ belongs to $\Psi_\infty^+$ for every
  $c>0$. (d) $e^{-(\theta/c)^\alpha}$ belongs to $\Psi_\infty^+$ for $\alpha\in(0,1]$ and to
  no $\Psi_d$ for $\alpha>1$; the Matérn correlation in great-circle distance belongs to
  $\Psi_\infty^+$ for $\nu\in(0,\tfrac12]$ and to no $\Psi_d$ for $\nu>\tfrac12$.

### Gaussian fields: continuity, suprema, and excursion sets

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

* **21. Borell–TIS inequality.** Let $f$ be a centred Gaussian field, almost surely bounded
  on $T$, and separable. Put $\|f\|=\sup_{t\in T}f(t)$ and
  $\sigma_T^2=\sup_{t\in T}\mathbb E f(t)^2$. Then $\mathbb E\|f\|<\infty$ and for every $u>0$
  $$\mathbb P\{\|f\|-\mathbb E\|f\|>u\}\le e^{-u^2/(2\sigma_T^2)} .$$

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

### Reference guide for Part 1

Items 1–2: Spodarev (LNM 2068), Theorem 9.2, p. 282; Cressie, §2.3, p. 52; van Lieshout
(2019), Proposition 2.1, p. 12; Adler–Taylor, p. 11; Gaetan–Guyon, Definition 1.3, p. 3;
Schmidt (LNM 2120), Definition 11.2, p. 323. Stationarity definitions: Cressie, p. 53 and
(2.2.5)–(2.2.6), p. 40; Gaetan–Guyon, Definitions 1.4–1.6, pp. 3–8; Spodarev,
Definitions 9.20–9.23, pp. 306–307; van Lieshout (2019), Definitions 2.3–2.5, pp. 13–16.
Gaetan–Guyon define intrinsic stationarity through the stationarity of every increment
process, which is equivalent to the definition above; they give the variogram $|h|$ of
Brownian motion on p. 8. Item 3: Gaetan–Guyon, Proposition 1.1, p. 4, whose proof gives the
continuity estimate; Stein, §2.3, pp. 19–20, with the same estimate on p. 21;
Chilès–Delfiner, p. 62; Spodarev, Theorem 9.13, p. 312, for scaling, sums, products and
limits, and Theorem 9.14, pp. 312–313, for linear substitution and mixtures.

Items 4–5: Stein, §2.5, Theorem 1, p. 24, inversion (11), p. 25, and the spectral
representation (7), p. 23; Adler–Taylor, Theorems 5.4.1 and 5.4.2, pp. 109–110;
Spodarev, Theorem 9.6, p. 309, Remark 9.4, p. 310, Theorem 9.8 (lattice), p. 310;
van Lieshout (2019), Theorem 2.1, p. 18, with a complete proof in §2.5 from p. 20;
Gaetan–Guyon, (1.2), pp. 5–6; Handbook, (2.6)–(2.7), pp. 20–21; Cressie, (2.5.3)–(2.5.4),
p. 84; Chilès–Delfiner, (2.14)–(2.18), pp. 66–68, with the bounded continuous density of an
integrable covariance on p. 68 and the symmetry $W(-A)=\overline{W(A)}$ of the random measure
of a real field on p. 67. Stein's Theorem 1 assumes that a density exists rather than that
$C$ is integrable. Cressie, p. 84, writes "independent increments" where orthogonal
increments are meant. Item 6: Gaetan–Guyon, Definition 1.7 and Proposition 1.3, p. 16,
for centred fields; Stein, §2.4, pp. 20–21; Handbook, §2.6, p. 23. Item 7: Stein, §2.4,
pp. 21–22, and §2.6, pp. 26–27. Gaetan–Guyon, Proposition 1.4, pp. 16–17, gives a
nonstationary version; its hypothesis ("$\partial^2C/\partial s\partial t$ exists and is
finite on the diagonal") is weaker than the continuity at $(s,s)$ that its proof uses. In
the example of item 7 the spectral measure has density $1/(2\pi(1+\omega^2))$, so
$\int\omega^2F(d\omega)=\infty$, and the covariance is $e^{-|h|}/2$.

Items 8–11: the classes $\Phi_d$, complete monotonicity and Bernstein's theorem are in
Gneiting (2013), p. 1329, the Handbook, p. 21, Gneiting (2002), p. 592, and (9), p. 593, and
Chilès–Delfiner, footnote 13, p. 72. Gneiting (2013), (4)–(5), pp. 1329–1330, attributes
items 8 and 10 to Schoenberg (1938), which is not local; Handbook, (2.9)–(2.11),
pp. 21–22, Table 2.1, p. 22; Stein, §2.10, (26)–(29), pp. 43–46, Theorem 5, p. 44;
Adler–Taylor, Theorem 5.7.1, p. 115, and Theorem 5.7.2, p. 116; Spodarev,
Theorems 9.9–9.11, p. 311; Matérn, §2.3, pp. 13–16, (2.3.7)–(2.3.9), p. 15, (2.3.17), p. 16,
and (2.4.4)–(2.4.10), pp. 17–18; Chilès–Delfiner, (2.20)–(2.28), pp. 69–73, with the
criterion through $\varphi(\sqrt t)$ on p. 73; Gneiting (2002), pp. 592–593; Cressie,
pp. 84–86. Cressie, p. 85, states the nesting of the classes in the reverse direction. The
strict nesting and the strict positive definiteness in item 8 (Sun) are reported by
Gneiting (2013), p. 1330. The bound $-1/d$ and the rigidity statement of item 9 are in
Matérn, p. 13, and Adler–Taylor, Theorem 5.7.1, p. 115. The sources round the minima of
$\Omega_d$ outward: Stein, p. 45, the Handbook, Table 2.1, p. 22, Matérn, (2.3.17), p. 16,
and Gaetan–Guyon, p. 6, print $-0.218$ for $d=3$, and Matérn, p. 16, prints $-0.133$ for
$d=4$; Gaetan–Guyon, p. 6, print $-0.113$ for $d=4$, a misprint. The Handbook, p. 22, calls
members of $\Phi_\infty$ strictly decreasing; constants must be excluded. The examples with
$0<\alpha\le2$ in item 10 are in Gneiting (2013), Table 2, p. 1330. Item 11(a), Pólya's
criterion: Handbook, p. 23; Chilès–Delfiner, (2.20), p. 69; Cressie, p. 86. Item 11(b):
Chilès–Delfiner, pp. 63–64, state the equivalence and attribute it to Golubov (1981),
without proof; Spodarev, Theorem 9.9 (Pólya–Askey), p. 311; Gneiting (2013), Table 3,
p. 1331, lists the truncated power function in $\Phi_3$ for exponent at least $2$; Stein,
p. 47, for the triangular function.

Items 12–13: Stein, (14), p. 31, the small-lag expansions (15)–(16), p. 32, with the
statement on mean-square differentiability on pp. 31–32, restated in §2.10, (32)–(33),
pp. 48–50; Matérn, (2.4.5)–(2.4.7), pp. 17–18; Handbook, (2.13) and Table 2.2, p. 24;
Gneiting (2002), (10), p. 593; Gneiting (2013), Table 2, p. 1330, and (6), p. 1330;
van Lieshout (2019), Example 2.11, p. 18. Four parametrisations occur: Stein's
$\phi(\alpha r)^\nu\mathcal K_\nu(\alpha r)$, the normalised form above with scale $\theta$,
Gneiting's (2002) inverse scale $c$, and Stein's $\rho$-form (33), p. 50, in which the
correlation does not depend on $d$. Gneiting (2013), (36), p. 1345, and Table 2, p. 1330,
print the prefactor $2^{\nu-1}/\Gamma(\nu)$, a misprint for $2^{1-\nu}/\Gamma(\nu)$. Matérn
(2.4.7) admits $\nu=0$, which is degenerate. At $\nu=1$ the logarithmic term in Stein's
expansion (16), p. 32, gives the leading order $t^2\log(1/t)$. This is the boundary case in
the power-law descriptions in the Handbook, (2.12), p. 23, and Gneiting (2013), Table 2,
p. 1330. The Handbook's smoothness claim on p. 24 concerns sample paths, and Stein's
concerns mean-square derivatives. Complete monotonicity of the Matérn correlation for
$0<\nu\le\frac12$ is cited by Gneiting (2013), p. 1345, from Miller and Samko. The converse
is not stated in a local source: for $\nu>\frac12$ the right derivative at $0$ vanishes, and a
completely monotone function with this property is constant by Bernstein's theorem.

Items 14–15: Gaetan–Guyon, Proposition 1.2, pp. 8–9, and p. 10 for the equivalence of
(a) and (b) in item 15; Chilès–Delfiner, (2.9)–(2.11), pp. 63–64, and (2.21)–(2.22),
pp. 69–70, in ordinary frequency with $4\pi^2|u|^2$ in place of $\|\omega\|^2$; Cressie,
(2.5.6)–(2.5.8), pp. 86–88, where (2.5.7), p. 87, requires the measure to have no atom at the
origin; Stein, §2.9, p. 38. Gaetan–Guyon state item 14(d) at points where $\gamma$ is locally
bounded; the qualification is redundant, since $\gamma$ is finite and
$\sqrt{\gamma(s+h)}\le\sqrt{\gamma(s)}+\sqrt{\gamma(h)}$, and Chilès–Delfiner, p. 59, state
continuity everywhere. Chilès–Delfiner state the sign convention with $-\gamma$
conditionally positive definite. In item 15, (a) and (b) are equivalent and imply (c) only
with continuity; (c) implies (a) for every $\gamma$. For $\gamma(h)=|h|^\alpha$ on
$\mathbb R$ with $0<\alpha<2$, $\chi$ has density proportional to $|\omega|^{1-\alpha}$;
$\alpha=2$ is the quadratic form $Q$. Schoenberg's metric-embedding theorem is not stated
in any local source.

Items 16–19: Gneiting (2002), Theorem 1, p. 592, with the damping criterion on the same
page, Theorem 2, (11)–(14), p. 593, the family (4), p. 591, and Tables 1–2, p. 591;
Handbook, ch. 23, (23.9), pp. 430–431, and (23.12)–(23.13), p. 432, which take
$\beta\in(0,1]$; Gneiting (2013), Theorem 1, pp. 1332–1333, with the Gegenbauer
normalisation and the closure properties of item 18(d) on p. 1332, (7), p. 1331 (Yadrenko),
Theorems 2–3, pp. 1337–1338, Theorems 7–8, pp. 1343–1344, and Examples 1–2, p. 1345.
Schoenberg (1942) is not local and is cited through Gneiting (2013). Gneiting (2013), (15),
p. 1333, prints the Legendre series as $\sum b_{n,2}(n+1)^{-1}P_n(\cos\theta)$; since
$C_n^{1/2}(1)=1$, its own (11) gives $\sum b_{n,2}P_n(\cos\theta)$. Item 17 and
Gneiting (2013), Theorem 7, need $\varphi$ continuous at $0$, which the derivative conditions
on $(0,\infty)$ do not give; the definition above includes it. The Handbook, p. 432, lists
$\psi(r)=\log(ar^\alpha+1)$, which vanishes at $0$; Gneiting (2002), Table 2, uses
$\log(at^\alpha+b)/\log b$ with $b>1$.

Items 20–23: Adler–Taylor, (1.3.1), p. 12, with the standing assumption there that $d$ be
continuous for the topology of $T$, Definition 1.3.2, p. 13, Theorem 1.3.3 and
Corollary 1.3.4, p. 14, Theorem 1.3.5, p. 15, Theorem 1.4.1 with condition (1.4.4),
pp. 20–21, Theorem 1.5.4, p. 47; Theorem 2.1.1, p. 50; (11.1.3)–(11.1.4), p. 265,
Theorem 11.2.1 and (11.2.4), p. 267, Corollary 11.2.2, p. 269; Theorem 11.7.2 and
Corollary 11.7.3, (11.7.11)–(11.7.12), p. 293, with the Hermite polynomials
(11.6.9)–(11.6.10), p. 288; Theorem 12.4.1, p. 315; Theorem 15.9.4, (15.9.6), pp. 424–425,
and its special case Theorem 15.9.5, p. 425. Adler–Taylor state Theorem 1.5.4 for compact
groups, but its proof rests on Theorem 1.5.3, p. 45, which is stated for compact abelian
groups; they do not attribute it, and the attribution to Fernique is not in a local source.
In Theorem 2.1.1 separability is the standing convention of p. 15, not a further hypothesis.
Gaetan–Guyon, p. 16, and van Lieshout (2019), p. 19, state continuity criteria from Adler's
work. The Kolmogorov–Chentsov moment criterion is not stated in any local source; item 20
serves for Gaussian fields.

## 2. Geostatistics: spatial prediction and covariance-parameter inference

This part covers linear prediction (kriging) under known and unknown mean, the equivalence
and orthogonality of Gaussian measures with its consequences for prediction under a
misspecified covariance and for the consistency of covariance-parameter estimates under
infill (fixed-domain) asymptotics, likelihood-based estimation under increasing-domain
asymptotics, and variogram estimation.

Throughout, $Z=\{Z(x):x\in D\}$, $D\subseteq\mathbb R^d$, is a second-order field with mean
$m(x)$ and covariance $K(x,y)$. The observations are
$\mathbf Z=(Z(x_1),\dots,Z(x_n))^\top$ and the predictand is $Z(x_0)$. Write
$\mathbf K=(K(x_i,x_j))_{i,j\le n}$, $\mathbf k=(K(x_i,x_0))_{i\le n}$, $k_0=K(x_0,x_0)$,
and $\mathbf m=(m(x_i))_{i\le n}$.

### Linear prediction

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

* **25. Projection characterisation.** A predictor $\hat Z=m(x_0)+\lambda^\top(\mathbf Z-\mathbf m)$
  is the best linear predictor if and only if
  $\mathop{\mathrm{Cov}}(Z(x_i),Z(x_0)-\hat Z)=0$ for $i=1,\dots,n$; more generally, for
  observations indexed by an infinite set, the best linear predictor is the orthogonal
  projection in $L^2$ of the centred predictand onto the closed linear span of the centred
  observations, plus the mean. In particular
  $\mathop{\mathrm{Var}}Z(x_0)=\mathop{\mathrm{Var}}\hat Z+\mathbb E(Z(x_0)-\hat Z)^2$, and
  the best linear predictor is linear in the predictand.

* **26. Best predictor and Gaussian conditioning.** Let $T$ and $Y$ be random elements
  with $\mathbb E T^2<\infty$. For every measurable $t$ with $\mathbb E t(Y)^2<\infty$,
  $$\mathbb E(T-t(Y))^2=\mathbb E\mathop{\mathrm{Var}}(T\mid Y)+\mathbb E\bigl(\mathbb E(T\mid Y)-t(Y)\bigr)^2,$$
  so the conditional mean is the unique minimum-mean-squared-error predictor up to null
  sets. If $(X_1,X_2)\sim N(\mu,\Sigma)$ with $\Sigma_{22}$ nonsingular, then
  $X_1\mid X_2\sim N\bigl(\mu_1+\Sigma_{12}\Sigma_{22}^{-1}(X_2-\mu_2),\
  \Sigma_{11}-\Sigma_{12}\Sigma_{22}^{-1}\Sigma_{21}\bigr)$. Hence, for a Gaussian field
  with known $m$, $K$ and nonsingular $\mathbf K$, the simple kriging predictor is the best
  predictor among all square-integrable functions of the data, and the conditional
  variance $k_0-\mathbf k^\top\mathbf K^{-1}\mathbf k$ does not depend on the data.

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

* **28. Ordinary kriging.** In item 27 take $p=1$ and $f\equiv1$, with $\mathbf K$
  nonsingular and $\mathbf 1=(1,\dots,1)^\top$. The best linear unbiased predictor is
  $$\hat Z(x_0)=\mathbf k^\top\mathbf K^{-1}\mathbf Z+
  \frac{1-\mathbf 1^\top\mathbf K^{-1}\mathbf k}{\mathbf 1^\top\mathbf K^{-1}\mathbf 1}\,
  \mathbf 1^\top\mathbf K^{-1}\mathbf Z,$$
  its weights sum to $1$, and its mean squared error is
  $k_0-\mathbf k^\top\mathbf K^{-1}\mathbf k+(1-\mathbf 1^\top\mathbf K^{-1}\mathbf k)^2/
  (\mathbf 1^\top\mathbf K^{-1}\mathbf 1)$.

* **29. Kriging with a variogram.** Let $Z(x)=\mu+\delta(x)$ with $\mu$ unknown and
  $\delta$ intrinsically stationary with semivariogram $\gamma$. For weights with
  $\sum_i\lambda_i=1$ the prediction error is a contrast, and
  $$\mathbb E\Bigl(Z(x_0)-\sum_i\lambda_iZ(x_i)\Bigr)^2=2\sum_i\lambda_i\gamma(x_0-x_i)
  -\sum_{i,j}\lambda_i\lambda_j\gamma(x_i-x_j).$$
  The minimising weights solve $\sum_j\lambda_j\gamma(x_i-x_j)+\mu^\ast=\gamma(x_0-x_i)$
  for $i\le n$, $\sum_j\lambda_j=1$, and the minimum is
  $\sum_i\lambda_i\gamma(x_0-x_i)+\mu^\ast$. If the matrix
  $\Gamma=(\gamma(x_i-x_j))_{i,j\le n}$ is nonsingular and $\boldsymbol\gamma=(\gamma(x_0-x_i))_i$,
  the minimum equals
  $\boldsymbol\gamma^\top\Gamma^{-1}\boldsymbol\gamma-(\mathbf 1^\top\Gamma^{-1}\boldsymbol\gamma-1)^2/
  (\mathbf 1^\top\Gamma^{-1}\mathbf 1)$. The system is unchanged when $\gamma$ is replaced
  by $\gamma+c$. For a second-order stationary field the weights coincide with those of
  item 28.

* **30. Properties of kriging weights; exact interpolation.** Kriging weights and kriging
  variances do not depend on the observed values. Multiplying the covariance by $c>0$
  leaves the weights unchanged and multiplies the variance by $c$. For a stationary
  covariance, the weights and variances of simple and ordinary kriging are invariant under
  translation of the whole configuration, and so are those of universal kriging when the
  span of $f_1,\dots,f_p$ is translation invariant, as for polynomials of bounded degree.
  If $x_0=x_i$
  is a data site and $\mathbf K$ is nonsingular, simple, ordinary, and universal kriging
  return $Z(x_i)$ with variance $0$.

* **31. Dual kriging and radial basis interpolation.** Suppose the bordered matrix of item
  27 is nonsingular and let $z\in\mathbb R^n$ be the observed values. Let $(b,c)$ solve
  $$\begin{pmatrix}\mathbf K&\mathbf F\\ \mathbf F^\top&0\end{pmatrix}
  \begin{pmatrix}b\\ c\end{pmatrix}=\begin{pmatrix}z\\ 0\end{pmatrix}.$$
  Then the universal kriging prediction at every $x$ is
  $z^\ast(x)=\sum_ib_iK(x_i,x)+\sum_\ell c_\ell f_\ell(x)$, with $(b,c)$ independent of
  $x$, $\mathbf F^\top b=0$, and $z^\ast(x_i)=z_i$. For a stationary isotropic covariance
  this is radial basis function interpolation with polynomial side conditions; in one
  dimension the cubic generalised covariance gives the cubic spline interpolant.

* **32. Simple cokriging.** Let $(Z_1,\dots,Z_p)$ be a centred second-order vector field,
  with $Z_i$ observed at the finite set $S_i$, and let the target be $Z_1(x_0)$. The best
  linear predictor $\sum_i\lambda_i^\top\mathbf Z_i$ solves
  $\sum_j\mathbf C_{ij}\lambda_j=\mathbf c_{i0}$ for $i=1,\dots,p$, where $\mathbf C_{ij}$ is
  the cross-covariance matrix of $\mathbf Z_i$ and $\mathbf Z_j$ and $\mathbf c_{i0}$ the
  covariance vector of $\mathbf Z_i$ with the target. It is the orthogonal projection of the
  target on the span of all observations, and its mean squared error is at most that of the
  simple kriging predictor from $\mathbf Z_1$ alone.

* **33. Bayesian interpretation of universal kriging.** In the setting of item 27 with
  $\mathbf K$ nonsingular and $\mathbf F$ of full column rank, let the field be Gaussian
  and let $\beta\sim N(\mu,a^2V)$ independently, $V$ positive definite. The predictive law
  of $Z(x_0)$ given $\mathbf Z$ is Gaussian, and as $a^2\to\infty$ it converges to the
  normal law whose mean is the universal kriging predictor and whose variance is its mean
  squared error.

### Misspecified covariances and equivalence of Gaussian measures

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

* **36. Spectral criteria for equivalence.** Let $Z$ be centred and stationary on
  $\mathbb R^d$ under two spectral densities $f_0,f_1$. Suppose $f_0(\omega)\|\omega\|^\alpha$
  is bounded away from $0$ and $\infty$ for large $\|\omega\|$ and some $\alpha>0$
  (necessarily $\alpha>d$, since $f_0$ is integrable), and that
  for some $C<\infty$
  $$\int_{\|\omega\|>C}\Bigl(\frac{f_1(\omega)-f_0(\omega)}{f_0(\omega)}\Bigr)^2d\omega<\infty .$$
  Then $G_D(0,K_0)\equiv G_D(0,K_1)$ for every bounded $D$. On an interval, the exponential
  covariances $\sigma_i^2e^{-\alpha_i|t|}$ give equivalent laws if
  $\sigma_0^2\alpha_0=\sigma_1^2\alpha_1$ and orthogonal laws otherwise.

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

* **38. Matching high-frequency behaviour on a lattice.** Let $Z$ be centred and stationary
  on $\mathbb R^d$, observed on $\delta\mathbb Z^d$, with spectral densities $f_0,f_1$ such
  that $f_0/f_1$ is bounded away from $0$ and $\infty$ on $\mathbb R^d$,
  $f_1/f_0\to c\in(0,\infty)$ as $\|\omega\|\to\infty$, $f_1$ is bounded away from $0$ on
  bounded sets, and $f_1(\omega)\to0$ as $\|\omega\|\to\infty$. Then, as $\delta\downarrow0$,
  uniformly over predictands with positive error variance,
  $\mathbb E_1e_1^2/\mathbb E_0e_1^2\to c$ and $\mathbb E_0(e_0-e_1)^2/\mathbb E_0e_0^2\to0$.
  Here equivalence of the measures is not required.

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

* **41. Consistency of the microergodic parameter.** In item 40 let $\nu$ be known, let
  $D_n$ be an increasing sequence of finite sets whose union is bounded and infinite, and
  fix $\alpha_1>0$. Let $\hat\sigma_n^2$ maximise the Gaussian likelihood of
  $Z|_{D_n}$ over $\sigma^2$ with $\alpha=\alpha_1$. Then
  $\hat\sigma_n^2\alpha_1^{2\nu}\to\sigma_0^2\alpha_0^{2\nu}$ almost surely under the true
  parameters $(\sigma_0^2,\alpha_0)$.

### Likelihood inference under increasing-domain asymptotics

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

* **43. Profile likelihood.** Let $\mathbf Y\sim N(\mathbf X\beta,\sigma^2R(\tau))$ with
  $\mathbf X$ of full column rank and $R(\tau)$ positive definite. For fixed $\tau$ the
  likelihood is maximised by
  $\hat\beta(\tau)=(\mathbf X^\top R^{-1}\mathbf X)^{-1}\mathbf X^\top R^{-1}\mathbf Y$ and
  $\hat\sigma^2(\tau)=n^{-1}(\mathbf Y-\mathbf X\hat\beta)^\top R^{-1}(\mathbf Y-\mathbf X\hat\beta)$,
  and the profile log-likelihood is
  $-\tfrac12\{n\log(2\pi)+n\log\hat\sigma^2(\tau)+\log\det R(\tau)+n\}$.

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

### Variogram estimation and generalised linear models

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

* **46. Generalised linear geostatistical model.** Let $S$ be a stationary Gaussian field
  and, conditionally on $S$, let $Y_1,\dots,Y_n$ be independent with means $\mu_i$ given by
  $h(\mu_i)=S(x_i)+\sum_k\beta_kd_k(x_i)$, for a known link $h$, covariates $d_k$, and a
  generalised-linear-model error law with variance function $v$. The Gaussian model is the
  case of the identity link and normal errors, $Y_i=S(x_i)+\varepsilon_i$ with
  $\varepsilon_i$ independent $N(0,\tau^2)$. Without covariates and with $S$ centred,
  $\mu_i=g(\alpha+S(x_i))$ with $g=h^{-1}$ and conditional variances $v(\mu_i)$. Suppose
  $\mathbb E\,g(\alpha+S(x))^2<\infty$ and $\mathbb E\,v(g(\alpha+S(x)))<\infty$. Then for
  distinct sites $x_i\ne x_j$
  $$\tfrac12\mathbb E(Y_i-Y_j)^2
  =\tfrac12\mathbb E\bigl(g(\alpha+S(x_i))-g(\alpha+S(x_j))\bigr)^2
  +\mathbb E\,v\bigl(g(\alpha+S(x_i))\bigr),$$
  a function of $x_i-x_j$ (of $\|x_i-x_j\|$ when $S$ is isotropic), whose second term is a
  positive constant whenever $v>0$, so a nugget effect appears automatically.

### Reference guide for Part 2

Items 24–26: Stein, §1.2, (1)–(2), pp. 2–3, and §1.3, p. 5; Gaetan–Guyon, Proposition 1.9,
(1.35), p. 43, and p. 44; van Lieshout (2019), Theorems 2.2–2.3, pp. 27–28;
Chilès–Delfiner, (3.2)–(3.3), pp. 152–153, and §5.3.2, pp. 303–304; Diggle–Ribeiro,
Theorems 6.1–6.2, pp. 135–136, and (6.6)–(6.8), pp. 136–137. Diggle–Ribeiro's
Theorem 6.1 omits $\mathbb E T^2<\infty$, and their Theorem 6.2 omits the nonsingularity of
$\Sigma_{22}$. Gaetan–Guyon call simple kriging "BLUP", and van Lieshout calls ordinary
kriging "best linear predictor"; here, following Stein, the best linear predictor has a
known mean and the best linear unbiased predictor an unknown one.

Items 27–31: Stein, §1.5, (6)–(11), pp. 7–8, and pp. 8–9; Gaetan–Guyon, Proposition 1.10,
(1.36)–(1.37), p. 44, pp. 44–45, and p. 45 for exact interpolation and the cubic spline;
van Lieshout (2019), Theorem 2.4, p. 31, and §2.10, (2.14)–(2.15), pp. 32–33;
Chilès–Delfiner, (3.17)–(3.25), pp. 164–171, p. 153 for item 30 (shift invariance is
stated there for simple kriging in the stationary case), and §3.4.9,
(3.44)–(3.49), pp. 186–187, for item 31; Cressie, §3.2, (3.2.4)–(3.2.17), pp. 120–122;
Handbook, ch. 6, p. 82. The nonsingularity criterion in item 27(c) is elementary linear
algebra; Chilès–Delfiner, p. 170, state the sufficient condition. Chilès–Delfiner, p. 164,
state that the ordinary kriging system has a unique solution if and only if the covariance
matrix is strictly positive definite; only the "if" holds, as $\mathbf K=\mathop{\mathrm{diag}}(1,0)$
with $n=2$ shows. Cressie's closed form for item 29 needs $\Gamma$ nonsingular, which he
does not state. Chilès–Delfiner, p. 171, write "$\gamma$ strictly conditionally positive
definite" where $-\gamma$ is meant. The sign of the Lagrange multiplier differs between
Stein, Cressie, and Chilès–Delfiner. Items 32–33: Chilès–Delfiner, §5.3.1–5.3.2,
(5.1)–(5.3), pp. 303–304; Stein, §1.5, (12)–(13), p. 9; Diggle–Ribeiro, pp. 137–138.

Items 34–39: Stein, §3.2, (1), p. 58, (3)–(6), pp. 59–61, Theorem 1, p. 60; §3.8,
Theorem 10, (54)–(56), p. 102, whose hypotheses include $f_0\asymp f_1$ on all of
$\mathbb R^d$; §4.2, p. 111, (7)–(10), pp. 115–116, Lemmas 2–3 and
Theorem 4, pp. 116–117, Corollary 5, p. 117, (19)–(24), pp. 120–122, Theorem 1, pp.
113–114, (4)–(5), p. 113; §4.3, Theorem 7, (30)–(32), pp. 129–130, Theorem 8, (35)–(38),
p. 130, Corollary 9 and Theorem 10, p. 132, Theorem 11, p. 134; §6.2, pp. 163–164;
Handbook, ch. 6, (6.1)–(6.4) and Theorem 1, pp. 82–83, and p. 86; Zhang, (3)–(5), p.
252. The Handbook (6.1) and Zhang (4) require only $\alpha>0$; integrability of $f_0$ forces
$\alpha>d$, and Stein, p. 120, phrases the condition through his class $Q_d$. The variance
formula of item 39 is Stein, p. 113, with (5) there; at $K(t)=e^{-|t|}$ ($D=1$) one has
$n\mathop{\mathrm{Var}}U_n=1.983$ and $1.998$ at $n=100$ and $1000$. Stein notes, p. 120,
that the claim of Ibragimov and Rozanov that the integral
condition of item 36 is necessary in one dimension is false. Stein, p. 163, warns that
microergodicity need not imply the existence of consistent estimators for an uncountable
parameter set.

Items 40–41: Zhang, (1)–(2), p. 251, Theorems 1–2, p. 252, Corollaries 1–2 and (6)–(7),
p. 253, Theorem 3, p. 253; Handbook, ch. 6, p. 86; Stein, §6.5, pp. 176–177;
Diggle–Ribeiro, p. 113. Zhang's Corollary 1 requires $d\le3$ and an infinite $T$, though he
writes only "$T$ bounded". His isotropic spectral density (2) omits the factor
$\Gamma(\nu+d/2)/\Gamma(\nu)$, which does not affect the equivalence condition, and his
remark that the field is $[\nu]-1$ times mean-square differentiable should read
$\lceil\nu\rceil-1$. In other parametrisations the microergodic quantity is
$\sigma^2/\phi^{2\kappa}$ (Diggle–Ribeiro, $\phi=1/\alpha$, $\kappa=\nu$) and Stein's spectral
coefficient $\phi$. For the exponential covariance on an interval, item 41 is due to Ying
(1991), as reported by Zhang and the Handbook.

Items 42–44: Mardia–Marshall, (2.1)–(2.5), p. 136, Theorems 1–2, pp. 138–139, Theorem 3,
p. 140; Gaetan–Guyon, (5.19)–(5.22), pp. 182–183, Theorem 5.2, p. 183, Corollary 5.1,
p. 184; Diggle–Ribeiro, (5.12)–(5.16), pp. 112–113, and §5.4.5, pp. 116–117. Mardia and
Marshall rest on Sweeting (1980) and do not discuss the existence or uniqueness of the
maximiser; their conclusion $\hat\phi_n\sim N(\phi,B_n^{-1})$ is written informally, and item 42
states the normalised form. They use $q$ for the regression and $p$ for the covariance
dimension. Diggle–Ribeiro's example $A=I-\mathbf X(\mathbf X^\top\mathbf X)^{-1}\mathbf X^\top$ is
square and singular; item 44 uses $n-q$ independent contrasts.

Items 45–46: Cressie, (2.4.1)–(2.4.3), p. 69, and pp. 70, 76; Gaetan–Guyon, (5.1),
p. 151, Proposition 5.1, p. 153, and Proposition 5.3, p. 157, which gives asymptotic
normality under increasing-domain mixing conditions; Diggle–Ribeiro, §1.4, (1.1), p. 13,
§2.2, p. 29, §4.1, pp. 79–80, §4.2, (4.1), p. 81, and §5.2, p. 103; Zhang, p. 251. The
extracted text of
Gaetan–Guyon's formula for $A(h)$ is unclear; item 45(b) is stated from first principles.

## 3. Lattice models, Markov random fields, and Gibbs measures

This part covers conditionally specified models on a finite or countable set of sites,
including the Brook–Besag factorisation, the Hammersley–Clifford theorem, Besag's auto-models,
conditional and simultaneous autoregressions, Gaussian Markov random fields, Gibbs measures
on infinite lattices, estimation by coding and pseudolikelihood, finite Gibbs sampling, and the
stochastic partial differential equation link between Matérn fields and sparse Gaussian
Markov random fields.

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

### Conditional specification and the Hammersley–Clifford theorem

* **47. Brook's factorisation lemma.** Let $\pi$ satisfy the positivity condition and let
  $x,y$ lie in its support. Then
  $$\frac{\pi(x)}{\pi(y)}=\prod_{i=1}^n
  \frac{\pi_i(x_i\mid x_1,\dots,x_{i-1},y_{i+1},\dots,y_n)}
  {\pi_i(y_i\mid x_1,\dots,x_{i-1},y_{i+1},\dots,y_n)} .$$
  Consequently two densities satisfying the positivity condition, with the same support and
  the same full conditionals on it, coincide.

* **48. Canonical potential.** Let $S$ be finite, $L$ countable, $\pi>0$ on $L^S$, and fix
  $a\in L$. For $B\subseteq S$ let $x^B$ agree with $x$ on $B$ and equal $a$ off $B$, and put
  $$V_A(x)=\sum_{B\subseteq A}(-1)^{|A\setminus B|}\log\pi(x^B),\qquad A\subseteq S .$$
  Then $\pi(x)=\exp\sum_{A\subseteq S}V_A(x)$, each $V_A$ depends only on $x_A$, and
  $V_A(x)=0$ whenever $A\ne\emptyset$ and $x_i=a$ for some $i\in A$. $V$ is the unique
  potential with these properties, and each $V_A$ can be written through the full
  conditionals. The proof is Möbius inversion on the lattice of subsets of $S$.

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

* **51. Auto-Poisson model.** Let $E_i=\mathbb N_0$ and let the full conditionals be Poisson
  with $\log\mathbb E(X_i\mid x_{-i})=\alpha_i+\sum_{j\ne i}\beta_{ij}x_j$, $\beta_{ij}=\beta_{ji}$.
  The function
  $Q(x)=\sum_i(\alpha_ix_i-\log x_i!)+\sum_{i<j}\beta_{ij}x_ix_j$ satisfies
  $\sum_{x\in\mathbb N_0^n}e^{Q(x)}<\infty$, so that a joint law with these conditionals
  exists, if and only if $\beta_{ij}\le0$ for all $i\ne j$.

### Conditional and simultaneous autoregressions

* **52. Gaussian conditional specification.** Let the full conditionals be
  $X_i\mid x_{-i}\sim N\bigl(\mu_i+\sum_{j\ne i}c_{ij}(x_j-\mu_j),\ \kappa_i\bigr)$ with
  $\kappa_i>0$. Put $C=(c_{ij})$ with zero diagonal and $M=\mathop{\mathrm{diag}}(\kappa_i)$.
  These are the full conditionals of a joint law if and only if $M^{-1}(I-C)$ is symmetric
  and positive definite, that is, $c_{ij}\kappa_j=c_{ji}\kappa_i$ and $I-C$ has positive
  eigenvalues; the joint law is then $N\bigl(\mu,(I-C)^{-1}M\bigr)$, a **conditional
  autoregression**. If $C=\phi N$ with $N$ the adjacency matrix and $\phi\ne0$, symmetry
  forces $\kappa_i$ to be constant on each connected component of the graph, and then
  $|\phi|\,|\partial i|<1$ for every $i$ suffices.

* **53. Simultaneous autoregressions are conditional autoregressions.** Let
  $X=\mu+B(X-\mu)+\varepsilon$ with $B$ of zero diagonal, $I-B$ nonsingular, and
  $\varepsilon\sim N(0,\Lambda)$, $\Lambda=\mathop{\mathrm{diag}}(\lambda_i)$ positive. Then
  $X\sim N\bigl(\mu,(I-B)^{-1}\Lambda(I-B^\top)^{-1}\bigr)$, and there is a unique conditional
  autoregression $(C,M)$ with the same law:
  $M^{-1}(I-C)=(I-B^\top)\Lambda^{-1}(I-B)$, so
  $\kappa_i^{-1}=\lambda_i^{-1}+\sum_jb_{ji}^2\lambda_j^{-1}$. Every neighbour pair $\{i,j\}$
  has $b_{ij}\ne0$, $b_{ji}\ne0$, or $b_{li}b_{lj}\ne0$ for some $l$; the converse fails,
  since $\sum_lb_{li}b_{lj}\lambda_l^{-1}$ can cancel the other terms.

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

### Gaussian Markov random fields

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

* **57. Conditional laws.** If $x\sim N_C(b,Q)$ and $\{1,\dots,n\}=A\cup B$ is a partition
  into nonempty sets, then $x_A\mid x_B\sim N_C(b_A-Q_{AB}x_B,\ Q_{AA})$, a Gaussian Markov
  random field for the induced subgraph on $A$; in mean form,
  $\mathbb E(x_A\mid x_B)=\mu_A-Q_{AA}^{-1}Q_{AB}(x_B-\mu_B)$. If in addition
  $y\mid x\sim N(x,P^{-1})$ with $P$ positive definite, then $x\mid y\sim N_C(b+Py,\ Q+P)$.

* **58. Cholesky factor and conditional independence.** Let $Q=LL^\top$ with $L$ lower
  triangular with positive diagonal. If $z\sim N(0,I)$ and $L^\top v=z$, then
  $\mu+v\sim N(\mu,Q^{-1})$. For $i<j$ put $F(i,j)=\{i+1,\dots,n\}\setminus\{j\}$; then
  $L_{ji}=0$ if and only if $x_i$ and $x_j$ are conditionally independent given
  $x_{F(i,j)}$. In particular $L_{ji}=0$ whenever $F(i,j)$ separates $i$ from $j$ in $G$
  (the converse fails), and if $Q$ has bandwidth $p$, so that $Q_{ij}=0$ for $|i-j|>p$, then
  $L_{ji}=0$ for $j-i>p$. Also $\mathop{\mathrm{Var}}(x_i\mid x_{i+1},\dots,x_n)=L_{ii}^{-2}$.

* **59. Improper and intrinsic Gaussian Markov random fields.** Let $Q$ be symmetric
  positive semidefinite of rank $n-k$, $0<n-k<n$. The improper density
  $(2\pi)^{-(n-k)/2}(\det{}^\ast Q)^{1/2}\exp\{-\tfrac12(x-\mu)^\top Q(x-\mu)\}$, with
  $\det^\ast$ the product of the nonzero eigenvalues, defines an **improper** Gaussian
  Markov random field of rank $n-k$; it is an **intrinsic** Gaussian Markov random field of
  first order when $k=1$ and $Q\mathbf 1=0$. Then the density is invariant under
  $x\mapsto x+c\mathbf 1$, and for each $i$ with $Q_{ii}>0$ the full conditional mean
  $\sum_{j\sim i}(-Q_{ij}/Q_{ii})x_j$ is an affine combination of the neighbours: its weights
  sum to one but need not be nonnegative. The first-order random walk, with independent increments
  $x_{i+1}-x_i\sim N(0,\kappa^{-1})$, has $Q=\kappa D^\top D$ with $D$ the first-difference
  matrix, of rank $n-1$.

### Gibbs measures on infinite lattices

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

* **60. Existence of Gibbs measures.** If $(E,\mathcal E)$ is a standard Borel space,
  $0<\lambda(E)<\infty$, and $\Phi$ is absolutely summable, then $\mathcal G(\gamma^\Phi)$ is
  nonempty, convex, and compact in the topology of local convergence. This covers every
  nonempty finite state space with counting measure and an absolutely summable potential,
  such as the Ising model on $\mathbb Z^d$ and the auto-logistic models with
  $\sum_j|\beta_{ij}|<\infty$ for every $i$.

* **61. Extreme Gibbs measures.** Let $\gamma$ be a specification. A measure
  $\mu\in\mathcal G(\gamma)$ is extreme in $\mathcal G(\gamma)$ if and only if it is trivial
  on $\mathcal T$. If $\mu\in\mathcal G(\gamma)$ and $\nu$ is a probability measure with
  $\nu\ll\mu$, then $\nu\in\mathcal G(\gamma)$ if and only if $d\nu/d\mu$ has a
  $\mathcal T$-measurable version. Each element of
  $\mathcal G(\gamma)$ is determined within $\mathcal G(\gamma)$ by its restriction to
  $\mathcal T$, and distinct extreme elements are mutually singular on $\mathcal T$.

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

* **63. No phase transition in one dimension.** Let $S=\mathbb Z$, $E$ finite and nonempty,
  and $\lambda$ counting measure. Call $\gamma$ a positive homogeneous Markov specification when
  $\gamma_{\{i\}}(\sigma_i=y\mid\omega)=g(\omega_{i-1},y,\omega_{i+1})$ with $g>0$. Such a
  specification has exactly one Gibbs measure, the stationary Markov chain with a transition
  matrix $P$ with positive entries, and $\gamma\mapsto P$ is a bijection onto these
  matrices. Explicitly, fix $a\in E$, put $Q(x,y)=g(a,x,y)/g(a,a,y)$, let $q$ be the Perron
  eigenvalue of $Q$ and $r$ a positive right eigenvector; then $P(x,y)=Q(x,y)r(y)/(q\,r(x))$.

* **64. Phase transition of the two-dimensional Ising model.** Let $S=\mathbb Z^2$,
  $E=\{-1,1\}$, $\lambda$ counting measure, and $\Phi_{\{i,j\}}=-\sigma_i\sigma_j$ for
  nearest neighbours $i,j$, with all other $\Phi_A=0$. For all sufficiently large $\beta$
  there are two shift-invariant Gibbs measures $\mu_\pm^\beta\in\mathcal G(\beta\Phi)$, each
  the spin-flip image of the other, with $\mu_-^\beta(\sigma_0)<0<\mu_+^\beta(\sigma_0)$, and
  they can be chosen so that they converge locally to the point masses on the all-plus and
  all-minus configurations as $\beta\to\infty$. Hence $|\mathcal G(\beta\Phi)|>1$ for large
  $\beta$. The critical value in this normalisation is $\beta_c=\tfrac12\log(1+\sqrt2)$,
  with uniqueness for $\beta<\beta_c$ and a phase transition for $\beta>\beta_c$.

### Estimation by coding and pseudolikelihood

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

### Finite Gibbs sampling

* **123. Finite Gibbs sampler.** Let $S$ be a nonempty finite set of sites with nonempty
  finite state spaces $E_i$, and let $\pi$ be a strictly positive probability law on
  $\prod_{i\in S}E_i$. Let $P_i$ resample coordinate $i$ from its full conditional
  $\pi_i(\cdot\mid x_{-i})$, keeping all other coordinates fixed. Each $P_i$ is reversible
  for $\pi$. A sweep applying each $P_i$ once in a fixed order preserves $\pi$, and
  the random-scan kernel $\sum_{i\in S}q_iP_i$ is reversible for $\pi$ when the $q_i$
  are fixed positive probabilities summing to one. For either kernel $P$, the iterates $\nu P^n$
  converge in total variation to $\pi$ uniformly over initial laws $\nu$.

### Matérn fields and the stochastic partial differential equation

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

### Reference guide for Part 3

Items 47–49: Besag (1974), §2, (2.2), pp. 195–196, and §3, (3.1)–(3.3), pp. 196–198;
Cressie, §6.4, (6.4.3), pp. 412–413, (6.4.5)–(6.4.8) and the corollary, pp. 415–418;
Rue–Held, Lemma 2.3, p. 29; van Lieshout (2019), Theorem 3.1 and Corollary 3.1, pp. 51–52,
Definitions 3.4–3.7 and Theorems 3.2–3.4, pp. 55–60, Example 3.9, pp. 61–62, Corollary 3.2,
p. 62; Gaetan–Guyon, Definition 2.2 and Theorem 2.1, pp. 65–66; Handbook, ch. 12,
Lemma 12.1, p. 176, Theorem 12.7, p. 194, Corollaries 12.2–12.5, p. 195; Spodarev,
Lemma 9.6, p. 299, Theorem 9.3, p. 300. Rue–Held's Lemma 2.3 and Handbook Lemma 12.1 assume
only that $x$ and $y$ have positive density; the intermediate configurations must also have
positive density, which the positivity condition guarantees. Full conditionals are defined
only on the support, which is why item 47 compares densities with the same support.
Positivity is stated in three forms in the sources: product support (Besag, Cressie),
$\pi>0$ everywhere (van Lieshout, Spodarev, Handbook), and positivity of all conditional laws
(Gaetan–Guyon). Besag, Cressie, and the Handbook derive the neighbour relation from the
conditionals; the other sources fix the graph first. The implication from nonnegative clique
products in item 49 is the first half of the proof of van Lieshout's Theorem 3.4, p. 60,
which does not use positivity; the $2\times2$ example is her Example 3.9, pp. 61–62, after
Moussouris (1974), which is not local. Energy signs differ: Besag and Cressie write
$\exp Q$, Gaetan–Guyon $\exp U$, and Georgii $\exp(-H)$.

Items 50–51: Besag (1974), §4.1–4.3, (4.1)–(4.8) and (4.14)–(4.15), pp. 199–203, with the
auto-Poisson model in §4.2.4, p. 202; Gaetan–Guyon, Theorem 2.2, p. 67, Definition 2.3 and
Corollary 2.3, p. 68, pp. 68–70; Cressie, (6.5.6)–(6.5.8), pp. 427–428; van Lieshout (2019),
Examples 3.3 and 3.5, pp. 51, 55. Besag's Assumption 1, p. 200, and Gaetan–Guyon's (2.10)
assume the pairwise expansion rather than derive it, and both use a reference value $0$ in
each state space. Besag's theorem needs $\log\pi_i(0\mid\cdot)$ finite. Gaetan–Guyon, p. 69,
print the auto-Poisson energy with $+\log x_i!$; the correct sign is $-\log x_i!$.

Items 52–54: Besag (1974), (4.9)–(4.13), p. 201; Cressie, pp. 409–414, (6.3.16), p. 409;
Rue–Held, (2.17)–(2.18) and Theorem 2.6, p. 28, Definitions 2.9–2.10 and Theorem 2.13,
pp. 72–73; Gaetan–Guyon, Definition 1.9 and Propositions 1.7–1.8, pp. 31–33, and pp. 35–37;
van Lieshout (2019), Examples 3.2 and 3.4, pp. 50–51, Definition 3.3, pp. 52–53,
Proposition 3.1, pp. 53–54. Rue–Held write the conditional mean with $-\sum_j\beta_{ij}$, the
other sources with $+\sum_jc_{ij}$. Van Lieshout's sufficient condition for $C=\phi N$,
Example 3.2, p. 50, is Gershgorin's theorem for $I-\phi N$; it is not sharp (on the star with
three leaves the exact bound is $|\phi|<1/\sqrt3$), and the symmetry condition then needs
$\kappa_i$ constant on components. Gaetan–Guyon, p. 37, state the neighbour relation of
item 53 as an equivalence; cancellation makes it an inclusion. On a finite set the sources
disagree about the converse of item 53: Gaetan–Guyon, p. 36, say the two families coincide,
while Cressie, pp. 409–410, says a low-order conditional autoregression generally has no
simultaneous representation of the same neighbourhood order. The answer depends on the
constraints placed on $B$, and only the inclusion of item 53 is recorded.

Items 55–59: Rue–Held, Definition 2.1, pp. 21–22, Theorem 2.2, p. 21, Theorem 2.3 and
(2.5)–(2.7), p. 22, Theorem 2.4, p. 24, Theorem 2.5 and (2.15), p. 26, Definition 2.2 and
Lemma 2.1, p. 27, Lemma 2.2 and (2.16), p. 28, Algorithms 2.3–2.4, p. 34, Theorem 2.7,
Corollary 2.1 and Algorithm 2.5, p. 35, Theorem 2.8 and Corollary 2.2, p. 42, Theorem 2.9,
p. 45, Definitions 3.2–3.3 and (3.18)–(3.23), pp. 93–96; Handbook, ch. 12, Definition 12.1,
p. 173, Theorems 12.1–12.6, pp. 173–187; Spodarev, Theorems 9.4–9.5, pp. 302–303; van
Lieshout (2019), Examples 3.6–3.7, pp. 56–59, and p. 54. Rue–Held state item 56 without proof
(Theorem 2.4); Handbook Theorem 12.3, p. 175, gives only the global property, and Spodarev
lists the three properties as holding rather than as equivalent. The bandwidth statement of
item 58 is Rue–Held Theorem 2.9 and Handbook Theorems 12.4–12.6, pp. 186–187. Rue–Held call
the density of item 59 an improper Gaussian Markov random field (Definition 3.2) and reserve
"intrinsic" for the first-order case $Q\mathbf 1=0$ (Definition 3.3); the first-order random
walk is on p. 96.

Items 60–64: Georgii, (1.18)–(1.19), p. 13, Definition (1.23) and Remark (1.24), pp. 16–17,
(2.2)–(2.12), pp. 27–29, with $\lambda$-admissibility (2.7), p. 27, the Gibbsian
specification (2.9), p. 28, and absolute summability (2.11)–(2.12), pp. 28–29, Theorem (3.5)
and Corollary (3.9), pp. 45–46, with the explicit transition matrix in (3.7) and the
converse formula $g(x,y,z)=P(x,y)P(y,z)/P^2(x,z)$ in (3.11), p. 47, Definition (4.2), p. 59,
Theorems (4.22)–(4.23), pp. 71–72, (6.8)–(6.9), pp. 99–100, the opening of §7.1, p. 115,
Theorem (7.7), p. 118, (8.1)–(8.8), pp. 141–143; Gaetan–Guyon, Definition 2.1, pp. 55–56,
and p. 58; Cressie, (6.5.5), p. 425. Item 60 is Theorem (4.23)(a), with convexity from
p. 115 and the topology of local convergence from Definition (4.2). Dobrushin's matrix and
condition are (8.5)–(8.6), p. 142, the uniqueness theorem is (8.7), and the sufficient
condition of item 62 is Proposition (8.8), p. 143, for a $\lambda$-admissible potential with
$\sigma$-finite $\lambda$; Georgii notes on p. 144 that the constant $2$ cannot be enlarged. For
the Ising model of item 64 it gives $8\beta<2$, while the exact Dobrushin condition is
$4\tanh\beta<1$, $\beta<0.2554$; both lie below $\beta_c$. Item 64 is Theorem (6.9), p. 100,
stated there as convergence of the set of shift-invariant Gibbs measures to the point masses,
and proved by the Peierls argument. Georgii states without proof, with references, the
existence of a critical value, uniqueness for $\beta<\beta_c$, and $\sinh2\beta_c=1$, that is,
$\beta_c=\tfrac12\log(1+\sqrt2)\approx0.4407$; $\beta_c>0$ follows from Theorem (8.7), as he
notes on p. 100. Gaetan–Guyon's single-site conditional on p. 58,
$\exp\{x_i(\alpha+\beta v_i)\}/2\cosh(\alpha+\beta v_i)$ with $x_i\in\{-1,1\}$ and $v_i$ the
sum of the neighbouring spins, is Georgii's $\beta\Phi$ for $\alpha=0$, so its critical value
is $\tfrac12\log(1+\sqrt2)$. Their printed value $\log(1+\sqrt2)/4\approx0.2203$ is half of
it, the critical value when each pair is counted twice, as their energy display reads for
pairs inside $\Lambda$; it is a misprint for their own conditional law. Gaetan–Guyon, p. 56,
credit Dobrushin with existence for Polish $E$ and finite $\lambda$ without a summability
condition; the existence theorem is verified only in the form of item 60.

Item 65: Besag (1974), §6.1, pp. 211–212; Gaetan–Guyon, §5.4.2–5.4.3, pp. 191–199,
Theorem 5.4 and Lemma 5.1, p. 194, with the proof of Theorem 5.4 on pp. 194–195,
Theorem 5.6, p. 199; van Lieshout (2019), pp. 64–65. The precise conditions are (C1)–(C3),
(N1)–(N2) of Gaetan–Guyon, pp. 193–194 and 199. Gaetan–Guyon, p. 199, define $I_n^C$ as an
average over the coding sites; Theorem 5.6(1) holds with the sum recorded in item 65.

Item 123: Winkler (2003), Lemma 5.1.1 and Theorems 5.1.1–5.1.3, pp. 114–116, and
Theorem 4.3.1, p. 85. The fixed-order update in (5.2) is a sweep, and (5.3) is a mixture of
single-site kernels. Theorem 5.1.2, p. 115, states the uniform convergence for the sweep;
Theorem 5.1.3, pp. 115–116, states convergence for the random scan for each initial law, and
uniformity follows from Theorem 4.3.1 as in the proof of Theorem 5.1.2. A sweep is invariant
but in general not reversible.

Items 66–67: Lindgren–Rue–Lindström, (1)–(4), pp. 426–427, (5)–(6), pp. 427–428,
Result 1, p. 429, (7)–(10) and Result 2, pp. 429–431, remarks (b), (e), and (f), p. 431,
(12), p. 436, Definitions 7–8, p. 450, Appendix C.2, Theorems 2–4, pp. 451–452, and
Appendix C.5, p. 453. The authors state item 66 "in a loose and imprecise form" and
attribute it to Whittle (1954, 1963); unit-variance white noise and "the only stationary
solutions" are on pp. 426–427, and the remark on the null space on p. 427 concerns the
differential operator. Their (12) is the non-stationary model with $\kappa(u)$ and $\tau(u)$,
whose constant-coefficient case is recorded. Theorem 2, p. 451, carries the hypothesis
$\partial_n\psi_k=0$; Theorems 3–4 are stated on a manifold. With the exact mass matrix $C$
the precisions $Q_\alpha$, $\alpha\ge2$, are dense; the lumped matrix is treated in
Appendix C.5. The lattice stencil (5)–(6) is stated for $|a|>4$, and its marginal variance
$1/\{4\pi\nu(a-4)^\nu\}$, p. 428, agrees with the formula of item 66 for $d=2$. Fractional
$\alpha$ is not covered by item 67.

## 4. Point processes and random measures

This part covers the general theory of point processes and random measures, the Poisson
process and its operations, stochastic intensities for temporal counts, and Palm theory.
It also treats Cox processes, including log-Gaussian and shot-noise Cox processes, and
determinantal point processes.

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

### General theory

* **68. Campbell's formula.** Let $\xi$ be a random measure with intensity measure
  $\Lambda$. For every measurable $u:\mathbb X\to[0,\infty]$,
  $\mathbb E\int u\,d\xi=\int u\,d\Lambda$. The same holds for measurable real $u$ with
  $\int|u|\,d\Lambda<\infty$, and then $\int|u|\,d\xi<\infty$ almost surely.

* **69. Determination of the law.** For random measures $\xi,\xi'$ the following are
  equivalent: $\xi$ and $\xi'$ have the same law; their finite-dimensional distributions
  on pairwise disjoint sets agree; $L_\xi=L_{\xi'}$; $\int u\,d\xi$ and $\int u\,d\xi'$ have
  the same law for every measurable $u\ge0$. For locally finite point processes on a
  complete separable metric space it suffices to take $u$ continuous with bounded support.

* **70. Void probabilities determine simple point processes.** Let $\mathbb X$ be a Borel
  space and $\eta,\eta'$ simple point processes with
  $\mathbb P(\eta(B)=0)=\mathbb P(\eta'(B)=0)$ for every $B\in\mathcal X$. Then $\eta$ and
  $\eta'$ have the same law. In the locally finite framework it suffices that the void
  probabilities agree on a generating ring of bounded sets, and for general point processes
  this equality characterises the laws of the supports.

For $\mu=\sum_{i\le k}\delta_{x_i}$ the **$m$-th factorial measure** is
$\mu^{(m)}=\sum^{\neq}_{i_1,\dots,i_m}\delta_{(x_{i_1},\dots,x_{i_m})}$, the sum over pairwise
distinct indices; the definition extends measurably to all of $\mathbf N$. The **$m$-th
factorial moment measure** of $\eta$ is $\alpha_m(C)=\mathbb E\eta^{(m)}(C)$. On
$\mathbb R^d$, if $\alpha_m$ has a density $\rho^{(m)}$ with respect to Lebesgue measure,
$\rho^{(m)}$ is the **$m$-th product density**, $\rho=\rho^{(1)}$ is the **intensity
function**, and $g(x,y)=\rho^{(2)}(x,y)/(\rho(x)\rho(y))$, with $a/0=0$, is the **pair
correlation function**. Product densities are defined almost everywhere.

* **71. Factorial measures.** For $\mu\in\mathbf N$ and pairwise disjoint $B_1,\dots,B_m$,
  $\mu^{(m)}(B_1\times\dots\times B_m)=\prod_j\mu(B_j)$, and
  $\mu^{(m)}(B^m)=\mu(B)(\mu(B)-1)\cdots(\mu(B)-m+1)$. If $\Lambda(B_1\cap B_2)<\infty$, then
  $\mathbb E[\eta(B_1)\eta(B_2)]=\alpha_2(B_1\times B_2)+\Lambda(B_1\cap B_2)$. On a Borel
  space, $\mu$ is simple if and only if $\mu^{(2)}$ vanishes on the diagonal. On
  $\mathbb R^d$, $\mathbb E\sum^{\neq}_{x,y\in\eta}h(x,y)=\iint h\,\rho^{(2)}$ for
  measurable $h\ge0$ whenever $\rho^{(2)}$ exists.

### The Poisson process

Let $\lambda$ be an s-finite measure. A point process $\eta$ is a **Poisson process with
intensity measure $\lambda$** when $\eta(B)\sim\mathrm{Po}(\lambda(B))$ for every $B$ and
$\eta(B_1),\dots,\eta(B_m)$ are independent for pairwise disjoint $B_1,\dots,B_m$.

* **72. Existence, uniqueness, and conditional structure.** For every s-finite $\lambda$
  there is a Poisson process with intensity measure $\lambda$, and any two have the same
  law; for $\lambda=0$ it is the zero measure. If $0<\lambda(\mathbb X)<\infty$, it has the
  law of $\sum_{n\le\kappa}\delta_{X_n}$ with $\kappa\sim\mathrm{Po}(\lambda(\mathbb X))$
  independent of independent $X_n$ with law $\lambda/\lambda(\mathbb X)$; conditionally on
  $\eta(\mathbb X)=m\ge1$, its points are $m$ independent points with that law.

* **73. Laplace functional.** A point process $\eta$ is Poisson with s-finite intensity
  $\lambda$ if and only if
  $$L_\eta(u)=\exp\Bigl(-\int\bigl(1-e^{-u(x)}\bigr)\lambda(dx)\Bigr)\quad
  \text{for all measurable }u:\mathbb X\to[0,\infty].$$

* **74. Superposition, restriction, and mapping.** (a) The sum of countably many
  independent Poisson processes with intensities $\lambda_i$ is a Poisson process with
  intensity $\sum_i\lambda_i$. (b) The restrictions of a Poisson process to pairwise disjoint
  measurable sets are independent Poisson processes with the restricted intensities. (c)
  If $T:\mathbb X\to\mathbb Y$ is measurable and $\eta$ is Poisson with intensity $\lambda$,
  then $\eta\circ T^{-1}$ is Poisson with intensity $\lambda\circ T^{-1}$.

* **75. Marking theorem.** Let $K$ be a probability kernel from $\mathbb X$ to $\mathbb Y$
  and $\eta=\sum_{n\le\kappa}\delta_{X_n}$ a Poisson process with intensity $\lambda$. If,
  given $\kappa$ and $X_1,X_2,\dots$, the marks $Y_n$ are independent with laws $K(X_n,\cdot)$,
  then
  $\sum_{n\le\kappa}\delta_{(X_n,Y_n)}$ is a Poisson process on $\mathbb X\times\mathbb Y$
  with intensity measure $(\lambda\otimes K)(C)=\iint\mathbf 1_C(x,y)K(x,dy)\lambda(dx)$.

* **76. Thinning theorem.** Let $p:\mathbb X\to[0,1]$ be measurable, and retain each point
  $x$ of a Poisson process with intensity $\lambda$ independently with probability $p(x)$.
  The retained and deleted processes are independent Poisson processes with intensities
  $p\,\lambda$ and $(1-p)\lambda$. Independent thinning of any point process with product
  densities multiplies $\rho$ by $p$ and $\rho^{(2)}(x,y)$ by $p(x)p(y)$, and so leaves $g(x,y)$
  unchanged where $p(x)p(y)>0$.

* **77. Simplicity.** On a Borel space, a Poisson process is simple if and only if its
  intensity measure is diffuse.

* **78. Rényi's theorem.** Let $\mathbb X$ be a Borel space, $\lambda$ a diffuse s-finite
  measure, and $\eta$ a simple point process with $\mathbb P(\eta(B)=0)=e^{-\lambda(B)}$ for
  every $B\in\mathcal X$. Then $\eta$ is Poisson with intensity $\lambda$. Likewise, a random
  measure on a localized Borel space with no fixed atoms is a Poisson process if and only if
  $\xi(U)$ is Poisson distributed for every $U$ in a generating ring of bounded sets.

* **79. Mecke equation.** Let $\lambda$ be s-finite. A point process $\eta$ is Poisson with
  intensity $\lambda$ if and only if
  $$\mathbb E\int f(x,\eta)\,\eta(dx)=\int\mathbb E f(x,\eta+\delta_x)\,\lambda(dx)$$
  for every measurable $f:\mathbb X\times\mathbf N\to[0,\infty]$.

* **80. Multivariate Mecke equation.** If $\eta$ is Poisson with s-finite intensity
  $\lambda$ and $m\ge1$, then for every measurable $f\ge0$
  $$\mathbb E\int f(x_1,\dots,x_m,\eta)\,\eta^{(m)}(d(x_1,\dots,x_m))
  =\int\mathbb E f\bigl(x_1,\dots,x_m,\eta+\delta_{x_1}+\dots+\delta_{x_m}\bigr)\,
  \lambda^m(d(x_1,\dots,x_m)).$$
  In particular $\alpha_m=\lambda^m$; on $\mathbb R^d$ with intensity function $\rho$,
  $\rho^{(m)}(x_1,\dots,x_m)=\prod_i\rho(x_i)$, and $g(x,y)=1$ where $\rho(x)\rho(y)>0$.

* **81. Poincaré inequality.** Let $\eta$ be Poisson with $\sigma$-finite intensity
  $\lambda$, and put $D_xf(\mu)=f(\mu+\delta_x)-f(\mu)$. If $\mathbb E f(\eta)^2<\infty$, then
  $$\mathop{\mathrm{Var}}f(\eta)\le\int\mathbb E\bigl(D_xf(\eta)\bigr)^2\lambda(dx),$$
  with equality for $f(\mu)=\mu(B)$, $\lambda(B)<\infty$.

### Temporal counting processes

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

* **125. Time rescaling by a stochastic intensity.** Let $N$ be a simple locally finite
  point process on $(0,\infty)$ with adapted counts $N_t=N((0,t])$ and nonnegative
  predictable intensity $\lambda_t$ for a right-continuous filtration $(\mathcal F_t)$.
  Suppose $N_t-A_t$ is a local martingale and $A_t=\int_0^t\lambda_s\,ds$ is almost
  surely finite at finite times, strictly increasing and unbounded. For
  $\tau(u)=A^{-1}(u)$, the rescaled count $N_{\tau(u)}$ is a rate-one Poisson process
  relative to $(\mathcal F_{\tau(u)})_{u\ge0}$. If $T_n$ are the arrival times and
  $T_0=0$, the transformed gaps $A_{T_n}-A_{T_{n-1}}$ are independent standard
  exponential variables.

* **126. Likelihood of a counting process with predictable intensity.** For $0<T<\infty$
  let $P_0$ be the rate-one Poisson law on finite simple configurations in $(0,T]$ with
  their natural filtration. Let $\lambda_t$ be a predictable function of the
  configuration up to time $t$, with deterministic bounds $0<c\le\lambda_t\le C<\infty$.
  There is a unique law $P$ on this configuration space under which
  $N_t-\int_0^t\lambda_s\,ds$ is a martingale. Its likelihood relative to $P_0$ is
  $$\frac{dP}{dP_0}
    =\exp\!\left(\int_0^T(1-\lambda_t)\,dt\right)
       \prod_{t\in N\cap(0,T]}\lambda_t.$$

### Stationarity and Palm theory

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

* **83. Palm distributions and the refined Campbell theorem.** Let $\eta$ be a stationary
  point process on $\mathbb R^d$ with intensity $\gamma\in(0,\infty)$. There is a unique
  probability measure $P^0$ on $\mathbf N$, the **Palm distribution**, such that
  $$\mathbb E\int f(x,\theta_x\eta)\,\eta(dx)=\gamma\int\!\!\int f(x,\mu)\,P^0(d\mu)\,dx$$
  for every measurable $f\ge0$, and $P^0(\mu\{0\}>0)=1$. In general, for a random measure
  with $\sigma$-finite intensity measure $M$ on a complete separable metric space there is a
  kernel $x\mapsto P_x$ of local Palm distributions, unique up to $M$-null sets, with
  $\mathbb E\int g(x,\xi)\,\xi(dx)=\iint g(x,\mu)\,P_x(d\mu)\,M(dx)$.

* **84. Slivnyak–Mecke theorem.** A stationary point process $\eta$ on $\mathbb R^d$ with
  intensity in $(0,\infty)$ is Poisson if and only if its Palm distribution is the law of
  $\eta+\delta_0$. More generally, a point process with locally finite intensity measure $M$
  is Poisson if and only if $P_x$ is the law of $\eta+\delta_x$ for $M$-almost every $x$.

* **127. Palm inversion on the line.** Let $N$ be an almost surely nonempty stationary
  simple point process on $\mathbb R$ with intensity $\gamma\in(0,\infty)$ and Palm law
  $P^0$. Under $P^0$, let $T_1$ be the first point strictly to the right of $0$. Then
  $\mathbb E^0T_1=1/\gamma$ and for every nonnegative measurable function $f$ of the
  configuration,
  $$\mathbb E f(N)=\gamma\,\mathbb E^0\int_0^{T_1} f(\theta_tN)\,dt.$$
  Equivalently, bias the Palm law by the length of the next gap and shift the origin
  to a uniform location in that gap to obtain the stationary law.

### Cox processes

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

* **87. Shot-noise and Neyman–Scott processes.** Let $\Phi$ be a Poisson process on
  $\mathbb R^d\times(0,\infty)$ with intensity measure $\zeta$, let $k(c,\cdot)$ be a
  probability density for each $c$, and put $Z(x)=\sum_{(c,\gamma)\in\Phi}\gamma k(c,x)$. If
  $\rho(x)=\int\gamma k(c,x)\,\zeta(d(c,\gamma))$ is locally integrable and
  $\beta(x,y)=\int\gamma^2k(c,x)k(c,y)\,\zeta(d(c,\gamma))$ is finite, the Cox
  process directed by $Z(x)\,dx$ has intensity $\rho$ and second product density
  $\rho(x)\rho(y)+\beta(x,y)$, so $g=1+\beta/(\rho\otimes\rho)\ge1$ where $\rho(x)\rho(y)>0$.
  In the Neyman–Scott case, $\zeta(d(c,\gamma))=\kappa\,dc\,\delta_\alpha(d\gamma)$ with
  $\kappa,\alpha>0$ and $k(c,x)=k(x-c)$: the parents form a homogeneous Poisson process of
  intensity $\kappa$, each parent $c$ has a Poisson($\alpha$) number of independent offspring
  with density $k(\cdot-c)$, and
  $$\rho=\alpha\kappa,\qquad g(x,y)=1+\kappa^{-1}\int k(x-z)k(y-z)\,dz .$$

### Determinantal point processes

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

* **89. Macchi–Soshnikov theorem.** Let $K$ be a kernel whose integral operator on
  $L^2(\Lambda,\mu)$ is Hermitian and locally of trace class, with $K$ equal on the diagonal to
  the version given by the spectral expansion. A determinantal point process with kernel $K$
  exists if and only if the spectrum of the operator is contained in $[0,1]$.

* **90. Number of points.** Let the kernel be Hermitian of trace class,
  $K(x,y)=\sum_k\lambda_k\varphi_k(x)\overline{\varphi_k(y)}$ with orthonormal $\varphi_k$ and
  $\lambda_k\in[0,1]$, and let $I_k$ be independent Bernoulli($\lambda_k$) variables. The
  process is a mixture over $I$ of the determinantal projection processes with kernels
  $\sum_kI_k\varphi_k(x)\overline{\varphi_k(y)}$. In particular the total number of points has
  the law of $\sum_kI_k$, with mean $\sum_k\lambda_k$, variance $\sum_k\lambda_k(1-\lambda_k)$,
  and void probability $\prod_k(1-\lambda_k)$. Applied to the restriction to a compact $D$,
  this gives the law of $X(D)$ in terms of the eigenvalues of $K$ on $D$.

* **91. Stationary determinantal processes.** Let $C(x,y)=C_0(x-y)$ with $C_0$ a continuous
  covariance function on $\mathbb R^d$ belonging to $L^2$, and let
  $\varphi(\omega)=\int C_0(h)e^{-2\pi i\langle\omega,h\rangle}dh$ be its spectral density.
  A determinantal point process with kernel $C$ exists if and only if $\varphi\le1$. It is
  stationary with intensity $\rho=C_0(0)$, and for $\rho>0$
  $$g(h)=1-\frac{|C_0(h)|^2}{C_0(0)^2}\in[0,1] .$$
  For a parametric family, existence therefore bounds the intensity by a maximum that
  depends on the other parameters.

### Reference guide for Part 4

Locators for Møller and Waagepetersen (2004) are given by number only: the local PDF has no
printed page numbers.

Items 68–71: Last–Penrose, Definitions 2.1, 2.5, 2.13, pp. 11–16, Proposition 2.7, p. 13,
Propositions 2.10–2.14, pp. 14–17, (4.4)–(4.9), p. 28, Proposition 4.3, p. 29,
Definition 4.9 and (4.24), p. 34, Propositions 6.7 and Theorem 6.11, pp. 49–50,
Proposition 13.2 and (13.1), p. 128; Daley–Vere-Jones II, Definition 9.2.I and
Proposition 9.2.III, p. 26, Theorem 9.2.XII, p. 35, Definition 9.5.I and
Proposition 9.5.II, p. 66; Kallenberg, Theorem 2.2 and Corollary 2.3, pp. 52–53,
Theorem 3.8, p. 79; Baccelli–Błaszczyszyn–Karray, Theorem 1.2.5, p. 8; Chiu et al.,
Theorem 4.1, p. 114; van Lieshout (2019), Theorem 4.1, p. 94; Møller–Waagepetersen,
Definitions 4.1–4.4, Proposition 4.1. The pair correlation function is defined with
$a/0=0$ by Møller–Waagepetersen and Lavancier–Møller–Rubak; the latter set $g(x,x)=0$.
Last–Penrose, p. 73, define it only for stationary processes and note that it does not
exist for non-simple ones.

For item 68 see also Baddeley, in Barndorff-Nielsen–Kendall–van Lieshout, Theorem 1.2,
p. 11 of the local 1998 printing.

Items 72–81: Last–Penrose, Definition 3.1 and Propositions 3.2–3.3, pp. 19–20,
Theorem 3.6 and Corollary 3.7, pp. 21–22, Proposition 3.8 and Theorem 3.9, p. 23,
Theorems 4.1 and 4.4, pp. 27–30, Corollary 4.10, p. 34, Theorems 5.1–5.2, pp. 38–39,
Definition 5.3 and Theorem 5.6, pp. 40–42, Definition 5.7, Theorem 5.8, Corollary 5.9,
pp. 43–44, Proposition 6.9, p. 49, Theorems 6.10–6.14, pp. 50–54, (18.1), p. 187,
Theorem 18.7 and Corollary 18.8, p. 193; Kallenberg, Lemma 3.1, p. 73, Theorem 3.5, p. 77,
Lemma 3.6, p. 78, Corollary 3.9, p. 80; Baccelli–Błaszczyszyn–Karray, Proposition 2.1.4,
p. 30, Corollaries 2.2.3 and 2.2.7, pp. 36–38; van Lieshout (2019), Theorem 4.2, p. 97;
Møller–Waagepetersen, Definitions 3.2, 3.6, 3.7, Theorems 3.1–3.3, Propositions 3.2,
3.6, 3.7, 3.9, 4.2; Chiu et al., (4.69), p. 132. In the locally finite framework,
superposition (item 74(a)) gives a Poisson process only when $\sum_i\lambda_i$ is locally
finite (Baccelli–Błaszczyszyn–Karray; Møller–Waagepetersen), and mapping can destroy local
finiteness. Møller–Waagepetersen and Chiu et al. write the Mecke equation in the reduced
form, removing the point $x$ from the process on the left, rather than adding it on the right.
Item 76 and the last clause of item 80 use the convention $a/0=0$ of the definition of $g$: where
$p(x)p(y)=0$ or $\rho(x)\rho(y)=0$ the pair correlation of the thinned or Poisson process is
$0$. Last and Penrose define the marking of item 75 conditionally on the number and the
locations of the points (Definition 5.3, p. 40); conditioning on the measure $\eta$ alone does
not fix the enumeration $X_n$ to which the marks are attached.

For item 75, Baddeley, in Barndorff-Nielsen–Kendall–van Lieshout, Theorem 1.3,
pp. 15–16, treats marks with a common conditional distribution.

Items 124–126: Brémaud (2020), Theorem 2.4.1, p. 59, Corollary 2.4.2, p. 60, and
Theorem 10.3.1 and Remark 10.3.2, p. 385. Reiss (1993), §9.1, pp. 225–227, introduces
compensators and attributes the Poisson characterisation to Watanabe. Karr (1991),
Example 2.12, p. 60, and Theorems 2.14, 2.18–2.19, pp. 61–63, relate compensators
to martingales and conditional waiting-time laws. Item 126 uses the bounded positive
case of Karr's Theorem 2.31 and (2.34), p. 71, and Brémaud's Theorem 5.5.1 and
(5.33)–(5.34), pp. 198–199.

Items 82–84: Last–Penrose, Definition 8.1 and Propositions 8.2–8.3, p. 70, Definition 8.6
and Proposition 8.7, pp. 71–72, Propositions 8.12–8.13, pp. 75–76, Theorem 8.14, p. 77,
Theorem 9.1, pp. 82–83, Definition 9.3 and (9.7), p. 84, Theorem 9.4, p. 85;
Daley–Vere-Jones II, Definition 13.1.I, pp. 270–271, Propositions 13.1.IV and 13.1.VII,
pp. 273 and 281, Theorem 13.2.III, p. 288; Baccelli–Błaszczyszyn–Karray, Theorem 3.1.9,
p. 121, Theorem 3.2.4, p. 130; Chiu et al., (4.61), p. 129, Theorem 4.2, p. 130. Last and
Penrose prove item 82(d) for $d=2$ and leave general $d$ to the reader. The shift conventions
differ: Last–Penrose's $\theta_x$ moves $x$ to the origin, Chiu et al. write $\varphi_x$ for the
translate $\varphi+x$, and Daley–Vere-Jones use $S_x$.

For item 83 see also Reiss (1993), (7.33)–(7.34), p. 176 and Theorem 7.3.1, p. 178,
and Baddeley, in Barndorff-Nielsen–Kendall–van Lieshout, Theorems 1.8–1.9, pp. 30–32.
Item 127: Brémaud (2020), Theorem 7.3.4 and (7.15)–(7.16), pp. 272–273, and the
gap-length-biased interpretation on p. 273. Equation (7.22), p. 277, gives
reconstruction from a law invariant under shifts to the points of the process.

Items 85–87: Last–Penrose, Definition 13.5, Proposition 13.6, (13.10), Theorems
13.7–13.8, pp. 129–131; Kallenberg, p. 73, Lemma 3.6, p. 78, which gives item 85(e) on a
localized Borel space; Møller–Waagepetersen,
Definitions 5.1 and 5.3, (5.2)–(5.12), Propositions 5.1 and 5.4; Møller–Syversveen–
Waagepetersen, §2, pp. 452–453, Theorem 1 and (2)–(4), p. 456; van Lieshout (2019),
Definition 4.13 and Theorems 4.6–4.7, pp. 118–120. Møller–Syversveen–Waagepetersen state
Theorem 1 for the stationary planar case; its proof contains two misprints,
$\exp(\mu+\sigma^2)$ for $\exp(\mu+\sigma^2/2)$ and $\sigma^2=g(0)$ for $\sigma^2=\log g(0)$, while
the theorem itself is correct. They give continuity conditions on the correlation near $0$
that ensure local integrability. Møller and Waagepetersen note that the set of cluster
centres need not be locally finite.

Items 88–91: Hough–Krishnapur–Peres–Virág, Definition 4.2.1, p. 48, Assumption 4.2.3,
p. 51, Lemma 4.2.6, pp. 52–53, Theorems 4.5.3 and 4.5.5, pp. 67–68;
Baccelli–Błaszczyszyn–Karray, Definition 5.1.1 and Lemmas 5.1.3–5.1.4, pp. 227–228,
Definitions 5.2.10–5.2.11, pp. 244–245, Theorems 5.2.16–5.2.17 and Corollary 5.2.18,
pp. 246–248; Lavancier–Møller–Rubak, Definition 1 and (2.2)–(2.5), pp. 857–858,
Conditions 1–2 and Theorem 1, p. 858, Theorem 2 and (2.10), p. 859, §3 with (3.1)–(3.3),
Proposition 1, p. 861, Corollary 1 and Remark 2, p. 862. The diagonal values of the kernel
matter: Hough et al. redefine the kernel on a null set through its spectral expansion,
Baccelli et al. assume a regular kernel, and Lavancier et al. assume continuity. Hough et al.
require simplicity in the definition, while Baccelli et al. deduce it. Lavancier et al. use
the Fourier transform with $e^{-2\pi i\langle\omega,h\rangle}$, as in item 91.

## 5. Gibbs point processes and statistics of point patterns

This part covers point processes with a density on a bounded window, the Papangelou
conditional intensity and the Georgii–Nguyen–Zessin formula, Markov point processes and
their clique factorisation, infinite-volume Gibbs point processes, second-order and
distance-based summary statistics, likelihood, pseudolikelihood, and estimating-equation
inference, and Markov chain Monte Carlo for point processes.

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

* **92. Poisson densities.** Let $\rho_1,\rho_2$ be integrable intensity functions on $W$ with
  $\rho_2>0$ wherever $\rho_1>0$, and $\mu_i(W)=\int_W\rho_i$. The Poisson process with
  intensity $\rho_1$ has density
  $$f(\mathbf x)=e^{\mu_2(W)-\mu_1(W)}\prod_{\xi\in\mathbf x}\frac{\rho_1(\xi)}{\rho_2(\xi)}$$
  with respect to the Poisson process with intensity $\rho_2$; in particular its density with
  respect to $\Pi_W$ is $e^{|W|-\mu_1(W)}\prod_{\xi\in\mathbf x}\rho_1(\xi)$, and its
  conditional intensity is $\rho_1$. Homogeneous Poisson processes of different intensities
  on $\mathbb R^d$, $d\ge1$, are mutually singular.

* **93. Factorisation by the conditional intensity.** If $f$ is hereditary, then for every
  enumeration of $\mathbf x=\{x_1,\dots,x_n\}$
  $$f(\mathbf x)=f(\emptyset)\prod_{i=1}^n\lambda^\ast(\{x_1,\dots,x_{i-1}\},x_i),$$
  so a hereditary density is determined by its conditional intensity up to the constant
  $f(\emptyset)$. The hypothesis is needed: the process consisting of one uniform point has
  $f(\emptyset)=0$.

* **94. Stability and normalisability.** Let $\phi^\ast:W\to[0,\infty)$ be integrable. A
  function $h$ is **locally stable** when $h(\mathbf x\cup\{\xi\})\le\phi^\ast(\xi)h(\mathbf x)$
  for all $\mathbf x$ and $\xi\notin\mathbf x$, and **Ruelle stable** when
  $h(\mathbf x)\le\alpha\prod_{\xi\in\mathbf x}\phi^\ast(\xi)$ for some $\alpha>0$. Local
  stability implies Ruelle stability and heredity, and gives $\lambda^\ast\le\phi^\ast$.
  Ruelle stability implies $\int h\,d\Pi_W<\infty$; for $\phi^\ast\equiv\beta$ the bound is
  $\int h\,d\Pi_W\le h(\emptyset)e^{(\beta-1)|W|}$ when $h$ is locally stable. A locally stable
  $h$ with $h(\emptyset)>0$ is therefore proportional to a probability density.

* **95. Georgii–Nguyen–Zessin formula.** If $X$ has a hereditary density with conditional
  intensity $\lambda^\ast$, then for every measurable $h\ge0$
  $$\mathbb E\sum_{\xi\in X}h(\xi,X\setminus\{\xi\})=\int_W\mathbb E\bigl[h(\xi,X)\,\lambda^\ast(X,\xi)\bigr]\,d\xi .$$
  Conversely, let $H$ be a non-degenerate, hereditary, stable energy (item 99), $z>0$,
  $\beta\ge0$, and $\Lambda$ bounded with $|\Lambda|>0$. A probability measure $P$ on finite
  configurations in $\Lambda$ satisfies the formula with
  $\lambda^\ast(\mathbf x,\xi)=ze^{-\beta(H(\mathbf x\cup\{\xi\})-H(\mathbf x))}$ for all $h$
  if and only if $P$ is the Gibbs measure $P^{z,\beta}_\Lambda$ of item 99. For
  $\lambda^\ast=\rho$ the formula is the Mecke equation, item 79.

* **96. Moment densities from the conditional intensity.** Under item 95,
  $\rho(\xi)=\mathbb E\lambda^\ast(X,\xi)$ and
  $\rho^{(2)}(\xi,\eta)=\mathbb E\bigl[\lambda^\ast(X,\xi)\lambda^\ast(X\cup\{\xi\},\eta)\bigr]$.

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

### Gibbs point processes

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

* **101. Uniqueness and phase transition.** Let $H$ be an energy as in item 100, of finite
  range $R$, with local energy bounded below, $h\ge C$. There is $z_d\in(0,\infty]$, the
  percolation threshold of the Poisson Boolean model with balls of radius $\tfrac12$, finite
  for $d\ge2$, such that for every $\beta\ge0$ and $z<z_de^{C\beta}/R^d$ the infinite-volume
  Gibbs measure is unique. For $d\ge2$ and the Widom–Rowlinson energy
  $H(\mathbf x)=|\bigcup_{\xi\in\mathbf x}B(\xi,R)|$ there are at least two infinite-volume
  Gibbs measures when $z=\beta$ is large enough.

### Summary statistics

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

* **102. Second-order functions.** If $g(\xi,\eta)=g(\xi-\eta)$, then
  $\mathcal K(B)=\int_Bg$; if $g$ is moreover isotropic,
  $K(r)=d\omega_d\int_0^rt^{d-1}g(t)\,dt$. For a stationary process, $\rho K(r)$ is the
  Palm-expected number of further points within distance $r$ of the typical point.
  $\mathcal K$ is invariant under independent thinning with retention probabilities that are
  positive everywhere. For a Poisson process, $g\equiv1$,
  $K(r)=\omega_dr^d$, and $L(r)=r$.

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

* **104. $F$, $G$, and $J$.** For a stationary Poisson process of intensity $\lambda>0$
  on $\mathbb R^d$ with $d\ge1$, $1-F(r)=e^{-\lambda\omega_dr^d}$ and $F=G$, so $J\equiv1$.
  For a stationary Gibbs process with translation-invariant interaction function and
  intensity $\rho>0$,
  $J(r)=\mathbb E[\lambda^\ast(X,0)\mid X\cap B(0,r)=\emptyset]/\rho$; if the interaction has
  finite range $R$, then $J(r)=\lambda^\ast(\emptyset,0)/\rho$ for $r\ge R$ with $F(r)<1$.

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

* **129. Space–time $K$ for a Cox process.** On $\mathbb R^2\times\mathbb R$ let a Cox
  process have almost surely locally integrable directing density $\rho(x,t)R(x,t)$,
  where $\rho$ is deterministic, locally integrable and strictly positive and $R$ is a nonnegative
  stationary second-order field with $\mathbb E R=1$. If its covariance is isotropic
  in the spatial lag and equals $C(s,u)$ at spatial distance $s$ and time lag $u$,
  then the process is second-order intensity-reweighted stationary with pair
  correlation $1+C(s,u)$. For the displacement cylinder
  $B_{\mathbb R^2}(0,r)\times(0,v]$, the one-sided $K$-function is
  $$K(r,v)=\pi r^2v+2\pi\int_0^v\int_0^r C(s,u)\,s\,ds\,du.$$
  If $C(s,u)=\sigma^2 r_S(s)r_T(u)$, the excess over the Poisson value factors as
  $2\pi\sigma^2(\int_0^r r_S(s)s\,ds)(\int_0^v r_T(u)\,du)$.

### Likelihood and estimating equations

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

* **109. Minimum contrast estimation.** For a second-order intensity-reweighted stationary
  process with parametric isotropic pair correlation $g(\cdot;\theta)$ and a nonparametric
  estimate $\hat g$, a minimum contrast estimator minimises
  $\int_{t_0}^{t_1}|\hat g(r)-g(r;\theta)|^2dr$, $0<t_0<t_1$; variants use $K$, powers of
  $K$, or $F$. For a log-Gaussian Cox process with covariance $\sigma^2e^{-\beta r^2}$, item 86
  gives $g(r)=\exp(\sigma^2e^{-\beta r^2})$.

### Simulation

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

* **111. Spatial birth–death processes.** Let a spatial birth–death process on
  $\{\mathbf x:f(\mathbf x)>0\}$ have birth rate density $b(\mathbf x,\xi)$ and death rate
  $D(\mathbf x,\xi)$ for the point $\xi$ of $\mathbf x\cup\{\xi\}$, and suppose detailed
  balance, $b(\mathbf x,\xi)f(\mathbf x)=D(\mathbf x,\xi)f(\mathbf x\cup\{\xi\})>0$ whenever
  $f(\mathbf x\cup\{\xi\})>0$. If the process exists, it is time-reversible and $f$ is its
  unique equilibrium distribution; then $b/D=\lambda^\ast$.

### Reference guide for Part 5

Locators for Møller and Waagepetersen (2004) are given by number only.

Items 92–98: Møller–Waagepetersen, (3.11), Proposition 3.8, (6.1)–(6.2), Definitions
6.1–6.3, (6.6), (6.9), (6.13)–(6.15), (6.22)–(6.24), (6.30)–(6.32), Example 6.1,
Example 6.4, Theorem 6.1, Remark 6.3, Propositions 6.1–6.2; Møller–Waagepetersen (2007),
(31), p. 657; van Lieshout (2019), (4.7)–(4.8) and Example 4.9, pp. 104–105, Definition
4.10 and Proposition 4.2, p. 106, Examples 4.10 and 4.12, pp. 105–107, Definition 4.11,
Theorem 4.3 and Example 4.14, pp. 108–109, Definition 4.12 and Theorem 4.4, p. 110; van
Lieshout (2000), Definition 2.3, p. 48, Theorem 2.2, p. 49, Theorem 4.1, pp. 117–118;
Gaetan–Guyon, Definition 3.3 and (3.5)–(3.7), pp. 93–94, p. 95, Definition 3.4 and
Proposition 3.1, pp. 102–103; Ripley (1977), §3.3, p. 176; Kutoyants, Theorem 1.3, (1.27),
p. 28; Dereudre, Definitions 5.1 and 5.4, pp. 185 and 192, Propositions 5.4–5.5,
pp. 192–193, p. 186; Baccelli–Błaszczyszyn–Karray, Corollary 3.2.8, p. 134.
Gaetan–Guyon's Proposition 3.1 assumes strictly positive densities, whereas
Møller–Waagepetersen and van Lieshout allow zeros under heredity. The inductive definition
of $\phi$ in item 97 uses the convention $0/0=1$ in Møller–Waagepetersen and $0/0=0$ in van
Lieshout; the resulting factorisation is the same. The Kelly–Ripley characterisation of the
Strauss family by the form of $\lambda^\ast$ is quoted, not proved, by Møller–Waagepetersen.
The non-integrability in item 98 needs a subset of $W$ of positive measure and diameter less
than $R$, which every $W$ with $|W|>0$ contains. Møller–Waagepetersen's Proposition 3.8(i)
states only that the homogeneous Poisson laws are not absolutely continuous; the strong-law
event in its proof has probability one under one law and zero under the other, which is
mutual singularity.

Items 99–101: Dereudre, Definitions 5.1–5.3 and Propositions 5.1–5.3, pp. 185–191,
Definitions 5.6–5.8, pp. 195–199, Propositions 5.7–5.10, pp. 194–202, Theorems 5.1–5.2,
pp. 200–201, Proposition 5.13 and Theorems 5.4–5.5, pp. 206–210. The reading of
$e^{-\beta H}$ at $\beta=0$ follows Dereudre's remark, p. 188, that $\beta=0$ gives the Poisson
process; with the weight $0$ on $\{H=+\infty\}$ also at $\beta=0$, the variational principle
of item 99 fails at $\beta=0$ for hard-core energies, whose minimiser is then the Poisson
process and not the conditioned one. Dereudre requires a Gibbs
measure to be stationary (Definition 5.8), while his Theorem 5.2 begins with an arbitrary
probability measure; item 100 states the characterisation for stationary $P$. He also
quotes Ruelle's estimate $P^{z,\beta}_\Lambda(n(\cdot\cap\Delta)\ge k)\le c_1e^{-c_2k^2}$,
uniform in $\Lambda$, for superstable, lower-regular energies. His Theorem 5.4 is stated for
energy functions in the sense of his Definition 5.1 with a finite range, and its Gibbs measures
are those of his Definition 5.8; item 101 records these hypotheses through item 100.

Items 102–104: Møller–Waagepetersen, Definitions 4.5–4.7, (4.4)–(4.10), Proposition 4.3,
Lemma 4.2 and (4.14), Proposition 6.3 and (6.33)–(6.35); Ripley (1977), pp. 173–174 and §6,
p. 180; Gaetan–Guyon, pp. 100–101, (3.11)–(3.13), pp. 213–214, Theorem 5.7, p. 214, the
latter due to Heinrich; van Lieshout (2019), Proposition 4.1 and Example 4.8, pp. 101–102;
van Lieshout (2000), (1.13)–(1.14), Examples 1.21 and 1.24, pp. 36–42. Ripley assumes
motion invariance and writes $\lambda^2K$; Møller–Waagepetersen and Gaetan–Guyon use the
intensity-reweighted measure. Van Lieshout (2000) defines $F$ with open balls, Møller and
Waagepetersen with closed ones. Ripley's conditional mean of the ratio estimator holds for
$t\le t_0$ with $t_0$ the least radius at which a circle centred in $W$ misses $W$, so
$t_0=\sqrt2/2$ for the unit square; Gaetan–Guyon, p. 214, give $\sqrt2$ for the unit square,
and the estimator is biased for $\sqrt2/2<t<\sqrt2$. Invariance of $\mathcal K$ under thinning
needs positive retention probabilities: thinning with probability $0$ on a set of positive
volume destroys second-order intensity-reweighted stationarity.

Item 128: Illian–Penttinen–Stoyan–Stoyan (2008), (5.3.34)–(5.3.37), pp. 350–351,
and (5.3.44)–(5.3.47), p. 353. The Palm normalisation uses the ground intensity and the
mean weight for two independent marks, so independent labelling recovers the ground $K$.

Item 129: Diggle (2014), §11.4.2 and (11.7), pp. 216–217, and (12.2)–(12.6),
pp. 225–226. The displacement cylinder uses positive time lags, so its Poisson
baseline is $\pi r^2v$. In (12.5)–(12.6) the factor $\lambda^{-2}$ is extraneous under
(12.2), where $\sigma^2$ is the variance of $R$ and $\mathbb E R=1$.

Items 105–109: van Lieshout (2019), §4.8, (4.10), p. 113, §4.9, p. 115, Definition 4.14 and
Example 4.17, pp. 121–122; Møller–Waagepetersen, (3.11), §9.2.1, (9.12)–(9.16);
Møller–Waagepetersen (2007), (47), p. 672, §8.1, p. 672, §8.2 from p. 673; Kutoyants,
Definition 2.1, pp. 45–46, conditions A1–A3, p. 46, Theorems 2.1–2.2, pp. 47–48,
Definitions 2.2–2.3, p. 49, conditions B1–B5, pp. 49–50, Theorem 2.4 and Lemma 2.1, p. 51;
Gaetan–Guyon, Theorem 5.8 and (5.38)–(5.41), pp. 219–220, Example 5.18, p. 221; Dereudre,
(5.37), Definition 5.10 and Theorem 5.7, pp. 217–218, Definition 5.11 and Theorem 5.8,
p. 221. Kutoyants states his results for a general sequence of experiments; the case of
intensity $nS(\vartheta,x)$ is a specialisation, not a separately numbered statement.
Consistency of the maximum pseudolikelihood estimator for finite-range exponential-family
models is due to Jensen and Møller, and asymptotic normality to Jensen and Künsch, as
reported by Gaetan–Guyon, pp. 221–222. Gaetan–Guyon's display of the pseudolikelihood
limit contains a stray factor $\lambda$; Møller–Waagepetersen include $e^{-|A|}$ in the
definition.

Items 110–111: Møller–Waagepetersen, Algorithm 7.4, Remark 7.6, Propositions 7.12–7.15;
van Lieshout (2019), Theorem 4.5, pp. 116–117; Gaetan–Guyon, Proposition 4.2, p. 131;
Ripley (1977), §4.1, (1), pp. 177–178. The precise irreducibility conditions are
Møller–Waagepetersen (7.10)–(7.11). Møller–Waagepetersen state the uniform-ergodicity bound
(7.20) of Proposition 7.8, and hence the bound of Proposition 7.14(iii), with exponent $m/n_0$;
the bound from an $(n_0,M)$-small state space is $(1-M(\Omega))^{\lfloor m/n_0\rfloor}$, and the
exponent $m/n_0$ fails for $m<n_0$ already for chains on four states.

## 6. Stochastic and integral geometry

This part covers random closed sets, capacity functionals and selection expectations,
the Boolean model, the integral geometry of convex bodies, and the laws and mean
values of cells in random tessellations.

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

### Integral geometry of convex bodies

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

* **115. Hadwiger's characterisation theorem.** Let $\psi:\mathcal K^d\to\mathbb R$ be
  additive, $\psi(K\cup M)+\psi(K\cap M)=\psi(K)+\psi(M)$ whenever $K\cup M$ is convex,
  invariant under rigid motions, and continuous in the Hausdorff metric. Then
  $\psi=\sum_{i=0}^dc_iV_i$ for real constants $c_i$. If $\psi$ is monotone instead of
  continuous, the same holds with $c_i\ge0$.

* **116. Crofton formula.** Let $\mu_k$ be the motion-invariant measure on the space $A(d,k)$
  of affine $k$-flats, normalised as the integral over linear subspaces $L$, under the
  rotation-invariant probability, of Lebesgue measure on $L^\perp$. For $K\in\mathcal K^d$,
  $1\le k\le d-1$, and $0\le j\le k$,
  $$\int_{A(d,k)}V_j(K\cap F)\,\mu_k(dF)=c^{k,\,d-k+j}_{j,\,d}\,V_{d-k+j}(K).$$
  For $j=0$ this expresses $V_{d-k}(K)$ through the measure of the flats that hit $K$.

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

### Mean values for Boolean models and tessellations

* **118. Boolean models with isotropic convex grains.** If in item 113 the grain $\Xi_0$ is
  almost surely convex and its law is rotation invariant, then for every convex $K$
  $$-\log\bigl(1-T(K)\bigr)=\lambda\sum_{k=0}^dc^{k,\,d-k}_{0,\,d}\,\mathbb E V_k(\Xi_0)\,V_{d-k}(K).$$

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

* **120. Poisson flat processes.** Let $X$ be a stationary Poisson process of $k$-flats in
  $\mathbb R^d$. If $k<d/2$, any two flats of $X$ are almost surely disjoint. If the
  directional distribution has no atoms, almost surely no two flats are parallel translates.
  If it is absolutely continuous with respect to the invariant measure on the Grassmannian,
  the flats are almost surely in general position.

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

* **122. Poisson–Voronoi tessellation.** For the Voronoi tessellation of a stationary Poisson
  process of intensity $\gamma$ in $\mathbb R^d$, the cell intensity is $\gamma$, so the
  typical cell has mean volume $1/\gamma$. In the plane, every vertex lies on three cells
  almost surely; the intensities of vertices and edges are $2\gamma$ and $3\gamma$; the
  typical cell has on average $6$ vertices and mean perimeter $4/\sqrt\gamma$; the mean
  edge length is $2/(3\sqrt\gamma)$; and the edge length per unit area is $2\sqrt\gamma$. In
  space the vertex and edge intensities are $\frac{24\pi^2}{35}\gamma$ and
  $\frac{48\pi^2}{35}\gamma$, and the face intensity is $(\frac{24\pi^2}{35}+1)\gamma$.

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

* **132. Containment probabilities for the typical Poisson–Voronoi cell.** For a
  homogeneous Poisson process $\eta$ of intensity $\gamma>0$ in $\mathbb R^d$,
  $d\ge1$, the typical cell centred at its nucleus has the law of the cell of
  $0$ in the tessellation generated by $\eta+\delta_0$. For compact $K$ containing
  $0$ define its **Voronoi flower** by $D(K)=\bigcup_{x\in K}B^\circ(x,\|x\|)$,
  using open balls. Then
  $$\mathbb P(K\subset C_{\mathrm{typ}})=e^{-\gamma|D(K)|}.$$
  The radius $R_0$ of the largest ball about the nucleus contained in the typical
  cell satisfies $\mathbb P(R_0>r)=\exp(-\gamma\omega_d(2r)^d)$ for $r\ge0$.

### Reference guide for Part 6

Items 112–113: Schneider–Weil, Definitions 2.1.1–2.1.3 and Theorems 2.1.2–2.1.3,
pp. 18–22, Theorem 2.2.1, p. 22, with proof pp. 22–31, Theorem 9.1.1 and (9.5), p. 380;
Chiu et al., §6.1.3, p. 207, Theorem 6.1, p. 208, (3.6)–(3.30), pp. 71–78; Spodarev
(Molchanov), Theorem 1.1, p. 11; Baccelli–Błaszczyszyn–Karray, Theorem 9.2.14 and
Corollary 9.2.15, pp. 427–428; Last–Penrose, Theorem 17.3, (17.6), (17.10),
Proposition 17.4, pp. 180–181, Proposition 17.7, p. 182, Theorem 17.8, p. 183, which gives
the covariance in the equivalent form $p^2+(1-p)^2(e^{\lambda\mathbb E V_d(\Xi_0\cap(\Xi_0-r))}-1)$,
and Theorem 17.10 with (17.17), p. 184, for identifiability through a centre map. Molchanov
states complete alternation through successive differences of $T$ with the opposite sign
convention. Chiu et al. (3.30), read with their definition (3.28), holds as printed for
symmetric $B$; for general $B$ the formula of item 113 follows from the capacity functional
at $K=-rB$, since $0\in\Xi\oplus rB$ exactly when $\Xi$ hits $-rB$, and it reduces to
theirs on replacing the grains by their reflections.

For item 112 see also Molchanov (2017), Theorem 1.1.29, p. 15. Item 130 uses
Molchanov's Definition 2.1.21, p. 238, Theorem 2.1.30, p. 243, and Theorem 2.1.35 and
(2.1.12), p. 247, in the integrably bounded finite-dimensional case.

Items 114–117: Schneider–Weil, (14.5)–(14.6), p. 600, (14.7)–(14.8), p. 601, p. 171,
Theorem 14.4.6, p. 628, Proposition 14.4.1, p. 629, (5.4)–(5.8) and Theorem 5.1.1,
pp. 171–172, Theorem 5.1.2 and (5.9), p. 173, with the convention $\varphi(\emptyset)=0$
stated there, Theorem 5.1.3 and (5.10), p. 175; Spodarev (Kiderlen), Exercise 2.1 and
Theorem 2.1, p. 24, Theorem 2.2, p. 25, Theorem 2.4, p. 27; Chiu et al., (1.44), p. 16.
Schneider–Weil and Chiu et al. give the continuous version of Hadwiger's theorem; Kiderlen
quotes the monotone version without proof. The constants in items 116–117 depend on the
normalisation of the invariant measures stated there.

Items 118–122: Schneider–Weil, Theorem 9.1.1, p. 380, Theorems 9.1.3–9.1.5,
pp. 388–391, Theorem 4.4.5, p. 128, Theorem 4.4.8, p. 134, Theorems 10.2.3–10.2.5,
pp. 472–477, (10.39), p. 488, Theorem 10.3.3 and (10.43)–(10.46), p. 489, p. 490; Chiu
et al., (3.31)–(3.32) and Theorem 3.1, p. 78, (3.45)–(3.53), pp. 80–81, (9.64)–(9.69) and Table 9.1,
pp. 371–372, (9.96)–(9.99), p. 377; Last–Penrose, Theorem 19.8 and (19.22), p. 207, which
gives the mean Euler characteristic of a planar Boolean model in a finite window;
Spodarev (Kiderlen), Theorem 2.10, pp. 39–40. Kiderlen, p. 40, states that the
general-dimension constants of Schneider–Weil's Theorem 9.1.4 are incorrect and gives
corrected ones; the formulas of item 119 for $d=2,3$ agree across Schneider–Weil, Chiu et
al., and Last–Penrose. In Chiu et al. (3.52), $\bar L^2$ means $(\mathbb E L)^2$. Isotropy is
needed only for the formulas involving $\pi$. For grains of zero volume, such as segments,
the volume fraction is $0$ and Chiu et al. give separate formulas. The planar Poisson–Voronoi
values are due to Meijering (1953) and Miles (1970), as reported by Chiu et al.

Item 168: Schneider–Weil, Definition 9.2.1, p. 397, Theorem 9.2.1, p. 398, Theorem 9.4.7,
p. 421, and (9.36)–(9.38), p. 426; Spodarev (Kiderlen), Theorems 2.8–2.9, pp. 37–38.

Item 131: Schneider–Weil, Theorem 10.4.1, p. 493, which gives the volume-biased form for
the zero cell; Calka, in Kendall–Molchanov (2010), §5.1.2.3, (5.3)–(5.4), p. 148.
The inverse-volume form (5.4) recovers the typical-cell mean from the zero-cell
law. Item 132: Calka, in Coupier (2019), §1.3.4.3, pp. 18–19. The Poisson
realisation of the typical cell is also in Calka, in Kendall–Molchanov (2010),
§5.1.2.4, p. 149. Calka states the containment formula for convex $K$ containing $0$; the
argument, that $K\subset C_{\mathrm{typ}}$ exactly when no point of $\eta$ lies in $D(K)$,
uses only compactness of $K$.
