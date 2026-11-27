module

public import MSSS.Geostatistics.Equivalence
public import MSSS.RandomFields.Matern
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Matérn fields and the stochastic partial differential equation

SYNOPSIS items 66 and 67: Whittle's equation `(κ² - Δ)^{α/2} x = 𝒲` and its finite-element
Gaussian Markov random field approximations.

A stationary field with spectral measure `F` solves Whittle's equation in the spectral sense
when `(κ² + ‖k‖²)^α F` is the spectral measure `(2π)^{-d} dk` of Gaussian white noise; the
operator `(κ² - Δ)^{α/2}` acts as the Fourier multiplier `(κ² + ‖k‖²)^{α/2}`. Gaussian white
noise is represented spectrally. The finite-element results include the precision recursion,
its positive definiteness, lumped sparsity, and weak covariance convergence formulated with
energy-space projections and Hilbert adjoints from Mathlib.
The spectral identity uses the Matérn characteristic function and Mathlib's change of
density and real-part integral. The lattice symbol estimate uses Mathlib's cosine
remainder bound.

## Main definitions

* `MSSS.whittleDensity d ν κ`: the spectral density `(2π)^{-d} (κ² + ‖k‖²)^{-(ν + d/2)}`.
* `MSSS.femPrecision K C α`: the precision matrices `Q_α` of item 67.

## Main results

* `MSSS.spectralCov_whittleDensity`, `MSSS.whittle_spectral_iff`,
  `MSSS.exp_mem_null_helmholtz`: SYNOPSIS item 66.
* `MSSS.tendsto_inner_galerkinCovariance`: weak covariance convergence in item 67.
* `MSSS.femPrecision_posDef`, `MSSS.femPrecision_eq_zero_of_lt_edist`,
  `MSSS.latticeSymbol_isBigO`, `MSSS.tendsto_latticeSymbol_div`: SYNOPSIS item 67.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set Matrix Asymptotics Laplacian
open scoped RealInnerProductSpace

namespace MSSS

/-! ### Whittle's equation (SYNOPSIS item 66) -/

/-- The spectral density `(2π)^{-d} (κ² + ‖k‖²)^{-(ν + d/2)}` of the stationary solution of
Whittle's equation. -/
def whittleDensity (d : ℕ) (ν κ : ℝ) (k : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ)) * (κ ^ 2 + ‖k‖ ^ 2) ^ (-(ν + d / 2))

lemma whittleDensity_def (d : ℕ) (ν κ : ℝ) (k : EuclideanSpace ℝ (Fin d)) :
    whittleDensity d ν κ k = (2 * Real.pi) ^ (-(d : ℝ)) * (κ ^ 2 + ‖k‖ ^ 2) ^ (-(ν + d / 2)) := by
  rw [whittleDensity]

/-- Changing from Matérn range to Whittle inverse range accounts for the powers of
the inverse range in the density. -/
private lemma inv_range_pow_mul_rpow {κ : ℝ} (hκ : 0 < κ) (ν y : ℝ) (hy : 0 ≤ y) (d : ℕ) :
    (1 / κ) ^ d * (1 + (1 / κ) ^ 2 * y) ^ (-ν - (d : ℝ) / 2) =
      κ ^ (2 * ν) * (κ ^ 2 + y) ^ (-ν - (d : ℝ) / 2) := by
  have hbase : 1 + κ⁻¹ ^ 2 * y = κ⁻¹ ^ 2 * (κ ^ 2 + y) := by
    field_simp [hκ.ne']
  have hp : 0 ≤ κ ^ 2 + y := add_nonneg (sq_nonneg _) hy
  rw [one_div, hbase, Real.mul_rpow (sq_nonneg _) hp, ← mul_assoc, ← Real.rpow_two,
    ← Real.rpow_mul (inv_nonneg.mpr hκ.le), ← Real.rpow_natCast,
    ← Real.rpow_add (inv_pos.mpr hκ)]
  have he : (d : ℝ) + 2 * (-ν - (d : ℝ) / 2) = -(2 * ν) := by ring
  rw [he, Real.rpow_neg (inv_nonneg.mpr hκ.le), Real.inv_rpow hκ.le, inv_inv]

/-- The Whittle spectral density is the Matérn spectral density times its variance. -/
private lemma whittleDensity_eq_maternDensity_mul {d : ℕ} {ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ)
    (x : EuclideanSpace ℝ (Fin d)) :
    whittleDensity d ν κ x =
      (Real.Gamma ν / (Real.Gamma (ν + d / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) *
        κ ^ (2 * ν))) *
      (Real.Gamma (ν + d / 2) / (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2)) * (1 / κ) ^ d *
        (1 + (1 / κ) ^ 2 * ‖x‖ ^ 2) ^ (-ν - d / 2)) := by
  let p : ℝ := (d : ℝ) / 2
  have hg₁ : 0 < Real.Gamma ν := Real.Gamma_pos_of_pos hν
  have hg₂ : 0 < Real.Gamma (ν + p) := Real.Gamma_pos_of_pos (by dsimp only [p]; positivity)
  have hc : (4 * Real.pi) ^ p * Real.pi ^ p = (2 * Real.pi) ^ (d : ℝ) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) Real.pi_pos.le]
    have hh : (4 * Real.pi) * Real.pi = (2 * Real.pi) ^ 2 := by ring
    rw [hh, ← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ 2 * Real.pi)]
    congr 1
    dsimp only [p]
    ring
  have hpow : -(ν + (d : ℝ) / 2) = -ν - (d : ℝ) / 2 := by ring
  rw [whittleDensity_def, hpow, mul_assoc
    (Real.Gamma (ν + d / 2) / (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2))),
    inv_range_pow_mul_rpow hκ ν _ (sq_nonneg _) d, Real.rpow_neg (by positivity)]
  dsimp only [p] at hg₂ hc
  rw [← hc]
  field_simp [hg₁.ne', hg₂.ne', (Real.rpow_pos_of_pos hκ _).ne',
    (Real.rpow_pos_of_pos Real.pi_pos _).ne', (Real.rpow_pos_of_pos (by positivity : 0 <
      4 * Real.pi) _).ne']

/-- Taking the real part of the Matérn characteristic function gives its cosine transform. -/
private lemma spectralCov_maternDensity {d : ℕ} (hd : 1 ≤ d) {ν θ : ℝ}
    (hν : 0 < ν) (hθ : 0 < θ) (h : EuclideanSpace ℝ (Fin d)) :
    spectralCov (fun ξ ↦ Real.Gamma (ν + d / 2) /
        (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2)) * θ ^ d *
          (1 + θ ^ 2 * ‖ξ‖ ^ 2) ^ (-ν - d / 2)) h = maternCorrelation ν θ ‖h‖ := by
  let f (x : EuclideanSpace ℝ (Fin d)) :=
    Real.Gamma (ν + d / 2) / (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2)) * θ ^ d *
      (1 + θ ^ 2 * ‖x‖ ^ 2) ^ (-ν - d / 2)
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity fun x ↦ ENNReal.ofReal (f x)
  have h0 : charFun μ 0 = 1 := by
    simpa only [maternCorrelation_def, norm_zero, ite_true, Complex.ofReal_one] using
      charFun_maternSpectralMeasure hν hθ hd 0
  have ht : μ Set.univ ≠ ⊤ := by
    intro htop
    rw [charFun_zero, measureReal_def, htop, ENNReal.toReal_top, Complex.ofReal_zero] at h0
    exact zero_ne_one h0
  let _ : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr ht⟩
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      Complex.exp ((⟪x, h⟫ : ℝ) * Complex.I)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ fun x ↦ le_of_eq (Complex.norm_exp_ofReal_mul_I ⟪x, h⟫)
  have hc : charFun μ h = (maternCorrelation ν θ ‖h‖ : ℂ) :=
    charFun_maternSpectralMeasure hν hθ hd h
  have hre := congrArg Complex.re hc
  have heq := integral_re hi
  simp only [RCLike.re_eq_complex_re] at heq
  rw [charFun_apply, ← heq] at hre
  simp only [Complex.ofReal_re, Complex.exp_ofReal_mul_I_re] at hre
  have hf : Measurable (fun x ↦ ENNReal.ofReal (f x)) := by
    dsimp only [f]
    fun_prop
  have hf₀ (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ f x := by
    have hg₁ := Real.Gamma_pos_of_pos hν
    have hg₂ : 0 < Real.Gamma (ν + (d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
    dsimp only [f]
    positivity
  dsimp only [μ] at hre
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hf
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun x ↦ Real.cos ⟪x, h⟫)] at hre
  rw [spectralCov_def]
  calc
    _ = ∫ x, (ENNReal.ofReal (f x)).toReal • Real.cos ⟪x, h⟫ := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [ENNReal.toReal_ofReal (hf₀ x), smul_eq_mul]
      rw [mul_comm, real_inner_comm]
    _ = _ := hre

/-- SYNOPSIS item 66: the stationary solution of `(κ² - Δ)^{α/2} x = 𝒲`, `α = ν + d/2`, is the
Matérn field with smoothness `ν`, inverse scale `κ`, and variance
`σ² = Γ(ν) / (Γ(ν + d/2) (4π)^{d/2} κ^{2ν})`; the equation for `τ x` gives variance `σ²/τ²`. -/
theorem spectralCov_whittleDensity {d : ℕ} (hd : 1 ≤ d) {ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ)
    (h : EuclideanSpace ℝ (Fin d)) {τ : ℝ} (hτ : τ ≠ 0) :
    let σsq := Real.Gamma ν / (Real.Gamma (ν + d / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) *
      κ ^ (2 * ν))
    spectralCov (whittleDensity d ν κ) h = σsq * maternCorrelation ν (1 / κ) ‖h‖ ∧
      spectralCov (fun k ↦ whittleDensity d ν κ k / τ ^ 2) 0 = σsq / τ ^ 2 := by
  intro σsq
  let f (x : EuclideanSpace ℝ (Fin d)) :=
    Real.Gamma (ν + d / 2) / (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2)) * (1 / κ) ^ d *
      (1 + (1 / κ) ^ 2 * ‖x‖ ^ 2) ^ (-ν - d / 2)
  have hs (z : EuclideanSpace ℝ (Fin d)) :
      spectralCov (whittleDensity d ν κ) z = σsq * maternCorrelation ν (1 / κ) ‖z‖ := by
    have hz (x : EuclideanSpace ℝ (Fin d)) :
        whittleDensity d ν κ x = σsq * f x := whittleDensity_eq_maternDensity_mul hν hκ x
    rw [spectralCov_def]
    simp only [hz, mul_left_comm (Real.cos _), integral_const_mul, ← spectralCov_def]
    rw [spectralCov_maternDensity hd hν (one_div_pos.mpr hκ)]
  refine ⟨hs h, ?_⟩
  rw [spectralCov_def]
  have he (x : EuclideanSpace ℝ (Fin d)) :
      Real.cos ⟪0, x⟫ * (whittleDensity d ν κ x / τ ^ 2) =
        (Real.cos ⟪0, x⟫ * whittleDensity d ν κ x) / τ ^ 2 := by
    field_simp [hτ]
  simp only [he, integral_div, ← spectralCov_def, hs, norm_zero, maternCorrelation_def,
    ite_true, mul_one]

/-- SYNOPSIS item 66: a stationary field with finite spectral measure `F` solves Whittle's
equation in the spectral sense, `(κ² + ‖k‖²)^α F = (2π)^{-d} dk`, if and only if `F` has the
Matérn spectral density `MSSS.whittleDensity`. -/
theorem whittle_spectral_iff {d : ℕ} {ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ)
    (F : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure F] :
    F.withDensity (fun k ↦ ENNReal.ofReal ((κ ^ 2 + ‖k‖ ^ 2) ^ (ν + d / 2))) =
        ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ))) • volume ↔
      F = volume.withDensity fun k ↦ ENNReal.ofReal (whittleDensity d ν κ k) := by
  let W := fun k : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal ((κ ^ 2 + ‖k‖ ^ 2) ^ (ν + d / 2))
  let c := ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ)))
  have hpos (k : EuclideanSpace ℝ (Fin d)) : 0 < κ ^ 2 + ‖k‖ ^ 2 := by positivity
  have hwpos (k : EuclideanSpace ℝ (Fin d)) :
      0 < (κ ^ 2 + ‖k‖ ^ 2) ^ (ν + d / 2) := Real.rpow_pos_of_pos (hpos k) _
  have hc : Continuous (fun k : EuclideanSpace ℝ (Fin d) ↦ κ ^ 2 + ‖k‖ ^ 2) := by fun_prop
  have he : 0 ≤ ν + (d : ℝ) / 2 := by positivity
  have hm : Measurable W :=
    ((Real.continuous_rpow_const he).comp hc).measurable.ennreal_ofReal
  have hminv : Measurable (fun k ↦ (W k)⁻¹) := by fun_prop
  have hne (k) : W k ≠ 0 := (ENNReal.ofReal_pos.mpr (hwpos k)).ne'
  have htop (k) : W k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv (μ : Measure (EuclideanSpace ℝ (Fin d))) :
      (μ.withDensity W).withDensity (fun k ↦ (W k)⁻¹) = μ :=
    withDensity_inv_same hm (Filter.Eventually.of_forall hne) (Filter.Eventually.of_forall htop)
  have hweight : (fun k ↦ ENNReal.ofReal (whittleDensity d ν κ k)) = fun k ↦ c * (W k)⁻¹ := by
    funext k
    rw [whittleDensity_def, ENNReal.ofReal_mul (by positivity), Real.rpow_neg (hpos k).le,
      ENNReal.ofReal_inv_of_pos (hwpos k)]
  have hsmul : c • (fun k ↦ (W k)⁻¹) = fun k ↦ c * (W k)⁻¹ := by
    funext k
    rw [Pi.smul_apply, smul_eq_mul]
  suffices F.withDensity W = c • volume ↔
      F = (c • volume).withDensity (fun k ↦ (W k)⁻¹) by
    rw [hweight, ← hsmul, withDensity_smul c hminv, ← withDensity_smul_measure]
    exact this
  refine ⟨fun h ↦ (hinv F).symm.trans
    (congrArg (fun μ : Measure _ ↦ μ.withDensity fun k ↦ (W k)⁻¹) h), fun h ↦ ?_⟩
  rw [h]
  simpa only [inv_inv] using
    (withDensity_inv_same (μ := c • volume) hminv
      (Filter.Eventually.of_forall fun k ↦ ENNReal.inv_ne_zero.mpr (htop k))
      (Filter.Eventually.of_forall fun k ↦ ENNReal.inv_ne_top.mpr (hne k)))

/-- SYNOPSIS item 66: for `α ≥ 2` the operator has a nontrivial null space, so stationarity is
needed for uniqueness: `u(x) = e^{κ x_1}` satisfies `(κ² - Δ) u = 0`. -/
theorem exp_mem_null_helmholtz {d : ℕ} (hd : 1 ≤ d) (κ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    κ ^ 2 * Real.exp (κ * WithLp.ofLp x ⟨0, hd⟩) -
      Δ (fun y : EuclideanSpace ℝ (Fin d) ↦ Real.exp (κ * WithLp.ofLp y ⟨0, hd⟩)) x = 0 := by
  let i : Fin d := ⟨0, hd⟩
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := κ • EuclideanSpace.proj i
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ Real.exp (L y)
  have hder (y : EuclideanSpace ℝ (Fin d)) : HasFDerivAt f (f y • L) y := by
    exact (Real.hasDerivAt_exp (L y)).comp_hasFDerivAt y L.hasFDerivAt
  have hfd : fderiv ℝ f = fun y ↦ f y • L := funext fun y ↦ (hder y).fderiv
  have hsecond (v w : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ (fderiv ℝ f) x v w = f x * L v * L w := by
    rw [hfd, ((hder x).smul_const L).fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  let basis := EuclideanSpace.basisFun (Fin d) ℝ
  have hb (j : Fin d) : L (basis j) = if i = j then κ else 0 := by
    dsimp only [L, basis]
    by_cases hj : i = j
    · subst j
      simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply, hj]
  have hlap : Δ f x = κ ^ 2 * f x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f basis]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hsecond, hb]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      ring
    · intro j _ hj
      simp [Ne.symm hj]
    · exact fun hi ↦ (hi (Finset.mem_univ _)).elim
  have hgoal : κ ^ 2 * f x - Δ f x = 0 := by rw [hlap, sub_self]
  exact hgoal

/-! ### Finite-element approximations (SYNOPSIS item 67) -/

/-- SYNOPSIS item 67, weak Galerkin covariance convergence in Hilbert-space form.
For the Neumann problem, `V` carries the coercive energy inner product, `H` is `L²`, and
`J : V →L[ℝ] H` is the inclusion. The resolvent is `J J†`, and replacing the energy space by
a subspace `U n` inserts its orthogonal projection. The `α`th powers give the covariance
operators for integer orders. The conclusion is convergence on every pair of test functions.
See Lindgren, Rue and Lindström (2011), Definitions 7–8, p. 450, and Theorems 3–4, p. 451. -/
theorem tendsto_inner_galerkinCovariance {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →L[ℝ] H) (U : ℕ → Submodule ℝ V) [∀ n, (U n).HasOrthogonalProjection]
    (hU : ∀ v : V, ∃ w : ℕ → V, (∀ n, w n ∈ U n) ∧ Tendsto w atTop (𝓝 v))
    (f g : H) (α : ℕ) :
    Tendsto (fun n ↦ ⟪f, ((J.comp ((U n).starProjection.comp J.adjoint)) ^ α) g⟫)
      atTop (𝓝 ⟪f, ((J.comp J.adjoint) ^ α) g⟫) := by
  have hP (v : V) : Tendsto (fun n ↦ (U n).starProjection v) atTop (𝓝 v) := by
    obtain ⟨w, hw, hlim⟩ := hU v
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n ↦ norm_nonneg _) _ (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
    intro n
    calc
      ‖(U n).starProjection v - v‖ = ‖v - (U n).starProjection v‖ := norm_sub_rev _ _
      _ = ⨅ x : U n, ‖v - (x : V)‖ := Submodule.starProjection_minimal v
      _ ≤ ‖v - w n‖ :=
        ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ (⟨w n, hw n⟩ : U n)
      _ = ‖w n - v‖ := norm_sub_rev _ _
  have hproj {v : ℕ → V} {v₀ : V} (hv : Tendsto v atTop (𝓝 v₀)) :
      Tendsto (fun n ↦ (U n).starProjection (v n)) atTop (𝓝 v₀) := by
    have herr : Tendsto (fun n ↦ (U n).starProjection (v n - v₀)) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun n ↦ (U n).norm_starProjection_apply_le _) (tendsto_iff_norm_sub_tendsto_zero.mp hv)
    simpa only [map_sub, sub_add_cancel, zero_add] using herr.add (hP v₀)
  let B : ℕ → H →L[ℝ] H := fun n ↦ J.comp ((U n).starProjection.comp J.adjoint)
  let B₀ : H →L[ℝ] H := J.comp J.adjoint
  have hpower (k : ℕ) : Tendsto (fun n ↦ (B n ^ k) g) atTop (𝓝 ((B₀ ^ k) g)) := by
    induction k with
    | zero => simpa only [pow_zero] using tendsto_const_nhds
    | succ k hk =>
      simp only [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, B, B₀]
      exact (J.continuous.tendsto _).comp (hproj ((J.adjoint.continuous.tendsto _).comp hk))
  exact tendsto_const_nhds.inner (hpower α)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite-element precision matrices `Q_0 = C`, `Q_1 = K`, `Q_{α+2} = K C⁻¹ Q_α C⁻¹ K`, so
that `Q_2 = K C⁻¹ K`. -/
def femPrecision (K C : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => C
  | 1 => K
  | α + 2 => K * C⁻¹ * femPrecision K C α * C⁻¹ * K

lemma femPrecision_zero (K C : Matrix ι ι ℝ) : femPrecision K C 0 = C := by
  rw [femPrecision]

lemma femPrecision_one (K C : Matrix ι ι ℝ) : femPrecision K C 1 = K := by
  rw [femPrecision]

lemma femPrecision_add_two (K C : Matrix ι ι ℝ) (α : ℕ) :
    femPrecision K C (α + 2) = K * C⁻¹ * femPrecision K C α * C⁻¹ * K := by
  rw [femPrecision]

/-- SYNOPSIS item 67: for a positive definite mass matrix `C`, a positive semidefinite stiffness
matrix `G`, and `κ > 0`, every `Q_α` built from `K = κ² C + G` is positive definite. -/
theorem femPrecision_posDef {C G : Matrix ι ι ℝ} (hC : C.PosDef) (hG : G.PosSemidef) {κ : ℝ}
    (hκ : 0 < κ) (α : ℕ) : (femPrecision (κ ^ 2 • C + G) C α).PosDef := by
  let K := κ ^ 2 • C + G
  have hK : K.PosDef := (hC.smul (pow_pos hκ 2)).add_posSemidef hG
  have hinj : Function.Injective (C⁻¹ * K).mulVec :=
    mulVec_injective_of_isUnit (hC.inv.isUnit.mul hK.isUnit)
  have hstep (a : ℕ) (hQ : (femPrecision K C a).PosDef) :
      (femPrecision K C (a + 2)).PosDef := by
    simpa only [femPrecision_add_two, conjTranspose_mul, hK.isHermitian.eq,
      hC.inv.isHermitian.eq, Matrix.mul_assoc] using hQ.conjTranspose_mul_mul_same hinj
  induction α using Nat.twoStepInduction with
  | zero => simpa only [femPrecision_zero] using hC
  | one => simpa only [femPrecision_one] using hK
  | more a ih _ => exact hstep a ih

/-- SYNOPSIS item 67: with the lumped diagonal mass matrix `C̃` and `K` supported on the edges of
the triangulation graph, `Q_α` vanishes between nodes at graph distance greater than `α`, so the
approximation is a Gaussian Markov random field. -/
theorem femPrecision_eq_zero_of_lt_edist (Gr : SimpleGraph ι) {K C : Matrix ι ι ℝ}
    (hC : ∀ i j, i ≠ j → C i j = 0) (hCpos : ∀ i, 0 < C i i)
    (hK : ∀ i j, i ≠ j → ¬ Gr.Adj i j → K i j = 0) (α : ℕ) {i j : ι}
    (hij : (α : ℕ∞) < Gr.edist i j) : femPrecision K C α i j = 0 := by
  have hmul {A B : Matrix ι ι ℝ} {a b : ℕ∞}
      (hA : ∀ i j, a < Gr.edist i j → A i j = 0)
      (hB : ∀ i j, b < Gr.edist i j → B i j = 0) :
      ∀ i j, a + b < Gr.edist i j → (A * B) i j = 0 := by
    intro u v huv
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ ↦ ?_
    by_cases huw : a < Gr.edist u w
    · rw [hA u w huw, zero_mul]
    have hwv : b < Gr.edist w v := by
      by_contra! hwv
      exact (not_le_of_gt huv) (Gr.edist_triangle.trans (add_le_add (le_of_not_gt huw) hwv))
    rw [hB w v hwv, mul_zero]
  have hCdiag : C = Matrix.diagonal (fun u ↦ C u u) := by
    ext u v
    by_cases h : u = v
    · subst v
      simp
    · simp only [Matrix.diagonal_apply_ne _ h, hC u v h]
  have hCinv : C⁻¹ = Matrix.diagonal (fun u ↦ (C u u)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    conv_lhs => rw [hCdiag]
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      mul_inv_cancel₀ (hCpos _).ne', Matrix.diagonal_one]
  have hInv : ∀ u v, (0 : ℕ∞) < Gr.edist u v → C⁻¹ u v = 0 := by
    intro u v huv
    have hne : u ≠ v := fun h ↦ by simp [h] at huv
    rw [hCinv, Matrix.diagonal_apply_ne _ hne]
  have hOne : ∀ u v, (1 : ℕ∞) < Gr.edist u v → K u v = 0 := by
    intro u v huv
    have hn := mt Gr.edist_le_one_iff_adj_or_eq.mpr (not_le_of_gt huv)
    exact hK u v (fun h ↦ hn (Or.inr h)) (fun h ↦ hn (Or.inl h))
  revert i j
  induction α using Nat.twoStepInduction with
  | zero =>
    intro i j hij
    rw [femPrecision_zero]
    exact hC i j (fun h ↦ by simp [h] at hij)
  | one =>
    intro i j hij
    simpa only [femPrecision_one] using hOne i j hij
  | more n ih _ =>
    intro i j hij
    have hstep := hmul (hmul (hmul (hmul hOne hInv) (fun i j ↦ @ih i j)) hInv) hOne
    have hn : (1 : ℕ∞) + 0 + (n : ℕ∞) + 0 + 1 = ((n + 2 : ℕ) : ℕ∞) := by
      simp only [Nat.cast_add, add_zero, ← one_add_one_eq_two]
      ac_rfl
    rw [femPrecision_add_two]
    exact hstep i j (hn.symm ▸ hij)

/-- SYNOPSIS item 67, the lattice field on `ℤ²` with full conditional mean
`a⁻¹ (x_{i-1,j} + x_{i+1,j} + x_{i,j-1} + x_{i,j+1})` and variance `1/a` has precision symbol
`a - 2 cos ω₁ - 2 cos ω₂ = κ² + ‖ω‖² + O(‖ω‖⁴)` with `κ² = a - 4`, the Matérn symbol at low
frequencies. -/
theorem latticeSymbol_isBigO (a : ℝ) :
    (fun ω : ℝ × ℝ ↦ a - 2 * Real.cos ω.1 - 2 * Real.cos ω.2 - ((a - 4) + ω.1 ^ 2 + ω.2 ^ 2))
      =O[𝓝 0] fun ω ↦ ‖ω‖ ^ 4 := by
  refine IsBigO.of_bound (4 * (5 / 96)) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) zero_lt_one] with ω hω
  have hnorm : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
  have h₁ : |ω.1| ≤ ‖ω‖ := by
    rw [← Real.norm_eq_abs]
    exact le_max_left _ _
  have h₂ : |ω.2| ≤ ‖ω‖ := by
    rw [← Real.norm_eq_abs]
    exact le_max_right _ _
  have hb₁ := Real.cos_bound (h₁.trans hnorm.le)
  have hb₂ := Real.cos_bound (h₂.trans hnorm.le)
  have heq : a - 2 * Real.cos ω.1 - 2 * Real.cos ω.2 - ((a - 4) + ω.1 ^ 2 + ω.2 ^ 2) =
      -2 * ((Real.cos ω.1 - (1 - ω.1 ^ 2 / 2)) + (Real.cos ω.2 - (1 - ω.2 ^ 2 / 2))) := by
    ring
  rw [heq, Real.norm_eq_abs, abs_mul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  norm_num only [abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0), neg_neg]
  have hb (x : ℝ) (hx : |x| ≤ ‖ω‖) : |x| ^ 4 * (5 / 96) ≤ ‖ω‖ ^ 4 * (5 / 96) := by
    gcongr
  have hsum := (abs_add_le _ _).trans (add_le_add (hb₁.trans (hb _ h₁)) (hb₂.trans (hb _ h₂)))
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2)]

/-- SYNOPSIS item 67: for `a > 4` and `κ² = a - 4`, the symbol of the `α`-fold convolution of the
lattice precision agrees with the Matérn symbol `(κ² + ‖ω‖²)^α` to first order at low
frequencies. -/
theorem tendsto_latticeSymbol_div {a : ℝ} (ha : 4 < a) (α : ℕ) :
    Tendsto (fun ω : ℝ × ℝ ↦ (a - 2 * Real.cos ω.1 - 2 * Real.cos ω.2) ^ α /
      ((a - 4) + ω.1 ^ 2 + ω.2 ^ 2) ^ α) (𝓝 0) (𝓝 1) := by
  have hnum : Continuous (fun ω : ℝ × ℝ ↦ (a - 2 * Real.cos ω.1 - 2 * Real.cos ω.2) ^ α) :=
    by fun_prop
  have hden : Continuous (fun ω : ℝ × ℝ ↦ ((a - 4) + ω.1 ^ 2 + ω.2 ^ 2) ^ α) := by fun_prop
  have hzero : (a - 4) ^ α ≠ 0 := pow_ne_zero _ (sub_pos.mpr ha).ne'
  have hval : a - 2 - 2 = a - 4 := by ring
  have hlim := hnum.continuousAt.div hden.continuousAt
    (a := (0 : ℝ × ℝ)) (by simpa using hzero)
  simpa [hval, hzero] using! hlim.tendsto

end MSSS
