module

public import MSSS.Geostatistics.Likelihood
public import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Matheron's variogram estimator

SYNOPSIS item 45. For data sites `s_i` and a lag `h`, `N(h)` is the set of pairs `(i, j)` with
`s_i - s_j = h`, and Matheron's estimator is
`γ̂(h) = (2 |N(h)|)⁻¹ ∑_{N(h)} (Z(s_i) - Z(s_j))²`.

## Main definitions

* `MSSS.lagPairs s h`: the set `N(h)`.
* `MSSS.matheronEstimator s h z`: the estimate `γ̂(h)` for data `z`.
* `MSSS.matheronMatrix s h`: the matrix `A(h)` with `γ̂(h) = zᵀ A(h) z`.

## Main results

* `MSSS.integral_matheronEstimator`, `MSSS.integral_sq_sub_of_mean`: SYNOPSIS item 45 (a).
* `MSSS.matheronMatrix_properties`, `MSSS.map_matheronEstimator_gaussianLaw`,
  `MSSS.moments_matheronEstimator_gaussianLaw`: SYNOPSIS item 45 (b).
* `MSSS.charpoly_sqrt_mul_matheronMatrix_mul_sqrt`: the spectral comparison in item 45 (b).
* `MSSS.exists_matheronEstimator_not_condNegDef`: SYNOPSIS item 45 (c).

The Gaussian law and moment proofs use Mathlib’s orthonormal-basis representation of the
standard Gaussian, and TauCeti’s square-root quadratic form and Gaussian moment formulas.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace ENNReal

namespace MSSS

variable {E ι : Type*} [AddCommGroup E] [DecidableEq E] [Fintype ι] [DecidableEq ι]

/-- The set `N(h)` of pairs of data sites `(s_i, s_j)` with `s_i - s_j = h`. -/
def lagPairs (s : ι → E) (h : E) : Finset (ι × ι) :=
  Finset.univ.filter fun p ↦ s p.1 - s p.2 = h

/-- **Matheron's estimator** `γ̂(h) = (2 |N(h)|)⁻¹ ∑_{N(h)} (z_i - z_j)²`. -/
def matheronEstimator (s : ι → E) (h : E) (z : ι → ℝ) : ℝ :=
  (2 * (lagPairs s h).card : ℝ)⁻¹ * ∑ p ∈ lagPairs s h, (z p.1 - z p.2) ^ 2

/-- The matrix `A(h) = (2 |N(h)|)⁻¹ ∑_{N(h)} (e_i - e_j)(e_i - e_j)ᵀ`. -/
def matheronMatrix (s : ι → E) (h : E) : Matrix ι ι ℝ :=
  (2 * (lagPairs s h).card : ℝ)⁻¹ • ∑ p ∈ lagPairs s h,
    vecMulVec (Pi.single p.1 1 - Pi.single p.2 1) (Pi.single p.1 1 - Pi.single p.2 1)

omit [DecidableEq ι] in
lemma lagPairs_def (s : ι → E) (h : E) :
    lagPairs s h = Finset.univ.filter fun p ↦ s p.1 - s p.2 = h := by
  rw [lagPairs]

omit [DecidableEq ι] in
lemma matheronEstimator_def (s : ι → E) (h : E) (z : ι → ℝ) :
    matheronEstimator s h z =
      (2 * (lagPairs s h).card : ℝ)⁻¹ * ∑ p ∈ lagPairs s h, (z p.1 - z p.2) ^ 2 := by
  rw [matheronEstimator]

lemma matheronMatrix_def (s : ι → E) (h : E) :
    matheronMatrix s h = (2 * (lagPairs s h).card : ℝ)⁻¹ • ∑ p ∈ lagPairs s h,
      vecMulVec (Pi.single p.1 1 - Pi.single p.2 1) (Pi.single p.1 1 - Pi.single p.2 1) := by
  rw [matheronMatrix]

omit [DecidableEq ι] in
/-- SYNOPSIS item 45 (a): if `Z` has constant mean and `E (Z(x + h) - Z(x))² = 2γ(h)`, then
`E 2γ̂(h) = 2γ(h)` whenever `N(h)` is nonempty. -/
theorem integral_matheronEstimator {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : E → Ω → ℝ} (hZ : ∀ x, MemLp (Z x) 2 P)
    (_hmean : ∀ x y, P[Z x] = P[Z y]) {γ : E → ℝ}
    (hγ : ∀ x h, ∫ ω, (Z (x + h) ω - Z x ω) ^ 2 ∂P = 2 * γ h) (s : ι → E) {h : E}
    (hN : (lagPairs s h).Nonempty) :
    ∫ ω, 2 * matheronEstimator s h (fun i ↦ Z (s i) ω) ∂P = 2 * γ h := by
  have hterm (p : ι × ι) (hp : p ∈ lagPairs s h) :
      (∫ ω, (Z (s p.1) ω - Z (s p.2) ω) ^ 2 ∂P) = 2 * γ h := by
    have hp' : s p.1 - s p.2 = h := (Finset.mem_filter.mp hp).2
    have hadd : s p.2 + h = s p.1 := by rw [← hp', add_sub_cancel]
    simpa only [hadd] using hγ (s p.2) h
  have hcard : ((lagPairs s h).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hN
  simp only [matheronEstimator, ← mul_assoc]
  rw [integral_const_mul, integral_finsetSum]
  · rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    field_simp
  · exact fun p _ ↦ ((hZ (s p.1)).sub (hZ (s p.2))).integrable_sq

omit [DecidableEq E] in
/-- SYNOPSIS item 45 (a): for `Z = μ + ε` with `ε` of constant mean and
`E (ε(x + h) - ε(x))² = 2γ(h)`, `E (Z(x) - Z(y))² = 2γ(x - y) + (μ(x) - μ(y))²`. -/
theorem integral_sq_sub_of_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ε : E → Ω → ℝ} (hε : ∀ x, MemLp (ε x) 2 P)
    (hmean : ∀ x y, P[ε x] = P[ε y]) {γ : E → ℝ}
    (hγ : ∀ x h, ∫ ω, (ε (x + h) ω - ε x ω) ^ 2 ∂P = 2 * γ h) (μ : E → ℝ) (x y : E) :
    ∫ ω, ((μ x + ε x ω) - (μ y + ε y ω)) ^ 2 ∂P = 2 * γ (x - y) + (μ x - μ y) ^ 2 := by
  let d : Ω → ℝ := fun ω ↦ ε x ω - ε y ω
  let b : ℝ := μ x - μ y
  have hd : MemLp d 2 P := (hε x).sub (hε y)
  have hε₁ (t : E) : Integrable (ε t) P := (hε t).integrable (by norm_num)
  have hd₁ : Integrable d P := (hε₁ x).sub (hε₁ y)
  have hdmean : P[d] = 0 := by
    dsimp only [d]
    rw [integral_sub (hε₁ x) (hε₁ y), hmean x y, sub_self]
  have hdsq : ∫ ω, d ω ^ 2 ∂P = 2 * γ (x - y) := by
    simpa only [d, add_sub_cancel] using hγ y (x - y)
  have hexpand (ω : Ω) :
      ((μ x + ε x ω) - (μ y + ε y ω)) ^ 2 =
        (d ω ^ 2 + (2 * b) * d ω) + b ^ 2 := by
    dsimp only [d, b]
    ring
  simp only [hexpand]
  have hcross : Integrable (fun ω ↦ (2 * b) * d ω) P := hd₁.const_mul _
  have hsum : Integrable (fun ω ↦ d ω ^ 2 + (2 * b) * d ω) P :=
    hd.integrable_sq.add hcross
  rw [integral_add hsum (integrable_const (b ^ 2)), integral_add hd.integrable_sq hcross,
    integral_const_mul, hdmean, mul_zero, add_zero, hdsq, integral_const, probReal_univ, one_smul]

/-- SYNOPSIS item 45 (b): `γ̂(h) = zᵀ A(h) z` with `A(h)` symmetric positive semidefinite and
`A(h) 𝟏 = 0`. -/
theorem matheronMatrix_properties (s : ι → E) (h : E) :
    (matheronMatrix s h).PosSemidef ∧ matheronMatrix s h *ᵥ (fun _ ↦ 1) = 0 ∧
      ∀ z, matheronEstimator s h z = z ⬝ᵥ (matheronMatrix s h *ᵥ z) := by
  let v (p : ι × ι) : ι → ℝ := Pi.single p.1 1 - Pi.single p.2 1
  have hdot (p : ι × ι) (z : ι → ℝ) : v p ⬝ᵥ z = z p.1 - z p.2 := by
    simp only [v, sub_dotProduct, single_one_dotProduct]
  have hmul (p : ι × ι) (z : ι → ℝ) :
      vecMulVec (v p) (v p) *ᵥ z = (z p.1 - z p.2) • v p := by
    rw [vecMulVec_mulVec, hdot]
    ext i
    exact mul_comm _ _
  have hdot' (p : ι × ι) (z : ι → ℝ) : z ⬝ᵥ v p = z p.1 - z p.2 := by
    rw [dotProduct_comm, hdot]
  have hmat : matheronMatrix s h =
      (2 * (lagPairs s h).card : ℝ)⁻¹ • ∑ p ∈ lagPairs s h, vecMulVec (v p) (v p) := rfl
  rw [hmat]
  refine ⟨?_, ?_, ?_⟩
  · apply (posSemidef_sum _ ?_).smul (by positivity)
    intro p _
    simpa only [Pi.star_apply, star_trivial] using posSemidef_vecMulVec_self_star (v p)
  · simp only [smul_mulVec, sum_mulVec, hmul, sub_self, zero_smul, Finset.sum_const_zero,
      smul_zero]
  · intro z
    simp only [matheronEstimator, smul_mulVec, sum_mulVec, hmul, dotProduct_smul,
      dotProduct_sum, hdot', smul_eq_mul, pow_two]

/-- SYNOPSIS item 45 (b): the symmetric matrix `√Σ A(h) √Σ` and `A(h) Σ` have the same
characteristic polynomial, including for singular `Σ`. -/
theorem charpoly_sqrt_mul_matheronMatrix_mul_sqrt (s : ι → E) (h : E)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (CFC.sqrt S * matheronMatrix s h * CFC.sqrt S).charpoly =
      (matheronMatrix s h * S).charpoly := by
  rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, CFC.sqrt_mul_sqrt_self S hS.nonneg]

omit [DecidableEq ι] in
/-- Adding a common offset to all observations leaves Matheron's estimator unchanged. -/
lemma matheronEstimator_add_const (s : ι → E) (h : E) (z : ι → ℝ) (m : ℝ) :
    matheronEstimator s h (fun i ↦ m + z i) = matheronEstimator s h z := by
  simp only [matheronEstimator_def, add_sub_add_left_eq_sub]

omit [DecidableEq ι] in
/-- The estimator is a finite sum of squared coordinate differences. -/
lemma measurable_matheronEstimator (s : ι → E) (h : E) : Measurable (matheronEstimator s h) := by
  unfold matheronEstimator
  fun_prop

/-- The standard Gaussian quadratic form in a symmetric matrix has the law of the
eigenvalue-weighted sum of coordinate squares. -/
lemma map_inner_toEuclideanLin_stdGaussian_eq {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun u ↦ ⟪u, A.toEuclideanLin u⟫) =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun u : EuclideanSpace ℝ ι ↦ ∑ i, hA.eigenvalues i * (WithLp.ofLp u i) ^ 2) := by
  conv_lhs => rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis]
  conv_rhs => rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, hA.inner_toEuclideanLin_sum_smul_eigenvectorBasis,
    RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs, sq_abs]

set_option linter.unusedVariables false in
/-- SYNOPSIS item 45 (b): if `𝐙 ∼ N(μ𝟏, Σ)`, then `γ̂(h)` has the law of `∑ λ_i χ²_{1,i}` with
independent `χ²₁` variables, where `λ_i` are the eigenvalues of `Σ^{1/2} A(h) Σ^{1/2}`; its
nonzero eigenvalues are those of `A(h) Σ`. -/
theorem map_matheronEstimator_gaussianLaw (s : ι → E) (h : E) (μ : ℝ) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef)
    (hB : (CFC.sqrt S * matheronMatrix s h * CFC.sqrt S).IsHermitian) :
    (gaussianLaw (fun _ ↦ μ) S).map (matheronEstimator s h) =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        fun u : EuclideanSpace ℝ ι ↦ ∑ i, hB.eigenvalues i * (WithLp.ofLp u i) ^ 2 := by
  let A := matheronMatrix s h
  let F := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ ↦ μ)
  have hF (u : EuclideanSpace ℝ ι) :
      matheronEstimator s h (WithLp.ofLp (a + F u)) =
        ⟪u, (CFC.sqrt S * A * CFC.sqrt S).toEuclideanLin u⟫ := by
    have hm : WithLp.ofLp (a + F u) = fun i ↦ μ + WithLp.ofLp (F u) i := rfl
    rw [hm, matheronEstimator_add_const, (matheronMatrix_properties s h).2.2]
    calc
      _ = ⟪F u, A.toEuclideanLin (F u)⟫ := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
          Matrix.ofLp_toLpLin, Matrix.toLin'_apply, A, dotProduct_comm]
      _ = _ := Matrix.inner_toEuclideanCLM_sqrt_toEuclideanLin S A u
  have hOf : Measurable (WithLp.ofLp : EuclideanSpace ℝ ι → ι → ℝ) :=
    (PiLp.continuous_ofLp 2 (fun _ : ι ↦ ℝ)).measurable
  rw [gaussianLaw_def, multivariateGaussian, Measure.map_map (measurable_matheronEstimator s h) hOf,
    Measure.map_map ((measurable_matheronEstimator s h).comp hOf) (by fun_prop)]
  calc
    _ = (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun u ↦ ⟪u, (CFC.sqrt S * A * CFC.sqrt S).toEuclideanLin u⟫) := by
      congr 1
      funext u
      exact hF u
    _ = _ := map_inner_toEuclideanLin_stdGaussian_eq hB


/-- A standard Gaussian square is square integrable. -/
lemma memLp_sq_gaussianReal_zero_one :
    MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 1) := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  have h4 := TauCeti.Probability.integral_sub_pow_four_gaussianReal 0 1
  norm_num at h4
  simpa only [Pi.pow_apply, ← pow_mul, Nat.reduceMul, h4] using (three_ne_zero : (3 : ℝ) ≠ 0)

/-- A standard Gaussian square has variance two. -/
lemma variance_sq_gaussianReal_zero_one :
    Var[fun x : ℝ ↦ x ^ 2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub memLp_sq_gaussianReal_zero_one]
  have h2 := TauCeti.Probability.integral_sq_gaussianReal 0 1
  have h4 := TauCeti.Probability.integral_sub_pow_four_gaussianReal 0 1
  norm_num at h2 h4
  simp only [Pi.pow_apply, ← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [h2, h4]
  norm_num

omit [DecidableEq ι] in
/-- The moments of a weighted sum of independent standard Gaussian squares. -/
lemma integral_variance_sum_mul_sq_pi_gaussianReal (c : ι → ℝ) :
    (∫ x : ι → ℝ, ∑ i, c i * x i ^ 2 ∂Measure.pi (fun _ ↦ gaussianReal 0 1)) = ∑ i, c i ∧
    Var[fun x : ι → ℝ ↦ ∑ i, c i * x i ^ 2; Measure.pi (fun _ ↦ gaussianReal 0 1)] =
      2 * ∑ i, c i ^ 2 := by
  let ν := gaussianReal 0 1
  let νπ := Measure.pi (fun _ : ι ↦ ν)
  let f (i : ι) (x : ℝ) := c i * x ^ 2
  have hf (i : ι) : MemLp (f i) 2 ν := memLp_sq_gaussianReal_zero_one.const_mul (c i)
  have hfi (i : ι) : Integrable (fun x : ι → ℝ ↦ f i (x i)) νπ :=
    ((hf i).comp_measurePreserving (measurePreserving_eval _ i)).integrable (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [integral_finsetSum _ (fun i _ ↦ hfi i)]
    apply Finset.sum_congr rfl
    intro i _
    have he := integral_comp_eval (μ := fun _ : ι ↦ ν) (i := i)
      (hf i).aestronglyMeasurable
    rw [he]
    dsimp only [f, ν]
    rw [integral_const_mul, TauCeti.Probability.integral_sq_gaussianReal]
    norm_num
  · have hv := variance_sum_pi (μ := fun _ : ι ↦ ν) (X := f) hf
    have hfun : (∑ i, fun x : ι → ℝ ↦ f i (x i)) =
        fun x : ι → ℝ ↦ ∑ i, c i * x i ^ 2 := by
      funext x
      simp only [Finset.sum_apply, f]
    rw [hfun] at hv
    simp only [f, ν, variance_const_mul, variance_sq_gaussianReal_zero_one] at hv
    rw [hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- Cyclicity of the trace removes the square root from both traces in the Gaussian moments. -/
lemma trace_sqrt_mul_mul_sqrt_and_sq {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (A : Matrix ι ι ℝ) :
    (CFC.sqrt S * A * CFC.sqrt S).trace = (A * S).trace ∧
    ((CFC.sqrt S * A * CFC.sqrt S) ^ 2).trace = ((A * S) ^ 2).trace := by
  let R := CFC.sqrt S
  have hR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  refine ⟨?_, ?_⟩
  · calc
      (R * A * R).trace = (R * (R * A)).trace := Matrix.trace_mul_comm _ _
      _ = (A * S).trace := by rw [← mul_assoc, hR, Matrix.trace_mul_comm]
  · calc
      ((R * A * R) ^ 2).trace = (R * (A * S * A * R)).trace := by
        rw [← hR]
        simp only [pow_two, mul_assoc]
      _ = (A * S * A * R * R).trace := Matrix.trace_mul_comm _ _
      _ = ((A * S) ^ 2).trace := by
        rw [mul_assoc (A * S * A), hR, pow_two, mul_assoc (A * S)]

/-- SYNOPSIS item 45 (b): if `𝐙 ∼ N(μ𝟏, Σ)`, then `E γ̂(h) = tr(A(h) Σ)` and
`Var γ̂(h) = 2 tr((A(h) Σ)²)`. -/
theorem moments_matheronEstimator_gaussianLaw (s : ι → E) (h : E) (μ : ℝ)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∫ z, matheronEstimator s h z ∂gaussianLaw (fun _ ↦ μ) S = (matheronMatrix s h * S).trace ∧
      Var[matheronEstimator s h; gaussianLaw (fun _ ↦ μ) S] =
        2 * ((matheronMatrix s h * S) ^ 2).trace := by
  let A := matheronMatrix s h
  let B := CFC.sqrt S * A * CFC.sqrt S
  have hB : B.IsHermitian :=
    Matrix.isHermitian_sqrt_mul_mul_sqrt S (matheronMatrix_properties s h).1.isHermitian
  let νπ := Measure.pi (fun _ : ι ↦ gaussianReal 0 1)
  let f (x : ι → ℝ) := ∑ i, hB.eigenvalues i * x i ^ 2
  have hf : Measurable f := by unfold f; fun_prop
  have hG : HasLaw f (νπ.map f) νπ := hasLaw_map hf.aemeasurable
  have hE : HasLaw (matheronEstimator s h) (νπ.map f) (gaussianLaw (fun _ ↦ μ) S) := by
    refine ⟨(measurable_matheronEstimator s h).aemeasurable, ?_⟩
    rw [map_matheronEstimator_gaussianLaw s h μ hS hB, ← map_pi_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have htrace := trace_sqrt_mul_mul_sqrt_and_sq hS A
  obtain ⟨hEpi, hVpi⟩ := integral_variance_sum_mul_sq_pi_gaussianReal hB.eigenvalues
  have hEtr : ∫ x, f x ∂νπ = B.trace :=
    hEpi.trans hB.trace_eq_sum_eigenvalues.symm
  have hVtr : Var[f; νπ] = 2 * (B ^ 2).trace := by
    rw [hB.trace_pow_eq_sum_eigenvalues_pow]
    exact hVpi
  constructor
  · rw [hE.integral_eq, ← hG.integral_eq, hEtr]
    exact htrace.1
  · rw [hE.variance_eq, ← hG.variance_eq, hVtr]
    exact congrArg (2 * ·) htrace.2

/-- SYNOPSIS item 45 (c): the estimated variogram need not be conditionally negative definite.
There are sites and data on the line and points `x_k`, all of whose differences are observed
lags, with weights `c_k` summing to zero and `∑_{k,l} c_k c_l γ̂(x_k - x_l) > 0`. -/
theorem exists_matheronEstimator_not_condNegDef :
    ∃ (n : ℕ) (s z : Fin n → ℝ) (m : ℕ) (x c : Fin m → ℝ), ∑ k, c k = 0 ∧
      (∀ k l, (lagPairs s (x k - x l)).Nonempty) ∧
      0 < ∑ k, ∑ l, c k * c l * matheronEstimator s (x k - x l) z := by
  let s : Fin 4 → ℝ := ![0, 1, 2, 3]
  let z : Fin 4 → ℝ := ![0, 1, 3, 4]
  let x : Fin 3 → ℝ := ![0, 1, 2]
  let c : Fin 3 → ℝ := ![1, -2, 1]
  refine ⟨4, s, z, 3, x, c, ?_, ?_, ?_⟩
  · norm_num [c, Fin.sum_univ_succ]
  · intro k l
    refine ⟨(Fin.castSucc k, Fin.castSucc l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    fin_cases k <;> fin_cases l <;> rfl
  · have h₀ : lagPairs s 0 = {(0, 0), (1, 1), (2, 2), (3, 3)} := by
      ext p
      obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> norm_num [lagPairs, s]
    have h₁ : lagPairs s 1 = {(1, 0), (2, 1), (3, 2)} := by
      ext p
      obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> norm_num [lagPairs, s]
    have hn₁ : lagPairs s (-1) = {(0, 1), (1, 2), (2, 3)} := by
      ext p
      obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> norm_num [lagPairs, s]
    have h₂ : lagPairs s 2 = {(2, 0), (3, 1)} := by
      ext p
      obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> norm_num [lagPairs, s]
    have hn₂ : lagPairs s (-2) = {(0, 2), (1, 3)} := by
      ext p
      obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> norm_num [lagPairs, s]
    have hzero : matheronEstimator s 0 z = 0 := by norm_num [matheronEstimator, h₀, z]
    have hpos : matheronEstimator s 1 z = 1 := by norm_num [matheronEstimator, h₁, z]
    have hneg : matheronEstimator s (-1) z = 1 := by norm_num [matheronEstimator, hn₁, z]
    have hpos₂ : matheronEstimator s 2 z = 9 / 2 := by norm_num [matheronEstimator, h₂, z]
    have hneg₂ : matheronEstimator s (-2) z = 9 / 2 := by norm_num [matheronEstimator, hn₂, z]
    norm_num [x, c, Fin.sum_univ_succ, hzero, hpos, hneg, hpos₂, hneg₂]

end MSSS
