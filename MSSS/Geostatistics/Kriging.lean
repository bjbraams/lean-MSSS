module

public import MSSS.RandomFields.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import TauCeti.Analysis.Matrix.PosSemidef.Block

/-!
# Kriging

SYNOPSIS items 24 and 27: simple kriging (best linear prediction with known mean) and
universal kriging (best linear unbiased prediction with a linear mean model).

Observations are `Z (x i)`, `i : ι`, of a second-order field `Z`, and the predictand is
`Z x₀`. The covariance matrix is `𝐊 = (Cov(Z(x_i), Z(x_j)))`, the cross-covariance vector is
`𝐤 = (Cov(Z(x_i), Z(x₀)))`, and `k₀ = Var Z(x₀)`.

For universal kriging the field is `Z_β(t) = f(t) ⬝ β + ε(t)` with a known regressor
`f : T → ℝᵖ`, an unknown `β`, and a centred second-order residual field `ε` with known
covariance; `𝐅` is the design matrix with rows `f(x_i)`.

## Main definitions

* `MSSS.affineMSE P Y ψ c w`: the mean squared error `E (ψ - c - ∑ w_i Y_i)²`.
* `MSSS.IsBestAffinePredictor P Y ψ c w`: `(c, w)` minimises `affineMSE`.
* `MSSS.bestAffineWeights P Y ψ`: a chosen minimiser, and `MSSS.predictionError P Y ψ` its error.
* `MSSS.obsCov`, `MSSS.crossCov`: the matrix `𝐊` and the vector `𝐤`.
* `MSSS.designMatrix f x`: the matrix `𝐅`.
* `MSSS.ukMSE`, `MSSS.IsUnbiasedPredictor`, `MSSS.IsBLUP`: mean squared error, unbiasedness, and
  best linear unbiased prediction in the universal kriging model; `MSSS.blupWeights` is a chosen
  best linear unbiased predictor.
* `MSSS.glsMatrix K F`: the generalised least-squares matrix `(𝐅ᵀ 𝐊⁻¹ 𝐅)⁻¹ 𝐅ᵀ 𝐊⁻¹`.

## Main results

The column-space result uses TauCeti’s range inclusion for positive-semidefinite block matrices.

* SYNOPSIS item 24: `MSSS.affineMSE_eq`, `MSSS.exists_obsCov_mulVec_eq_crossCov`,
  `MSSS.isBestAffinePredictor_iff`, `MSSS.exists_isBestAffinePredictor`,
  `MSSS.IsBestAffinePredictor.ae_eq`, `MSSS.isBestAffinePredictor_simpleKriging`,
  `MSSS.affineMSE_simpleKriging`.
* SYNOPSIS item 27: `MSSS.isUnbiasedPredictor_iff`, `MSSS.exists_isUnbiasedPredictor_iff`,
  `MSSS.isBLUP_iff`, `MSSS.exists_krigingSystem`, `MSSS.IsBLUP.ae_eq`,
  `MSSS.det_borderedMatrix_ne_zero_iff`, `MSSS.det_borderedMatrix_ne_zero_of_posDef`,
  `MSSS.isBLUP_universalKriging`, `MSSS.gls_isBLUE`, `MSSS.gls_isMinOn_gaussianLikelihood`,
  `MSSS.IsBLUP.error_contrast`, `MSSS.isBLUP_iff_of_contrastVariance_eq`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace MSSS

variable {Ω T ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-! ### Best affine prediction -/

/-- The mean squared error `E (ψ - c - ∑ w_i Y_i)²` of the affine predictor `c + ∑ w_i Y_i`. -/
def affineMSE (P : Measure Ω) (Y : ι → Ω → ℝ) (ψ : Ω → ℝ) (c : ℝ) (w : ι → ℝ) : ℝ :=
  ∫ ω, (ψ ω - c - ∑ i, w i * Y i ω) ^ 2 ∂P

/-- `c + ∑ w_i Y_i` is a **best affine predictor** of `ψ`: it minimises the mean squared error
among all affine predictors. -/
def IsBestAffinePredictor (P : Measure Ω) (Y : ι → Ω → ℝ) (ψ : Ω → ℝ) (c : ℝ) (w : ι → ℝ) :
    Prop :=
  ∀ c' w', affineMSE P Y ψ c w ≤ affineMSE P Y ψ c' w'

/-- A chosen best affine predictor (intercept and weights); a minimiser exists for
square-integrable variables (`MSSS.exists_isBestAffinePredictor`). -/
def bestAffineWeights (P : Measure Ω) (Y : ι → Ω → ℝ) (ψ : Ω → ℝ) : ℝ × (ι → ℝ) :=
  Classical.epsilon fun p : ℝ × (ι → ℝ) ↦ IsBestAffinePredictor P Y ψ p.1 p.2

/-- The error `ψ - ψ̂` of the chosen best affine predictor of `ψ` from `Y`. -/
def predictionError (P : Measure Ω) (Y : ι → Ω → ℝ) (ψ : Ω → ℝ) (ω : Ω) : ℝ :=
  ψ ω - (bestAffineWeights P Y ψ).1 - ∑ i, (bestAffineWeights P Y ψ).2 i * Y i ω

lemma affineMSE_def (P : Measure Ω) (Y : ι → Ω → ℝ) (ψ : Ω → ℝ) (c : ℝ) (w : ι → ℝ) :
    affineMSE P Y ψ c w = ∫ ω, (ψ ω - c - ∑ i, w i * Y i ω) ^ 2 ∂P := by
  rw [affineMSE]

lemma isBestAffinePredictor_def {P : Measure Ω} {Y : ι → Ω → ℝ} {ψ : Ω → ℝ} {c : ℝ}
    {w : ι → ℝ} : IsBestAffinePredictor P Y ψ c w ↔
      ∀ c' w', affineMSE P Y ψ c w ≤ affineMSE P Y ψ c' w' := Iff.rfl

lemma isBestAffinePredictor_bestAffineWeights {P : Measure Ω} {Y : ι → Ω → ℝ} {ψ : Ω → ℝ}
    (h : ∃ c w, IsBestAffinePredictor P Y ψ c w) :
    IsBestAffinePredictor P Y ψ (bestAffineWeights P Y ψ).1 (bestAffineWeights P Y ψ).2 := by
  obtain ⟨c, w, hcw⟩ := h
  exact Classical.epsilon_spec (p := fun p : ℝ × (ι → ℝ) ↦ IsBestAffinePredictor P Y ψ p.1 p.2)
    ⟨(c, w), hcw⟩

lemma predictionError_def (P : Measure Ω) (Y : ι → Ω → ℝ) (ψ : Ω → ℝ) (ω : Ω) :
    predictionError P Y ψ ω =
      ψ ω - (bestAffineWeights P Y ψ).1 - ∑ i, (bestAffineWeights P Y ψ).2 i * Y i ω := by
  rw [predictionError]

/-- The covariance matrix `𝐊 = (Cov(Z(x_i), Z(x_j)))` of the observations. -/
def obsCov (P : Measure Ω) (Z : T → Ω → ℝ) (x : ι → T) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ cov[Z (x i), Z (x j); P]

/-- The cross-covariance vector `𝐤 = (Cov(Z(x_i), Z(x₀)))`. -/
def crossCov (P : Measure Ω) (Z : T → Ω → ℝ) (x : ι → T) (x₀ : T) : ι → ℝ :=
  fun i ↦ cov[Z (x i), Z x₀; P]

omit [Fintype ι] in
lemma obsCov_apply (P : Measure Ω) (Z : T → Ω → ℝ) (x : ι → T) (i j : ι) :
    obsCov P Z x i j = cov[Z (x i), Z (x j); P] := by
  rw [obsCov, Matrix.of_apply]

omit [Fintype ι] in
lemma crossCov_apply (P : Measure Ω) (Z : T → Ω → ℝ) (x : ι → T) (x₀ : T) (i : ι) :
    crossCov P Z x x₀ i = cov[Z (x i), Z x₀; P] := by
  rw [crossCov]

/-! ### Simple kriging (SYNOPSIS item 24) -/

section SimpleKriging

variable {P : Measure Ω} [IsProbabilityMeasure P] {Z : T → Ω → ℝ} (x : ι → T) (x₀ : T)

/-- The observation covariance quadratic form is the variance of the weighted sum. -/
theorem variance_weighted_observations (hZ : IsSecondOrderField Z P) (w : ι → ℝ) :
    Var[fun ω ↦ ∑ i, w i * Z (x i) ω; P] = w ⬝ᵥ (obsCov P Z x *ᵥ w) := by
  rw [variance_fun_sum (fun i ↦ (isSecondOrderField_iff.mp hZ (x i)).const_mul (w i))]
  have hcov (i j : ι) :
      cov[fun ω ↦ w i * Z (x i) ω, fun ω ↦ w j * Z (x j) ω; P] =
        w i * (cov[Z (x i), Z (x j); P] * w j) := by
    rw [covariance_const_mul_left, covariance_const_mul_right, mul_comm (w j)]
  simp only [hcov, dotProduct, mulVec, obsCov_apply, Finset.mul_sum]

omit [Fintype ι] in
/-- The covariance matrix of a finite observation vector is positive semidefinite. -/
theorem obsCov_posSemidef (hZ : IsSecondOrderField Z P) : (obsCov P Z x).PosSemidef := by
  exact (posSemidef_covariance hZ).submatrix x

/-- SYNOPSIS item 24: the mean squared error of an affine predictor `λ₀ + λ ⬝ 𝐙` is
`(m(x₀) - λ₀ - λ ⬝ 𝐦)² + k₀ - 2 λ ⬝ 𝐤 + λ ⬝ 𝐊 λ`. -/
theorem affineMSE_eq (hZ : IsSecondOrderField Z P) (c : ℝ) (w : ι → ℝ) :
    affineMSE P (fun i ↦ Z (x i)) (Z x₀) c w =
      (P[Z x₀] - c - w ⬝ᵥ fun i ↦ P[Z (x i)]) ^ 2 + Var[Z x₀; P] -
        2 * (w ⬝ᵥ crossCov P Z x x₀) + w ⬝ᵥ (obsCov P Z x *ᵥ w) := by
  have hW : ∀ i, MemLp (fun ω ↦ w i * Z (x i) ω) 2 P :=
    fun i ↦ (isSecondOrderField_iff.mp hZ (x i)).const_mul _
  have hS := memLp_finsetSum Finset.univ (fun i _ ↦ hW i)
  have hX : MemLp (fun ω ↦ Z x₀ ω - c) 2 P := (isSecondOrderField_iff.mp hZ x₀).sub (memLp_const _)
  have hMean :
      (∫ ω, Z x₀ ω - c - ∑ i, w i * Z (x i) ω ∂P) =
        P[Z x₀] - c - w ⬝ᵥ fun i ↦ P[Z (x i)] := by
    rw [integral_sub (hX.integrable one_le_two) (hS.integrable one_le_two),
      integral_sub ((isSecondOrderField_iff.mp hZ x₀).integrable one_le_two) (integrable_const c),
      integral_finsetSum _ (fun i _ ↦ (hW i).integrable one_le_two)]
    simp [dotProduct, integral_const_mul]
  have hCov : cov[Z x₀, fun ω ↦ ∑ i, w i * Z (x i) ω; P] =
      w ⬝ᵥ crossCov P Z x x₀ := by
    rw [covariance_comm, covariance_fun_sum_left hW (isSecondOrderField_iff.mp hZ x₀)]
    simp only [covariance_const_mul_left, dotProduct, crossCov_apply]
  have hVar := variance_eq_sub (hX.sub hS)
  simp only [Pi.sub_apply, Pi.pow_apply] at hVar
  rw [hMean, variance_sub hX hS,
    variance_sub_const (isSecondOrderField_iff.mp hZ x₀).aestronglyMeasurable,
    covariance_fun_sub_left (isSecondOrderField_iff.mp hZ x₀) (memLp_const c) hS,
    covariance_const_left, sub_zero, hCov, variance_weighted_observations x hZ] at hVar
  rw [affineMSE_def]
  linarith

/-- SYNOPSIS item 24: the vector `𝐤` lies in the column space of `𝐊`. -/
theorem exists_obsCov_mulVec_eq_crossCov (hZ : IsSecondOrderField Z P) :
    ∃ v, obsCov P Z x *ᵥ v = crossCov P Z x x₀ := by
  classical
  let S := obsCov P Z (Sum.elim x (fun _ : Unit ↦ x₀))
  have hS : S.PosSemidef := obsCov_posSemidef _ hZ
  have hK : S.toBlocks₁₁ = obsCov P Z x := by
    ext i j
    simp [S, obsCov_apply, Matrix.toBlocks₁₁]
  have hk : S.toBlocks₁₂ *ᵥ (fun _ ↦ 1) = crossCov P Z x x₀ := by
    ext i
    simp [S, mulVec, dotProduct, obsCov_apply, crossCov_apply, Matrix.toBlocks₁₂]
  have hmem : WithLp.toLp 2 (crossCov P Z x x₀) ∈
      LinearMap.range S.toBlocks₁₂.toEuclideanLin := by
    exact ⟨WithLp.toLp 2 (fun _ ↦ 1), by simp [toEuclideanLin, toLpLin_apply, hk]⟩
  obtain ⟨v, hv⟩ := hS.range_toEuclideanLin_toBlocks₁₂_le hmem
  exact ⟨v.ofLp, by simpa [hK, toEuclideanLin, toLpLin_apply] using congrArg WithLp.ofLp hv⟩

/-- SYNOPSIS item 24: the minimisers of the mean squared error are exactly the pairs with
`𝐊 λ = 𝐤` and `λ₀ = m(x₀) - λ ⬝ 𝐦`. -/
theorem isBestAffinePredictor_iff (hZ : IsSecondOrderField Z P) (c : ℝ) (w : ι → ℝ) :
    IsBestAffinePredictor P (fun i ↦ Z (x i)) (Z x₀) c w ↔
      obsCov P Z x *ᵥ w = crossCov P Z x x₀ ∧ c = P[Z x₀] - w ⬝ᵥ fun i ↦ P[Z (x i)] := by
  obtain ⟨v, hv⟩ := exists_obsCov_mulVec_eq_crossCov x x₀ hZ
  let K := obsCov P Z x
  let k := crossCov P Z x x₀
  let m : ι → ℝ := fun i ↦ P[Z (x i)]
  have hK : K.PosSemidef := obsCov_posSemidef x hZ
  have hv' : K *ᵥ v = k := hv
  have hKt : Kᵀ = K := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hRisk (d : ℝ) (u : ι → ℝ) :
      affineMSE P (fun i ↦ Z (x i)) (Z x₀) d u =
        Var[Z x₀; P] - v ⬝ᵥ k + (P[Z x₀] - d - u ⬝ᵥ m) ^ 2 +
          (u - v) ⬝ᵥ (K *ᵥ (u - v)) := by
    have hsym : v ⬝ᵥ (K *ᵥ u) = u ⬝ᵥ k := by
      rw [← dotProduct_transpose_mulVec K u v, hKt, hv']
    rw [affineMSE_eq x x₀ hZ]
    simp only [mulVec_sub, sub_dotProduct, dotProduct_sub, hv', hsym, K, k, m]
    ring
  have hnonneg (u : ι → ℝ) : 0 ≤ (u - v) ⬝ᵥ (K *ᵥ (u - v)) := by
    simpa only [star_trivial] using hK.dotProduct_mulVec_nonneg (u - v)
  constructor
  · intro h
    have hmin := isBestAffinePredictor_def.mp h (P[Z x₀] - v ⬝ᵥ m) v
    rw [hRisk, hRisk] at hmin
    simp only [sub_self, mulVec_zero, dotProduct_zero, add_zero] at hmin
    have hbias : P[Z x₀] - c - w ⬝ᵥ m = 0 := by nlinarith [hnonneg w]
    have hquad : (w - v) ⬝ᵥ (K *ᵥ (w - v)) = 0 := by
      have hb : P[Z x₀] - (P[Z x₀] - v ⬝ᵥ m) - v ⬝ᵥ m = 0 := by ring
      rw [hbias, hb] at hmin
      linarith [hnonneg w]
    have hz := hK.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial] using hquad)
    rw [mulVec_sub, hv', sub_eq_zero] at hz
    exact ⟨hz, by linarith⟩
  · rw [isBestAffinePredictor_def]
    rintro ⟨hw, rfl⟩ c' w'
    have hw' : K *ᵥ w = k := hw
    rw [hRisk, hRisk, mulVec_sub, hw', hv', sub_self, dotProduct_zero]
    have hb : P[Z x₀] - (P[Z x₀] - w ⬝ᵥ m) - w ⬝ᵥ m = 0 := by ring
    rw [hb]
    nlinarith [hnonneg w', sq_nonneg (P[Z x₀] - c' - w' ⬝ᵥ m)]

/-- SYNOPSIS item 24: a best linear predictor always exists. -/
theorem exists_isBestAffinePredictor (hZ : IsSecondOrderField Z P) :
    ∃ c w, IsBestAffinePredictor P (fun i ↦ Z (x i)) (Z x₀) c w := by
  obtain ⟨v, hv⟩ := exists_obsCov_mulVec_eq_crossCov x x₀ hZ
  exact ⟨_, v, (isBestAffinePredictor_iff x x₀ hZ _ _).2 ⟨hv, rfl⟩⟩

/-- SYNOPSIS item 24: any two best linear predictors agree almost surely. -/
theorem IsBestAffinePredictor.ae_eq (hZ : IsSecondOrderField Z P) {c c' : ℝ} {w w' : ι → ℝ}
    (h : IsBestAffinePredictor P (fun i ↦ Z (x i)) (Z x₀) c w)
    (h' : IsBestAffinePredictor P (fun i ↦ Z (x i)) (Z x₀) c' w') :
    (fun ω ↦ c + ∑ i, w i * Z (x i) ω) =ᵐ[P] fun ω ↦ c' + ∑ i, w' i * Z (x i) ω := by
  obtain ⟨hw, hc⟩ := (isBestAffinePredictor_iff x x₀ hZ c w).mp h
  obtain ⟨hw', hc'⟩ := (isBestAffinePredictor_iff x x₀ hZ c' w').mp h'
  let d := w - w'
  let S : Ω → ℝ := fun ω ↦ ∑ i, d i * Z (x i) ω
  have hv : Var[S; P] = 0 := by
    dsimp only [S, d]
    rw [variance_weighted_observations x hZ, mulVec_sub, hw, hw', sub_self, dotProduct_zero]
  have hW (i : ι) : MemLp (fun ω ↦ d i * Z (x i) ω) 2 P :=
    (isSecondOrderField_iff.mp hZ (x i)).const_mul _
  have hS : MemLp S 2 P := memLp_finsetSum Finset.univ (fun i _ ↦ hW i)
  have hMean : P[S] = d ⬝ᵥ fun i ↦ P[Z (x i)] := by
    dsimp only [S]
    rw [integral_finsetSum _ (fun i _ ↦ (hW i).integrable one_le_two)]
    simp only [integral_const_mul, dotProduct]
  filter_upwards [ae_eq_integral_of_variance_eq_zero hS hv] with ω hω
  rw [hMean] at hω
  simp only [S, d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_dotProduct] at hω
  rw [hc, hc']
  linarith

section Inverse

variable [DecidableEq ι]

/-- SYNOPSIS item 24: if `𝐊` is nonsingular, the simple kriging predictor is
`m(x₀) + 𝐤ᵀ 𝐊⁻¹ (𝐙 - 𝐦)`. -/
theorem isBestAffinePredictor_simpleKriging (hZ : IsSecondOrderField Z P)
    (hK : IsUnit (obsCov P Z x).det) :
    IsBestAffinePredictor P (fun i ↦ Z (x i)) (Z x₀)
      (P[Z x₀] - ((obsCov P Z x)⁻¹ *ᵥ crossCov P Z x x₀) ⬝ᵥ fun i ↦ P[Z (x i)])
      ((obsCov P Z x)⁻¹ *ᵥ crossCov P Z x x₀) := by
  apply (isBestAffinePredictor_iff x x₀ hZ _ _).2
  refine ⟨?_, rfl⟩
  rw [mulVec_mulVec, mul_nonsing_inv _ hK, one_mulVec]

/-- SYNOPSIS item 24: if `𝐊` is nonsingular, the simple kriging variance is
`k₀ - 𝐤ᵀ 𝐊⁻¹ 𝐤 ≤ k₀`. -/
theorem affineMSE_simpleKriging (hZ : IsSecondOrderField Z P)
    (hK : IsUnit (obsCov P Z x).det) :
    affineMSE P (fun i ↦ Z (x i)) (Z x₀)
        (P[Z x₀] - ((obsCov P Z x)⁻¹ *ᵥ crossCov P Z x x₀) ⬝ᵥ fun i ↦ P[Z (x i)])
        ((obsCov P Z x)⁻¹ *ᵥ crossCov P Z x x₀) =
      Var[Z x₀; P] - crossCov P Z x x₀ ⬝ᵥ ((obsCov P Z x)⁻¹ *ᵥ crossCov P Z x x₀) ∧
    Var[Z x₀; P] - crossCov P Z x x₀ ⬝ᵥ ((obsCov P Z x)⁻¹ *ᵥ crossCov P Z x x₀) ≤
      Var[Z x₀; P] := by
  let K := obsCov P Z x
  let k := crossCov P Z x x₀
  let v := K⁻¹ *ᵥ k
  have hv : K *ᵥ v = k := by
    dsimp only [v]
    rw [mulVec_mulVec, mul_nonsing_inv _ hK, one_mulVec]
  have hM : affineMSE P (fun i ↦ Z (x i)) (Z x₀)
      (P[Z x₀] - v ⬝ᵥ fun i ↦ P[Z (x i)]) v = Var[Z x₀; P] - k ⬝ᵥ v := by
    rw [affineMSE_eq x x₀ hZ, hv]
    rw [dotProduct_comm k v]
    ring
  refine ⟨hM, ?_⟩
  have hMin := isBestAffinePredictor_def.mp
    (isBestAffinePredictor_simpleKriging x x₀ hZ hK) (P[Z x₀]) 0
  rw [hM, affineMSE_eq x x₀ hZ] at hMin
  simpa using hMin

end Inverse

end SimpleKriging

/-! ### Universal kriging (SYNOPSIS item 27) -/

/-- The design matrix `𝐅` with rows `f(x_i)`. -/
def designMatrix {p : ℕ} (f : T → Fin p → ℝ) (x : ι → T) : Matrix ι (Fin p) ℝ :=
  Matrix.of fun i j ↦ f (x i) j

omit [Fintype ι] in
lemma designMatrix_apply {p : ℕ} (f : T → Fin p → ℝ) (x : ι → T) (i : ι) (j : Fin p) :
    designMatrix f x i j = f (x i) j := by
  rw [designMatrix, Matrix.of_apply]

/-- The mean squared error, for the parameter `β`, of the affine predictor `c + ∑ w_i Z_β(x_i)`
of `Z_β(x₀)`, where `Z_β(t) = f(t) ⬝ β + ε(t)`. -/
def ukMSE (P : Measure Ω) (ε : T → Ω → ℝ) {p : ℕ} (f : T → Fin p → ℝ) (x : ι → T) (x₀ : T)
    (β : Fin p → ℝ) (c : ℝ) (w : ι → ℝ) : ℝ :=
  ∫ ω, (f x₀ ⬝ᵥ β + ε x₀ ω - c - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) ^ 2 ∂P

/-- The affine predictor `c + ∑ w_i Z_β(x_i)` is **unbiased**: its error has mean zero for
every `β`. -/
def IsUnbiasedPredictor (P : Measure Ω) (ε : T → Ω → ℝ) {p : ℕ} (f : T → Fin p → ℝ)
    (x : ι → T) (x₀ : T) (c : ℝ) (w : ι → ℝ) : Prop :=
  ∀ β : Fin p → ℝ,
    ∫ ω, (f x₀ ⬝ᵥ β + ε x₀ ω - c - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) ∂P = 0

/-- `∑ w_i Z_β(x_i)` is a **best linear unbiased predictor** of `Z_β(x₀)`: it is unbiased and,
for every `β`, its mean squared error is minimal among unbiased affine predictors. -/
def IsBLUP (P : Measure Ω) (ε : T → Ω → ℝ) {p : ℕ} (f : T → Fin p → ℝ) (x : ι → T) (x₀ : T)
    (w : ι → ℝ) : Prop :=
  IsUnbiasedPredictor P ε f x x₀ 0 w ∧ ∀ c' w', IsUnbiasedPredictor P ε f x x₀ c' w' →
    ∀ β, ukMSE P ε f x x₀ β 0 w ≤ ukMSE P ε f x x₀ β c' w'

lemma ukMSE_def (P : Measure Ω) (ε : T → Ω → ℝ) {p : ℕ} (f : T → Fin p → ℝ) (x : ι → T)
    (x₀ : T) (β : Fin p → ℝ) (c : ℝ) (w : ι → ℝ) : ukMSE P ε f x x₀ β c w =
      ∫ ω, (f x₀ ⬝ᵥ β + ε x₀ ω - c - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) ^ 2 ∂P := by
  rw [ukMSE]

lemma isUnbiasedPredictor_def {P : Measure Ω} {ε : T → Ω → ℝ} {p : ℕ} {f : T → Fin p → ℝ}
    {x : ι → T} {x₀ : T} {c : ℝ} {w : ι → ℝ} : IsUnbiasedPredictor P ε f x x₀ c w ↔
      ∀ β : Fin p → ℝ,
        ∫ ω, (f x₀ ⬝ᵥ β + ε x₀ ω - c - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) ∂P = 0 :=
  Iff.rfl

lemma isBLUP_def {P : Measure Ω} {ε : T → Ω → ℝ} {p : ℕ} {f : T → Fin p → ℝ} {x : ι → T}
    {x₀ : T} {w : ι → ℝ} : IsBLUP P ε f x x₀ w ↔
      IsUnbiasedPredictor P ε f x x₀ 0 w ∧ ∀ c' w', IsUnbiasedPredictor P ε f x x₀ c' w' →
        ∀ β, ukMSE P ε f x x₀ β 0 w ≤ ukMSE P ε f x x₀ β c' w' := Iff.rfl

/-- A chosen best linear unbiased predictor (its weights); one exists whenever an unbiased
predictor exists (`MSSS.exists_krigingSystem`, `MSSS.isBLUP_iff`). -/
def blupWeights (P : Measure Ω) (ε : T → Ω → ℝ) {p : ℕ} (f : T → Fin p → ℝ) (x : ι → T)
    (x₀ : T) : ι → ℝ :=
  Classical.epsilon (IsBLUP P ε f x x₀)

lemma isBLUP_blupWeights {P : Measure Ω} {ε : T → Ω → ℝ} {p : ℕ} {f : T → Fin p → ℝ}
    {x : ι → T} {x₀ : T} (h : ∃ w, IsBLUP P ε f x x₀ w) :
    IsBLUP P ε f x x₀ (blupWeights P ε f x x₀) :=
  Classical.epsilon_spec h

section UniversalKriging

variable {P : Measure Ω} [IsProbabilityMeasure P] {ε : T → Ω → ℝ} {p : ℕ}
  (f : T → Fin p → ℝ) (x : ι → T) (x₀ : T)

/-- SYNOPSIS item 27 (a): `λ₀ + λ ⬝ 𝐙` is unbiased if and only if `λ₀ = 0` and `𝐅ᵀ λ = f₀`. -/
theorem isUnbiasedPredictor_iff (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0) (c : ℝ)
    (w : ι → ℝ) :
    IsUnbiasedPredictor P ε f x x₀ c w ↔ c = 0 ∧ (designMatrix f x)ᵀ *ᵥ w = f x₀ := by
  have hInt (β : Fin p → ℝ) :
      (∫ ω, f x₀ ⬝ᵥ β + ε x₀ ω - c - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω) ∂P) =
        f x₀ ⬝ᵥ β - c - β ⬝ᵥ ((designMatrix f x)ᵀ *ᵥ w) := by
    have hεInt (t : T) := (isSecondOrderField_iff.mp hε t).integrable one_le_two
    have hZ (t : T) : Integrable (fun ω ↦ f t ⬝ᵥ β + ε t ω) P :=
      (integrable_const _).add (hεInt t)
    have hX : Integrable (fun ω ↦ f x₀ ⬝ᵥ β + ε x₀ ω - c) P :=
      (hZ x₀).sub (integrable_const c)
    have hS : Integrable (fun ω ↦ ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) P :=
      integrable_finsetSum Finset.univ fun i _ ↦ (hZ (x i)).const_mul _
    rw [integral_sub hX hS,
      integral_sub (hZ x₀) (integrable_const c),
      integral_finsetSum _ (fun i _ ↦ (hZ (x i)).const_mul _),
      dotProduct_transpose_mulVec]
    simp_rw [integral_const_mul, integral_add (integrable_const _) (hεInt _),
      integral_const, hc, probReal_univ, one_smul, add_zero]
    simp only [dotProduct, mulVec, designMatrix_apply]
  simp only [isUnbiasedPredictor_def, hInt]
  constructor
  · intro h
    have hc' : c = 0 := by simpa using h 0
    refine ⟨hc', ?_⟩
    ext j
    have hβ := h (Pi.single j 1)
    rw [hc', sub_zero, dotProduct_single_one, single_one_dotProduct, sub_eq_zero] at hβ
    exact hβ.symm
  · rintro ⟨rfl, hw⟩ β
    rw [hw, sub_zero, dotProduct_comm (f x₀) β, sub_self]

/-- SYNOPSIS item 27 (a): an unbiased linear predictor exists if and only if `f₀` lies in the
column space of `𝐅ᵀ`. -/
theorem exists_isUnbiasedPredictor_iff (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0) :
    (∃ c w, IsUnbiasedPredictor P ε f x x₀ c w) ↔ ∃ w, (designMatrix f x)ᵀ *ᵥ w = f x₀ := by
  simp only [isUnbiasedPredictor_iff f x x₀ hε hc]
  exact ⟨fun ⟨_, w, _, hw⟩ ↦ ⟨w, hw⟩, fun ⟨w, hw⟩ ↦ ⟨0, w, rfl, hw⟩⟩

/-- Unbiased weights reproduce the linear mean at the target site. -/
theorem sum_mul_design_eq {w : ι → ℝ} (hw : (designMatrix f x)ᵀ *ᵥ w = f x₀)
    (β : Fin p → ℝ) : ∑ i, w i * (f (x i) ⬝ᵥ β) = f x₀ ⬝ᵥ β := by
  have h := dotProduct_transpose_mulVec (designMatrix f x) β w
  rw [hw, dotProduct_comm β (f x₀)] at h
  simpa only [dotProduct, mulVec, designMatrix_apply] using h.symm

/-- For unbiased weights, the prediction error depends only on the residual field. -/
theorem ukMSE_eq_variance_of_mulVec_eq (hε : IsSecondOrderField ε P)
    (hc : ∀ t, P[ε t] = 0) {w : ι → ℝ} (hw : (designMatrix f x)ᵀ *ᵥ w = f x₀)
    (β : Fin p → ℝ) :
    ukMSE P ε f x x₀ β 0 w =
      Var[fun ω ↦ (1 : ℝ) * ε x₀ ω + ∑ i, (-w i) * ε (x i) ω; P] := by
  have hLp (i : ι) : MemLp (fun ω ↦ (-w i) * ε (x i) ω) 2 P :=
    (isSecondOrderField_iff.mp hε (x i)).const_mul _
  have hx₀ := (isSecondOrderField_iff.mp hε x₀).const_mul (1 : ℝ)
  have hsum := memLp_finsetSum Finset.univ (fun i _ ↦ hLp i)
  have hm :
      (∫ ω, (1 : ℝ) * ε x₀ ω + ∑ i, (-w i) * ε (x i) ω ∂P) = 0 := by
    rw [integral_add (hx₀.integrable one_le_two) (hsum.integrable one_le_two),
      integral_finsetSum _ (fun i _ ↦ (hLp i).integrable one_le_two)]
    simp only [integral_const_mul, hc, mul_zero, Finset.sum_const_zero, add_zero]
  have hErr : MemLp (fun ω ↦ (1 : ℝ) * ε x₀ ω + ∑ i, (-w i) * ε (x i) ω) 2 P :=
    hx₀.add hsum
  rw [ukMSE_def, variance_of_integral_eq_zero hErr.aemeasurable hm]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [mul_add, Finset.sum_add_distrib, sum_mul_design_eq f x x₀ hw β, sub_zero,
    one_mul, neg_mul, Finset.sum_neg_distrib]
  ring

/-- A BLUP minimises the variance of the residual contrast among feasible weights. -/
theorem isBLUP_iff_min_residual_variance (hε : IsSecondOrderField ε P)
    (hc : ∀ t, P[ε t] = 0) (w : ι → ℝ) :
    IsBLUP P ε f x x₀ w ↔ (designMatrix f x)ᵀ *ᵥ w = f x₀ ∧
      ∀ v, (designMatrix f x)ᵀ *ᵥ v = f x₀ →
        Var[fun ω ↦ (1 : ℝ) * ε x₀ ω + ∑ i, (-w i) * ε (x i) ω; P] ≤
          Var[fun ω ↦ (1 : ℝ) * ε x₀ ω + ∑ i, (-v i) * ε (x i) ω; P] := by
  rw [isBLUP_def]
  constructor
  · rintro ⟨hu, hmin⟩
    have hw := ((isUnbiasedPredictor_iff f x x₀ hε hc _ _).1 hu).2
    refine ⟨hw, fun v hv ↦ ?_⟩
    have hu' := (isUnbiasedPredictor_iff f x x₀ hε hc 0 v).2 ⟨rfl, hv⟩
    simpa only [ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hw,
      ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hv] using hmin 0 v hu' 0
  · rintro ⟨hw, hmin⟩
    refine ⟨(isUnbiasedPredictor_iff f x x₀ hε hc _ _).2 ⟨rfl, hw⟩, ?_⟩
    intro c v hu' β
    obtain ⟨rfl, hv⟩ := (isUnbiasedPredictor_iff f x x₀ hε hc _ _).1 hu'
    simpa only [ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hw,
      ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hv] using hmin v hv

/-- For feasible weights, the universal kriging risk is the centred affine risk. -/
private lemma ukMSE_eq_centered_affineMSE (hε : IsSecondOrderField ε P)
    (hc : ∀ t, P[ε t] = 0) {w : ι → ℝ} (hw : (designMatrix f x)ᵀ *ᵥ w = f x₀)
    (β : Fin p → ℝ) :
    ukMSE P ε f x x₀ β 0 w = affineMSE P (fun i ↦ ε (x i)) (ε x₀) 0 w := by
  rw [ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hw β,
    ← ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hw 0, ukMSE_def, affineMSE_def]
  simp only [dotProduct_zero, zero_add, sub_zero]

/-- Quadratic expansion of the centred prediction risk along a direction of weights. -/
private lemma affineMSE_add_smul_sub (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0)
    (w d : ι → ℝ) (t : ℝ) :
    let K := obsCov P ε x
    let k := crossCov P ε x x₀
    let risk := affineMSE P (fun i ↦ ε (x i)) (ε x₀) 0
    risk (w + t • d) - risk w =
      (d ⬝ᵥ (K *ᵥ d)) * (t * t) + (-2 * (d ⬝ᵥ (k - K *ᵥ w))) * t := by
  have hK := obsCov_posSemidef x hε
  have hKt : (obsCov P ε x)ᵀ = obsCov P ε x := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hsym : w ⬝ᵥ (obsCov P ε x *ᵥ d) = d ⬝ᵥ (obsCov P ε x *ᵥ w) := by
    rw [← dotProduct_transpose_mulVec, hKt]
  have hmean : (fun i ↦ P[ε (x i)]) = (0 : ι → ℝ) := funext fun i ↦ hc (x i)
  dsimp only
  rw [affineMSE_eq x x₀ hε, affineMSE_eq x x₀ hε]
  simp only [hc x₀, hmean, dotProduct_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hsym, dotProduct_sub]
  ring

/-- SYNOPSIS item 27 (b): `λ ⬝ 𝐙` is a best linear unbiased predictor if and only if there is
`μ ∈ ℝᵖ` with `𝐊 λ + 𝐅 μ = 𝐤` and `𝐅ᵀ λ = f₀`, the bordered kriging system. -/
theorem isBLUP_iff (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0) (w : ι → ℝ) :
    IsBLUP P ε f x x₀ w ↔ ∃ μ : Fin p → ℝ,
      obsCov P ε x *ᵥ w + designMatrix f x *ᵥ μ = crossCov P ε x x₀ ∧
        (designMatrix f x)ᵀ *ᵥ w = f x₀ := by
  classical
  let K := obsCov P ε x
  let k := crossCov P ε x x₀
  let F := designMatrix f x
  let r := k - K *ᵥ w
  let risk := affineMSE P (fun i ↦ ε (x i)) (ε x₀) 0
  have hK := obsCov_posSemidef x hε
  have hRisk (v : ι → ℝ) (hv : Fᵀ *ᵥ v = f x₀) (β : Fin p → ℝ) :
      ukMSE P ε f x x₀ β 0 v = risk v :=
    ukMSE_eq_centered_affineMSE f x x₀ hε hc hv β
  have hdiff (t : ℝ) (d : ι → ℝ) :
      risk (w + t • d) - risk w = (d ⬝ᵥ (K *ᵥ d)) * (t * t) + (-2 * (d ⬝ᵥ r)) * t :=
    affineMSE_add_smul_sub x x₀ hε hc w d t
  constructor
  · intro h
    obtain ⟨hu, hmin⟩ := isBLUP_def.mp h
    have hw := ((isUnbiasedPredictor_iff f x x₀ hε hc 0 w).1 hu).2
    have horth (d : ι → ℝ) (hd : Fᵀ *ᵥ d = 0) : d ⬝ᵥ r = 0 := by
      have hq : ∀ t : ℝ, 0 ≤ (d ⬝ᵥ (K *ᵥ d)) * (t * t) + (-2 * (d ⬝ᵥ r)) * t + 0 := by
        intro t
        have hv : Fᵀ *ᵥ (w + t • d) = f x₀ := by
          rw [mulVec_add, mulVec_smul, hd, smul_zero, add_zero, hw]
        have hle := hmin 0 _ ((isUnbiasedPredictor_iff f x x₀ hε hc 0 _).2 ⟨rfl, hv⟩) 0
        rw [hRisk w hw, hRisk _ hv] at hle
        rw [add_zero, ← hdiff, sub_nonneg]
        exact hle
      have hdisc := discrim_le_zero hq
      simp only [discrim, mul_zero, sub_zero] at hdisc
      nlinarith
    have hmem : WithLp.toLp 2 r ∈ (LinearMap.ker (Fᵀ).toEuclideanLin)ᗮ := by
      refine (Submodule.mem_orthogonal _ _).2 fun v hv ↦ ?_
      rw [LinearMap.mem_ker] at hv
      have hv' : Fᵀ *ᵥ v.ofLp = 0 := congrArg WithLp.ofLp hv
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct, mul_comm]
        using horth _ hv'
    rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial, transpose_transpose] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    have hμ' : F *ᵥ μ.ofLp = r := congrArg WithLp.ofLp hμ
    have hs : K *ᵥ w + F *ᵥ μ.ofLp = k := by rw [hμ', add_sub_cancel]
    exact ⟨μ.ofLp, hs, hw⟩
  · rintro ⟨μ, hμ, hw⟩
    refine isBLUP_def.mpr ⟨(isUnbiasedPredictor_iff f x x₀ hε hc 0 w).2 ⟨rfl, hw⟩, ?_⟩
    intro c v hu β
    obtain ⟨rfl, hv⟩ := (isUnbiasedPredictor_iff f x x₀ hε hc c v).1 hu
    let d := v - w
    have hd : Fᵀ *ᵥ d = 0 := by rw [mulVec_sub, hv, hw, sub_self]
    have hr : r = F *ᵥ μ := (eq_sub_of_add_eq' hμ).symm
    have horth : d ⬝ᵥ r = 0 := by rw [hr, ← dotProduct_transpose_mulVec, hd, dotProduct_zero]
    have hnonneg : 0 ≤ d ⬝ᵥ (K *ᵥ d) := by
      simpa only [star_trivial] using hK.dotProduct_mulVec_nonneg d
    have hv' : w + (1 : ℝ) • d = v := by
      dsimp only [d]
      rw [one_smul, add_sub_cancel]
    rw [hRisk w hw, hRisk v hv, ← sub_nonneg, ← hv', hdiff, horth]
    simpa only [mul_zero, one_mul, mul_one, add_zero] using hnonneg

/-- SYNOPSIS item 27 (b): the kriging system is solvable whenever an unbiased predictor
exists. -/
theorem exists_krigingSystem (hε : IsSecondOrderField ε P)
    (hex : ∃ w, (designMatrix f x)ᵀ *ᵥ w = f x₀) :
    ∃ (w : ι → ℝ) (μ : Fin p → ℝ),
      obsCov P ε x *ᵥ w + designMatrix f x *ᵥ μ = crossCov P ε x x₀ ∧
        (designMatrix f x)ᵀ *ᵥ w = f x₀ := by
  classical
  let K := obsCov P ε x
  let k := crossCov P ε x x₀
  let F := designMatrix f x
  let M := Matrix.fromBlocks K F Fᵀ (0 : Matrix (Fin p) (Fin p) ℝ)
  let b := Sum.elim k (f x₀)
  obtain ⟨w₀, hw₀⟩ := hex
  obtain ⟨w₁, hw₁⟩ := exists_obsCov_mulVec_eq_crossCov x x₀ hε
  have hK := obsCov_posSemidef x hε
  have hKt : Kᵀ = K := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hMt : Mᵀ = M := by
    simp only [M, fromBlocks_transpose, transpose_transpose, transpose_zero, hKt]
  have hmem : WithLp.toLp 2 b ∈ (LinearMap.ker M.toEuclideanLin)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun v hv ↦ ?_
    rw [LinearMap.mem_ker] at hv
    have hMv : M *ᵥ v.ofLp = 0 := congrArg WithLp.ofLp hv
    dsimp only [M] at hMv
    rw [fromBlocks_mulVec, zero_mulVec, add_zero] at hMv
    let u := v.ofLp ∘ Sum.inl
    let m := v.ofLp ∘ Sum.inr
    have hl : K *ᵥ u + F *ᵥ m = 0 := congrArg (· ∘ Sum.inl) hMv
    have hr : Fᵀ *ᵥ u = 0 := congrArg (· ∘ Sum.inr) hMv
    have huF : u ⬝ᵥ (F *ᵥ m) = 0 := by
      rw [← dotProduct_transpose_mulVec, hr, dotProduct_zero]
    have hquad : u ⬝ᵥ (K *ᵥ u) = 0 := by
      simpa only [dotProduct_add, huF, add_zero, dotProduct_zero] using
        congrArg (u ⬝ᵥ ·) hl
    have hu : K *ᵥ u = 0 := hK.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial])
    have hm : F *ᵥ m = 0 := by simpa only [hu, zero_add] using hl
    have h₁ : u ⬝ᵥ k = 0 := by
      have hw₁' : K *ᵥ w₁ = k := hw₁
      rw [← hw₁', ← dotProduct_transpose_mulVec, hKt, hu, dotProduct_zero]
    have h₀ : m ⬝ᵥ f x₀ = 0 := by
      have hw₀' : Fᵀ *ᵥ w₀ = f x₀ := hw₀
      rw [← hw₀', ← dotProduct_transpose_mulVec, transpose_transpose, hm, dotProduct_zero]
    calc
      _ = u ⬝ᵥ k + m ⬝ᵥ f x₀ := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct, u, m,
          b, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, mul_comm]
      _ = 0 := by rw [h₁, h₀, add_zero]
  rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial, hMt] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hMv : M *ᵥ v.ofLp = b := congrArg WithLp.ofLp hv
  dsimp only [M] at hMv
  rw [fromBlocks_mulVec, zero_mulVec, add_zero] at hMv
  exact ⟨v.ofLp ∘ Sum.inl, v.ofLp ∘ Sum.inr, congrArg (· ∘ Sum.inl) hMv,
    congrArg (· ∘ Sum.inr) hMv⟩

/-- SYNOPSIS item 27 (b): the best linear unbiased predictor is unique almost surely. -/
theorem IsBLUP.ae_eq (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0) {w w' : ι → ℝ}
    (h : IsBLUP P ε f x x₀ w) (h' : IsBLUP P ε f x x₀ w') (β : Fin p → ℝ) :
    (fun ω ↦ ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) =ᵐ[P]
      fun ω ↦ ∑ i, w' i * (f (x i) ⬝ᵥ β + ε (x i) ω) := by
  obtain ⟨μ, hμ, hw⟩ := (isBLUP_iff f x x₀ hε hc w).1 h
  obtain ⟨μ', hμ', hw'⟩ := (isBLUP_iff f x x₀ hε hc w').1 h'
  let K := obsCov P ε x
  let F := designMatrix f x
  let d := w - w'
  let D : Ω → ℝ := fun ω ↦ ∑ i, d i * ε (x i) ω
  have hd : Fᵀ *ᵥ d = 0 := by rw [mulVec_sub, hw, hw', sub_self]
  have hKd : K *ᵥ d = F *ᵥ (μ' - μ) := by
    have h₁ : K *ᵥ w = crossCov P ε x x₀ - F *ᵥ μ := eq_sub_of_add_eq hμ
    have h₂ : K *ᵥ w' = crossCov P ε x x₀ - F *ᵥ μ' := eq_sub_of_add_eq hμ'
    rw [mulVec_sub, mulVec_sub, h₁, h₂]
    abel
  have hv : Var[D; P] = 0 := by
    dsimp only [D]
    rw [variance_weighted_observations x hε, hKd, ← dotProduct_transpose_mulVec,
      hd, dotProduct_zero]
  have hLp (i : ι) : MemLp (fun ω ↦ d i * ε (x i) ω) 2 P :=
    (isSecondOrderField_iff.mp hε (x i)).const_mul _
  have hD : MemLp D 2 P := memLp_finsetSum Finset.univ (fun i _ ↦ hLp i)
  have hmean : P[D] = 0 := by
    dsimp only [D]
    rw [integral_finsetSum _ (fun i _ ↦ (hLp i).integrable one_le_two)]
    simp only [integral_const_mul, hc, mul_zero, Finset.sum_const_zero]
  filter_upwards [ae_eq_integral_of_variance_eq_zero hD hv] with ω hω
  rw [hmean] at hω
  simp only [D, d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at hω
  simp only [mul_add, Finset.sum_add_distrib, sum_mul_design_eq f x x₀ hw β,
    sum_mul_design_eq f x x₀ hw' β]
  linarith

/-- SYNOPSIS item 27 (c): for `𝐊` positive semidefinite, the bordered matrix
`[[𝐊, 𝐅], [𝐅ᵀ, 0]]` is nonsingular if and only if `𝐅` has full column rank and
`ker 𝐊 ∩ ker 𝐅ᵀ = {0}`. -/
theorem det_borderedMatrix_ne_zero_iff [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.PosSemidef)
    (F : Matrix ι (Fin p) ℝ) :
    (Matrix.fromBlocks K F Fᵀ 0).det ≠ 0 ↔
      Function.Injective F.mulVec ∧ ∀ v, K *ᵥ v = 0 → Fᵀ *ᵥ v = 0 → v = 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v huv
      have heq : (Matrix.fromBlocks K F Fᵀ 0) *ᵥ Sum.elim 0 u =
          (Matrix.fromBlocks K F Fᵀ 0) *ᵥ Sum.elim 0 v := by
        simp [Matrix.fromBlocks_mulVec, huv]
      exact congrArg (fun z ↦ z ∘ Sum.inr) (h heq)
    · intro v hv hFt
      have hz : (Matrix.fromBlocks K F Fᵀ 0) *ᵥ Sum.elim v 0 = 0 := by
        ext i
        cases i <;> simp [Matrix.fromBlocks_mulVec, hv, hFt]
      exact congrArg (fun z ↦ z ∘ Sum.inl) (h (hz.trans (Matrix.mulVec_zero _).symm))
  · rintro ⟨hF, hker⟩
    apply (injective_iff_map_eq_zero (Matrix.fromBlocks K F Fᵀ 0).mulVecLin).2
    intro v hv
    have hv' : (Matrix.fromBlocks K F Fᵀ 0) *ᵥ v = 0 := hv
    rw [Matrix.fromBlocks_mulVec] at hv'
    have hl := congrArg (fun z ↦ z ∘ Sum.inl) hv'
    have hr := congrArg (fun z ↦ z ∘ Sum.inr) hv'
    have hl' : K *ᵥ (v ∘ Sum.inl) + F *ᵥ (v ∘ Sum.inr) = 0 := by
      funext i
      exact congrFun hl i
    have hr' : Fᵀ *ᵥ (v ∘ Sum.inl) = 0 := by
      funext i
      simpa only [Function.comp_apply, Sum.elim_inr, zero_mulVec, add_zero, Pi.zero_apply]
        using congrFun hr i
    have hcross : (v ∘ Sum.inl) ⬝ᵥ (F *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [← dotProduct_transpose_mulVec F (v ∘ Sum.inr) (v ∘ Sum.inl), hr', dotProduct_zero]
    have hquad : (v ∘ Sum.inl) ⬝ᵥ (K *ᵥ (v ∘ Sum.inl)) = 0 := by
      have h := congrArg (fun z ↦ (v ∘ Sum.inl) ⬝ᵥ z) hl'
      simpa only [dotProduct_add, hcross, add_zero, dotProduct_zero] using h
    have hz := hker _ (hK.dotProduct_mulVec_zero_iff.mp
      (by simpa only [star_trivial] using hquad)) hr'
    have hmu : v ∘ Sum.inr = 0 := hF (by
      simpa only [hz, mulVec_zero, zero_add] using hl')
    ext i
    cases i with
    | inl i => exact congrFun hz i
    | inr i => exact congrFun hmu i

/-- SYNOPSIS item 27 (c): the bordered matrix is nonsingular if `𝐊` is positive definite and
`𝐅` has full column rank. -/
theorem det_borderedMatrix_ne_zero_of_posDef [DecidableEq ι] {K : Matrix ι ι ℝ}
    (hK : K.PosDef) {F : Matrix ι (Fin p) ℝ} (hF : Function.Injective F.mulVec) :
    (Matrix.fromBlocks K F Fᵀ 0).det ≠ 0 := by
  refine (det_borderedMatrix_ne_zero_iff hK.posSemidef F).2 ⟨hF, fun v hv _ ↦ ?_⟩
  exact hK.mulVec_injective (hv.trans (Matrix.mulVec_zero _).symm)

/-- The generalised least-squares matrix `(𝐅ᵀ 𝐊⁻¹ 𝐅)⁻¹ 𝐅ᵀ 𝐊⁻¹`, so that `β̂ = B 𝐙`. -/
def glsMatrix [DecidableEq ι] (K : Matrix ι ι ℝ) (F : Matrix ι (Fin p) ℝ) :
    Matrix (Fin p) ι ℝ :=
  (Fᵀ * K⁻¹ * F)⁻¹ * Fᵀ * K⁻¹

lemma glsMatrix_def [DecidableEq ι] (K : Matrix ι ι ℝ) (F : Matrix ι (Fin p) ℝ) :
    glsMatrix K F = (Fᵀ * K⁻¹ * F)⁻¹ * Fᵀ * K⁻¹ := by
  rw [glsMatrix]

/-- The kriging equations simplify the quadratic risk to a linear function of the weights. -/
private lemma ukMSE_eq_of_krigingSystem (hε : IsSecondOrderField ε P)
    (hc : ∀ t, P[ε t] = 0) {w : ι → ℝ} {μ : Fin p → ℝ}
    (hw : (designMatrix f x)ᵀ *ᵥ w = f x₀)
    (hKw : obsCov P ε x *ᵥ w = crossCov P ε x x₀ + designMatrix f x *ᵥ μ) (β : Fin p → ℝ) :
    ukMSE P ε f x x₀ β 0 w = Var[ε x₀; P] - w ⬝ᵥ crossCov P ε x x₀ + μ ⬝ᵥ f x₀ := by
  have hmean : (fun i ↦ P[ε (x i)]) = (0 : ι → ℝ) := funext fun i ↦ hc (x i)
  rw [ukMSE_eq_centered_affineMSE f x x₀ hε hc hw β, affineMSE_eq x x₀ hε, hKw]
  simp only [hc x₀, hmean, dotProduct_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    dotProduct_add, ← dotProduct_transpose_mulVec (designMatrix f x) μ w, hw]
  ring

/-- The GLS predictor formula follows by moving the symmetric inverse matrices across the
dot products. -/
private lemma dotProduct_universalKriging [DecidableEq ι] (K : Matrix ι ι ℝ)
    (F : Matrix ι (Fin p) ℝ) (k z : ι → ℝ) (f₀ : Fin p → ℝ)
    (hKinv : (K⁻¹).IsSymm) (hBinv : ((Fᵀ * K⁻¹ * F)⁻¹).IsSymm) :
    let g := f₀ - Fᵀ *ᵥ (K⁻¹ *ᵥ k)
    let w := K⁻¹ *ᵥ k + K⁻¹ *ᵥ (F *ᵥ ((Fᵀ * K⁻¹ * F)⁻¹ *ᵥ g))
    w ⬝ᵥ z = f₀ ⬝ᵥ (glsMatrix K F *ᵥ z) +
      k ⬝ᵥ (K⁻¹ *ᵥ (z - F *ᵥ (glsMatrix K F *ᵥ z))) := by
  intro g w
  let B := Fᵀ * K⁻¹ * F
  let q := B⁻¹ *ᵥ g
  let u := K⁻¹ *ᵥ k
  let b := glsMatrix K F *ᵥ z
  have hb : b = B⁻¹ *ᵥ (Fᵀ *ᵥ (K⁻¹ *ᵥ z)) := by
    simp only [b, B, glsMatrix_def, mulVec_mulVec, Matrix.mul_assoc]
  have hkF : k ⬝ᵥ (K⁻¹ *ᵥ (F *ᵥ b)) = (Fᵀ *ᵥ u) ⬝ᵥ b := by
    rw [← dotProduct_transpose_mulVec K⁻¹, hKinv.eq, dotProduct_comm (F *ᵥ b),
      ← dotProduct_transpose_mulVec F,
      dotProduct_comm b]
  have hu : u ⬝ᵥ z = k ⬝ᵥ (K⁻¹ *ᵥ z) := by
    dsimp only [u]
    rw [dotProduct_comm _ z, hKinv.dotProduct_mulVec_comm]
  have hq : (K⁻¹ *ᵥ (F *ᵥ q)) ⬝ᵥ z = g ⬝ᵥ b := by
    rw [dotProduct_comm _ z, ← dotProduct_transpose_mulVec K⁻¹, hKinv.eq,
      dotProduct_comm (F *ᵥ q), ← dotProduct_transpose_mulVec F]
    dsimp only [q]
    rw [dotProduct_comm (B⁻¹ *ᵥ g), hBinv.dotProduct_mulVec_comm, ← hb]
  have hg : g ⬝ᵥ b = f₀ ⬝ᵥ b - (Fᵀ *ᵥ u) ⬝ᵥ b := sub_dotProduct _ _ _
  have hwt : w = u + K⁻¹ *ᵥ (F *ᵥ q) := rfl
  rw [hwt, add_dotProduct, hu, hq, hg, mulVec_sub, dotProduct_sub, hkF]
  ring

/-- SYNOPSIS item 27 (d): if `𝐊` is nonsingular and `𝐅` has full column rank, the weights
`w = 𝐊⁻¹ 𝐤 + 𝐊⁻¹ 𝐅 (𝐅ᵀ 𝐊⁻¹ 𝐅)⁻¹ g`, `g = f₀ - 𝐅ᵀ 𝐊⁻¹ 𝐤`, give the best linear unbiased
predictor `f₀ ⬝ β̂ + 𝐤ᵀ 𝐊⁻¹ (𝐙 - 𝐅 β̂)`, with mean squared error
`k₀ - 𝐤ᵀ 𝐊⁻¹ 𝐤 + gᵀ (𝐅ᵀ 𝐊⁻¹ 𝐅)⁻¹ g`. -/
theorem isBLUP_universalKriging [DecidableEq ι] (hε : IsSecondOrderField ε P)
    (hc : ∀ t, P[ε t] = 0) (hK : IsUnit (obsCov P ε x).det)
    (hF : Function.Injective (designMatrix f x).mulVec) :
    let K := obsCov P ε x
    let F := designMatrix f x
    let k := crossCov P ε x x₀
    let g := f x₀ - Fᵀ *ᵥ (K⁻¹ *ᵥ k)
    let w := K⁻¹ *ᵥ k + K⁻¹ *ᵥ (F *ᵥ ((Fᵀ * K⁻¹ * F)⁻¹ *ᵥ g))
    IsBLUP P ε f x x₀ w ∧
      (∀ z : ι → ℝ, w ⬝ᵥ z = f x₀ ⬝ᵥ (glsMatrix K F *ᵥ z) +
        k ⬝ᵥ (K⁻¹ *ᵥ (z - F *ᵥ (glsMatrix K F *ᵥ z)))) ∧
      ∀ β, ukMSE P ε f x x₀ β 0 w =
        Var[ε x₀; P] - k ⬝ᵥ (K⁻¹ *ᵥ k) + g ⬝ᵥ ((Fᵀ * K⁻¹ * F)⁻¹ *ᵥ g) := by
  intro K F k g w
  let B := Fᵀ * K⁻¹ * F
  let q := B⁻¹ *ᵥ g
  let u := K⁻¹ *ᵥ k
  have hK' : IsUnit K.det := hK
  have hKpos : K.PosDef := (obsCov_posSemidef x hε).posDef_iff_isUnit.2
    (Matrix.isUnit_iff_isUnit_det _ |>.2 hK)
  have hB : B.PosDef := by
    simpa only [B, conjTranspose_eq_transpose_of_trivial] using
      hKpos.inv.conjTranspose_mul_mul_same hF
  have hBinv : (B⁻¹).IsSymm := by
    simpa only [Matrix.IsSymm, conjTranspose_eq_transpose_of_trivial] using hB.inv.isHermitian.eq
  have hKinv : (K⁻¹).IsSymm := by
    simpa only [Matrix.IsSymm, conjTranspose_eq_transpose_of_trivial] using hKpos.inv.isHermitian.eq
  have hBq : B *ᵥ q = g := by
    dsimp only [q]
    rw [mulVec_mulVec, mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.1 hB.isUnit), one_mulVec]
  have hwt : w = u + K⁻¹ *ᵥ (F *ᵥ q) := rfl
  have hw : Fᵀ *ᵥ w = f x₀ := by
    have hq' : Fᵀ *ᵥ (K⁻¹ *ᵥ (F *ᵥ q)) = g := by
      simpa only [mulVec_mulVec, B, Matrix.mul_assoc] using hBq
    have hsum : Fᵀ *ᵥ u + g = f x₀ := add_sub_cancel _ _
    rw [hwt, mulVec_add, hq', hsum]
  have hKw : K *ᵥ w = k + F *ᵥ q := by
    dsimp only [w]
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hK', one_mulVec, one_mulVec]
  have hBLUP : IsBLUP P ε f x x₀ w := by
    refine (isBLUP_iff f x x₀ hε hc w).2 ⟨-q, ?_, hw⟩
    rw [hKw, mulVec_neg, add_neg_cancel_right]
  have hadj (a : Fin p → ℝ) (z : ι → ℝ) :
      (K⁻¹ *ᵥ (F *ᵥ a)) ⬝ᵥ z = a ⬝ᵥ (Fᵀ *ᵥ (K⁻¹ *ᵥ z)) := by
    rw [dotProduct_comm _ z, ← dotProduct_transpose_mulVec K⁻¹, hKinv.eq,
      dotProduct_comm (F *ᵥ a), ← dotProduct_transpose_mulVec F]
  refine ⟨hBLUP, fun z ↦ dotProduct_universalKriging K F k z (f x₀) hKinv hBinv, ?_⟩
  intro β
  have hwk : w ⬝ᵥ crossCov P ε x x₀ = k ⬝ᵥ (K⁻¹ *ᵥ k) + q ⬝ᵥ (Fᵀ *ᵥ u) := by
    rw [hwt, add_dotProduct, hadj, dotProduct_comm u k]
  rw [ukMSE_eq_of_krigingSystem f x x₀ hε hc hw hKw β, hwk]
  simp only [g, sub_dotProduct]
  rw [dotProduct_comm (f x₀) q, dotProduct_comm (Fᵀ *ᵥ u) q]
  ring

/-- The GLS matrix is a left inverse of the design matrix, and multiplication by the
observation covariance cancels the inverse covariance in its definition. -/
private lemma glsMatrix_mul_design_cov [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.PosDef)
    {F : Matrix ι (Fin p) ℝ} (hF : Function.Injective F.mulVec) :
    glsMatrix K F * F = 1 ∧ glsMatrix K F * K = (Fᵀ * K⁻¹ * F)⁻¹ * Fᵀ := by
  let G := Fᵀ * K⁻¹ * F
  have hG : G.PosDef := by
    simpa only [G, conjTranspose_eq_transpose_of_trivial] using
      hK.inv.conjTranspose_mul_mul_same hF
  have hgls : glsMatrix K F = G⁻¹ * Fᵀ * K⁻¹ := glsMatrix_def K F
  refine ⟨?_, ?_⟩
  · have h : glsMatrix K F * F = G⁻¹ * G := by
      simp only [hgls, G, Matrix.mul_assoc]
    rw [h, nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.1 hG.isUnit)]
  · rw [hgls, Matrix.mul_assoc, nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.1 hK.isUnit),
      Matrix.mul_one]

/-- The covariance of two linear combinations of the residual observations. -/
private lemma covariance_weighted_residuals (hε : IsSecondOrderField ε P) (a b : ι → ℝ) :
    cov[fun ω ↦ ∑ i, a i * ε (x i) ω, fun ω ↦ ∑ i, b i * ε (x i) ω; P] =
      a ⬝ᵥ (obsCov P ε x *ᵥ b) := by
  have hLp (v : ι → ℝ) (i : ι) : MemLp (fun ω ↦ v i * ε (x i) ω) 2 P :=
    (isSecondOrderField_iff.mp hε (x i)).const_mul _
  rw [covariance_fun_sum_fun_sum (hLp a) (hLp b)]
  simp only [dotProduct, mulVec, obsCov_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, mul_comm (b j)]

/-- The variance of a scalar linear contrast of shifted residual observations. -/
private lemma variance_dotProduct_mulVec_add_residuals (hε : IsSecondOrderField ε P)
    (A : Matrix (Fin p) ι ℝ) (z : ι → ℝ) (a : Fin p → ℝ) :
    Var[fun ω ↦ a ⬝ᵥ (A *ᵥ (z + fun i ↦ ε (x i) ω)); P] =
      (Aᵀ *ᵥ a) ⬝ᵥ (obsCov P ε x *ᵥ (Aᵀ *ᵥ a)) := by
  have hscalar : (fun ω ↦ a ⬝ᵥ (A *ᵥ (z + fun i ↦ ε (x i) ω))) = fun ω ↦
      z ⬝ᵥ (Aᵀ *ᵥ a) + ∑ i, (Aᵀ *ᵥ a) i * ε (x i) ω := by
    funext ω
    rw [mulVec_add, dotProduct_add, ← dotProduct_transpose_mulVec A,
      ← dotProduct_transpose_mulVec A]
    simp only [dotProduct, mul_comm]
  have hlp : MemLp (fun ω ↦ ∑ i, (Aᵀ *ᵥ a) i * ε (x i) ω) 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦ (isSecondOrderField_iff.mp hε (x i)).const_mul _
  rw [hscalar, variance_const_add hlp.aestronglyMeasurable, variance_weighted_observations x hε]

/-- The scalar variances of unbiased estimators are minimised by the GLS weights. -/
private lemma gls_quadratic_min [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.PosDef)
    {F : Matrix ι (Fin p) ℝ} (hF : Function.Injective F.mulVec)
    (D : Matrix (Fin p) ι ℝ) (hD : D * F = 1) (a : Fin p → ℝ) :
    let L := glsMatrix K F
    let w := Lᵀ *ᵥ a
    let v := Dᵀ *ᵥ a
    w ⬝ᵥ (K *ᵥ w) ≤ v ⬝ᵥ (K *ᵥ v) := by
  intro L w v
  let d := v - w
  obtain ⟨hLF, hLK⟩ := glsMatrix_mul_design_cov hK hF
  have hKt : Kᵀ = K := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hKw : K *ᵥ w = F *ᵥ (((Fᵀ * K⁻¹ * F)⁻¹)ᵀ *ᵥ a) := by
    have ht : K * Lᵀ = F * ((Fᵀ * K⁻¹ * F)⁻¹)ᵀ := by
      simpa only [transpose_mul, transpose_transpose, hKt] using congrArg Matrix.transpose hLK
    simp only [w, mulVec_mulVec, ht]
  have ho : Fᵀ *ᵥ d = 0 := by
    have hl : Fᵀ * Lᵀ = 1 := by
      simpa only [transpose_mul, transpose_one] using congrArg Matrix.transpose hLF
    have hd : Fᵀ * Dᵀ = 1 := by
      simpa only [transpose_mul, transpose_one] using congrArg Matrix.transpose hD
    simp only [d, w, v, mulVec_sub, mulVec_mulVec, hl, hd, sub_self]
  have hdk : d ⬝ᵥ (K *ᵥ w) = 0 := by
    rw [hKw, ← dotProduct_transpose_mulVec F, ho, dotProduct_zero]
  have hwk : w ⬝ᵥ (K *ᵥ d) = 0 := by
    rw [← dotProduct_transpose_mulVec K, hKt, hdk]
  have hv : v = w + d := (add_sub_cancel w v).symm
  have hq : 0 ≤ d ⬝ᵥ (K *ᵥ d) := by
    simpa only [star_trivial] using hK.posSemidef.dotProduct_mulVec_nonneg d
  rw [hv, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hdk, hwk,
    add_zero, zero_add]
  exact le_add_of_nonneg_right hq

/-- SYNOPSIS item 27 (d): the generalised least-squares estimator `β̂ = B 𝐙` is unbiased, has
covariance `(𝐅ᵀ 𝐊⁻¹ 𝐅)⁻¹`, and is the best linear unbiased estimator of `β`: every linear
unbiased estimator `C 𝐙` (`C 𝐅 = 1`) has `Var(a ⬝ C 𝐙) ≥ Var(a ⬝ β̂)` for every `a`. -/
theorem gls_isBLUE [DecidableEq ι] (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0)
    (hK : IsUnit (obsCov P ε x).det) (hF : Function.Injective (designMatrix f x).mulVec) :
    let K := obsCov P ε x
    let F := designMatrix f x
    let Zβ : (Fin p → ℝ) → Ω → ι → ℝ := fun β ω i ↦ f (x i) ⬝ᵥ β + ε (x i) ω
    (∀ β j, ∫ ω, (glsMatrix K F *ᵥ Zβ β ω) j ∂P = β j) ∧
      (∀ β j l, cov[fun ω ↦ (glsMatrix K F *ᵥ Zβ β ω) j,
        fun ω ↦ (glsMatrix K F *ᵥ Zβ β ω) l; P] = (Fᵀ * K⁻¹ * F)⁻¹ j l) ∧
      ∀ C : Matrix (Fin p) ι ℝ, C * F = 1 → ∀ (a β : Fin p → ℝ),
        Var[fun ω ↦ a ⬝ᵥ (glsMatrix K F *ᵥ Zβ β ω); P] ≤
          Var[fun ω ↦ a ⬝ᵥ (C *ᵥ Zβ β ω); P] := by
  intro K F Zβ
  let L := glsMatrix K F
  have hKpos : K.PosDef := (obsCov_posSemidef x hε).posDef_iff_isUnit.2
    (Matrix.isUnit_iff_isUnit_det _ |>.2 hK)
  obtain ⟨hLF, hLK⟩ := glsMatrix_mul_design_cov hKpos hF
  have hLF' : L * F = 1 := hLF
  have hLK' : L * K = (Fᵀ * K⁻¹ * F)⁻¹ * Fᵀ := hLK
  have hmean (β : Fin p → ℝ) (ω : Ω) : Zβ β ω = F *ᵥ β + fun i ↦ ε (x i) ω := rfl
  have hrow (D : Matrix (Fin p) ι ℝ) (β : Fin p → ℝ) (j : Fin p) (ω : Ω) :
      (D *ᵥ Zβ β ω) j = ((D * F) *ᵥ β) j + ∑ i, D j i * ε (x i) ω := by
    rw [hmean, mulVec_add, mulVec_mulVec, Pi.add_apply]
    rfl
  have hLp (w : ι → ℝ) : MemLp (fun ω ↦ ∑ i, w i * ε (x i) ω) 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦ (isSecondOrderField_iff.mp hε (x i)).const_mul _
  have hrowL (β : Fin p → ℝ) (j : Fin p) :
      (fun ω ↦ (glsMatrix K F *ᵥ Zβ β ω) j) = fun ω ↦ β j + ∑ i, L j i * ε (x i) ω := by
    funext ω
    calc
      _ = ((L * F) *ᵥ β) j + ∑ i, L j i * ε (x i) ω := hrow L β j ω
      _ = _ := by rw [hLF', one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro β j
    rw [hrowL β j]
    rw [integral_add (integrable_const _) ((hLp _).integrable one_le_two),
      integral_finsetSum _ (fun i _ ↦
        ((isSecondOrderField_iff.mp hε _).const_mul (L j i)).integrable one_le_two)]
    simp only [integral_const_mul, hc, mul_zero, Finset.sum_const_zero, integral_const,
      probReal_univ, one_smul, add_zero]
  · intro β j l
    rw [hrowL β j, hrowL β l]
    rw [covariance_const_add_left ((hLp _).integrable one_le_two),
      covariance_const_add_right ((hLp _).integrable one_le_two),
      covariance_weighted_residuals x hε]
    have h := calc
      L * K * Lᵀ = (Fᵀ * K⁻¹ * F)⁻¹ * (L * F)ᵀ := by
        rw [hLK', transpose_mul, Matrix.mul_assoc]
      _ = (Fᵀ * K⁻¹ * F)⁻¹ := by rw [hLF', transpose_one, Matrix.mul_one]
    rw [← h]
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_mul]
    simp only [K, mul_assoc]
  · intro D hD a β
    have hvar (A : Matrix (Fin p) ι ℝ) :
        Var[fun ω ↦ a ⬝ᵥ (A *ᵥ Zβ β ω); P] =
          (Aᵀ *ᵥ a) ⬝ᵥ (K *ᵥ (Aᵀ *ᵥ a)) :=
      variance_dotProduct_mulVec_add_residuals x hε A (F *ᵥ β) a
    rw [hvar L, hvar D]
    exact gls_quadratic_min hKpos hF D hD a

/-- SYNOPSIS item 27 (d): `β̂` is the maximum-likelihood estimator of `β` for Gaussian
observations with known covariance `𝐊`: it minimises `(𝐳 - 𝐅β)ᵀ 𝐊⁻¹ (𝐳 - 𝐅β)` for every data
vector `𝐳`. -/
theorem gls_isMinOn_gaussianLikelihood [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.PosDef)
    {F : Matrix ι (Fin p) ℝ} (hF : Function.Injective F.mulVec) (z : ι → ℝ)
    (β : Fin p → ℝ) :
    (z - F *ᵥ (glsMatrix K F *ᵥ z)) ⬝ᵥ (K⁻¹ *ᵥ (z - F *ᵥ (glsMatrix K F *ᵥ z))) ≤
      (z - F *ᵥ β) ⬝ᵥ (K⁻¹ *ᵥ (z - F *ᵥ β)) := by
  let B := Fᵀ * K⁻¹ * F
  let b := glsMatrix K F *ᵥ z
  let r := z - F *ᵥ b
  let d := F *ᵥ (b - β)
  have hB : B.PosDef := by
    simpa only [B, conjTranspose_eq_transpose_of_trivial] using
      hK.inv.conjTranspose_mul_mul_same hF
  have hgls : glsMatrix K F = B⁻¹ * Fᵀ * K⁻¹ := glsMatrix_def K F
  have hb : B *ᵥ b = Fᵀ *ᵥ (K⁻¹ *ᵥ z) := by
    have hLeft : B * glsMatrix K F = Fᵀ * K⁻¹ := by
      rw [hgls, ← Matrix.mul_assoc B (B⁻¹ * Fᵀ), ← Matrix.mul_assoc B B⁻¹,
        mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.1 hB.isUnit), Matrix.one_mul]
    dsimp only [b]
    rw [mulVec_mulVec, hLeft, ← mulVec_mulVec]
  have hOrth : Fᵀ *ᵥ (K⁻¹ *ᵥ r) = 0 := by
    have hBr : Fᵀ *ᵥ (K⁻¹ *ᵥ (F *ᵥ b)) = B *ᵥ b := by
      simp only [B, mulVec_mulVec, Matrix.mul_assoc]
    dsimp only [r]
    rw [mulVec_sub, mulVec_sub, hBr, hb, sub_self]
  have hcross : d ⬝ᵥ (K⁻¹ *ᵥ r) = 0 := by
    dsimp only [d]
    rw [dotProduct_comm (F *ᵥ (b - β)), ← dotProduct_transpose_mulVec F,
      hOrth, dotProduct_zero]
  have hKt : (K⁻¹)ᵀ = K⁻¹ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hK.inv.isHermitian.eq
  have hcross' : r ⬝ᵥ (K⁻¹ *ᵥ d) = 0 := by
    rw [← dotProduct_transpose_mulVec _ d r, hKt, hcross]
  have hSum : z - F *ᵥ β = r + d := by
    dsimp only [r, d]
    rw [mulVec_sub, sub_add_sub_cancel]
  have hnonneg : 0 ≤ d ⬝ᵥ (K⁻¹ *ᵥ d) := by
    simpa only [star_trivial] using hK.inv.posSemidef.dotProduct_mulVec_nonneg d
  rw [hSum, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcross, hcross',
    zero_add, add_zero]
  exact le_add_of_nonneg_right hnonneg

/-- SYNOPSIS item 27 (e): the error of the best linear unbiased predictor is a contrast, with
mean zero for every `β`, and it is uncorrelated with every contrast `c ⬝ 𝐙` of the observations
(`𝐅ᵀ c = 0`). -/
theorem IsBLUP.error_contrast (hε : IsSecondOrderField ε P) (hc : ∀ t, P[ε t] = 0)
    {w : ι → ℝ} (h : IsBLUP P ε f x x₀ w) (β : Fin p → ℝ) :
    (∫ ω, (f x₀ ⬝ᵥ β + ε x₀ ω - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) ∂P) = 0 ∧
      ∀ c : ι → ℝ, (designMatrix f x)ᵀ *ᵥ c = 0 →
        cov[fun ω ↦ f x₀ ⬝ᵥ β + ε x₀ ω - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω),
          fun ω ↦ ∑ i, c i * (f (x i) ⬝ᵥ β + ε (x i) ω); P] = 0 := by
  refine ⟨by simpa only [sub_zero] using (isBLUP_def.mp h).1 β, ?_⟩
  obtain ⟨μ, hμ, hw⟩ := (isBLUP_iff f x x₀ hε hc w).1 h
  intro c hc'
  let W : Ω → ℝ := fun ω ↦ ∑ i, w i * ε (x i) ω
  let C : Ω → ℝ := fun ω ↦ ∑ i, c i * ε (x i) ω
  have hErr : (fun ω ↦ f x₀ ⬝ᵥ β + ε x₀ ω - ∑ i, w i * (f (x i) ⬝ᵥ β + ε (x i) ω)) =
      fun ω ↦ ε x₀ ω - W ω := by
    funext ω
    simp only [W, mul_add, Finset.sum_add_distrib, sum_mul_design_eq f x x₀ hw β,
      add_sub_add_left_eq_sub]
  have hContrast : (fun ω ↦ ∑ i, c i * (f (x i) ⬝ᵥ β + ε (x i) ω)) = C := by
    have hmean : ∑ i, c i * (f (x i) ⬝ᵥ β) = 0 := by
      have hd := dotProduct_transpose_mulVec (designMatrix f x) β c
      rw [hc', dotProduct_zero] at hd
      simpa only [dotProduct, mulVec, designMatrix_apply] using hd.symm
    funext ω
    simp only [C, mul_add, Finset.sum_add_distrib, hmean, zero_add]
  have hLp (z : ι → ℝ) (i : ι) : MemLp (fun ω ↦ z i * ε (x i) ω) 2 P :=
    (isSecondOrderField_iff.mp hε (x i)).const_mul _
  have h₀ := isSecondOrderField_iff.mp hε x₀
  have hW : MemLp W 2 P := memLp_finsetSum Finset.univ (fun i _ ↦ hLp w i)
  have hC : MemLp C 2 P := memLp_finsetSum Finset.univ (fun i _ ↦ hLp c i)
  have hCross : cov[ε x₀, C; P] = c ⬝ᵥ crossCov P ε x x₀ := by
    dsimp only [C]
    rw [covariance_comm, covariance_fun_sum_left (hLp c) h₀]
    simp only [covariance_const_mul_left, dotProduct, crossCov_apply]
  have hObs : cov[W, C; P] = c ⬝ᵥ (obsCov P ε x *ᵥ w) := by
    dsimp only [W, C]
    rw [covariance_comm, covariance_fun_sum_fun_sum (hLp c) (hLp w)]
    simp only [dotProduct, mulVec, obsCov_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, mul_comm (w j)]
  rw [hErr, hContrast, covariance_fun_sub_left h₀ hW hC, hCross, hObs, ← dotProduct_sub]
  have hr : crossCov P ε x x₀ - obsCov P ε x *ᵥ w = designMatrix f x *ᵥ μ :=
    (eq_sub_of_add_eq' hμ).symm
  rw [hr, ← dotProduct_transpose_mulVec, hc', dotProduct_zero]

/-- SYNOPSIS item 27 (e): the best linear unbiased predictor and its mean squared error depend
on the covariance only through the variances of contrasts `c₀ Z(x₀) + ∑ c_i Z(x_i)`
(`c₀ f₀ + 𝐅ᵀ c = 0`): two residual fields with the same contrast variances have the same best
linear unbiased predictors, with the same mean squared errors. -/
theorem isBLUP_iff_of_contrastVariance_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {ε' : T → Ω' → ℝ} (hε : IsSecondOrderField ε P)
    (hc : ∀ t, P[ε t] = 0) (hε' : IsSecondOrderField ε' P') (hc' : ∀ t, P'[ε' t] = 0)
    (hvar : ∀ (c₀ : ℝ) (c : ι → ℝ), c₀ • f x₀ + (designMatrix f x)ᵀ *ᵥ c = 0 →
      Var[fun ω ↦ c₀ * ε x₀ ω + ∑ i, c i * ε (x i) ω; P] =
        Var[fun ω ↦ c₀ * ε' x₀ ω + ∑ i, c i * ε' (x i) ω; P'])
    (w : ι → ℝ) :
    (IsBLUP P ε f x x₀ w ↔ IsBLUP P' ε' f x x₀ w) ∧
      (IsBLUP P ε f x x₀ w → ∀ β, ukMSE P ε f x x₀ β 0 w = ukMSE P' ε' f x x₀ β 0 w) := by
  have hV (v : ι → ℝ) (hv : (designMatrix f x)ᵀ *ᵥ v = f x₀) :
      Var[fun ω ↦ (1 : ℝ) * ε x₀ ω + ∑ i, (-v i) * ε (x i) ω; P] =
        Var[fun ω ↦ (1 : ℝ) * ε' x₀ ω + ∑ i, (-v i) * ε' (x i) ω; P'] := by
    apply hvar 1 (-v)
    rw [mulVec_neg, hv, one_smul, add_neg_cancel]
  have hEq : IsBLUP P ε f x x₀ w ↔ IsBLUP P' ε' f x x₀ w := by
    rw [isBLUP_iff_min_residual_variance f x x₀ hε hc,
      isBLUP_iff_min_residual_variance f x x₀ hε' hc']
    apply and_congr_right
    intro hw
    constructor <;> intro h v hv
    · rw [← hV w hw, ← hV v hv]
      exact h v hv
    · rw [hV w hw, hV v hv]
      exact h v hv
  refine ⟨hEq, fun h β ↦ ?_⟩
  have hw := ((isBLUP_iff_min_residual_variance f x x₀ hε hc w).1 h).1
  rw [ukMSE_eq_variance_of_mulVec_eq f x x₀ hε hc hw,
    ukMSE_eq_variance_of_mulVec_eq f x x₀ hε' hc' hw, hV w hw]

end UniversalKriging

end MSSS
