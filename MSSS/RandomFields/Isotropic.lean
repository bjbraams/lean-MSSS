module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.CompletelyMonotone.Basic

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Bochner.Gaussian.Basic
import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Power
import TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel

/-!
# Isotropic covariances on Euclidean spaces

SYNOPSIS items 8, 10, and 11: Schoenberg's characterisation of isotropic correlation functions
in `ℝ^d`, the class `Φ_∞` of functions valid in every dimension, and Pólya-type criteria.

A function `φ : ℝ → ℝ` is used only through its values on `[0, ∞)`. Positive definiteness of
`x ↦ φ ‖x‖` is TauCeti's `IsPositiveDefiniteSub`, with complex coefficients as in the synopsis.

## Main definitions

* `MSSS.sphereCharFun d t`: `Ω_d(t) = Γ(d/2) (2/t)^{(d-2)/2} J_{(d-2)/2}(t)`, `Ω_d(0) = 1`.
* `MSSS.isotropicClass d`: the class `Φ_d`.
* `MSSS.isotropicClassInf`: the class `Φ_∞ = ⋂_{d ≥ 1} Φ_d`.
* `MSSS.IsStrictlyPositiveDefiniteSub`: strict positive definiteness of a function on a group.

The Gaussian scale-mixture argument uses TauCeti's Hausdorff–Bernstein–Widder theorem,
Gaussian kernel positivity, and the composition rules for Bernstein functions.
The triangular covariance results use Mathlib's length of closed intervals and TauCeti's
finite quadratic-form criterion for positive definiteness.

## Main results

* `MSSS.mem_isotropicClass_iff`, `MSSS.eq_of_integral_sphereCharFun_eq`,
  `MSSS.integral_sphereCharFun_map_norm`, `MSSS.eq_withDensity_of_mem_isotropicClass`,
  `MSSS.isotropicClass_succ_ssubset`, `MSSS.isotropicClassInf_ssubset`,
  `MSSS.isStrictlyPositiveDefiniteSub_of_mem_isotropicClass`: SYNOPSIS item 8.
* `MSSS.mem_isotropicClassInf_iff_gaussianMixture`,
  `MSSS.mem_isotropicClassInf_iff_completelyMonotone`, `MSSS.properties_of_mem_isotropicClassInf`,
  `MSSS.tendstoUniformlyOn_sphereCharFun`, `MSSS.mem_isotropicClassInf_of_completelyMonotone`,
  `MSSS.exp_neg_rpow_mem_isotropicClassInf`, `MSSS.cauchyType_mem_isotropicClassInf`:
  SYNOPSIS item 10.
* `MSSS.mem_isotropicClass_one_of_convexOn`, `MSSS.truncatedPower_mem_isotropicClass_iff`,
  `MSSS.triangular_mem_isotropicClass_one`, `MSSS.triangular_not_mem_isotropicClass_two`:
  SYNOPSIS item 11.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ComplexOrder ComplexConjugate NNReal

namespace MSSS

/-- The function `Ω_d(t) = Γ(d/2) (2/t)^{(d-2)/2} J_{(d-2)/2}(t)` for `t ≠ 0`, with
`Ω_d(0) = 1`; `Ω_d(‖·‖)` is the characteristic function of the uniform law on the unit sphere
of `ℝ^d`. It is used for `t ≥ 0`. -/
def sphereCharFun (d : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then 1 else
    Real.Gamma (d / 2) * (2 / t) ^ (((d : ℝ) - 2) / 2) *
      (Complex.besselJ ((((d : ℝ) - 2) / 2 : ℝ) : ℂ) t).re

lemma sphereCharFun_def (d : ℕ) (t : ℝ) : sphereCharFun d t = if t = 0 then 1 else
    Real.Gamma (d / 2) * (2 / t) ^ (((d : ℝ) - 2) / 2) *
      (Complex.besselJ ((((d : ℝ) - 2) / 2 : ℝ) : ℂ) t).re := by
  rw [sphereCharFun]

/-- The class `Φ_d` of continuous `φ : [0, ∞) → ℝ` with `φ 0 = 1` such that `x ↦ φ ‖x‖` is
positive definite on `ℝ^d`. -/
def isotropicClass (d : ℕ) : Set (ℝ → ℝ) :=
  {φ | ContinuousOn φ (Ici 0) ∧ φ 0 = 1 ∧
    TauCeti.IsPositiveDefiniteSub fun x : EuclideanSpace ℝ (Fin d) ↦ (φ ‖x‖ : ℂ)}

/-- The class `Φ_∞ = ⋂_{d ≥ 1} Φ_d` of isotropic correlation functions valid in every
dimension. -/
def isotropicClassInf : Set (ℝ → ℝ) := ⋂ d : ℕ, isotropicClass (d + 1)

lemma mem_isotropicClass {d : ℕ} {φ : ℝ → ℝ} : φ ∈ isotropicClass d ↔
    ContinuousOn φ (Ici 0) ∧ φ 0 = 1 ∧
      TauCeti.IsPositiveDefiniteSub fun x : EuclideanSpace ℝ (Fin d) ↦ (φ ‖x‖ : ℂ) := by
  rw [isotropicClass, mem_ofPred_eq]

lemma mem_isotropicClassInf {φ : ℝ → ℝ} :
    φ ∈ isotropicClassInf ↔ ∀ d : ℕ, φ ∈ isotropicClass (d + 1) := by
  rw [isotropicClassInf, mem_iInter]

/-- A function `F` on an additive group is **strictly positive definite** when the Hermitian
form `∑ c_i conj(c_j) F(v_i - v_j)` is positive for pairwise distinct points `v` and
coefficients `c` that do not all vanish. -/
def IsStrictlyPositiveDefiniteSub {G : Type*} [AddCommGroup G] (F : G → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → G), Function.Injective v → c ≠ 0 →
    0 < ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * F (v i - v j)

lemma isStrictlyPositiveDefiniteSub_iff {G : Type*} [AddCommGroup G] {F : G → ℂ} :
    IsStrictlyPositiveDefiniteSub F ↔ ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → G),
      Function.Injective v → c ≠ 0 →
        0 < ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * F (v i - v j) := Iff.rfl

/-! ### Schoenberg's theorem in `ℝ^d` (SYNOPSIS item 8) -/

/-- SYNOPSIS item 8, representation: for `d ≥ 1`, `φ ∈ Φ_d` if and only if
`φ(t) = ∫ Ω_d(r t) F₀(dr)` for `t ≥ 0` and a probability measure `F₀` on `[0, ∞)`. -/
theorem mem_isotropicClass_iff {d : ℕ} (hd : 1 ≤ d) {φ : ℝ → ℝ} :
    φ ∈ isotropicClass d ↔ ∃ F₀ : Measure ℝ, IsProbabilityMeasure F₀ ∧ F₀ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → φ t = ∫ r, sphereCharFun d (r * t) ∂F₀ := by
  sorry

/-- SYNOPSIS item 8, uniqueness: the measure `F₀` in the representation is unique. -/
theorem eq_of_integral_sphereCharFun_eq {d : ℕ} (hd : 1 ≤ d) {F₀ F₁ : Measure ℝ}
    [IsProbabilityMeasure F₀] [IsProbabilityMeasure F₁] (h₀ : F₀ (Iio 0) = 0)
    (h₁ : F₁ (Iio 0) = 0)
    (h : ∀ t, 0 ≤ t → ∫ r, sphereCharFun d (r * t) ∂F₀ = ∫ r, sphereCharFun d (r * t) ∂F₁) :
    F₀ = F₁ := by
  sorry

/-- SYNOPSIS item 8, identification: if `F` is the spectral measure of `x ↦ φ ‖x‖`, then the
image of `F` under `ω ↦ ‖ω‖` represents `φ`; by uniqueness it is the measure `F₀`. -/
theorem integral_sphereCharFun_map_norm {d : ℕ} (hd : 1 ≤ d) {φ : ℝ → ℝ}
    (F : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure F]
    (hF : ∀ x, charFun F x = (φ ‖x‖ : ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    φ t = ∫ r, sphereCharFun d (r * t) ∂(F.map fun ξ ↦ ‖ξ‖) := by
  sorry

/-- SYNOPSIS item 8, spectral density: if `φ ∈ Φ_d` and `∫₀^∞ r^{d-1} |φ(r)| dr < ∞`, the
spectral measure of `x ↦ φ ‖x‖` has the radial density
`f(u) = (2π)^{-d/2} ∫₀^∞ (u r)^{-(d-2)/2} J_{(d-2)/2}(u r) r^{d-1} φ(r) dr`. -/
theorem eq_withDensity_of_mem_isotropicClass {d : ℕ} (hd : 1 ≤ d) {φ : ℝ → ℝ}
    (hφ : φ ∈ isotropicClass d)
    (hint : IntegrableOn (fun r ↦ r ^ (d - 1) * φ r) (Ioi 0))
    (F : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure F]
    (hF : ∀ x, charFun F x = (φ ‖x‖ : ℂ)) :
    F = volume.withDensity fun ξ ↦ ENNReal.ofReal
      ((2 * Real.pi) ^ (-(d : ℝ) / 2) * ∫ r in Ioi (0 : ℝ),
        (‖ξ‖ * r) ^ (-((d : ℝ) - 2) / 2) *
          (Complex.besselJ ((((d : ℝ) - 2) / 2 : ℝ) : ℂ) (‖ξ‖ * r)).re *
          r ^ (d - 1) * φ r) := by
  sorry

/-- SYNOPSIS item 8, nesting: `Φ_{d+1} ⊊ Φ_d` for `d ≥ 1`. -/
theorem isotropicClass_succ_ssubset {d : ℕ} (hd : 1 ≤ d) :
    isotropicClass (d + 1) ⊂ isotropicClass d := by
  sorry

/-- SYNOPSIS item 8, nesting: `Φ_∞ ⊊ Φ_d` for `d ≥ 1`. -/
theorem isotropicClassInf_ssubset {d : ℕ} (hd : 1 ≤ d) :
    isotropicClassInf ⊂ isotropicClass d := by
  sorry

/-- SYNOPSIS item 8, strict positive definiteness: for `d ≥ 2`, every member of `Φ_d` that is
not constant on `[0, ∞)` is strictly positive definite on `ℝ^d`. -/
theorem isStrictlyPositiveDefiniteSub_of_mem_isotropicClass {d : ℕ} (hd : 2 ≤ d)
    {φ : ℝ → ℝ} (hφ : φ ∈ isotropicClass d) (hne : ∃ t, 0 ≤ t ∧ φ t ≠ 1) :
    IsStrictlyPositiveDefiniteSub fun x : EuclideanSpace ℝ (Fin d) ↦ (φ ‖x‖ : ℂ) := by
  sorry

/-! ### Covariances valid in every dimension (SYNOPSIS item 10) -/

/-- SYNOPSIS item 10: `φ ∈ Φ_∞` if and only if `φ` is a Gaussian scale mixture,
`φ(t) = ∫ e^{-r²t²} F(dr)` for `t ≥ 0` and a probability measure `F` on `[0, ∞)`. -/
theorem mem_isotropicClassInf_iff_gaussianMixture {φ : ℝ → ℝ} :
    φ ∈ isotropicClassInf ↔ ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → φ t = ∫ r, Real.exp (-(r ^ 2 * t ^ 2)) ∂F := by
  sorry

/-- SYNOPSIS item 10: `φ ∈ Φ_∞` if and only if `φ 0 = 1` and `t ↦ φ (√t)` is completely
monotone (continuous on `[0, ∞)`). -/
theorem mem_isotropicClassInf_iff_completelyMonotone {φ : ℝ → ℝ} :
    φ ∈ isotropicClassInf ↔
      φ 0 = 1 ∧ TauCeti.IsContinuousCompletelyMonotoneOnIoi fun t ↦ φ (Real.sqrt t) := by
  sorry

/-- SYNOPSIS item 10: every member of `Φ_∞` is positive, nonincreasing, strictly decreasing
unless it is constant, and infinitely differentiable on `(0, ∞)`. -/
theorem properties_of_mem_isotropicClassInf {φ : ℝ → ℝ} (hφ : φ ∈ isotropicClassInf) :
    (∀ t, 0 ≤ t → 0 < φ t) ∧ AntitoneOn φ (Ici 0) ∧
      ((∃ t, 0 ≤ t ∧ φ t ≠ 1) → StrictAntiOn φ (Ici 0)) ∧ ContDiffOn ℝ ∞ φ (Ioi 0) := by
  sorry

/-- SYNOPSIS item 10, the key analytic fact: `Ω_d((2d)^{1/2} t) → e^{-t²}` uniformly in
`t ≥ 0` as `d → ∞`. -/
theorem tendstoUniformlyOn_sphereCharFun :
    TendstoUniformlyOn (fun (d : ℕ) (t : ℝ) ↦ sphereCharFun d (Real.sqrt (2 * d) * t))
      (fun t ↦ Real.exp (-t ^ 2)) atTop (Ici 0) := by
  sorry

/-- A completely monotone function of the squared norm is positive definite on a real
inner-product space. -/
theorem isPositiveDefiniteSub_sq_norm_of_completelyMonotone {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : ℝ → ℝ}
    (hf : TauCeti.IsContinuousCompletelyMonotoneOnIoi f) :
    TauCeti.IsPositiveDefiniteSub fun x : E ↦ (f (‖x‖ ^ 2) : ℂ) := by
  -- TauCeti's Bernstein representation writes the kernel as a mixture of Gaussians.
  obtain ⟨μ, hμ⟩ := TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi hf
  let := hμ.isFiniteMeasure
  have hpd (r : ℝ≥0) : TauCeti.IsPositiveDefiniteSub fun x : E ↦
      (Real.exp (-(‖x‖ ^ 2 * (r : ℝ))) : ℂ) := by
    apply TauCeti.isPositiveDefiniteSub_iff_posSemidef.mpr
    simpa only [← Complex.ofReal_neg, ← Complex.ofReal_exp, mul_comm] using
      (TauCeti.posSemidef_cexp_neg_mul_sq_norm (V := E) r.coe_nonneg)
  refine TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg.mpr fun n c v ↦ ?_
  let term (i j : Fin n) (r : ℝ≥0) :=
    c i * conj (c j) * (Real.exp (-(‖v i - v j‖ ^ 2 * (r : ℝ))) : ℂ)
  have hint (i j : Fin n) : Integrable (term i j) μ := by
    apply Integrable.const_mul
    exact (TauCeti.integrable_exp_neg_mul μ (sq_nonneg _)).ofReal
  have hsum : Integrable (fun r ↦ ∑ i, ∑ j, term i j r) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j
  have heq (i j : Fin n) :
      c i * conj (c j) * (f (‖v i - v j‖ ^ 2) : ℂ) = ∫ r, term i j r ∂μ := by
    rw [hμ.eq_laplaceTransform (sq_nonneg _), TauCeti.laplaceTransform_apply,
      ← integral_complex_ofReal, integral_const_mul]
  simp_rw [heq]
  have hrow (i : Fin n) : (∑ j, ∫ r, term i j r ∂μ) =
      ∫ r, ∑ j, term i j r ∂μ :=
    (integral_finsetSum _ fun j _ ↦ hint i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  have hre : (∫ r, (∑ i, ∑ j, term i j r).re ∂μ) =
      (∫ r, ∑ i, ∑ j, term i j r ∂μ).re := integral_re hsum
  have him : (∫ r, (∑ i, ∑ j, term i j r).im ∂μ) =
      (∫ r, ∑ i, ∑ j, term i j r ∂μ).im := integral_im hsum
  rw [Complex.nonneg_iff, ← hre, ← him]
  exact ⟨integral_nonneg fun r ↦ (Complex.nonneg_iff.mp ((hpd r).sum_nonneg c v)).1, by
    have hz (r : ℝ≥0) : (∑ i, ∑ j, term i j r).im = 0 :=
      (Complex.nonneg_iff.mp ((hpd r).sum_nonneg c v)).2.symm
    simp only [hz, integral_zero]⟩

/-- SYNOPSIS item 10: every completely monotone `φ` with `φ 0 = 1` belongs to `Φ_∞`. -/
theorem mem_isotropicClassInf_of_completelyMonotone {φ : ℝ → ℝ}
    (hφ : TauCeti.IsContinuousCompletelyMonotoneOnIoi φ) (h0 : φ 0 = 1) :
    φ ∈ isotropicClassInf := by
  refine mem_isotropicClassInf.mpr fun d ↦ mem_isotropicClass.mpr ⟨hφ.continuousOn, h0, ?_⟩
  have h := hφ.comp_isBernsteinFunction
    (TauCeti.isBernsteinFunction_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  simpa only [Function.comp_apply, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)] using
    (isPositiveDefiniteSub_sq_norm_of_completelyMonotone
      (E := EuclideanSpace ℝ (Fin (d + 1))) h)

/-- SYNOPSIS item 10, example: `e^{-c t^α}` with `c ≥ 0` and `0 < α ≤ 1` belongs to `Φ_∞`. -/
theorem exp_neg_rpow_mem_isotropicClassInf {c α : ℝ} (hc : 0 ≤ c) (hα₀ : 0 < α)
    (hα₁ : α ≤ 1) : (fun t ↦ Real.exp (-c * t ^ α)) ∈ isotropicClassInf := by
  apply mem_isotropicClassInf_of_completelyMonotone
    (TauCeti.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul_rpow hc hα₀.le hα₁)
  simp [Real.zero_rpow hα₀.ne']

/-- SYNOPSIS item 10, example: the Cauchy-type function `(1 + t^α)^{-β/α}` with `0 < α ≤ 1` and
`β > 0` belongs to `Φ_∞`. -/
theorem cauchyType_mem_isotropicClassInf {α β : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) :
    (fun t ↦ (1 + t ^ α) ^ (-β / α)) ∈ isotropicClassInf := by
  have hb : TauCeti.IsBernsteinFunction (fun t : ℝ ↦ 1 + t ^ α) :=
    (TauCeti.isBernsteinFunction_rpow hα₀.le hα₁).const_add zero_le_one
  let f : ℝ → ℝ := fun t ↦ (1 + t ^ α) ^ (-β / α)
  have hbase : ∀ t ∈ Ici (0 : ℝ), 0 < 1 + t ^ α := fun t ht ↦
    add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg ht _)
  have hfc : ContinuousOn f (Ici 0) :=
    (continuousOn_const.add (Real.continuous_rpow_const hα₀.le).continuousOn).rpow_const
      fun t ht ↦ Or.inl (hbase t ht).ne'
  have hcm := (TauCeti.isCompletelyMonotoneOnIoi_rpow_neg
    (div_nonneg hβ.le hα₀.le)).comp_isBernsteinFunction hb (fun t ht ↦ hbase t ht.le)
  apply mem_isotropicClassInf_of_completelyMonotone (φ := f)
    (TauCeti.isContinuousCompletelyMonotoneOnIoi_iff.mpr
      ⟨hfc, hcm.congr fun t _ ↦ by simp only [f, Function.comp_apply, neg_div]⟩)
  simp [f, Real.zero_rpow hα₀.ne']

/-! ### Pólya-type criteria and compact support (SYNOPSIS item 11) -/

/-- SYNOPSIS item 11 (a), Pólya's criterion: a continuous convex `φ` on `[0, ∞)` with
`φ 0 = 1` and `φ t → 0` as `t → ∞` belongs to `Φ_1`. -/
theorem mem_isotropicClass_one_of_convexOn {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ici 0))
    (hconv : ConvexOn ℝ (Ici 0) φ) (h0 : φ 0 = 1) (hlim : Tendsto φ atTop (𝓝 0)) :
    φ ∈ isotropicClass 1 := by
  sorry

/-- SYNOPSIS item 11 (b): for `a > 0`, `ν > 0` and `n ≥ 1`, the truncated power function
`(1 - t/a)_+^ν` belongs to `Φ_n` if and only if `ν ≥ (n + 1)/2`. -/
theorem truncatedPower_mem_isotropicClass_iff {a ν : ℝ} (ha : 0 < a) (hν : 0 < ν) {n : ℕ}
    (hn : 1 ≤ n) :
    (fun t ↦ max (1 - t / a) 0 ^ ν) ∈ isotropicClass n ↔ ((n : ℝ) + 1) / 2 ≤ ν := by
  sorry

/-- The overlap of two translated intervals gives the triangular covariance. -/
private lemma integral_triangularIndicator_mul (x y a : ℝ) :
    (∫ u, (Icc x (x + a)).indicator (fun _ ↦ (1 : ℂ)) u *
      (Icc y (y + a)).indicator (fun _ ↦ (1 : ℂ)) u) =
        (↑(max (a - |x - y|) 0) : ℂ) := by
  have h : (fun u ↦ (Icc x (x + a)).indicator (fun _ ↦ (1 : ℂ)) u *
      (Icc y (y + a)).indicator (fun _ ↦ (1 : ℂ)) u) =
      (Icc (max x y) (min x y + a)).indicator (fun _ ↦ (1 : ℂ)) := by
    rw [← min_add_add_right, ← Icc_inter_Icc]
    funext u
    by_cases hx : u ∈ Icc x (x + a) <;> by_cases hy : u ∈ Icc y (y + a) <;>
      simp [hx, hy]
  rw [h, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
    Complex.real_smul, mul_one, ← max_sub_min_eq_abs]
  congr 2
  rw [max_comm x y, min_comm x y]
  ring

/-- The triangular covariance is the Gram kernel of interval indicators on the line. -/
private lemma triangular_real_pd {a : ℝ} (ha : 0 < a) :
    TauCeti.IsPositiveDefiniteSub fun x : ℝ ↦ ((max (1 - |x| / a) 0 : ℝ) : ℂ) := by
  refine TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg.mpr fun n c v ↦ ?_
  let A (i : Fin n) := Icc (v i) (v i + a)
  let e (i : Fin n) : ℝ → ℂ := (A i).indicator (fun _ ↦ 1)
  let f (i j : Fin n) (u : ℝ) := (c i * conj (c j)) * (e i u * e j u)
  have hi (i j : Fin n) : Integrable (f i j) := by
    apply Integrable.const_mul
    have he : (fun u ↦ e i u * e j u) = (A i ∩ A j).indicator (fun _ ↦ (1 : ℂ)) := by
      funext u
      by_cases h1 : u ∈ A i <;> by_cases h2 : u ∈ A j <;> simp [e, h1, h2]
    rw [he, integrable_indicator_iff (measurableSet_Icc.inter measurableSet_Icc)]
    exact integrableOn_const ((isCompact_Icc.inter isCompact_Icc).measure_lt_top.ne)
  have hre (i j : Fin n) : c i * conj (c j) * (↑(max (1 - |v i - v j| / a) 0) : ℂ) =
      (↑a : ℂ)⁻¹ * ∫ u, f i j u := by
    rw [integral_const_mul, integral_triangularIndicator_mul]
    have hdiv : max (1 - |v i - v j| / a) 0 = a⁻¹ * max (a - |v i - v j|) 0 := by
      rw [mul_max_of_nonneg _ _ (inv_nonneg.2 ha.le), mul_zero, mul_sub,
        inv_mul_cancel₀ ha.ne', div_eq_inv_mul]
    rw [hdiv, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  simp_rw [hre, ← Finset.mul_sum]
  have hrow (i : Fin n) : (∑ j, ∫ u, f i j u) =
      ∫ u, ∑ j, f i j u := (integral_finsetSum _ fun j _ ↦ hi i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j]
  have hscale : 0 ≤ (↑a : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.nonneg_iff]
    exact ⟨inv_nonneg.2 ha.le, rfl⟩
  apply mul_nonneg hscale
  have hpoint (u : ℝ) : (∑ i, ∑ j, f i j u) =
      (∑ i, c i * e i u) * conj (∑ j, c j * e j u) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he (k : Fin n) : conj (e k u) = e k u := by
      by_cases h : u ∈ A k <;> simp [e, h]
    rw [map_mul, he]
    dsimp only [f]
    ring
  have hint : Integrable (fun u ↦ ∑ i, ∑ j, f i j u) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j
  have hRe : (∫ u, (∑ i, ∑ j, f i j u).re) = (∫ u, ∑ i, ∑ j, f i j u).re :=
    integral_re hint
  have hIm : (∫ u, (∑ i, ∑ j, f i j u).im) = (∫ u, ∑ i, ∑ j, f i j u).im :=
    integral_im hint
  rw [Complex.nonneg_iff, ← hRe, ← hIm]
  have him (u : ℝ) : (∑ i, ∑ j, f i j u).im = 0 := by
    rw [hpoint, Complex.mul_conj]
    exact Complex.ofReal_im _
  refine ⟨integral_nonneg fun u ↦ ?_, by simp only [him, integral_zero]⟩
  rw [hpoint, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- SYNOPSIS item 11: the triangular function `(1 - t/a)_+` belongs to `Φ_1`. -/
theorem triangular_mem_isotropicClass_one {a : ℝ} (ha : 0 < a) :
    (fun t ↦ max (1 - t / a) 0) ∈ isotropicClass 1 := by
  refine mem_isotropicClass.mpr ⟨(by fun_prop : Continuous _).continuousOn, by simp, ?_⟩
  let ev : EuclideanSpace ℝ (Fin 1) →+ ℝ :=
    { toFun := fun x ↦ x 0
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hnorm (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  have hev (x : EuclideanSpace ℝ (Fin 1)) : ev x = x 0 := rfl
  simpa only [hnorm, hev] using (triangular_real_pd ha).comp_addMonoidHom ev

/-- Squared lattice distance on the grid used to test the triangular covariance. -/
private def triangleGridSq (u v : Fin 5 × Fin 5) : ℕ :=
  Int.natAbs ((u.1.val : ℤ) - v.1.val) ^ 2 + Int.natAbs ((u.2.val : ℤ) - v.2.val) ^ 2

/-- Product weights for the triangular covariance test on the square grid. -/
private def triangleGridWeight (u : Fin 5 × Fin 5) : ℤ :=
  let w : Fin 5 → ℤ := ![1, -2, 2, -2, 1]
  w u.1 * w u.2

/-- Embed the grid with spacing `a / √2` where the covariance range is `a`. -/
private def triangleGridPoint (a : ℝ) (u : Fin 5 × Fin 5) : EuclideanSpace ℝ (Fin 2) :=
  (a / Real.sqrt 2) • WithLp.toLp 2 ![(u.1.val : ℝ), (u.2.val : ℝ)]

/-- Squared Euclidean distance is squared lattice distance times the squared spacing. -/
private lemma triangleGridPoint_dist_sq (a : ℝ) (u v : Fin 5 × Fin 5) :
    ‖triangleGridPoint a u - triangleGridPoint a v‖ ^ 2 =
      (a / Real.sqrt 2) ^ 2 * (triangleGridSq u v : ℝ) := by
  simp only [triangleGridPoint, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    EuclideanSpace.norm_sq_eq, triangleGridSq, Nat.cast_add, Nat.cast_pow]
  congr 1
  rw [Fin.sum_univ_two]
  have hsq (m n : ℕ) : ((m : ℝ) - n) ^ 2 =
      ((Int.natAbs ((m : ℤ) - n) : ℕ) : ℝ) ^ 2 := by
    have h : (((Int.natAbs ((m : ℤ) - n) : ℕ) : ℤ) : ℝ) =
        (Int.natAbs ((m : ℤ) - n) : ℝ) := Int.cast_natCast _
    rw [← h, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      sq_abs]
  exact congrArg₂ (· + ·) (hsq u.1.val v.1.val) (hsq u.2.val v.2.val)

/-- The covariance vanishes beyond the horizontal and vertical grid neighbours. -/
private lemma triangleGridPoint_value {a : ℝ} (ha : 0 < a) (u v : Fin 5 × Fin 5) :
    max (1 - ‖triangleGridPoint a u - triangleGridPoint a v‖ / a) 0 =
      (if triangleGridSq u v = 0 then (1 : ℝ) else 0) +
      (1 - (Real.sqrt 2)⁻¹) * (if triangleGridSq u v = 1 then (1 : ℝ) else 0) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  let d := ‖triangleGridPoint a u - triangleGridPoint a v‖
  have hd : 0 ≤ d := norm_nonneg _
  have hsq : d ^ 2 = (a / Real.sqrt 2) ^ 2 * (triangleGridSq u v : ℝ) :=
    triangleGridPoint_dist_sq a u v
  -- Use the distance abbreviation for the real arithmetic in the three distance cases.
  change max (1 - d / a) 0 = _
  by_cases h0 : triangleGridSq u v = 0
  · have hdz : d = 0 := by rw [h0, Nat.cast_zero, mul_zero] at hsq; nlinarith
    simp [hdz, h0]
  by_cases h1 : triangleGridSq u v = 1
  · have hda : d = a / Real.sqrt 2 := by
      rw [h1, Nat.cast_one, mul_one] at hsq
      nlinarith [div_nonneg ha.le hs0.le]
    simp only [h1, Nat.one_ne_zero, ↓reduceIte, mul_one, zero_add, hda]
    have hdiv : a / Real.sqrt 2 / a = (Real.sqrt 2)⁻¹ := by field_simp
    rw [hdiv, max_eq_left]
    exact sub_nonneg.2 (inv_le_one_of_one_le₀ hs1.le)
  · simp only [h0, h1, ↓reduceIte, mul_zero, add_zero]
    have hD : (2 : ℝ) ≤ (triangleGridSq u v : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ triangleGridSq u v)
    have hda : a ≤ d := by
      have hle := mul_le_mul_of_nonneg_left hD (sq_nonneg (a / Real.sqrt 2))
      rw [← hsq, div_pow, hs] at hle
      nlinarith
    exact max_eq_right (sub_nonpos.2 ((le_div_iff₀ ha).2 (by simpa only [one_mul])))

/-- SYNOPSIS item 11: the triangular function `(1 - t/a)_+` does not belong to `Φ_2`. -/
theorem triangular_not_mem_isotropicClass_two {a : ℝ} (ha : 0 < a) :
    (fun t ↦ max (1 - t / a) 0) ∉ isotropicClass 2 := by
  intro h
  have hQ := ((mem_isotropicClass.mp h).2.2).sum_nonneg
    (fun u ↦ (triangleGridWeight u : ℂ)) (triangleGridPoint a)
  have hd (k : ℕ) (S : ℤ)
      (hS : (∑ u : Fin 5 × Fin 5, ∑ v : Fin 5 × Fin 5, triangleGridWeight u *
        triangleGridWeight v * (if triangleGridSq u v = k then 1 else 0)) = S) :
      (∑ u : Fin 5 × Fin 5, ∑ v : Fin 5 × Fin 5, (triangleGridWeight u : ℝ) *
        (triangleGridWeight v : ℝ) * (if triangleGridSq u v = k then 1 else 0)) = S := by
    exact_mod_cast hS
  -- The two integer sums are the diagonal and nearest-neighbour contributions.
  have h0 := hd 0 196 (by decide)
  have h1 := hd 1 (-672) (by decide)
  have hre := (Complex.nonneg_iff.mp hQ).1
  simp only [← Complex.ofReal_intCast, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re, mul_assoc, triangleGridPoint_value ha, mul_add] at hre
  have heq (u v : Fin 5 × Fin 5) :
      (triangleGridWeight u : ℝ) * ((triangleGridWeight v : ℝ) *
        (if triangleGridSq u v = 0 then 1 else 0)) +
      (triangleGridWeight u : ℝ) * ((triangleGridWeight v : ℝ) *
        ((1 - (Real.sqrt 2)⁻¹) * (if triangleGridSq u v = 1 then 1 else 0))) =
      (triangleGridWeight u : ℝ) * (triangleGridWeight v : ℝ) *
        (if triangleGridSq u v = 0 then 1 else 0) +
      (1 - (Real.sqrt 2)⁻¹) * ((triangleGridWeight u : ℝ) * (triangleGridWeight v : ℝ) *
        (if triangleGridSq u v = 1 then 1 else 0)) := by ring
  have hsum : (∑ u : Fin 5 × Fin 5, ∑ v : Fin 5 × Fin 5,
      ((triangleGridWeight u : ℝ) * ((triangleGridWeight v : ℝ) *
        (if triangleGridSq u v = 0 then 1 else 0)) +
      (triangleGridWeight u : ℝ) * ((triangleGridWeight v : ℝ) *
        ((1 - (Real.sqrt 2)⁻¹) * (if triangleGridSq u v = 1 then 1 else 0))))) =
      (∑ u : Fin 5 × Fin 5, ∑ v : Fin 5 × Fin 5, (triangleGridWeight u : ℝ) *
        (triangleGridWeight v : ℝ) * (if triangleGridSq u v = 0 then 1 else 0)) +
      (1 - (Real.sqrt 2)⁻¹) *
        (∑ u : Fin 5 × Fin 5, ∑ v : Fin 5 × Fin 5, (triangleGridWeight u : ℝ) *
          (triangleGridWeight v : ℝ) * (if triangleGridSq u v = 1 then 1 else 0)) := by
    simp_rw [heq, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum, h0, h1] at hre
  have hsmall : (Real.sqrt 2)⁻¹ < (17 : ℝ) / 24 := by
    apply (inv_lt_iff_one_lt_mul₀ (Real.sqrt_pos.2 (by norm_num))).2
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  norm_num at hre
  linarith

end MSSS
