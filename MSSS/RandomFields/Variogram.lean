module

public import MSSS.RandomFields.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Analysis.PositiveDefinite.AddGroup

import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import MSSS.RandomFields.Isotropic
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Power
import TauCeti.Analysis.PositiveDefinite.Kernel.Schoenberg

/-!
# Variograms

SYNOPSIS item 15, the Schoenberg–von Neumann characterisation of variograms.

## Main definitions

* `MSSS.IsCondNegDef γ`: `γ` is conditionally negative definite on an additive group.

## Main results

* `MSSS.isCondNegDef_tfae`, `MSSS.exists_isGaussianProcess_semivariogram`,
  `MSSS.isCondNegDef_norm_rpow`: SYNOPSIS item 15.

The semivariogram construction uses TauCeti's centring criterion for conditionally negative
semidefinite kernels to obtain the covariance of a field pinned at the origin. The norm-power
example uses TauCeti's Schoenberg criterion and complete monotonicity of stretched exponentials.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ComplexOrder

namespace MSSS

/-- A function `γ` on an additive group is **conditionally negative definite** when
`∑_{i,j} c_i c_j γ(x_i - x_j) ≤ 0` for all points `x_i` and real coefficients with
`∑ c_i = 0`. -/
def IsCondNegDef {G : Type*} [AddCommGroup G] (γ : G → ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ) (x : Fin n → G), ∑ i, c i = 0 →
    ∑ i, ∑ j, c i * c j * γ (x i - x j) ≤ 0

lemma isCondNegDef_iff {G : Type*} [AddCommGroup G] {γ : G → ℝ} :
    IsCondNegDef γ ↔ ∀ (n : ℕ) (c : Fin n → ℝ) (x : Fin n → G), ∑ i, c i = 0 →
      ∑ i, ∑ j, c i * c j * γ (x i - x j) ≤ 0 := Iff.rfl

variable {d : ℕ}

/-- The matrix of an even conditionally negative definite function on an additive group is
conditionally negative semidefinite in TauCeti's kernel formulation. -/
private lemma IsCondNegDef.condNegSemidef {G : Type*} [AddCommGroup G] {γ : G → ℝ}
    (hγ : IsCondNegDef γ) (heven : Function.Even γ) :
    (Matrix.of fun s t ↦ γ (s - t)).CondNegSemidef := by
  classical
  refine Matrix.condNegSemidef_iff_finite_sum.mpr ⟨?_, fun {ι : Type} _ x c hc ↦ ?_⟩
  · intro s t
    simpa only [Matrix.of_apply, star_trivial, neg_sub] using (heven (s - t)).symm
  · let e := (Fintype.equivFin ι).symm
    have hn := hγ _ (c ∘ e) (x ∘ e) ((e.sum_comp c).trans hc)
    simp only [Function.comp_apply] at hn
    have hinner (i : ι) : (∑ j, c i * c (e j) * γ (x i - x (e j))) =
        ∑ j, c i * c j * γ (x i - x j) := e.sum_comp (fun j ↦ c i * c j * γ (x i - x j))
    simp only [hinner] at hn
    rw [e.sum_comp (fun i ↦ ∑ j, c i * c j * γ (x i - x j))] at hn
    simpa only [star_trivial, Matrix.of_apply, mul_right_comm _ (γ _)] using hn

/-- SYNOPSIS item 15: for continuous even `γ` on `ℝ^d` with `γ 0 = 0`, these are equivalent:
(a) `γ` is conditionally negative definite; (b) `e^{-tγ}` is positive definite for every `t > 0`;
(c) `γ(h) = Q(h) + ∫ (1 - cos⟨ω, h⟩)/‖ω‖² χ(dω)` with `Q` a positive semidefinite quadratic form
and `χ` a symmetric measure with `χ {0} = 0` and `∫ (1 + ‖ω‖²)⁻¹ χ(dω) < ∞`. -/
theorem isCondNegDef_tfae {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ)
    (h0 : γ 0 = 0) (heven : Function.Even γ) :
    List.TFAE [IsCondNegDef γ,
      ∀ t : ℝ, 0 < t → TauCeti.IsPositiveDefiniteSub fun h ↦ (Real.exp (-t * γ h) : ℂ),
      ∃ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), T.IsPositive ∧
        ∃ χ : Measure (EuclideanSpace ℝ (Fin d)), χ.map Neg.neg = χ ∧ χ {0} = 0 ∧
          ∫⁻ ξ, ENNReal.ofReal (1 + ‖ξ‖ ^ 2)⁻¹ ∂χ < ⊤ ∧
          ∀ h, γ h = ⟪T h, h⟫ + ∫ ξ, (1 - Real.cos ⟪ξ, h⟫) / ‖ξ‖ ^ 2 ∂χ] := by
  sorry

/-- SYNOPSIS item 15: every even conditionally negative definite `γ` with `γ 0 = 0` (continuous
or not) is the semivariogram of a Gaussian intrinsically stationary field. The increments
`Z(x + h) - Z(x)` are centred with variance `2γ(h)`. -/
theorem exists_isGaussianProcess_semivariogram {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h0 : γ 0 = 0) (hcnd : IsCondNegDef γ) (heven : Function.Even γ) :
    ∃ P : Measure (EuclideanSpace ℝ (Fin d) → ℝ), IsProbabilityMeasure P ∧
      IsGaussianProcess (fun x (ω : EuclideanSpace ℝ (Fin d) → ℝ) ↦ ω x) P ∧
      ∀ x h, ∫ ω, (ω (x + h) - ω x) ∂P = 0 ∧
        Var[fun ω ↦ ω (x + h) - ω x; P] / 2 = γ h := by
  let K (s t : EuclideanSpace ℝ (Fin d)) := γ s + γ t - γ (s - t)
  have hK : (Matrix.of K).PosSemidef := by
    have h := hcnd.condNegSemidef heven
    convert (h.isHermitian.condNegSemidef_iff_posSemidef_centered 0).mp h using 1
    ext s t
    simp only [Matrix.of_apply, K, sub_zero, zero_sub, heven t, h0]
  obtain ⟨P, hP, hGauss, hmean, hcov⟩ := exists_isGaussianProcess_coord 0 K hK
  have hLp (s) := (hGauss.hasGaussianLaw_eval s).memLp_two
  have hVar (s) : Var[fun ω ↦ ω s; P] = γ s + γ s := by
    rw [← covariance_self (measurable_pi_apply s).aemeasurable, hcov]
    simp only [K, sub_self, h0, sub_zero]
  refine ⟨P, hP, hGauss, fun x h ↦ ⟨?_, ?_⟩⟩
  · have hint (s) : Integrable (fun ω ↦ ω s) P := MemLp.integrable (by norm_num) (hLp s)
    rw [integral_sub (hint (x + h)) (hint x), hmean, hmean]
    simp only [Pi.zero_apply, sub_zero]
  · rw [variance_fun_sub (hLp (x + h)) (hLp x), hVar, hVar, hcov]
    simp only [K, add_sub_cancel_left]
    ring

/-- SYNOPSIS item 15, example: `‖h‖^α` with `0 < α ≤ 2` is conditionally negative definite on
every `ℝ^d`, hence a semivariogram. -/
theorem isCondNegDef_norm_rpow {α : ℝ} (hα₀ : 0 < α) (hα₂ : α ≤ 2) :
    IsCondNegDef fun h : EuclideanSpace ℝ (Fin d) ↦ ‖h‖ ^ α := by
  let E := EuclideanSpace ℝ (Fin d)
  let K : Matrix E E ℂ := Matrix.of fun x y ↦ (‖x - y‖ ^ α : ℝ)
  have hK : K.CondNegSemidef := by
    -- TauCeti's Schoenberg criterion reduces the claim to Gaussian scale mixtures.
    apply Matrix.condNegSemidef_iff_forall_posSemidef_cexp_neg_mul.mpr
    intro t ht
    have hcm := TauCeti.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul_rpow ht.le
      (by linarith : 0 ≤ α / 2) (by linarith : α / 2 ≤ 1)
    have hpow (x : E) : (‖x‖ ^ (2 : ℕ)) ^ (α / 2) = ‖x‖ ^ α := by
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg x)]
      congr 1
      ring
    have heq :
        Matrix.of (fun x y ↦ Complex.exp (-(t * K x y))) =
          (fun x y : E ↦ (Real.exp (-t * (‖x - y‖ ^ 2) ^ (α / 2)) : ℂ)) := by
      ext x y
      simp only [Matrix.of_apply, K, hpow, Complex.ofReal_exp, Complex.ofReal_neg,
        Complex.ofReal_mul, neg_mul]
    rw [heq]
    exact (isPositiveDefiniteSub_sq_norm_of_completelyMonotone (E := E) hcm).posSemidef
  intro n c x hc
  have hcz : ∑ i, (c i : ℂ) = 0 := by exact_mod_cast hc
  have h := (Matrix.condNegSemidef_iff_finite_sum.mp hK).2 x (fun i ↦ (c i : ℂ)) hcz
  simp only [K, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal, mul_right_comm] at h
  exact_mod_cast h

end MSSS
