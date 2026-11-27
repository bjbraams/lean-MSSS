module

public import MSSS.Geostatistics.Kriging
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Probability.Distributions.Gaussian.Density
import TauCeti.Probability.Distributions.Gaussian.MixedMoments
import TauCeti.Probability.Moments.Chebyshev

/-!
# Misspecified covariances and equivalence of Gaussian measures

SYNOPSIS items 34–37 and 39: the effect of a misspecified covariance on linear prediction,
the Feldman–Hájek dichotomy, spectral criteria for equivalence, Stein's asymptotic optimality of
pseudo-best linear prediction, and microergodicity.

Two measures are *equivalent* when each is absolutely continuous with respect to the other and
*orthogonal* when they are mutually singular (`⟂ₘ`). The law `G_D(m, K)` of the Gaussian field on
an index set `D` with mean `m` and covariance `K` is a measure on the path space `D → ℝ` with its
product σ-algebra; it is `MSSS.gaussianFieldLaw m K`. On the product σ-algebra the dichotomy and
the equivalence criteria hold for every index set, so the closedness of `D` and the continuity of
`m` and `K` in the synopsis are not needed for the statements of item 35.

## Main definitions

* `MSSS.IsGaussianFieldLaw m K μ`: under `μ` the coordinates form a Gaussian field with mean `m`
  and covariance `K`.
* `MSSS.gaussianFieldLaw m K`: the Gaussian law `G_D(m, K)` on `D → ℝ`.
* `MSSS.spectralCov f h`: the covariance `∫ cos⟨h, ω⟩ f(ω) dω` with spectral density `f`.
* `MSSS.IsMicroergodic P h`: `h(θ) ≠ h(θ')` implies `P_θ ⟂ P_θ'`.

## Main results

* `MSSS.misspecified_prediction_bounds`: SYNOPSIS item 34.
* `MSSS.gaussianFieldLaw_equiv_or_mutuallySingular`, `MSSS.gaussianFieldLaw_equiv_iff`,
  `MSSS.gaussianFieldLaw_equiv_iff_summable`, `MSSS.multivariateGaussian_equiv_iff`:
  SYNOPSIS item 35.
* `MSSS.gaussianFieldLaw_equiv_of_spectralDensity`, `MSSS.gaussianFieldLaw_exponential`:
  SYNOPSIS item 36.
* `MSSS.stein_asymptotic_efficiency`, `MSSS.stein_asymptotic_efficiency_universalKriging`:
  SYNOPSIS item 37.
* `MSSS.not_consistent_of_equiv`, `MSSS.tendsto_quadraticVariation`,
  `MSSS.gaussianFieldLaw_mutuallySingular_of_slope_ne`: SYNOPSIS item 39.

The prediction risk bounds use Mathlib's quadratic discriminant criterion and integration
of square-integrable products. Finite-dimensional Gaussian equivalence uses TauCeti’s formula
for the standard Gaussian density and Mathlib’s change of variables for Lebesgue measure.
Quadratic variation uses Mathlib’s mean value theorem and Gaussian increment laws, together
with TauCeti’s Isserlis formula and Chebyshev inequality.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal RealInnerProductSpace

namespace MSSS

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-! ### Misspecified covariance in finite samples (SYNOPSIS item 34) -/

/-- The integral of a squared perturbation of a square-integrable variable. -/
lemma integral_sq_add_const_mul {P : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (t : ℝ) :
    (∫ ω, (f ω + t * g ω) ^ 2 ∂P) =
      (∫ ω, f ω ^ 2 ∂P) + 2 * t * (∫ ω, f ω * g ω ∂P) + t ^ 2 * (∫ ω, g ω ^ 2 ∂P) := by
  have hfg : Integrable (fun ω ↦ f ω * g ω) P := hf.integrable_mul hg
  have hl (ω : Ω) : (f ω + t * g ω) ^ 2 =
      (f ω ^ 2 + (2 * t) * (f ω * g ω)) + t ^ 2 * g ω ^ 2 := by ring
  simp_rw [hl]
  rw [integral_add (f := fun ω ↦ f ω ^ 2 + 2 * t * (f ω * g ω))
    (hf.integrable_sq.add (hfg.const_mul (2 * t))) (hg.integrable_sq.const_mul (t ^ 2)),
    integral_add hf.integrable_sq (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul]

/-- A best affine prediction of centred variables has zero intercept. Its error is orthogonal
in `L²` to every finite linear combination of the observations. -/
private lemma predictionError_centered_orthogonal {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ι → Ω → ℝ} {ψ : Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 P) (hψ : MemLp ψ 2 P)
    (hcY : ∀ i, P[Y i] = 0) (hcψ : P[ψ] = 0) :
    (bestAffineWeights P Y ψ).1 = 0 ∧ ∀ c : ι → ℝ,
      (∫ ω, predictionError P Y ψ ω * (∑ i, c i * Y i ω) ∂P) = 0 := by
  let Z : Option ι → Ω → ℝ := fun i ↦ i.elim ψ Y
  let loc : ι → Option ι := some
  have hZ : IsSecondOrderField Z P := isSecondOrderField_iff.mpr fun i ↦ by
    cases i with
    | none => exact hψ
    | some i => exact hY i
  let p := bestAffineWeights P Y ψ
  have hbest : IsBestAffinePredictor P Y ψ p.1 p.2 :=
    isBestAffinePredictor_bestAffineWeights (exists_isBestAffinePredictor loc none hZ)
  have hi : p.1 = 0 := by
    have hnorm := ((isBestAffinePredictor_iff loc none hZ p.1 p.2).mp hbest).2
    have hMean : (fun i ↦ P[Y i]) = (0 : ι → ℝ) := funext hcY
    have hnorm' : p.1 = P[ψ] - p.2 ⬝ᵥ fun i ↦ P[Y i] := hnorm
    rw [hnorm', hcψ, hMean, dotProduct_zero, sub_zero]
  refine ⟨hi, fun c ↦ ?_⟩
  let e := predictionError P Y ψ
  let d : Ω → ℝ := fun ω ↦ ∑ i, c i * Y i ω
  have hp (w : ι → ℝ) : MemLp (fun ω ↦ ∑ i, w i * Y i ω) 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦ (hY i).const_mul _
  have he : MemLp e 2 P := by
    have he' : e = fun ω ↦ ψ ω - p.1 - ∑ i, p.2 i * Y i ω :=
      funext (predictionError_def P Y ψ)
    rw [he']
    exact (hψ.sub (memLp_const p.1)).sub (hp p.2)
  have hmin (t : ℝ) :
      0 ≤ (∫ ω, d ω ^ 2 ∂P) * (t * t) + (2 * ∫ ω, e ω * d ω ∂P) * t + 0 := by
    have h := isBestAffinePredictor_def.mp hbest p.1 (p.2 - t • c)
    have hshift : affineMSE P Y ψ p.1 (p.2 - t • c) = ∫ ω, (e ω + t * d ω) ^ 2 ∂P := by
      simp only [affineMSE_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, e, d, predictionError_def, p]
      congr 1 with ω
      ring
    rw [hshift, integral_sq_add_const_mul he (hp c) t] at h
    have hval : affineMSE P Y ψ p.1 p.2 = ∫ ω, e ω ^ 2 ∂P := by
      simp only [affineMSE_def, e, predictionError_def, p]
    rw [hval] at h
    linarith only [h]
  have hd := discrim_le_zero hmin
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith

/-- The sharp two-dimensional bound for the increase in prediction error under comparable
quadratic risks. -/
private lemma prediction_risk_increase_le {a b Q D α β : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hQ : 0 < Q) (hβ : a * D ≤ β ∧ β ≤ b * D)
    (h : ∀ t : ℝ, a * (Q + D * (t * t)) ≤ α - 2 * β * t + β * (t * t) ∧
      α - 2 * β * t + β * (t * t) ≤ b * (Q + D * (t * t))) :
    4 * a * b * D ≤ (b - a) ^ 2 * Q := by
  let u := β - a * D
  let v := b * D - β
  have hu : 0 ≤ u := sub_nonneg.mpr hβ.1
  have hv : 0 ≤ v := sub_nonneg.mpr hβ.2
  have hβ' : 0 < β := (mul_pos ha hD).trans_le hβ.1
  have hlow : ∀ t : ℝ, 0 ≤ u * (t * t) + (-2 * β) * t + (α - a * Q) := by
    intro t
    dsimp only [u]
    linarith only [(h t).1]
  have hhigh : ∀ t : ℝ, 0 ≤ v * (t * t) + (2 * β) * t + (b * Q - α) := by
    intro t
    dsimp only [v]
    linarith only [(h t).2]
  have h₁ : β ^ 2 ≤ u * (α - a * Q) := by
    have hd := discrim_le_zero hlow
    dsimp only [discrim] at hd
    nlinarith only [hd]
  have h₂ : β ^ 2 ≤ v * (b * Q - α) := by
    have hd := discrim_le_zero hhigh
    dsimp only [discrim] at hd
    nlinarith only [hd]
  have huba : u + v = (b - a) * D := by dsimp only [u, v]; ring
  have huv : 0 < u := by
    by_contra! hup
    have h0 : u = 0 := le_antisymm hup hu
    rw [h0, zero_mul] at h₁
    exact (not_lt_of_ge h₁) (sq_pos_of_pos hβ')
  have hba : 0 < b - a := by
    rw [← mul_pos_iff_of_pos_right hD, ← huba]
    exact add_pos_of_pos_of_nonneg huv hv
  have hbound : D * β ^ 2 ≤ Q * u * v := by
    apply (mul_le_mul_iff_of_pos_left hba).1
    calc
      _ = β ^ 2 * v + β ^ 2 * u := by rw [← mul_add, add_comm v u, huba]; ring
      _ ≤ u * (α - a * Q) * v + v * (b * Q - α) * u :=
        add_le_add (mul_le_mul_of_nonneg_right h₁ hv) (mul_le_mul_of_nonneg_right h₂ hu)
      _ = _ := by ring
  have hK : 4 * a * b * (u * v) ≤ (b - a) ^ 2 * β ^ 2 := by
    dsimp only [u, v]
    nlinarith only [sq_nonneg ((a + b) * β - 2 * a * b * D)]
  have hb : 0 < b := by linarith only [ha, hba]
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hβ')).1
  calc
    _ = (4 * a * b) * (D * β ^ 2) := by ring
    _ ≤ (4 * a * b) * (Q * u * v) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = Q * (4 * a * b * (u * v)) := by ring
    _ ≤ Q * ((b - a) ^ 2 * β ^ 2) := mul_le_mul_of_nonneg_left hK hQ.le
    _ = _ := by ring

/-- Comparable quadratic risks give the sharp error bound when the error is orthogonal to
the change of predictor under its own law. -/
private lemma prediction_risk_ratios {P₀ P₁ : Measure Ω} {e₀ e₁ d : Ω → ℝ}
    (he : e₁ = fun ω ↦ e₀ ω + d ω) (he₀ : MemLp e₀ 2 P₀) (he₁ : MemLp e₀ 2 P₁)
    (hd₀ : MemLp d 2 P₀) (hd₁ : MemLp d 2 P₁)
    (hor₀ : (∫ ω, e₀ ω * d ω ∂P₀) = 0) (hor₁ : (∫ ω, e₁ ω * d ω ∂P₁) = 0)
    {a b : ℝ} (ha : 0 < a) (hQ : 0 < ∫ ω, e₀ ω ^ 2 ∂P₀)
    (hcomp : ∀ t : ℝ,
      a * (∫ ω, (e₀ ω + t * d ω) ^ 2 ∂P₀) ≤ (∫ ω, (e₀ ω + t * d ω) ^ 2 ∂P₁) ∧
      (∫ ω, (e₀ ω + t * d ω) ^ 2 ∂P₁) ≤ b * (∫ ω, (e₀ ω + t * d ω) ^ 2 ∂P₀))
    (hcompd : 0 < (∫ ω, d ω ^ 2 ∂P₀) →
      a * (∫ ω, d ω ^ 2 ∂P₀) ≤ (∫ ω, d ω ^ 2 ∂P₁) ∧
      (∫ ω, d ω ^ 2 ∂P₁) ≤ b * (∫ ω, d ω ^ 2 ∂P₀)) :
    1 ≤ (∫ ω, e₁ ω ^ 2 ∂P₀) / ∫ ω, e₀ ω ^ 2 ∂P₀ ∧
      (∫ ω, e₁ ω ^ 2 ∂P₀) / (∫ ω, e₀ ω ^ 2 ∂P₀) =
        1 + (∫ ω, (e₁ ω - e₀ ω) ^ 2 ∂P₀) / ∫ ω, e₀ ω ^ 2 ∂P₀ ∧
      (∫ ω, e₁ ω ^ 2 ∂P₀) / (∫ ω, e₀ ω ^ 2 ∂P₀) ≤ 1 + (b - a) ^ 2 / (4 * a * b) ∧
      a ≤ (∫ ω, e₁ ω ^ 2 ∂P₁) / ∫ ω, e₁ ω ^ 2 ∂P₀ ∧
      (∫ ω, e₁ ω ^ 2 ∂P₁) / (∫ ω, e₁ ω ^ 2 ∂P₀) ≤ b := by
  let Q := ∫ ω, e₀ ω ^ 2 ∂P₀
  let D := ∫ ω, d ω ^ 2 ∂P₀
  let B := ∫ ω, d ω ^ 2 ∂P₁
  have hD : 0 ≤ D := integral_nonneg fun _ ↦ sq_nonneg _
  have hsplit : (∫ ω, e₁ ω ^ 2 ∂P₀) = Q + D := by
    rw [he]
    simpa only [one_mul, hor₀, mul_zero, add_zero, one_pow] using
      integral_sq_add_const_mul he₀ hd₀ 1
  have hf : (fun ω ↦ e₁ ω - e₀ ω) = d := by
    rw [he]
    exact funext fun ω ↦ add_sub_cancel_left (e₀ ω) (d ω)
  have hcmp := hcomp 1
  simp only [one_mul] at hcmp
  simp_rw [← congrFun he] at hcmp
  have hE : 0 < (∫ ω, e₁ ω ^ 2 ∂P₀) := by rw [hsplit]; exact add_pos_of_pos_of_nonneg hQ hD
  have hb : 0 < b := pos_of_mul_pos_left ((mul_pos ha hE).trans_le (hcmp.1.trans hcmp.2)) hE.le
  have hbound : 4 * a * b * D ≤ (b - a) ^ 2 * Q := by
    rcases hD.eq_or_lt with hD₀ | hD'
    · rw [← hD₀, mul_zero]
      exact mul_nonneg (sq_nonneg _) hQ.le
    · have hcross : (∫ ω, e₀ ω * d ω ∂P₁) = -B := by
        rw [he] at hor₁
        simp only [add_mul, ← pow_two] at hor₁
        rw [integral_add (f := fun ω ↦ e₀ ω * d ω) (he₁.integrable_mul hd₁)
          hd₁.integrable_sq] at hor₁
        exact eq_neg_of_add_eq_zero_left hor₁
      apply prediction_risk_increase_le (α := ∫ ω, e₀ ω ^ 2 ∂P₁) (β := B)
        ha hD' hQ (hcompd hD')
      intro t
      have h₀ : (∫ ω, (e₀ ω + t * d ω) ^ 2 ∂P₀) = Q + D * (t * t) := by
        rw [integral_sq_add_const_mul he₀ hd₀, hor₀]
        dsimp only [Q, D]
        ring
      have h₁ : (∫ ω, (e₀ ω + t * d ω) ^ 2 ∂P₁) =
          (∫ ω, e₀ ω ^ 2 ∂P₁) - 2 * B * t + B * (t * t) := by
        rw [integral_sq_add_const_mul he₁ hd₁, hcross]
        dsimp only [B]
        ring
      simpa only [h₀, h₁] using hcomp t
  have hratio : D / Q ≤ (b - a) ^ 2 / (4 * a * b) :=
    (div_le_div_iff₀ hQ (by positivity)).2 (by simpa only [mul_comm D] using hbound)
  refine ⟨(le_div_iff₀ hQ).2 ?_, ?_, ?_, (le_div_iff₀ hE).2 hcmp.1,
    (div_le_iff₀ hE).2 hcmp.2⟩
  · rw [hsplit, one_mul]; exact le_add_of_nonneg_right hD
  · have hsq : (∫ ω, (e₁ ω - e₀ ω) ^ 2 ∂P₀) = D :=
      integral_congr_ae (ae_of_all _ fun ω ↦ congrArg (fun r : ℝ ↦ r ^ 2) (congrFun hf ω))
    rw [hsplit, hsq, add_div, div_self hQ.ne']
  · rw [hsplit, add_div, div_self hQ.ne']; exact add_le_add_right hratio 1

/-- SYNOPSIS item 34: let the observations `Y` and the predictand `ψ` be centred under the true
law `P₀` and the presumed law `P₁`, and let `a ≤ E₁ h² / E₀ h² ≤ b` for every `h` in their linear
span with `E₀ h² > 0`. With `e_j` the error of the best linear predictor computed under `P_j`,
`1 ≤ E₀ e₁² / E₀ e₀² = 1 + E₀ (e₁ - e₀)² / E₀ e₀² ≤ 1 + (b - a)² / (4ab)` and
`a ≤ E₁ e₁² / E₀ e₁² ≤ b`. The ratios are stated for `E₀ e₀² > 0`. -/
theorem misspecified_prediction_bounds {P₀ P₁ : Measure Ω} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] {Y : ι → Ω → ℝ} {ψ : Ω → ℝ} (hY₀ : ∀ i, MemLp (Y i) 2 P₀)
    (hY₁ : ∀ i, MemLp (Y i) 2 P₁) (hψ₀ : MemLp ψ 2 P₀) (hψ₁ : MemLp ψ 2 P₁)
    (hcY₀ : ∀ i, P₀[Y i] = 0) (hcY₁ : ∀ i, P₁[Y i] = 0) (hcψ₀ : P₀[ψ] = 0) (hcψ₁ : P₁[ψ] = 0)
    {a b : ℝ} (ha : 0 < a)
    (hcomp : ∀ (c₀ : ℝ) (c : ι → ℝ),
      0 < ∫ ω, (c₀ * ψ ω + ∑ i, c i * Y i ω) ^ 2 ∂P₀ →
        a * ∫ ω, (c₀ * ψ ω + ∑ i, c i * Y i ω) ^ 2 ∂P₀ ≤
            ∫ ω, (c₀ * ψ ω + ∑ i, c i * Y i ω) ^ 2 ∂P₁ ∧
          ∫ ω, (c₀ * ψ ω + ∑ i, c i * Y i ω) ^ 2 ∂P₁ ≤
            b * ∫ ω, (c₀ * ψ ω + ∑ i, c i * Y i ω) ^ 2 ∂P₀)
    (he : 0 < ∫ ω, predictionError P₀ Y ψ ω ^ 2 ∂P₀) :
    let e₀ := predictionError P₀ Y ψ
    let e₁ := predictionError P₁ Y ψ
    1 ≤ (∫ ω, e₁ ω ^ 2 ∂P₀) / ∫ ω, e₀ ω ^ 2 ∂P₀ ∧
      (∫ ω, e₁ ω ^ 2 ∂P₀) / (∫ ω, e₀ ω ^ 2 ∂P₀) =
        1 + (∫ ω, (e₁ ω - e₀ ω) ^ 2 ∂P₀) / ∫ ω, e₀ ω ^ 2 ∂P₀ ∧
      (∫ ω, e₁ ω ^ 2 ∂P₀) / (∫ ω, e₀ ω ^ 2 ∂P₀) ≤ 1 + (b - a) ^ 2 / (4 * a * b) ∧
      a ≤ (∫ ω, e₁ ω ^ 2 ∂P₁) / ∫ ω, e₁ ω ^ 2 ∂P₀ ∧
      (∫ ω, e₁ ω ^ 2 ∂P₁) / (∫ ω, e₁ ω ^ 2 ∂P₀) ≤ b := by
  intro e₀ e₁
  let w₀ := (bestAffineWeights P₀ Y ψ).2
  let w₁ := (bestAffineWeights P₁ Y ψ).2
  let d : Ω → ℝ := fun ω ↦ ∑ i, (w₀ i - w₁ i) * Y i ω
  obtain ⟨h₀, hor₀⟩ := predictionError_centered_orthogonal hY₀ hψ₀ hcY₀ hcψ₀
  obtain ⟨h₁, hor₁⟩ := predictionError_centered_orthogonal hY₁ hψ₁ hcY₁ hcψ₁
  have he₀ (ω : Ω) : e₀ ω = ψ ω - ∑ i, w₀ i * Y i ω := by
    simp only [e₀, predictionError_def, h₀, sub_zero, w₀]
  have he₁ (ω : Ω) : e₁ ω = ψ ω - ∑ i, w₁ i * Y i ω := by
    simp only [e₁, predictionError_def, h₁, sub_zero, w₁]
  have hrel : e₁ = fun ω ↦ e₀ ω + d ω := by
    funext ω
    simp only [d, he₀, he₁, sub_mul, Finset.sum_sub_distrib]
    ring
  have hLp {P : Measure Ω} (hY : ∀ i, MemLp (Y i) 2 P) (c : ι → ℝ) :
      MemLp (fun ω ↦ ∑ i, c i * Y i ω) 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦ (hY i).const_mul _
  have hLp₀ : MemLp e₀ 2 P₀ := by rw [funext he₀]; exact hψ₀.sub (hLp hY₀ w₀)
  have hLp₁ : MemLp e₀ 2 P₁ := by rw [funext he₀]; exact hψ₁.sub (hLp hY₁ w₀)
  have hD₀ : MemLp d 2 P₀ := hLp hY₀ (w₀ - w₁)
  have hD₁ : MemLp d 2 P₁ := hLp hY₁ (w₀ - w₁)
  have hor₀' : (∫ ω, e₀ ω * d ω ∂P₀) = 0 := hor₀ (w₀ - w₁)
  refine prediction_risk_ratios hrel hLp₀ hLp₁ hD₀ hD₁ hor₀'
    (hor₁ (w₀ - w₁)) ha he ?_ ?_
  · intro t
    have hspan (ω : Ω) : e₀ ω + t * d ω =
        1 * ψ ω + ∑ i, (-w₀ i + t * (w₀ i - w₁ i)) * Y i ω := by
      simp only [he₀, d, one_mul, add_mul, neg_mul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    simp only [hspan]
    refine hcomp 1 _ ?_
    simp_rw [← hspan]
    rw [integral_sq_add_const_mul hLp₀ hD₀, hor₀', mul_zero, add_zero]
    exact add_pos_of_pos_of_nonneg he
      (mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _))
  · simpa only [d, Pi.sub_apply, zero_mul, zero_add] using hcomp 0 (w₀ - w₁)

/-! ### Gaussian laws on path space (SYNOPSIS item 35) -/

section PathSpace

variable {D : Type*}

/-- The coordinates of `D → ℝ` form, under `μ`, a Gaussian field with mean `m` and
covariance `K`. -/
def IsGaussianFieldLaw (m : D → ℝ) (K : D → D → ℝ) (μ : Measure (D → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ IsGaussianProcess (fun t (x : D → ℝ) ↦ x t) μ ∧
    (∀ t, ∫ x, x t ∂μ = m t) ∧ ∀ s t, cov[fun x : D → ℝ ↦ x s, fun x ↦ x t; μ] = K s t

lemma isGaussianFieldLaw_def {m : D → ℝ} {K : D → D → ℝ} {μ : Measure (D → ℝ)} :
    IsGaussianFieldLaw m K μ ↔ IsProbabilityMeasure μ ∧
      IsGaussianProcess (fun t (x : D → ℝ) ↦ x t) μ ∧ (∀ t, ∫ x, x t ∂μ = m t) ∧
        ∀ s t, cov[fun x : D → ℝ ↦ x s, fun x ↦ x t; μ] = K s t := Iff.rfl

open Classical in
/-- The law `G_D(m, K)` on `D → ℝ` of the Gaussian field with mean `m` and covariance `K`. It
exists when `K` is positive semidefinite (`MSSS.gaussianFieldLaw_spec`) and is then unique
(`MSSS.map_eq_of_isGaussianProcess`); otherwise it is the Dirac mass at `m`. -/
def gaussianFieldLaw (m : D → ℝ) (K : D → D → ℝ) : Measure (D → ℝ) :=
  if h : ∃ μ, IsGaussianFieldLaw m K μ then Classical.choose h else Measure.dirac m

instance (m : D → ℝ) (K : D → D → ℝ) : IsProbabilityMeasure (gaussianFieldLaw m K) := by
  rw [gaussianFieldLaw]
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · infer_instance

/-- For a positive semidefinite covariance, the coordinates form under `G_D(m, K)` a Gaussian
field with mean `m` and covariance `K`. -/
lemma gaussianFieldLaw_spec (m : D → ℝ) {K : D → D → ℝ} (hK : (Matrix.of K).PosSemidef) :
    IsGaussianFieldLaw m K (gaussianFieldLaw m K) := by
  have h : ∃ μ, IsGaussianFieldLaw m K μ := exists_isGaussianProcess_coord m K hK
  rw [gaussianFieldLaw, dite_eq_left h]
  exact Classical.choose_spec h

/-- SYNOPSIS item 35, Feldman–Hájek dichotomy: two Gaussian laws on `D → ℝ` are either
equivalent or orthogonal. -/
theorem gaussianFieldLaw_equiv_or_mutuallySingular (m₀ m₁ : D → ℝ) {K₀ K₁ : D → D → ℝ}
    (hK₀ : (Matrix.of K₀).PosSemidef) (hK₁ : (Matrix.of K₁).PosSemidef) :
    (gaussianFieldLaw m₀ K₀ ≪ gaussianFieldLaw m₁ K₁ ∧
        gaussianFieldLaw m₁ K₁ ≪ gaussianFieldLaw m₀ K₀) ∨
      gaussianFieldLaw m₀ K₀ ⟂ₘ gaussianFieldLaw m₁ K₁ := by
  sorry

/-- SYNOPSIS item 35: `G_D(m₀, K₀) ≡ G_D(m₁, K₁)` if and only if `G_D(m₀, K₀) ≡ G_D(m₁, K₀)` and
`G_D(m₀, K₀) ≡ G_D(m₀, K₁)`. -/
theorem gaussianFieldLaw_equiv_iff (m₀ m₁ : D → ℝ) {K₀ K₁ : D → D → ℝ}
    (hK₀ : (Matrix.of K₀).PosSemidef) (hK₁ : (Matrix.of K₁).PosSemidef) :
    (gaussianFieldLaw m₀ K₀ ≪ gaussianFieldLaw m₁ K₁ ∧
        gaussianFieldLaw m₁ K₁ ≪ gaussianFieldLaw m₀ K₀) ↔
      (gaussianFieldLaw m₀ K₀ ≪ gaussianFieldLaw m₁ K₀ ∧
          gaussianFieldLaw m₁ K₀ ≪ gaussianFieldLaw m₀ K₀) ∧
        (gaussianFieldLaw m₀ K₀ ≪ gaussianFieldLaw m₀ K₁ ∧
          gaussianFieldLaw m₀ K₁ ≪ gaussianFieldLaw m₀ K₀) := by
  sorry

/-- SYNOPSIS item 35, the Hilbert–Schmidt criterion. Let the variances under the two laws be
comparable on the linear span of the coordinates, and let `(ψ_j)` be an orthonormal basis of the
Gaussian space of `G_D(m₀, K₀)` consisting of finite linear combinations of centred
coordinates. With `b_{jk} = Cov₁(ψ_j, ψ_k) - δ_{jk}` and `μ_j = E₁ ψ_j - E₀ ψ_j`, the laws are
equivalent if and only if `∑ b_{jk}² < ∞` and `∑ μ_j² < ∞`. -/
theorem gaussianFieldLaw_equiv_iff_summable {J : Type*} [Countable J] [DecidableEq J]
    (m₀ m₁ : D → ℝ) {K₀ K₁ : D → D → ℝ} (hK₀ : (Matrix.of K₀).PosSemidef)
    (hK₁ : (Matrix.of K₁).PosSemidef)
    (hcomp : ∃ a b : ℝ, 0 < a ∧ ∀ (S : Finset D) (c : D → ℝ),
      a * Var[fun x ↦ ∑ t ∈ S, c t * x t; gaussianFieldLaw m₀ K₀] ≤
          Var[fun x ↦ ∑ t ∈ S, c t * x t; gaussianFieldLaw m₁ K₁] ∧
        Var[fun x ↦ ∑ t ∈ S, c t * x t; gaussianFieldLaw m₁ K₁] ≤
          b * Var[fun x ↦ ∑ t ∈ S, c t * x t; gaussianFieldLaw m₀ K₀])
    (ψ : J → (D → ℝ) → ℝ)
    (hψ : ∀ j, ∃ (S : Finset D) (c : D → ℝ), ψ j = fun x ↦ ∑ t ∈ S, c t * (x t - m₀ t))
    (hon : ∀ j k, ∫ x, ψ j x * ψ k x ∂(gaussianFieldLaw m₀ K₀) = if j = k then 1 else 0)
    (hbasis : ∀ t, ∀ ε > 0, ∃ (S : Finset J) (c : J → ℝ),
      ∫ x, (x t - m₀ t - ∑ j ∈ S, c j * ψ j x) ^ 2 ∂(gaussianFieldLaw m₀ K₀) < ε) :
    (gaussianFieldLaw m₀ K₀ ≪ gaussianFieldLaw m₁ K₁ ∧
        gaussianFieldLaw m₁ K₁ ≪ gaussianFieldLaw m₀ K₀) ↔
      Summable (fun p : J × J ↦ (cov[ψ p.1, ψ p.2; gaussianFieldLaw m₁ K₁] -
          if p.1 = p.2 then 1 else 0) ^ 2) ∧
        Summable fun j ↦ (∫ x, ψ j x ∂(gaussianFieldLaw m₁ K₁) -
          ∫ x, ψ j x ∂(gaussianFieldLaw m₀ K₀)) ^ 2 := by
  sorry

end PathSpace

/-! ### Finite-dimensional Gaussian equivalence (SYNOPSIS item 35) -/

section FiniteGaussian

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Splitting the source into the kernel and a complement identifies a linear map with
projection to its range. -/
lemma exists_prod_range_ker_equiv {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) :
    ∃ e : (LinearMap.range T × LinearMap.ker T) ≃ₗ[K] V, ∀ x, T (e x) = x.1 := by
  obtain ⟨P, hP⟩ := T.ker.exists_isCompl
  let q := T.ker.quotientEquivOfIsCompl P hP
  let f := q.symm.trans T.quotKerEquivRange
  have hf (x : P) : (f x : W) = T x := by
    dsimp only [f, LinearEquiv.trans_apply]
    rw [← LinearMap.quotKerEquivRange_apply_mk]
    congr 1
  let e := (f.symm.prodCongr (LinearEquiv.refl K T.ker)).trans
    (P.prodEquivOfIsCompl T.ker hP.symm)
  refine ⟨e, fun x ↦ ?_⟩
  simp only [e, LinearEquiv.trans_apply, Submodule.coe_prodEquivOfIsCompl',
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_add, LinearMap.mem_ker.mp x.2.prop,
    add_zero]
  rw [← hf, f.apply_symm_apply]

/-- Linear maps with the same range agree after an invertible change of source. -/
lemma exists_linearEquiv_of_linearMap_range_eq {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    {T U : V →ₗ[K] W} (h : T.range = U.range) :
    ∃ e : V ≃ₗ[K] V, ∀ x, U (e x) = T x := by
  obtain ⟨eT, heT⟩ := exists_prod_range_ker_equiv T
  obtain ⟨eU, heU⟩ := exists_prod_range_ker_equiv U
  have hk : Module.finrank K T.ker = Module.finrank K U.ker := by
    have ht := T.finrank_range_add_finrank_ker
    rw [h] at ht
    have hu := U.finrank_range_add_finrank_ker
    omega
  refine ⟨(eT.symm.trans ((LinearEquiv.ofEq T.range U.range h).prodCongr
    (LinearEquiv.ofFinrankEq T.ker U.ker hk))).trans eU, fun x ↦ ?_⟩
  simp only [LinearEquiv.trans_apply, heU, LinearEquiv.prodCongr_apply, LinearEquiv.coe_ofEq_apply]
  rw [← heT, eT.apply_symm_apply]

section StandardGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian and Lebesgue measure have the same null sets. -/
lemma stdGaussian_volume_absolutelyContinuous :
    stdGaussian E ≪ volume ∧ volume ≪ stdGaussian E := by
  -- TauCeti's density formula is positive at every point.
  rw [TauCeti.Probability.stdGaussian_eq_withDensity_norm]
  refine ⟨withDensity_absolutelyContinuous _ _, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s _ hs
  have hm : Measurable (fun x : E ↦
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-‖x‖ ^ 2 / 2))) := by fun_prop
  rw [withDensity_apply_eq_zero' hm.aemeasurable] at hs
  have hpos (x : E) : 0 < (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-‖x‖ ^ 2 / 2) :=
    mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _) (Real.exp_pos _)
  simpa only [ENNReal.ofReal_ne_zero_iff, hpos, ofPred_true, univ_inter] using hs

/-- The affine image of standard Gaussians is absolutely continuous under an invertible
change in the Gaussian input. -/
lemma map_affine_stdGaussian_absolutelyContinuous (e : E ≃ₗ[ℝ] E) (w : E) :
    (stdGaussian E).map (fun x ↦ e x + w) ≪ stdGaussian E := by
  have he : Measurable (e.toLinearMap : E → E) :=
    e.toLinearMap.continuous_of_finiteDimensional.measurable
  have hew : Measurable (fun x ↦ e x + w) := he.add_const w
  have hv : (volume : Measure E).map e.toLinearMap ≪ volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (LinearEquiv.isUnit_det' e).ne_zero]
    exact Measure.smul_absolutelyContinuous
  have hshift := measurePreserving_add_right (volume : Measure E) w
  have hvol : (volume : Measure E).map ((fun x ↦ x + w) ∘ e.toLinearMap) ≪ volume := by
    simpa only [Measure.map_map hshift.measurable he, hshift.map_eq] using
      hv.map hshift.measurable
  exact (stdGaussian_volume_absolutelyContinuous.1.map hew).trans
    (hvol.trans stdGaussian_volume_absolutelyContinuous.2)

/-- The standard Gaussian gives positive measure to each nonempty open set, so absolute
continuity between affine images implies inclusion of their affine ranges. -/
lemma sub_mem_range_of_map_stdGaussian_absolutelyContinuous (T U : E →ₗ[ℝ] E) (m n : E)
    (h : (stdGaussian E).map (fun x ↦ m + T x) ≪
      (stdGaussian E).map (fun x ↦ n + U x)) (x : E) : m + T x - n ∈ LinearMap.range U := by
  let A : Set E := {y | y - n ∈ LinearMap.range U}
  have hc : IsClosed A :=
    U.range.isClosed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  have hT : Continuous (fun x ↦ m + T x) :=
    continuous_const.add T.continuous_of_finiteDimensional
  have hU : Measurable (fun x ↦ n + U x) :=
    (continuous_const.add U.continuous_of_finiteDimensional).measurable
  have hpre : (fun x ↦ n + U x) ⁻¹' Aᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hy (by simpa only [A, Set.mem_ofPred_eq, add_sub_cancel_left] using U.mem_range_self y)
  have hn : ((stdGaussian E).map (fun x ↦ n + U x)) Aᶜ = 0 := by
    rw [Measure.map_apply hU hc.isOpen_compl.measurableSet, hpre, measure_empty]
  have hz := h hn
  rw [Measure.map_apply hT.measurable hc.isOpen_compl.measurableSet] at hz
  by_contra hx
  have hp := (hc.isOpen_compl.preimage hT).measure_pos (volume : Measure E) ⟨x, hx⟩
  exact hp.ne' (stdGaussian_volume_absolutelyContinuous.2 hz)

/-- Equal linear ranges and a common affine origin suffice for absolute continuity of
the affine images of a standard Gaussian. -/
lemma map_stdGaussian_absolutelyContinuous_of_range_eq {T U : E →ₗ[ℝ] E} {m n : E}
    (h : T.range = U.range) (hm : m - n ∈ U.range) :
    (stdGaussian E).map (fun x ↦ m + T x) ≪ (stdGaussian E).map (fun x ↦ n + U x) := by
  obtain ⟨e, he⟩ := exists_linearEquiv_of_linearMap_range_eq h
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hm
  have hU : Measurable (fun x ↦ n + U x) :=
    (continuous_const.add U.continuous_of_finiteDimensional).measurable
  have hchange : (fun x ↦ m + T x) = (fun x ↦ n + U x) ∘ (fun x ↦ e x + w) := by
    funext x
    simp only [Function.comp_apply, map_add, he, hw]
    abel
  have hφ : Measurable (fun x ↦ e x + w) :=
    e.toLinearMap.continuous_of_finiteDimensional.measurable.add_const w
  simpa only [Measure.map_map hU hφ, ← hchange] using
    (map_affine_stdGaussian_absolutelyContinuous e w).map hU

end StandardGaussian

variable [DecidableEq ι]

/-- A positive semidefinite matrix and its square root have the same range. -/
lemma range_toEuclideanLin_sqrt_eq {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (CFC.sqrt S).toEuclideanLin.range = S.toEuclideanLin.range := by
  have hpos : (CFC.sqrt S).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hadj : LinearMap.adjoint (CFC.sqrt S).toEuclideanLin = (CFC.sqrt S).toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hpos.isHermitian.eq]
  have h := LinearMap.range_adjoint_comp_self (CFC.sqrt S).toEuclideanLin
  rw [hadj, ← Matrix.toLpLin_mul_same 2, CFC.sqrt_mul_sqrt_self S hS.nonneg] at h
  exact h.symm

/-- SYNOPSIS item 35, finite dimension: two Gaussian laws on `ℝⁿ` are equivalent if and only if
they are supported by the same affine subspace, that is, `S₀` and `S₁` have the same range and
`m₁ - m₀` lies in it. -/
theorem multivariateGaussian_equiv_iff (m₀ m₁ : EuclideanSpace ℝ ι)
    {S₀ S₁ : Matrix ι ι ℝ} (hS₀ : S₀.PosSemidef) (hS₁ : S₁.PosSemidef) :
    (multivariateGaussian m₀ S₀ ≪ multivariateGaussian m₁ S₁ ∧
        multivariateGaussian m₁ S₁ ≪ multivariateGaussian m₀ S₀) ↔
      LinearMap.range S₀.toEuclideanLin = LinearMap.range S₁.toEuclideanLin ∧
        m₁ - m₀ ∈ LinearMap.range S₀.toEuclideanLin := by
  rw [← range_toEuclideanLin_sqrt_eq hS₀, ← range_toEuclideanLin_sqrt_eq hS₁]
  simp only [multivariateGaussian, Matrix.toEuclideanCLM_apply]
  let T := (CFC.sqrt S₀).toEuclideanLin
  let V := (CFC.sqrt S₁).toEuclideanLin
  constructor
  · rintro ⟨h₁, h₂⟩
    have hm := sub_mem_range_of_map_stdGaussian_absolutelyContinuous T V m₀ m₁ h₁
    have hn := sub_mem_range_of_map_stdGaussian_absolutelyContinuous V T m₁ m₀ h₂
    have h₃ : m₀ - m₁ ∈ V.range := by simpa only [map_zero, add_zero] using hm 0
    have h₄ : m₁ - m₀ ∈ T.range := by simpa only [map_zero, add_zero] using hn 0
    refine ⟨le_antisymm ?_ ?_, h₄⟩
    · rintro _ ⟨x, rfl⟩
      have h := V.range.sub_mem (hm x) h₃
      convert h using 1; abel
    · rintro _ ⟨x, rfl⟩
      have h := T.range.sub_mem (hn x) h₄
      convert h using 1; abel
  · rintro ⟨h, hm⟩
    refine ⟨map_stdGaussian_absolutelyContinuous_of_range_eq h ?_,
      map_stdGaussian_absolutelyContinuous_of_range_eq h.symm hm⟩
    rw [h] at hm
    simpa only [neg_sub] using V.range.neg_mem hm

end FiniteGaussian

/-! ### Spectral criteria (SYNOPSIS item 36) -/

/-- The stationary covariance `K(h) = ∫ cos⟨h, ω⟩ f(ω) dω` with spectral density `f`. -/
def spectralCov {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  ∫ ξ, Real.cos ⟪h, ξ⟫ * f ξ

lemma spectralCov_def {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : EuclideanSpace ℝ (Fin d)) : spectralCov f h = ∫ ξ, Real.cos ⟪h, ξ⟫ * f ξ := by
  rw [spectralCov]

/-- SYNOPSIS item 36: let `f₀, f₁` be spectral densities on `ℝ^d` with `f₀(ω) ‖ω‖^α` bounded away
from `0` and `∞` for large `‖ω‖` and some `α > 0`, and with
`∫_{‖ω‖ > C} ((f₁ - f₀) / f₀)² < ∞` for some `C`. Then the centred Gaussian laws with the
corresponding stationary covariances are equivalent on every bounded `D ⊆ ℝ^d`. -/
theorem gaussianFieldLaw_equiv_of_spectralDensity {d : ℕ}
    {f₀ f₁ : EuclideanSpace ℝ (Fin d) → ℝ} (hf₀ : ∀ ξ, 0 ≤ f₀ ξ) (hf₁ : ∀ ξ, 0 ≤ f₁ ξ)
    (hi₀ : Integrable f₀) (hi₁ : Integrable f₁) {α : ℝ} (hα : 0 < α)
    (hbd : ∃ c C R : ℝ, 0 < c ∧ ∀ ξ, R ≤ ‖ξ‖ → c ≤ f₀ ξ * ‖ξ‖ ^ α ∧ f₀ ξ * ‖ξ‖ ^ α ≤ C)
    (hint : ∃ C : ℝ,
      IntegrableOn (fun ξ ↦ ((f₁ ξ - f₀ ξ) / f₀ ξ) ^ 2) {ξ | C < ‖ξ‖})
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : Bornology.IsBounded D) :
    gaussianFieldLaw (D := D) 0 (fun s t ↦ spectralCov f₀ ((s : EuclideanSpace ℝ (Fin d)) - t)) ≪
        gaussianFieldLaw (D := D) 0
          (fun s t ↦ spectralCov f₁ ((s : EuclideanSpace ℝ (Fin d)) - t)) ∧
      gaussianFieldLaw (D := D) 0
          (fun s t ↦ spectralCov f₁ ((s : EuclideanSpace ℝ (Fin d)) - t)) ≪
        gaussianFieldLaw (D := D) 0
          (fun s t ↦ spectralCov f₀ ((s : EuclideanSpace ℝ (Fin d)) - t)) := by
  sorry

/-- SYNOPSIS item 36: on an interval `[0, L]`, the centred Gaussian laws with exponential
covariances `σ_i² e^{-α_i |t|}` are equivalent if `σ₀² α₀ = σ₁² α₁` and orthogonal otherwise. -/
theorem gaussianFieldLaw_exponential {L : ℝ} (hL : 0 < L) {σsq₀ σsq₁ α₀ α₁ : ℝ}
    (hσ₀ : 0 < σsq₀) (hσ₁ : 0 < σsq₁) (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) :
    let G : ℝ → ℝ → Measure (Icc 0 L → ℝ) := fun σsq α ↦
      gaussianFieldLaw 0 fun s t ↦ σsq * Real.exp (-α * |(s : ℝ) - t|)
    (σsq₀ * α₀ = σsq₁ * α₁ → G σsq₀ α₀ ≪ G σsq₁ α₁ ∧ G σsq₁ α₁ ≪ G σsq₀ α₀) ∧
      (σsq₀ * α₀ ≠ σsq₁ * α₁ → G σsq₀ α₀ ⟂ₘ G σsq₁ α₁) := by
  sorry

/-! ### Stein's asymptotic optimality (SYNOPSIS item 37) -/

/-- SYNOPSIS item 37, Stein's theorem: let the coordinates `h_1, h_2, …` of `ℕ → ℝ` form a
Gaussian sequence under two equivalent laws `μ₀` and `μ₁`, and let `e_j(ψ, n)` be the error of the
best linear predictor of `ψ` from `h_1, …, h_n` computed under `μ_j`. Uniformly over predictands
`ψ` in the Gaussian space of `μ₀` (the closed affine span of the coordinates in `L²(μ₀)`) with
`E₀ e₀(ψ, n)² > 0`, `E₀ e₁² / E₀ e₀² → 1` and `E₁ e₁² / E₀ e₁² → 1`. A field whose observations
have a dense span in its Gaussian space reduces to this case. -/
theorem stein_asymptotic_efficiency {μ₀ μ₁ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] (h₀ : IsGaussianProcess (fun i (x : ℕ → ℝ) ↦ x i) μ₀)
    (h₁ : IsGaussianProcess (fun i (x : ℕ → ℝ) ↦ x i) μ₁) (hequiv : μ₀ ≪ μ₁ ∧ μ₁ ≪ μ₀) :
    let H : Set ((ℕ → ℝ) → ℝ) := {ψ | MemLp ψ 2 μ₀ ∧ ∀ ε > 0, ∃ (n : ℕ) (a : ℝ)
      (c : Fin n → ℝ), ∫ x, (ψ x - a - ∑ i, c i * x i) ^ 2 ∂μ₀ < ε}
    let e₀ : ℕ → ((ℕ → ℝ) → ℝ) → (ℕ → ℝ) → ℝ := fun n ψ ↦
      predictionError μ₀ (fun (i : Fin n) (x : ℕ → ℝ) ↦ x i) ψ
    let e₁ : ℕ → ((ℕ → ℝ) → ℝ) → (ℕ → ℝ) → ℝ := fun n ψ ↦
      predictionError μ₁ (fun (i : Fin n) (x : ℕ → ℝ) ↦ x i) ψ
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ ψ ∈ H, 0 < ∫ x, e₀ n ψ x ^ 2 ∂μ₀ →
      |(∫ x, e₁ n ψ x ^ 2 ∂μ₀) / (∫ x, e₀ n ψ x ^ 2 ∂μ₀) - 1| ≤ ε ∧
        |(∫ x, e₁ n ψ x ^ 2 ∂μ₁) / (∫ x, e₁ n ψ x ^ 2 ∂μ₀) - 1| ≤ ε := by
  sorry

/-- SYNOPSIS item 37 for universal kriging: let `G_T(0, K₀) ≡ G_T(0, K₁)` for centred Gaussian
residual fields, let `x₁, x₂, …` be a design for which unbiased predictors of `Z(x₀)` eventually
exist and `0 < E₀ e₀(x₀, n)² → 0`, and let `e_j(x₀, n)` be the error of the best linear
unbiased predictor from `x₁, …, x_n` computed under `K_j`. Then `E₀ e₁² / E₀ e₀² → 1` and
`E₁ e₁² / E₀ e₁² → 1`. The errors of unbiased predictors do not depend on `β`. -/
theorem stein_asymptotic_efficiency_universalKriging {T : Type*} {K₀ K₁ : T → T → ℝ}
    (hK₀ : (Matrix.of K₀).PosSemidef) (hK₁ : (Matrix.of K₁).PosSemidef)
    (hequiv : gaussianFieldLaw 0 K₀ ≪ gaussianFieldLaw 0 K₁ ∧
      gaussianFieldLaw 0 K₁ ≪ gaussianFieldLaw 0 K₀)
    {p : ℕ} (f : T → Fin p → ℝ) (x : ℕ → T) (x₀ : T)
    (hunb : ∀ᶠ n in atTop, ∃ w, (designMatrix f fun i : Fin n ↦ x i)ᵀ *ᵥ w = f x₀) :
    let μ : Fin 2 → Measure (T → ℝ) := ![gaussianFieldLaw 0 K₀, gaussianFieldLaw 0 K₁]
    let e : Fin 2 → ℕ → (T → ℝ) → ℝ := fun j n z ↦ z x₀ - ∑ i : Fin n,
      blupWeights (μ j) (fun t (z : T → ℝ) ↦ z t) f (fun i : Fin n ↦ x i) x₀ i * z (x i)
    (∀ᶠ n in atTop, 0 < ∫ z, e 0 n z ^ 2 ∂μ 0) →
    Tendsto (fun n ↦ ∫ z, e 0 n z ^ 2 ∂μ 0) atTop (𝓝 0) →
    Tendsto (fun n ↦ (∫ z, e 1 n z ^ 2 ∂μ 0) / ∫ z, e 0 n z ^ 2 ∂μ 0) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ (∫ z, e 1 n z ^ 2 ∂μ 1) / ∫ z, e 1 n z ^ 2 ∂μ 0) atTop (𝓝 1) := by
  sorry

/-! ### Microergodicity (SYNOPSIS item 39) -/

/-- A function `h` of the parameter of a family of laws `P θ` is **microergodic** when
`h θ ≠ h θ'` implies that `P θ` and `P θ'` are orthogonal. -/
def IsMicroergodic {Θ α : Type*} (P : Θ → Measure Ω) (h : Θ → α) : Prop :=
  ∀ θ θ', h θ ≠ h θ' → P θ ⟂ₘ P θ'

lemma isMicroergodic_def {Θ α : Type*} {P : Θ → Measure Ω} {h : Θ → α} :
    IsMicroergodic P h ↔ ∀ θ θ', h θ ≠ h θ' → P θ ⟂ₘ P θ' := Iff.rfl

-- Keep the estimator measurability hypothesis in the existing interface.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 39: if `P θ₀ ≡ P θ₁` and `h θ₀ ≠ h θ₁`, no sequence of estimators is weakly
consistent for `h` at both `θ₀` and `θ₁`. -/
theorem not_consistent_of_equiv {Θ α : Type*} [MetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (h : Θ → α) {θ₀ θ₁ : Θ} (hequiv : P θ₀ ≪ P θ₁ ∧ P θ₁ ≪ P θ₀) (hne : h θ₀ ≠ h θ₁)
    (est : ℕ → Ω → α) (hm : ∀ n, Measurable (est n)) :
    ¬ (TendstoInMeasure (P θ₀) est atTop (fun _ ↦ h θ₀) ∧
      TendstoInMeasure (P θ₁) est atTop (fun _ ↦ h θ₁)) := by
  rintro ⟨h₀, h₁⟩
  obtain ⟨ns, hns, hae₀⟩ := h₀.exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae₁⟩ := (h₁.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hae : ∀ᵐ ω ∂P θ₁, h θ₀ = h θ₁ := by
    filter_upwards [hequiv.2.ae_le hae₀, hae₁] with ω hω₀ hω₁
    exact tendsto_nhds_unique (hω₀.comp hms.tendsto_atTop) hω₁
  obtain ⟨_, heq⟩ := hae.exists
  exact hne heq

/-- A uniform second-derivative bound controls a centered second difference. -/
lemma abs_second_difference_le_of_iteratedDerivWithin_bound {f : ℝ → ℝ} {a b M x h : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioc a b))
    (hM : ∀ y ∈ Ioc a b, |iteratedDerivWithin 2 f (Ioc a b) y| ≤ M)
    (hh : 0 ≤ h) (ha : a < x - h) (hb : x + h ≤ b) :
    |f (x + h) - 2 * f x + f (x - h)| ≤ 2 * M * h ^ 2 := by
  let s := Ioc a b
  let t := Icc (x - h) (x + h)
  have ht : t ⊆ s := fun _ hy ↦ ⟨ha.trans_le hy.1, hy.2.trans hb⟩
  have hx : x ∈ t := ⟨by linarith only [hh], by linarith only [hh]⟩
  have hx₀ : x - h ∈ t := ⟨le_rfl, by linarith only [hh]⟩
  have hx₁ : x + h ∈ t := ⟨by linarith only [hh], le_rfl⟩
  have hd : DifferentiableOn ℝ f s := hf.differentiableOn (by norm_num)
  have hd₂ : DifferentiableOn ℝ (derivWithin f s) s := by
    have h₁ := (contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
      (n := 1) (uniqueDiffOn_Ioc a b)).mp hf
    rw [iteratedDerivWithin_one] at h₁
    exact h₁.2.differentiableOn (by norm_num)
  have hbound (y : ℝ) (hy : y ∈ s) : ‖derivWithin (derivWithin f s) s y‖ ≤ M := by
    simpa only [iteratedDerivWithin_succ, iteratedDerivWithin_one, iteratedDerivWithin_zero,
      Real.norm_eq_abs] using hM y hy
  let d := derivWithin f s x
  let g (y : ℝ) := f y - d * y
  have hgd (y : ℝ) (hy : y ∈ t) : HasDerivWithinAt g (derivWithin f s y - d) t y := by
    have hlin : HasDerivWithinAt (fun z : ℝ ↦ d * z) d t y := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id y).const_mul d).hasDerivWithinAt
        (s := t))
    exact ((hd y (ht hy)).hasDerivWithinAt.mono ht).sub hlin
  have hgb (y : ℝ) (hy : y ∈ t) : ‖derivWithin f s y - d‖ ≤ M * h := by
    have hm := hbound x (ht hx)
    have hM₀ : 0 ≤ M := (norm_nonneg _).trans hm
    have hbnd := Convex.norm_image_sub_le_of_norm_derivWithin_le hd₂ hbound
      (convex_Ioc a b) (ht hx) (ht hy)
    refine hbnd.trans (mul_le_mul_of_nonneg_left ?_ hM₀)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  have hplus := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hgd hgb
    (convex_Icc (x - h) (x + h)) hx hx₁
  have hminus := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hgd hgb
    (convex_Icc (x - h) (x + h)) hx₀ hx
  have hstep₁ : x + h - x = h := by ring
  have hstep₂ : x - (x - h) = h := by ring
  simp only [hstep₁, Real.norm_eq_abs, abs_of_nonneg hh] at hplus
  simp only [hstep₂, Real.norm_eq_abs, abs_of_nonneg hh] at hminus
  have he : f (x + h) - 2 * f x + f (x - h) =
      (g (x + h) - g x) - (g x - g (x - h)) := by
    dsimp only [g]
    ring
  rw [he]
  calc
    _ ≤ |g (x + h) - g x| + |g x - g (x - h)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (g (x + h) - g x) (g x - g (x - h))
    _ ≤ _ := by nlinarith only [hplus, hminus]


variable {P : Measure Ω}

/-- A real Gaussian variable has a square-integrable square, including at zero variance. -/
lemma memLp_sq_of_hasGaussianLaw {X : Ω → ℝ} (hX : HasGaussianLaw X P) :
    MemLp (fun ω ↦ X ω ^ 2) 2 P := by
  have h4 : MemLp X 4 P := by
    let := hX.isGaussian_map
    exact (memLp_map_measure_iff (g := id) measurable_id.aestronglyMeasurable hX.aemeasurable).1
      (IsGaussian.memLp_id _ 4 (by norm_num))
  refine (memLp_two_iff_integrable_sq (hX.aemeasurable.aestronglyMeasurable.pow 2)).2 ?_
  have h := h4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  convert h using 1
  funext ω
  simp only [Pi.pow_apply, ← pow_mul, Nat.reduceMul, Real.norm_eq_abs, ← abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ X ω ^ 4)]

/-- For a centered Gaussian vector, the covariance of two squared coordinates is twice the
squared covariance of the coordinates by Isserlis' formula. -/
lemma covariance_sq_sq_of_hasGaussianLaw {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (hX : HasGaussianLaw (fun ω i ↦ X i ω) P) (h0 : ∀ i, P[X i] = 0)
    (i j : ι) : cov[fun ω ↦ X i ω ^ 2, fun ω ↦ X j ω ^ 2; P] =
      2 * cov[X i, X j; P] ^ 2 := by
  let := hX.isProbabilityMeasure
  let G (ω : Ω) (i : ι) := X i ω
  let μ := P.map G
  let L (k : ι) : StrongDual ℝ (ι → ℝ) := ContinuousLinearMap.proj k
  let : IsGaussian μ := hX.isGaussian_map
  have hG : HasLaw G μ P := hasLaw_map hX.aemeasurable
  have hmean (k : ι) : L k (μ[id]) = 0 := by
    rw [← (L k).integral_comp_comm (IsGaussian.integrable_id (μ := μ))]
    simp only [id_eq]
    rw [← hG.integral_comp ((L k).continuous.measurable.aestronglyMeasurable)]
    exact h0 k
  have hcov (k l : ι) : covarianceBilinDual μ (L k) (L l) = cov[X k, X l; P] := by
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      ← hG.covariance_fun_comp (by fun_prop) (by fun_prop)]
    rfl
  have hwick := IsGaussian.integral_mul_mul_mul_sub_dual μ (L i) (L i) (L j) (L j)
  simp_rw [map_sub, hmean, sub_zero, hcov] at hwick
  have hm (k : ι) : (∫ ω, X k ω ^ 2 ∂P) = cov[X k, X k; P] := by
    rw [covariance_eq_sub (hX.eval k).memLp_two (hX.eval k).memLp_two,
      h0 k, zero_mul, sub_zero]
    congr 1
    funext ω
    exact pow_two _
  rw [covariance_eq_sub (memLp_sq_of_hasGaussianLaw (hX.eval i))
    (memLp_sq_of_hasGaussianLaw (hX.eval j)), hm, hm]
  have hf : AEStronglyMeasurable (fun u ↦ L i u * L i u * L j u * L j u) μ := by fun_prop
  rw [← hG.integral_comp hf] at hwick
  have he : (fun ω ↦ X i ω ^ 2 * X j ω ^ 2) =
      (fun u ↦ L i u * L i u * L j u * L j u) ∘ G := by
    funext ω
    change X i ω ^ 2 * X j ω ^ 2 = X i ω * X i ω * X j ω * X j ω
    ring
  simp only [Pi.mul_apply]
  rw [he, hwick]
  ring


/-- Second-order stationarity expresses any covariance as a function of the lag. -/
lemma covariance_eq_stationaryCov_sub [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) (x y : ℝ) :
    cov[Z x, Z y; P] = stationaryCov Z P (x - y) := by
  rw [stationaryCov_def]
  simpa only [sub_add_cancel, zero_add] using
    ((isSecondOrderStationary_iff.mp hZ).2.2 (x - y) 0 y)

/-- The increment on the (i)-th interval of the uniform mesh of ([0,1]). -/
def gridIncrement (Z : ℝ → Ω → ℝ) (n : ℕ) (i : Fin n) (ω : Ω) : ℝ :=
  Z (((i.val : ℝ) + 1) / n) ω - Z ((i.val : ℝ) / n) ω

omit [MeasurableSpace Ω] in
/-- The coordinate formula for an increment on the uniform grid. -/
lemma gridIncrement_def (Z : ℝ → Ω → ℝ) (n : ℕ) (i : Fin n) :
    gridIncrement Z n i = fun ω ↦ Z (((i.val : ℝ) + 1) / n) ω - Z ((i.val : ℝ) / n) ω := by
  funext ω
  rw [gridIncrement]

/-- The vector of increments on a uniform mesh of a Gaussian process is Gaussian. -/
lemma hasGaussianLaw_gridIncrement {Z : ℝ → Ω → ℝ} (hZ : IsGaussianProcess Z P) (n : ℕ) :
    HasGaussianLaw (fun ω (i : Fin n) ↦ gridIncrement Z n i ω) P := by
  let t (i : Fin (n + 1)) : ℝ := (i.val : ℝ) / n
  simpa only [gridIncrement_def, t, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
    Nat.cast_one] using
    hZ.hasGaussianLaw_increments (t := t)

/-- The covariance of two uniform-mesh increments is a centered second difference. -/
lemma covariance_gridIncrement [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) {n : ℕ} (i j : Fin n) :
    cov[gridIncrement Z n i, gridIncrement Z n j; P] =
      2 * stationaryCov Z P (((i.val : ℝ) - j.val) / n) -
        stationaryCov Z P (((i.val : ℝ) - j.val) / n + 1 / n) -
        stationaryCov Z P (((i.val : ℝ) - j.val) / n - 1 / n) := by
  have hL (x : ℝ) : MemLp (Z x) 2 P :=
    isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 x
  simp only [gridIncrement_def]
  rw [covariance_fun_sub_fun_sub (hL _) (hL _) (hL _) (hL _)]
  simp_rw [covariance_eq_stationaryCov_sub hZ]
  have h₀ : ((i.val : ℝ) + 1) / n - ((j.val : ℝ) + 1) / n =
      ((i.val : ℝ) - j.val) / n := by ring
  have h₁ : ((i.val : ℝ) + 1) / n - (j.val : ℝ) / n =
      ((i.val : ℝ) - j.val) / n + 1 / n := by ring
  have h₂ : (i.val : ℝ) / n - ((j.val : ℝ) + 1) / n =
      ((i.val : ℝ) - j.val) / n - 1 / n := by ring
  have h₃ : (i.val : ℝ) / n - (j.val : ℝ) / n = ((i.val : ℝ) - j.val) / n := by ring
  rw [h₀, h₁, h₂, h₃]
  ring

/-- Each increment has variance twice the covariance drop at the mesh spacing. -/
lemma variance_gridIncrement [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) {n : ℕ} (i : Fin n) :
    Var[gridIncrement Z n i; P] =
      2 * (stationaryCov Z P 0 - stationaryCov Z P (1 / n)) := by
  have hL (x : ℝ) : MemLp (Z x) 2 P :=
    isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 x
  simp only [gridIncrement_def, variance_fun_sub (hL _) (hL _),
    ← covariance_self (hL _).aemeasurable, covariance_eq_stationaryCov_sub hZ, sub_self]
  have he : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = 1 / n := by ring
  rw [he]
  ring

/-- The equal marginal variances of the increments bound every absolute covariance. -/
lemma abs_covariance_gridIncrement_le [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) {n : ℕ} (i j : Fin n) :
    |cov[gridIncrement Z n i, gridIncrement Z n j; P]| ≤
      2 * (stationaryCov Z P 0 - stationaryCov Z P (1 / n)) := by
  have hL (x : ℝ) : MemLp (Z x) 2 P :=
    isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 x
  have hI (k : Fin n) : MemLp (gridIncrement Z n k) 2 P := (hL _).sub (hL _)
  have ha := variance_nonneg (gridIncrement Z n i + gridIncrement Z n j) P
  have hs := variance_nonneg (gridIncrement Z n i - gridIncrement Z n j) P
  rw [variance_add (hI i) (hI j), variance_gridIncrement hZ, variance_gridIncrement hZ] at ha
  rw [variance_sub (hI i) (hI j), variance_gridIncrement hZ, variance_gridIncrement hZ] at hs
  exact abs_le.mpr ⟨by linarith only [ha], by linarith only [hs]⟩


/-- Beyond adjacent mesh intervals, a second-derivative bound controls the covariance. -/
lemma abs_covariance_gridIncrement_le_of_gap [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) {M : ℝ}
    (hf : ContDiffOn ℝ 2 (stationaryCov Z P) (Ioc 0 1))
    (hM : ∀ x ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 (stationaryCov Z P) (Ioc 0 1) x| ≤ M)
    {n : ℕ} {i j : Fin n} (hij : j.val + 1 < i.val) :
    |cov[gridIncrement Z n i, gridIncrement Z n j; P]| ≤ 2 * M * (1 / (n : ℝ)) ^ 2 := by
  let f := stationaryCov Z P
  let δ : ℝ := 1 / n
  let x : ℝ := ((i.val : ℝ) - j.val) / n
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hle : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hlt : (j.val : ℝ) + 1 < i.val := by exact_mod_cast hij
  have hx₀ : 0 < x - δ := by
    dsimp only [x, δ]
    rw [← sub_div]
    exact div_pos (by linarith only [hlt]) hn
  have hx₁ : x + δ ≤ 1 := by
    dsimp only [x, δ]
    rw [← add_div, div_le_one hn]
    have hz : 0 ≤ (j.val : ℝ) := by positivity
    linarith only [hle, hz]
  rw [covariance_gridIncrement hZ]
  -- Negation puts the covariance in the order of the centered second difference.
  change |2 * f x - f (x + δ) - f (x - δ)| ≤ 2 * M * δ ^ 2
  have he : 2 * f x - f (x + δ) - f (x - δ) = -(f (x + δ) - 2 * f x + f (x - δ)) := by ring
  rw [he, abs_neg]
  exact abs_second_difference_le_of_iteratedDerivWithin_bound hf hM (by positivity) hx₀ hx₁

/-- Each uniform mesh interval has at most three intervals within one index step. -/
lemma card_filter_near_grid {n : ℕ} (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter
      fun j ↦ j.val ≤ i.val + 1 ∧ i.val ≤ j.val + 1).card ≤ 3 := by
  let S := (Finset.univ : Finset (Fin n)).filter
    fun j ↦ j.val ≤ i.val + 1 ∧ i.val ≤ j.val + 1
  have hc : S.card ≤ (Finset.Icc (i.val - 1) (i.val + 1)).card := by
    refine Finset.card_le_card_of_injOn Fin.val ?_ Fin.val_injective.injOn
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_Icc.mpr ⟨by omega, hj'.1⟩
  rw [Nat.card_Icc] at hc
  exact hc.trans (by omega)

/-- The sum of squared covariances separates the nearby and separated grid intervals. -/
lemma sum_covariance_gridIncrement_sq_le [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) {M : ℝ}
    (hf : ContDiffOn ℝ 2 (stationaryCov Z P) (Ioc 0 1))
    (hM : ∀ x ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 (stationaryCov Z P) (Ioc 0 1) x| ≤ M)
    (n : ℕ) :
    ∑ i : Fin n, ∑ j : Fin n, cov[gridIncrement Z n i, gridIncrement Z n j; P] ^ 2 ≤
      3 * n * (2 * (stationaryCov Z P 0 - stationaryCov Z P (1 / n))) ^ 2 +
        n ^ 2 * (2 * M * (1 / (n : ℝ)) ^ 2) ^ 2 := by
  let b := (2 * (stationaryCov Z P 0 - stationaryCov Z P (1 / n))) ^ 2
  let e := (2 * M * (1 / (n : ℝ)) ^ 2) ^ 2
  let near (i j : Fin n) := j.val ≤ i.val + 1 ∧ i.val ≤ j.val + 1
  have hs (i j : Fin n) :
      cov[gridIncrement Z n i, gridIncrement Z n j; P] ^ 2 ≤
        (if near i j then b else 0) + e := by
    classical
    by_cases hij : near i j
    · rw [ite_eq_left hij]
      have h := abs_covariance_gridIncrement_le hZ i j
      dsimp only [b, e]
      nlinarith only [h, sq_abs (cov[gridIncrement Z n i, gridIncrement Z n j; P]),
        sq_nonneg (2 * M * (1 / (n : ℝ)) ^ 2),
        abs_nonneg (cov[gridIncrement Z n i, gridIncrement Z n j; P])]
    · rw [ite_eq_right hij, zero_add]
      have h : |cov[gridIncrement Z n i, gridIncrement Z n j; P]| ≤ 2 * M * (1 / (n : ℝ)) ^ 2 := by
        by_cases hh : j.val + 1 < i.val
        · exact abs_covariance_gridIncrement_le_of_gap hZ hf hM hh
        · rw [covariance_comm]
          exact abs_covariance_gridIncrement_le_of_gap hZ hf hM (by dsimp only [near] at hij; omega)
      dsimp only [e]
      nlinarith only [h, sq_abs (cov[gridIncrement Z n i, gridIncrement Z n j; P]),
        abs_nonneg (cov[gridIncrement Z n i, gridIncrement Z n j; P])]
  classical
  have hr (i : Fin n) : (∑ j : Fin n, ((if near i j then b else 0) + e)) ≤ 3 * b + n * e := by
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    gcongr
    exact_mod_cast card_filter_near_grid i
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ((if near i j then b else 0) + e) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hs i j
    _ ≤ ∑ _i : Fin n, (3 * b + n * e) := Finset.sum_le_sum fun i _ ↦ hr i
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [b, e]
      ring

/-- A linear cusp at zero determines the limit of the scaled covariance drop. -/
lemma tendsto_nat_mul_covariance_drop {f : ℝ → ℝ} {C D : ℝ}
    (hf : (fun t ↦ f t - (C - D * |t|)) =o[𝓝 0] fun t ↦ t) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (f 0 - f (1 / n))) atTop (𝓝 D) := by
  have h0 : ‖f 0 - C‖ ≤ 0 := by
    simpa only [Set.mem_ofPred_eq, norm_zero, abs_zero, mul_zero, sub_zero] using
      mem_of_mem_nhds (hf.bound (by norm_num : (0 : ℝ) < 1))
  have hC : f 0 = C := sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  have ht : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hrem := (hf.tendsto_div_nhds_zero.comp ht)
  have h := (tendsto_const_nhds (x := D)).sub hrem
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [Function.comp_apply, hC, abs_of_pos (one_div_pos.mpr hn')]
  field_simp
  ring


omit [MeasurableSpace Ω] in
/-- Half the sum of squared increments on the uniform mesh of the unit interval. -/
def halfQuadraticVariation (Z : ℝ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ (1 / 2) * ∑ i : Fin n, gridIncrement Z n i ω ^ 2

omit [MeasurableSpace Ω] in
/-- The sum defining half the quadratic variation. -/
lemma halfQuadraticVariation_def (Z : ℝ → Ω → ℝ) (n : ℕ) :
    halfQuadraticVariation Z n = fun ω ↦ (1 / 2) * ∑ i : Fin n, gridIncrement Z n i ω ^ 2 := by
  funext ω
  rw [halfQuadraticVariation]

/-- The centered process has centered increments. -/
lemma integral_gridIncrement_eq_zero [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (h0 : ∀ t, P[Z t] = 0) {n : ℕ} (i : Fin n) :
    P[gridIncrement Z n i] = 0 := by
  have hI (t : ℝ) : Integrable (Z t) P :=
    (hZ.hasGaussianLaw_eval t).memLp_two.integrable (by norm_num)
  rw [gridIncrement_def, integral_sub (hI _) (hI _), h0, h0, sub_self]

/-- Half the quadratic variation is square integrable. -/
lemma memLp_halfQuadraticVariation {Z : ℝ → Ω → ℝ} (hZ : IsGaussianProcess Z P) (n : ℕ) :
    MemLp (halfQuadraticVariation Z n) 2 P := by
  rw [halfQuadraticVariation_def]
  exact (memLp_finsetSum _ fun i _ ↦
    memLp_sq_of_hasGaussianLaw ((hasGaussianLaw_gridIncrement hZ n).eval i)).const_mul _

/-- The mean quadratic variation is the number of intervals times the covariance drop. -/
lemma integral_halfQuadraticVariation [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (hS : IsSecondOrderStationary Z P)
    (h0 : ∀ t, P[Z t] = 0) (n : ℕ) :
    P[halfQuadraticVariation Z n] =
      n * (stationaryCov Z P 0 - stationaryCov Z P (1 / n)) := by
  let X := gridIncrement Z n
  have hG := hasGaussianLaw_gridIncrement hZ n
  have he (i : Fin n) : (∫ ω, X i ω ^ 2 ∂P) =
      2 * (stationaryCov Z P 0 - stationaryCov Z P (1 / n)) := by
    have h := variance_eq_sub (hG.eval i).memLp_two
    rw [variance_gridIncrement hS, integral_gridIncrement_eq_zero hZ h0 i] at h
    simpa only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using h.symm
  have hi (i : Fin n) : Integrable (fun ω ↦ X i ω ^ 2) P :=
    (memLp_sq_of_hasGaussianLaw (hG.eval i)).integrable (by norm_num)
  rw [halfQuadraticVariation_def, integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Its variance is half the sum of the squared covariances of the increments. -/
lemma variance_halfQuadraticVariation [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (h0 : ∀ t, P[Z t] = 0) (n : ℕ) :
    Var[halfQuadraticVariation Z n; P] =
      (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, cov[gridIncrement Z n i, gridIncrement Z n j; P] ^ 2 := by
  have hG := hasGaussianLaw_gridIncrement hZ n
  rw [halfQuadraticVariation_def, variance_const_mul, variance_fun_sum (fun i ↦
    memLp_sq_of_hasGaussianLaw (hG.eval i))]
  simp_rw [covariance_sq_sq_of_hasGaussianLaw hG (integral_gridIncrement_eq_zero hZ h0),
    ← Finset.mul_sum]
  ring

/-- The covariance-sum bound vanishes when the scaled covariance drop has a finite limit. -/
lemma tendsto_variance_halfQuadraticVariation [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (hS : IsSecondOrderStationary Z P)
    (h0 : ∀ t, P[Z t] = 0) {D M : ℝ}
    (hf : ContDiffOn ℝ 2 (stationaryCov Z P) (Ioc 0 1))
    (hM : ∀ x ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 (stationaryCov Z P) (Ioc 0 1) x| ≤ M)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) * (stationaryCov Z P 0 - stationaryCov Z P (1 / n)))
      atTop (𝓝 D)) :
    Tendsto (fun n ↦ Var[halfQuadraticVariation Z n; P]) atTop (𝓝 0) := by
  let a (n : ℕ) := stationaryCov Z P 0 - stationaryCov Z P (1 / n)
  let b (n : ℕ) := 6 * ((n : ℝ) * a n) ^ 2 * (1 / (n : ℝ)) + 2 * M ^ 2 * (1 / (n : ℝ)) ^ 2
  have hz : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [a, b, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
      (((h.pow 2).const_mul 6).mul hz).add ((hz.pow 2).const_mul (2 * M ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun n ↦ variance_nonneg (halfQuadraticVariation Z n) P) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [variance_halfQuadraticVariation hZ h0]
  refine (mul_le_mul_of_nonneg_left (sum_covariance_gridIncrement_sq_le hS hf hM n)
    (by norm_num)).trans ?_
  apply le_of_eq
  dsimp only [b, a]
  field_simp [hn']
  ring

/-- Mean-square error is the variance plus the squared bias. -/
lemma integral_sq_sub_eq_variance_add_bias [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) (a : ℝ) :
    (∫ ω, (X ω - a) ^ 2 ∂P) = Var[X; P] + (P[X] - a) ^ 2 := by
  have he : Var[fun ω ↦ X ω - a; P] =
      (∫ ω, (X ω - a) ^ 2 ∂P) - (∫ ω, (X ω - a) ∂P) ^ 2 := by
    have h := variance_eq_sub (hX.sub (memLp_const a))
    have hfun : X - (fun _ : Ω ↦ a) = (fun ω ↦ X ω - a) := rfl
    rw [hfun] at h
    simpa only [Pi.pow_apply] using h
  rw [variance_sub_const hX.aestronglyMeasurable, integral_sub (hX.integrable (by norm_num))
    (integrable_const _), integral_const, probReal_univ, one_smul] at he
  linarith only [he]

set_option linter.unusedVariables false in
/-- SYNOPSIS item 39: for a centred stationary Gaussian process on `[0, 1]` whose autocovariance
satisfies `K(t) = C - D|t| + o(|t|)` near `0` with `D > 0` and has a bounded second derivative on
`(0, 1]`, the halved quadratic variations `U_n = ½ ∑_{j ≤ n} (Z(j/n) - Z((j-1)/n))²` converge to
`D` in `L²`. -/
theorem tendsto_quadraticVariation {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (hstat : IsSecondOrderStationary Z P) (hc : ∀ t, P[Z t] = 0)
    {C D : ℝ} (hD : 0 < D)
    (hK : (fun t ↦ stationaryCov Z P t - (C - D * |t|)) =o[𝓝 0] fun t ↦ t)
    (hK2 : ContDiffOn ℝ 2 (stationaryCov Z P) (Ioc 0 1))
    (hK2b : ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 (stationaryCov Z P) (Ioc 0 1) t| ≤ M) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ((1 / 2) * ∑ j ∈ Finset.range n,
      (Z ((j + 1) / n) ω - Z (j / n) ω) ^ 2 - D) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hK2b
  have hm := tendsto_nat_mul_covariance_drop hK
  have hv := tendsto_variance_halfQuadraticVariation hZ hstat hc hK2 hM hm
  have hb : Tendsto (fun n ↦ (P[halfQuadraticVariation Z n] - D) ^ 2) atTop (𝓝 0) := by
    simp_rw [integral_halfQuadraticVariation hZ hstat hc]
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      (hm.sub (tendsto_const_nhds (x := D))).pow 2
  have h := hv.add hb
  simp only [add_zero] at h
  refine h.congr (fun n ↦ ?_)
  rw [← integral_sq_sub_eq_variance_add_bias (memLp_halfQuadraticVariation hZ n) D,
    halfQuadraticVariation_def]
  congr 1
  funext ω
  simp only [gridIncrement_def, ← Fin.sum_univ_eq_sum_range]


/-- Restricting the coordinate index set restricts the mean and covariance of a Gaussian law. -/
lemma gaussianFieldLaw_map_subtype_val {T : Type*} (D : Set T) (m : T → ℝ)
    {K : T → T → ℝ} (hK : (Matrix.of K).PosSemidef) :
    (gaussianFieldLaw m K).map (fun z : T → ℝ ↦ fun t : D ↦ z t) =
      gaussianFieldLaw (fun t : D ↦ m t) (fun s t : D ↦ K s t) := by
  have h₀ := gaussianFieldLaw_spec m hK
  have hK' : (Matrix.of fun s t : D ↦ K s t).PosSemidef := hK.submatrix Subtype.val
  have h₁ := gaussianFieldLaw_spec (fun t : D ↦ m t) hK'
  have hG₀ : IsGaussianProcess (fun (t : D) (z : T → ℝ) ↦ z t) (gaussianFieldLaw m K) :=
    h₀.2.1.comp_right Subtype.val
  have h := map_eq_of_isGaussianProcess (fun (t : D) ↦ measurable_pi_apply (t : T))
    (fun (t : D) ↦ measurable_pi_apply t) hG₀ h₁.2.1
    (fun t ↦ (h₀.2.2.1 t).trans (h₁.2.2.1 t).symm)
    (fun s t ↦ (h₀.2.2.2 s t).trans (h₁.2.2.2 s t).symm)
  -- The coordinate map from the restricted path space to itself is the identity.
  change _ = (gaussianFieldLaw (fun t : D ↦ m t) (fun s t : D ↦ K s t)).map id at h
  rwa [Measure.map_id] at h

/-- Distinct limits in measure of the same sequence of measurable statistics separate the laws. -/
lemma mutuallySingular_of_tendstoInMeasure_const_ne {P₀ P₁ : Measure Ω}
    [IsFiniteMeasure P₀] [IsFiniteMeasure P₁] {d₀ d₁ : ℝ} (hne : d₀ ≠ d₁)
    {f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n))
    (h₀ : TendstoInMeasure P₀ f atTop (fun _ ↦ d₀))
    (h₁ : TendstoInMeasure P₁ f atTop (fun _ ↦ d₁)) : P₀ ⟂ₘ P₁ := by
  obtain ⟨ns, hns, h₀'⟩ := h₀.exists_seq_tendsto_ae
  obtain ⟨ms, hms, h₁'⟩ := (h₁.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  let A := {z | Tendsto (fun k ↦ f (ns (ms k)) z) atTop (𝓝 d₀)}
  have hA : MeasurableSet A := measurableSet_tendsto _ (fun k ↦ hf (ns (ms k)))
  have hP₀ : ∀ᵐ z ∂P₀, z ∈ A := by
    filter_upwards [h₀'] with z hz
    exact hz.comp hms.tendsto_atTop
  have hP₁ : ∀ᵐ z ∂P₁, z ∉ A := by
    filter_upwards [h₁'] with z hz hc
    exact hne (tendsto_nhds_unique hc hz)
  refine ⟨Aᶜ, hA.compl, ae_iff.mp hP₀, ?_⟩
  have hset : {z | ¬ z ∉ A} = A := by ext z; simp
  rw [compl_compl, ← hset]
  exact ae_iff.mp hP₁

/-- Square-mean convergence of real statistics implies convergence in measure to the same
constant. -/
lemma tendstoInMeasure_const_of_tendsto_integral_sq {f : ℕ → Ω → ℝ} {c : ℝ}
    (hLp : ∀ n, MemLp (fun ω ↦ f n ω - c) 2 P)
    (h : Tendsto (fun n ↦ ∫ ω, (f n ω - c) ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (h.div_const (ε ^ 2))
  simp only [zero_div, ENNReal.ofReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) (fun n ↦ ?_)
  have hY : Integrable (fun ω ↦ ‖f n ω - c‖ ^ 2) P := by
    simpa only [Real.norm_eq_abs, sq_abs] using (hLp n).integrable_sq
  simpa only [Function.comp_apply, Real.norm_eq_abs, sq_abs] using
    TauCeti.meas_ge_le_integral_norm_sq_div_sq hY hε

/-- A uniform grid point viewed as a point of the closed unit interval. -/
def unitIntervalGridPoint (n : ℕ) (i : Fin (n + 1)) : Icc (0 : ℝ) 1 :=
  ⟨(i.val : ℝ) / n, by
    refine ⟨by positivity, ?_⟩
    by_cases hn : n = 0
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast Nat.le_of_lt_succ i.isLt⟩

/-- Real coordinate of the embedded uniform grid point. -/
lemma coe_unitIntervalGridPoint (n : ℕ) (i : Fin (n + 1)) :
    (unitIntervalGridPoint n i : ℝ) = (i.val : ℝ) / n := by
  rw [unitIntervalGridPoint]

/-- Half the quadratic variation as an observable on the unit-interval path space. -/
def halfQuadraticVariationOnUnitInterval (n : ℕ) (z : Icc (0 : ℝ) 1 → ℝ) : ℝ :=
  (1 / 2) * ∑ i : Fin n,
    (z (unitIntervalGridPoint n i.succ) - z (unitIntervalGridPoint n i.castSucc)) ^ 2

/-- The sum formula for the quadratic variation of a path on the closed unit interval. -/
lemma halfQuadraticVariationOnUnitInterval_def (n : ℕ) (z : Icc (0 : ℝ) 1 → ℝ) :
    halfQuadraticVariationOnUnitInterval n z =
      (1 / 2) * ∑ i : Fin n,
        (z (unitIntervalGridPoint n i.succ) - z (unitIntervalGridPoint n i.castSucc)) ^ 2 := by
  rw [halfQuadraticVariationOnUnitInterval]

/-- The quadratic variation on path space is a measurable function of finitely many
coordinates. -/
lemma measurable_halfQuadraticVariationOnUnitInterval (n : ℕ) :
    Measurable (halfQuadraticVariationOnUnitInterval n) := by
  unfold halfQuadraticVariationOnUnitInterval
  fun_prop

/-- The restriction of a path to the unit interval preserves the uniform-grid statistic. -/
lemma halfQuadraticVariationOnUnitInterval_comp (n : ℕ) (z : ℝ → ℝ) :
    halfQuadraticVariationOnUnitInterval n (fun t ↦ z t) =
      halfQuadraticVariation (fun t (z : ℝ → ℝ) ↦ z t) n z := by
  simp only [halfQuadraticVariationOnUnitInterval, halfQuadraticVariation_def, gridIncrement_def,
    coe_unitIntervalGridPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.val_castSucc]

/-- The variance cusp of a centered Gaussian law is the limit in measure of its uniform-grid
quadratic variation on the interval. -/
lemma tendstoInMeasure_halfQuadraticVariationOnUnitInterval {K : ℝ → ℝ}
    (hK : (Matrix.of fun s t : ℝ ↦ K (s - t)).PosSemidef) {C D : ℝ} (hD : 0 < D)
    (hK0 : (fun t ↦ K t - (C - D * |t|)) =o[𝓝 0] fun t ↦ t)
    (hK2 : ContDiffOn ℝ 2 K (Ioc 0 1))
    (hK2b : ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 K (Ioc 0 1) t| ≤ M) :
    TendstoInMeasure (gaussianFieldLaw (D := Icc (0 : ℝ) 1) 0 (fun s t ↦ K (s - t)))
      halfQuadraticVariationOnUnitInterval atTop (fun _ ↦ D) := by
  let μ := gaussianFieldLaw (D := ℝ) 0 (fun s t ↦ K (s - t))
  let Z (t : ℝ) (z : ℝ → ℝ) := z t
  have hZ : IsGaussianFieldLaw 0 (fun s t : ℝ ↦ K (s - t)) μ := gaussianFieldLaw_spec 0 hK
  have hm (t : ℝ) : μ[Z t] = 0 := hZ.2.2.1 t
  have hc (s t : ℝ) : cov[Z s, Z t; μ] = K (s - t) := hZ.2.2.2 s t
  have hS : IsSecondOrderStationary Z μ := by
    refine isSecondOrderStationary_iff.mpr ⟨isSecondOrderField_iff.mpr
      (fun t ↦ (hZ.2.1.hasGaussianLaw_eval t).memLp_two),
      fun s t ↦ (hm s).trans (hm t).symm, fun s t u ↦ ?_⟩
    rw [hc, hc, add_sub_add_right_eq_sub]
  have he : stationaryCov Z μ = K := by
    funext t
    rw [stationaryCov_def, hc, sub_zero]
  have hr : μ.map (fun (z : ℝ → ℝ) (t : Icc (0 : ℝ) 1) ↦ z t) =
      gaussianFieldLaw (D := Icc (0 : ℝ) 1) 0 (fun s t ↦ K (s - t)) :=
    gaussianFieldLaw_map_subtype_val (Icc (0 : ℝ) 1) 0 hK
  have hmR : Measurable (fun (z : ℝ → ℝ) (t : Icc (0 : ℝ) 1) ↦ z t) :=
    Measurable.of_eval fun t ↦ measurable_pi_apply (t : ℝ)
  have hl := tendsto_quadraticVariation (P := μ) hZ.2.1 hS hm hD
    (he.symm ▸ hK0) (he.symm ▸ hK2) (he.symm ▸ hK2b)
  have hi (n : ℕ) : (fun z ↦ halfQuadraticVariationOnUnitInterval n z - D) ∘
      (fun (z : ℝ → ℝ) (t : Icc (0 : ℝ) 1) ↦ z t) =
        (fun z ↦ halfQuadraticVariation Z n z - D) := by
    funext z
    simp only [Function.comp_apply, halfQuadraticVariationOnUnitInterval_comp, Z]
  refine tendstoInMeasure_const_of_tendsto_integral_sq (fun n ↦ ?_) ?_
  · rw [← hr, memLp_map_measure_iff (by
      exact ((measurable_halfQuadraticVariationOnUnitInterval n).sub_const D).aestronglyMeasurable)
      hmR.aemeasurable, hi]
    exact (memLp_halfQuadraticVariation hZ.2.1 n).sub (memLp_const D)
  · have hInt (n : ℕ) : (∫ z, (halfQuadraticVariationOnUnitInterval n z - D) ^ 2
        ∂gaussianFieldLaw (D := Icc (0 : ℝ) 1) 0 (fun s t ↦ K (s - t))) =
        ∫ z, (halfQuadraticVariation Z n z - D) ^ 2 ∂μ := by
      have hpow : Measurable (fun z ↦ (halfQuadraticVariationOnUnitInterval n z - D) ^ 2) :=
        ((measurable_halfQuadraticVariationOnUnitInterval n).sub_const D).pow_const 2
      rw [← hr, integral_map hmR.aemeasurable hpow.aestronglyMeasurable]
      simp only [halfQuadraticVariationOnUnitInterval_comp, Z]
    simp_rw [hInt]
    simpa only [halfQuadraticVariation_def, gridIncrement_def, ← Fin.sum_univ_eq_sum_range] using hl

/-- SYNOPSIS item 39: for autocovariances `K_j(t) = C_j - D_j |t| + o(|t|)` with bounded second
derivatives on `(0, 1]`, the centred Gaussian laws on `[0, 1]` are orthogonal when `D₀ ≠ D₁`. -/
theorem gaussianFieldLaw_mutuallySingular_of_slope_ne {K₀ K₁ : ℝ → ℝ}
    (hK₀ : (Matrix.of fun s t : ℝ ↦ K₀ (s - t)).PosSemidef)
    (hK₁ : (Matrix.of fun s t : ℝ ↦ K₁ (s - t)).PosSemidef) {C₀ C₁ D₀ D₁ : ℝ} (hD₀ : 0 < D₀)
    (hD₁ : 0 < D₁) (h₀ : (fun t ↦ K₀ t - (C₀ - D₀ * |t|)) =o[𝓝 0] fun t ↦ t)
    (h₁ : (fun t ↦ K₁ t - (C₁ - D₁ * |t|)) =o[𝓝 0] fun t ↦ t)
    (h₀2 : ContDiffOn ℝ 2 K₀ (Ioc 0 1)) (h₁2 : ContDiffOn ℝ 2 K₁ (Ioc 0 1))
    (h₀b : ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 K₀ (Ioc 0 1) t| ≤ M)
    (h₁b : ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, |iteratedDerivWithin 2 K₁ (Ioc 0 1) t| ≤ M)
    (hne : D₀ ≠ D₁) :
    gaussianFieldLaw (D := Icc (0 : ℝ) 1) 0 (fun s t ↦ K₀ (s - t)) ⟂ₘ
      gaussianFieldLaw (D := Icc (0 : ℝ) 1) 0 (fun s t ↦ K₁ (s - t)) := by
  exact mutuallySingular_of_tendstoInMeasure_const_ne hne
    measurable_halfQuadraticVariationOnUnitInterval
    (tendstoInMeasure_halfQuadraticVariationOnUnitInterval hK₀ hD₀ h₀ h₀2 h₀b)
    (tendstoInMeasure_halfQuadraticVariationOnUnitInterval hK₁ hD₁ h₁ h₁2 h₁b)

end MSSS
