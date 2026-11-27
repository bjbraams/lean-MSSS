module

public import MSSS.RandomFields.Isotropic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Probability.Distributions.Gamma

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.Beta
import TauCeti.Analysis.CompletelyMonotone.Composition

/-!
# The Matérn family

SYNOPSIS item 12. The modified Bessel function of the second kind is defined by its
integral representation `𝒦_ν(x) = ∫₀^∞ e^{-x cosh u} cosh(ν u) du` for `x > 0`.

## Main definitions

* `MSSS.besselK ν x`: the modified Bessel function `𝒦_ν(x)` of the second kind.
* `MSSS.maternCorrelation ν θ t`: `φ_{ν,θ}(t) = 2^{1-ν}/Γ(ν) (t/θ)^ν 𝒦_ν(t/θ)`, `φ_{ν,θ}(0) = 1`.

The cases `ν = 1/2` and `ν = 3/2` use Mathlib's change of variables formula, Gaussian
integrals, and the Gamma recurrence. The full half-integer family uses the recurrence for
the order of the modified Bessel integral, proved by integration by parts on the positive
half-line. Positive definiteness in all dimensions uses Mathlib's
exponential and linear substitutions together with TauCeti's gamma integral transfer and
complete monotonicity of Laplace transforms. The spectral formula uses Mathlib's
Gaussian Fourier and Euler gamma integrals with the same gamma mixture. The Gaussian
limit uses TauCeti's mean, variance, and scaling identities for the gamma law.
Complete monotonicity in the lag uses TauCeti's gamma–beta factorization and negative gamma
moments, and Mathlib's criterion for convexity from a nonnegative second derivative.

## Main results

* `MSSS.charFun_maternSpectralMeasure`, `MSSS.maternCorrelation_mem_isotropicClassInf`,
  `MSSS.maternCorrelation_half`, `MSSS.maternCorrelation_halfInteger`,
  `MSSS.maternCorrelation_threeHalves`, `MSSS.tendsto_maternCorrelation_gaussian`,
  `MSSS.maternCorrelation_completelyMonotone_iff`: SYNOPSIS item 12.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff NNReal RealInnerProductSpace

namespace MSSS

/-- The modified Bessel function of the second kind, `𝒦_ν(x) = ∫₀^∞ e^{-x cosh u} cosh(ν u) du`,
used for `x > 0`. -/
def besselK (ν x : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)

lemma besselK_def (ν x : ℝ) :
    besselK ν x = ∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) * Real.cosh (ν * u) := by
  rw [besselK]

/-- The **Matérn correlation** `φ_{ν,θ}(t) = 2^{1-ν}/Γ(ν) (t/θ)^ν 𝒦_ν(t/θ)` for `t ≠ 0`, with
`φ_{ν,θ}(0) = 1`; used for `ν, θ > 0` and `t ≥ 0`. -/
def maternCorrelation (ν θ t : ℝ) : ℝ :=
  if t = 0 then 1 else 2 ^ (1 - ν) / Real.Gamma ν * (t / θ) ^ ν * besselK ν (t / θ)

lemma maternCorrelation_def (ν θ t : ℝ) : maternCorrelation ν θ t =
    if t = 0 then 1 else 2 ^ (1 - ν) / Real.Gamma ν * (t / θ) ^ ν * besselK ν (t / θ) := by
  rw [maternCorrelation]

/-! ### Matérn covariance and spectral density (SYNOPSIS item 12) -/

/-- The transformed Bessel integrand is dominated by a gamma kernel. -/
private lemma integrableOn_besselK_expIntegrand {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦ t ^ (ν - 1) * Real.exp (-(x / 2) * (t + t⁻¹))) (Ioi 0) := by
  have hI : IntegrableOn (fun t : ℝ ↦ t ^ (ν - 1) * Real.exp (-(x / 2) * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := ν - 1) (b := x / 2)
        (by linarith) one_pos (by positivity))
  apply hI.mono'
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      t ^ (ν - 1) * Real.exp (-(x / 2) * (t + t⁻¹))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hpow : 0 ≤ t ^ (ν - 1) := Real.rpow_nonneg ht'.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpow (Real.exp_pos _).le)]
    apply mul_le_mul_of_nonneg_left _ hpow
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (inv_nonneg.mpr ht'.le))
      (neg_nonpos.mpr (div_nonneg hx.le zero_le_two))

/-- Exponential substitution for the Bessel integrand with its Jacobian. -/
private lemma besselK_expIntegrand_comp_exp (ν x u : ℝ) :
    Real.exp u • ((Real.exp u) ^ (ν - 1) *
      Real.exp (-(x / 2) * (Real.exp u + (Real.exp u)⁻¹))) =
      Real.exp (-x * Real.cosh u) * Real.exp (ν * u) := by
  rw [smul_eq_mul, ← Real.exp_neg u, ← Real.exp_mul u (ν - 1), Real.cosh_eq,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  ring

/-- The hyperbolic cosine combines the positive and negative exponential weights. -/
private lemma two_mul_besselK_integrand (ν x u : ℝ) :
    2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) =
      Real.exp (-x * Real.cosh u) * Real.exp (ν * u) +
        Real.exp (-x * Real.cosh (-u)) * Real.exp (ν * -u) := by
  rw [Real.cosh_neg]
  simp only [Real.cosh_eq, mul_neg]
  ring

/-- Express twice the Bessel integral as a sum of reflected exponential integrands. -/
private lemma besselK_eq_integral_expWeighted (ν x : ℝ) :
    2 * besselK ν x =
      ∫ u in Ioi (0 : ℝ), (Real.exp (-x * Real.cosh u) * Real.exp (ν * u) +
        Real.exp (-x * Real.cosh (-u)) * Real.exp (ν * -u)) := by
  rw [besselK_def, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ two_mul_besselK_integrand ν x u

/-- The exponentially weighted Bessel integrand is integrable on the real line. -/
private lemma integrable_exp_cosh_mul_exp {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    Integrable (fun u : ℝ ↦ Real.exp (-x * Real.cosh u) * Real.exp (ν * u)) := by
  let g (t : ℝ) := t ^ (ν - 1) * Real.exp (-(x / 2) * (t + t⁻¹))
  have hg : Integrable (fun u ↦ Real.exp u • g (Real.exp u)) :=
    (integrable_comp_exp g).mpr (integrableOn_besselK_expIntegrand hν hx)
  exact hg.congr (ae_of_all _ (besselK_expIntegrand_comp_exp ν x))

/-- The exponential representation of the modified Bessel function on the positive half-line. -/
private lemma besselK_eq_expIntegral {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    2 * besselK ν x =
      ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-(x / 2) * (t + t⁻¹)) := by
  let g (t : ℝ) := t ^ (ν - 1) * Real.exp (-(x / 2) * (t + t⁻¹))
  let f (u : ℝ) := Real.exp (-x * Real.cosh u) * Real.exp (ν * u)
  -- Mathlib's exponential substitution relates both integrals and integrability.
  have hfeq : (fun u ↦ Real.exp u • g (Real.exp u)) =ᵐ[volume] f :=
    ae_of_all _ (besselK_expIntegrand_comp_exp ν x)
  have hf : Integrable f := integrable_exp_cosh_mul_exp hν hx
  have hF : (∫ u, f u) = ∫ t in Ioi 0, g t :=
    (integral_congr_ae hfeq).symm.trans (integral_comp_exp g)
  have hreflect (f : ℝ → ℝ) (hf : Integrable f) :
      (∫ u in Ioi (0 : ℝ), (f u + f (-u))) = ∫ u, f u := by
    have hneg : Integrable (fun u ↦ f (-u)) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hf
    calc
      _ = (∫ u in Ioi (0 : ℝ), f u) + (∫ u in Ioi (0 : ℝ), f (-u)) :=
        integral_add hf.integrableOn hneg.integrableOn
      _ = (∫ u in Ioi (0 : ℝ), f u) + (∫ u in (Ioi (0 : ℝ))ᶜ, f u) := by
        apply congrArg ((∫ u in Ioi (0 : ℝ), f u) + ·)
        simpa only [neg_zero, compl_Ioi] using integral_comp_neg_Ioi 0 f
      _ = _ := integral_add_compl measurableSet_Ioi hf
  exact (besselK_eq_integral_expWeighted ν x).trans <|
    (hreflect f hf).trans hF

/-- Scale the variable in the exponential representation to obtain a gamma kernel. -/
private lemma besselK_eq_gammaIntegral {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    2 * (x / 2) ^ ν * besselK ν x =
      ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t)) := by
  let G (t : ℝ) := t ^ (ν - 1) * Real.exp (-t - x ^ 2 / (4 * t))
  let c := x / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hscale : (∫ t in Ioi (0 : ℝ), c * G (c * t)) = ∫ t in Ioi (0 : ℝ), G t := by
    rw [integral_const_mul]
    simpa only [smul_eq_mul, mul_zero] using integral_comp_mul_left_Ioi' G 0 hc
  have hcomp (t : ℝ) (ht : t ∈ Ioi 0) :
      c * G (c * t) = c ^ ν * (t ^ (ν - 1) * Real.exp (-c * (t + t⁻¹))) := by
    have ht' : 0 < t := ht
    have hs : - (c * t) - x ^ 2 / (4 * (c * t)) = -c * (t + t⁻¹) := by
      dsimp only [c]
      field_simp [hx.ne', ht'.ne']
      ring
    have hp : c * c ^ (ν - 1) = c ^ ν := calc
      _ = c ^ (1 : ℝ) * c ^ (ν - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hc]; congr 1; ring
    dsimp only [G]
    rw [hs, Real.mul_rpow hc.le ht'.le, ← mul_assoc, ← mul_assoc, hp]
    ring
  calc
    _ = c ^ ν * (2 * besselK ν x) := by ring
    _ = ∫ t in Ioi (0 : ℝ), c ^ ν * (t ^ (ν - 1) * Real.exp (-c * (t + t⁻¹))) := by
      rw [besselK_eq_expIntegral hν hx, integral_const_mul]
    _ = ∫ t in Ioi (0 : ℝ), c * G (c * t) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ (hcomp t ht).symm)
    _ = _ := hscale

/-- The Matérn correlation as a normalized gamma integral at positive lags. -/
private lemma maternCorrelation_eq_gammaIntegral {ν θ t : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    (ht : 0 < t) : maternCorrelation ν θ t =
      (Real.Gamma ν)⁻¹ *
        ∫ u in Ioi (0 : ℝ), u ^ (ν - 1) * Real.exp (-u - (t / θ) ^ 2 / (4 * u)) := by
  have hx : 0 < t / θ := div_pos ht hθ
  have hp : 2 * (t / θ / 2) ^ ν = 2 ^ (1 - ν) * (t / θ) ^ ν := by
    rw [Real.div_rpow hx.le zero_le_two, Real.rpow_sub two_pos, Real.rpow_one]
    ring
  rw [maternCorrelation_def, ite_eq_right ht.ne', ← besselK_eq_gammaIntegral hν hx, hp]
  ring

/-- The Matérn correlation is the expectation of a Gaussian profile with an inverse gamma scale. -/
lemma maternCorrelation_eq_integral_gammaMeasure {ν θ t : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    (ht : 0 ≤ t) : maternCorrelation ν θ t =
      ∫ u, Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u))) ∂gammaMeasure ν 1 := by
  have hprob := isProbabilityMeasure_gammaMeasure hν one_pos
  rcases ht.eq_or_lt with rfl | ht
  · simp [maternCorrelation_def]
  rw [maternCorrelation_eq_gammaIntegral hν hθ ht, ← integral_const_mul,
    TauCeti.Probability.integral_gammaMeasure_eq_integral_Ioi hν one_pos]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  have hθt : (t / θ) ^ 2 / (4 * u) = t ^ 2 / (4 * θ ^ 2 * u) := by
    rw [div_pow]
    ring
  simp only [hθt, smul_eq_mul, Real.one_rpow, one_div, one_mul, sub_eq_add_neg, Real.exp_add]
  ring

/-- The Gaussian density with quadratic rate `b` in dimension `d`. -/
private def gaussianRateDensity (d : ℕ) (b : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (b / Real.pi) ^ ((d : ℝ) / 2) * Real.exp (-b * ‖x‖ ^ 2)

/-- Combine a Gaussian density with the complex Fourier phase. -/
private lemma gaussianRateDensity_mul_cexp {d : ℕ} (b : ℝ) (x h : EuclideanSpace ℝ (Fin d)) :
    (gaussianRateDensity d b x : ℂ) * Complex.exp (⟪x, h⟫ * Complex.I) =
      ((b / Real.pi) ^ ((d : ℝ) / 2) : ℝ) *
        Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + Complex.I * ⟪h, x⟫) := by
  rw [gaussianRateDensity, Complex.ofReal_mul, Complex.ofReal_exp, Complex.exp_add,
    real_inner_comm h x, mul_comm Complex.I, ← mul_assoc]
  push_cast
  rfl

/-- The Fourier transform of a normalized Gaussian density. -/
private lemma integral_cexp_mul_gaussianRateDensity {d : ℕ} {b : ℝ} (hb : 0 < b)
    (h : EuclideanSpace ℝ (Fin d)) :
    ∫ x : EuclideanSpace ℝ (Fin d),
      (gaussianRateDensity d b x : ℂ) * Complex.exp (⟪x, h⟫ * Complex.I) =
      (Real.exp (-(‖h‖ ^ 2 / (4 * b))) : ℂ) := by
  simp_rw [gaussianRateDensity_mul_cexp]
  -- Apply Mathlib's inner-product-space Gaussian Fourier formula.
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (by simpa only [Complex.ofReal_re] using hb),
    Fintype.card_fin, Complex.I_sq, neg_one_mul]
  have hp : (↑Real.pi / (b : ℂ)) ^ ((d : ℂ) / 2) =
      ((Real.pi / b) ^ ((d : ℝ) / 2) : ℝ) := by
    rw [Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / b), Complex.ofReal_div,
      Complex.ofReal_div, Complex.ofReal_natCast]
    norm_num
  have hscale : (b / Real.pi) ^ ((d : ℝ) / 2) * (Real.pi / b) ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show b / Real.pi * (Real.pi / b) = 1 by field_simp, Real.one_rpow]
  rw [hp, ← mul_assoc, ← Complex.ofReal_mul, hscale, Complex.ofReal_one, one_mul,
    Complex.ofReal_exp]
  push_cast
  rw [neg_div]

/-- The Gaussian Fourier integrand is integrable and its absolute value has integral one. -/
private lemma integrable_norm_gaussianRateDensity {d : ℕ} {b : ℝ} (hb : 0 < b)
    (h : EuclideanSpace ℝ (Fin d)) :
    let f (x : EuclideanSpace ℝ (Fin d)) :=
      (gaussianRateDensity d b x : ℂ) * Complex.exp (⟪x, h⟫ * Complex.I)
    Integrable f ∧ (∫ x, ‖f x‖) = 1 := by
  dsimp only
  constructor
  · have hi := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ (Fin d)) (b := (b : ℂ)) (by simpa only [Complex.ofReal_re] using hb)
      Complex.I h).const_mul (((b / Real.pi) ^ ((d : ℝ) / 2) : ℝ) : ℂ)
    exact hi.congr <| ae_of_all _ fun x ↦ (gaussianRateDensity_mul_cexp b x h).symm
  · have hnon (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gaussianRateDensity d b x := by
      unfold gaussianRateDensity
      positivity
    simp_rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hnon _)]
    have hz := integral_cexp_mul_gaussianRateDensity hb (0 : EuclideanSpace ℝ (Fin d))
    norm_num [inner_zero_right, Complex.exp_zero] at hz
    apply Complex.ofReal_injective
    rwa [← integral_complex_ofReal]

/-- Mixing Gaussian densities over the gamma law yields the Matérn spectral density. -/
private lemma integral_gaussianRateDensity_gammaMeasure {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    {d : ℕ} (hd : 1 ≤ d) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ u, gaussianRateDensity d (θ ^ 2 * u) ξ ∂gammaMeasure ν 1 =
      Real.Gamma (ν + d / 2) / (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2)) * θ ^ d *
        (1 + θ ^ 2 * ‖ξ‖ ^ 2) ^ (-ν - d / 2) := by
  let p := (d : ℝ) / 2
  let b := 1 + θ ^ 2 * ‖ξ‖ ^ 2
  let c := (θ ^ 2 / Real.pi) ^ p / Real.Gamma ν
  have hp : 0 < p :=
    div_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd) two_pos
  have hb : 0 < b := by dsimp only [b]; positivity
  have hpow : (θ ^ 2 / Real.pi) ^ p = θ ^ d / Real.pi ^ p := by
    rw [Real.div_rpow (by positivity) Real.pi_pos.le]
    congr 1
    rw [← Real.rpow_natCast θ 2, ← Real.rpow_mul hθ.le, ← Real.rpow_natCast θ d]
    have hcast : ((2 : ℕ) : ℝ) * p = (d : ℝ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hcast]
  rw [TauCeti.Probability.integral_gammaMeasure_eq_integral_Ioi hν one_pos]
  calc
    _ = ∫ u in Ioi 0, c * (u ^ (ν + p - 1) * Real.exp (-(b * u))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
      have hu' : 0 < u := hu
      have hrate : θ ^ 2 * u / Real.pi = θ ^ 2 / Real.pi * u := by ring
      have hexp : -(b * u) = -u + -(θ ^ 2 * u) * ‖ξ‖ ^ 2 := by dsimp only [b]; ring
      simp only [gaussianRateDensity, hrate, smul_eq_mul, Real.one_rpow, one_div, one_mul,
        Real.mul_rpow (by positivity : 0 ≤ θ ^ 2 / Real.pi) hu'.le, hexp, Real.exp_add]
      dsimp only [c, p]
      rw [show ν + (d : ℝ) / 2 - 1 = ν - 1 + (d : ℝ) / 2 by ring, Real.rpow_add hu']
      ring
    _ = _ := by
      have hv : 0 < ν + p := add_pos hν hp
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hv hb]
      dsimp only [c]
      rw [hpow, one_div, Real.inv_rpow hb.le]
      rw [show -ν - (d : ℝ) / 2 = -(ν + p) by dsimp only [p]; ring, Real.rpow_neg hb.le]
      ring

/-- SYNOPSIS item 12: for `ν, θ > 0` and every `d ≥ 1`, `φ_{ν,θ}(‖h‖)` is the characteristic
function of the measure with density
`Γ(ν + d/2) / (Γ(ν) π^{d/2}) θ^d (1 + θ² ‖ω‖²)^{-ν-d/2}`. -/
theorem charFun_maternSpectralMeasure {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) {d : ℕ}
    (hd : 1 ≤ d) (h : EuclideanSpace ℝ (Fin d)) :
    charFun (volume.withDensity fun ξ : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal
      (Real.Gamma (ν + d / 2) / (Real.Gamma ν * Real.pi ^ ((d : ℝ) / 2)) * θ ^ d *
        (1 + θ ^ 2 * ‖ξ‖ ^ 2) ^ (-ν - d / 2))) h = (maternCorrelation ν θ ‖h‖ : ℂ) := by
  let μ := gammaMeasure ν 1
  have hp : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure hν one_pos
  let F (u : ℝ) (x : EuclideanSpace ℝ (Fin d)) :=
    (gaussianRateDensity d (θ ^ 2 * u) x : ℂ) * Complex.exp (⟪x, h⟫ * Complex.I)
  have hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) := by
    have hm : Measurable (Function.uncurry F) := by
      dsimp only [F, Function.uncurry, gaussianRateDensity]
      fun_prop
    exact hm.aestronglyMeasurable
  have hint : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (integrable_prod_iff hF).2
    have hpos : ∀ᵐ u ∂μ, 0 < u := TauCeti.Probability.ae_pos_gammaMeasure ν 1
    have hb : ∀ᵐ u ∂μ, 0 < θ ^ 2 * u := by
      filter_upwards [hpos] with u hu using mul_pos (sq_pos_of_pos hθ) hu
    refine ⟨hb.mono (fun u hu ↦ (integrable_norm_gaussianRateDensity hu h).1),
      (integrable_const (1 : ℝ)).congr ?_⟩
    exact hb.mono fun _ hu ↦ (integrable_norm_gaussianRateDensity hu h).2.symm
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _]
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin d), ∫ u, F u x ∂μ := by
      refine integral_congr_ae <| ae_of_all _ fun x ↦ ?_
      dsimp only [F]
      rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul,
        ← integral_gaussianRateDensity_gammaMeasure hν hθ hd x, ← integral_complex_ofReal,
        ← integral_mul_const]
    _ = ∫ u, (∫ x : EuclideanSpace ℝ (Fin d), F u x) ∂μ :=
      (integral_integral_swap hint).symm
    _ = _ := by
      rw [maternCorrelation_eq_integral_gammaMeasure hν hθ (norm_nonneg _),
        ← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
      have hb : 0 < θ ^ 2 * u := mul_pos (sq_pos_of_pos hθ) hu
      dsimp only [F]
      rw [integral_cexp_mul_gaussianRateDensity hb h]
      congr 3
      ring

/-- The Matérn correlation at a square-root lag is the Laplace transform of the inverse
gamma rate. -/
private lemma maternCorrelation_eq_laplace {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    ∃ μ : Measure ℝ≥0, IsProbabilityMeasure μ ∧
      ∀ t ≥ 0, maternCorrelation ν θ (Real.sqrt t) = TauCeti.laplaceTransform μ t := by
  let rate (u : ℝ) := Real.toNNReal ((4 * θ ^ 2 * u)⁻¹)
  have hm : Measurable rate := by fun_prop
  let μ := (gammaMeasure ν 1).map rate
  let : IsProbabilityMeasure (gammaMeasure ν 1) := isProbabilityMeasure_gammaMeasure hν one_pos
  let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2
    inferInstance
  refine ⟨μ, inferInstance, fun t ht ↦ ?_⟩
  let f (x : ℝ≥0) := Real.exp (-(t * (x : ℝ)))
  have hmeas : Continuous f := by fun_prop
  rw [maternCorrelation_eq_integral_gammaMeasure hν hθ (Real.sqrt_nonneg t),
    TauCeti.laplaceTransform_apply]
  -- Write the Laplace integrand using the continuous function `f` for the pushforward.
  change _ = ∫ x, f x ∂(Measure.map rate (gammaMeasure ν 1))
  rw [integral_map hm.aemeasurable hmeas.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
  rw [Real.sq_sqrt ht]
  simp only [f, rate, Real.coe_toNNReal _ (by positivity : 0 ≤ (4 * θ ^ 2 * u)⁻¹),
    div_eq_mul_inv]

/-- SYNOPSIS item 12: the Matérn correlation belongs to `Φ_∞`. -/
theorem maternCorrelation_mem_isotropicClassInf {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    maternCorrelation ν θ ∈ isotropicClassInf := by
  obtain ⟨μ, hμ, hm⟩ := maternCorrelation_eq_laplace hν hθ
  let := hμ
  have heq (t : ℝ) (ht : 0 ≤ t) :
      maternCorrelation ν θ t = TauCeti.laplaceTransform μ (t ^ 2) := by
    simpa only [Real.sqrt_sq ht] using hm (t ^ 2) (sq_nonneg t)
  have hl := TauCeti.isContinuousCompletelyMonotoneOnIoi_laplaceTransform μ
  refine mem_isotropicClassInf.mpr fun d ↦ mem_isotropicClass.mpr ⟨?_, by
    simp [maternCorrelation_def], ?_⟩
  · refine (hl.continuousOn.comp (by fun_prop : Continuous (fun t : ℝ ↦ t ^ 2)).continuousOn
      (fun t _ ↦ sq_nonneg t)).congr fun t ht ↦ ?_
    exact heq t ht
  · have hpd := isPositiveDefiniteSub_sq_norm_of_completelyMonotone
        (E := EuclideanSpace ℝ (Fin (d + 1))) hl
    have hfun : (fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦
        (maternCorrelation ν θ ‖x‖ : ℂ)) =
        fun x ↦ (TauCeti.laplaceTransform μ (‖x‖ ^ 2) : ℂ) := by
      funext x
      rw [heq _ (norm_nonneg x)]
    rw [hfun]
    exact hpd

/-- Substitution by `sinh (u / 2)` on the positive half-line. -/
lemma integral_Ioi_comp_sinh_half (g : ℝ → ℝ) :
    ∫ u in Ioi (0 : ℝ), g (Real.sinh (u / 2)) * Real.cosh (u / 2) =
      2 * ∫ v in Ioi (0 : ℝ), g v := by
  let f (u : ℝ) := Real.sinh (u / 2)
  have hf : StrictMono f := Real.sinh_strictMono.comp fun _ _ h ↦ div_lt_div_of_pos_right h two_pos
  have hf_zero : f 0 = 0 := by simp [f]
  have hI : f '' Ioi (0 : ℝ) = Ioi 0 := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h := hf hu
      rw [hf_zero] at h
      exact h
    · intro hv
      obtain ⟨u, hu⟩ := Real.sinh_surjective v
      have heq : f (u * 2) = v := by simp [f, hu]
      exact ⟨u * 2, hf.lt_iff_lt.mp (by rwa [heq, hf_zero]), heq⟩
  have hd (u : ℝ) : HasDerivAt f (Real.cosh (u / 2) / 2) u := by
    simpa only [f, id_eq, div_eq_mul_inv, one_mul] using ((hasDerivAt_id u).div_const 2).sinh
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (0 : ℝ)))
    (fun u _ ↦ (hd u).hasDerivWithinAt) hf.injective.injOn g
  rw [hI] at h
  rw [h, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only
  rw [smul_eq_mul, abs_of_pos (div_pos (Real.cosh_pos _) two_pos)]
  dsimp only [f]
  ring

/-- The hyperbolic double-angle identity in the variable used to integrate `besselK`. -/
lemma cosh_eq_one_add_two_mul_sinh_half_sq (u : ℝ) :
    Real.cosh u = 1 + 2 * Real.sinh (u / 2) ^ 2 := by
  calc
    Real.cosh u = Real.cosh (2 * (u / 2)) := by congr 1; ring
    _ = 1 + 2 * Real.sinh (u / 2) ^ 2 := by
      rw [Real.cosh_two_mul, Real.cosh_sq]
      ring

/-- The integral defining `K_{1/2}` reduces to a Gaussian integral. -/
private lemma besselK_half (x : ℝ) :
    besselK (1 / 2) x = Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) := by
  rw [besselK_def]
  calc
    _ = ∫ u in Ioi (0 : ℝ),
        (Real.exp (-x) * Real.exp (-(2 * x) * (Real.sinh (u / 2)) ^ 2)) *
          Real.cosh (u / 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only
      have hhalf : (1 / 2 : ℝ) * u = u / 2 := by ring
      have hexp : -x * (1 + 2 * Real.sinh (u / 2) ^ 2) =
          -x + -(2 * x) * Real.sinh (u / 2) ^ 2 := by ring
      rw [hhalf, cosh_eq_one_add_two_mul_sinh_half_sq u, ← Real.exp_add, hexp]
    _ = Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) := by
      rw [integral_Ioi_comp_sinh_half (fun v ↦ Real.exp (-x) * Real.exp (-(2 * x) * v ^ 2)),
        integral_const_mul, integral_gaussian_Ioi]
      ring

/-- SYNOPSIS item 12: for `ν = 1/2` the Matérn correlation is `e^{-t/θ}`. -/
theorem maternCorrelation_half {θ : ℝ} (hθ : 0 < θ) {t : ℝ} (ht : 0 ≤ t) :
    maternCorrelation (1 / 2) θ t = Real.exp (-t / θ) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [maternCorrelation_def]
  · have hx : 0 < t / θ := div_pos ht hθ
    rw [maternCorrelation_def, ite_eq_right ht.ne', besselK_half, Real.Gamma_one_half_eq,
      Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul zero_le_two, neg_div]
    norm_num only [Real.sqrt_eq_rpow, show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
    field_simp [Real.rpow_pos_of_pos hx, Real.rpow_pos_of_pos Real.pi_pos,
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- A function dominated by an exponential on the positive real axis can multiply the
Bessel weight without losing integrability. -/
private lemma integrableOn_exp_cosh_mul {x ν : ℝ} (hx : 0 < x) (hν : 0 < ν)
    {g : ℝ → ℝ} (hg : Measurable g) (h : ∀ u > 0, ‖g u‖ ≤ Real.exp (ν * u)) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-x * Real.cosh u) * g u) (Ioi 0) := by
  apply (integrable_exp_cosh_mul_exp hν hx).integrableOn.mono'
  · exact ((by fun_prop : Measurable (fun u : ℝ ↦ Real.exp (-x * Real.cosh u))).mul
      hg).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (h u hu) (Real.exp_pos _).le

/-- Each hyperbolic factor is dominated by the exponential of the absolute argument. -/
private lemma norm_hyperbolic_le_exp_abs (u : ℝ) :
    ‖Real.sinh u‖ ≤ Real.exp |u| ∧ ‖Real.cosh u‖ ≤ Real.exp |u| := by
  simp only [Real.norm_eq_abs, Real.abs_sinh, abs_of_pos (Real.cosh_pos _), ← Real.cosh_abs u]
  constructor
  · rw [Real.sinh_eq]
    linarith [Real.exp_pos (-|u|), Real.exp_pos |u|]
  · rw [Real.cosh_eq]
    have he := Real.exp_le_exp.mpr (show -|u| ≤ |u| by linarith [abs_nonneg u])
    linarith

/-- The hyperbolic cosine integral defining the Bessel function is absolutely integrable. -/
private lemma integrableOn_besselK (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) (Ioi 0) := by
  refine integrableOn_exp_cosh_mul hx (ν := |ν| + 1) (by positivity) (by fun_prop)
    fun u hu ↦ (norm_hyperbolic_le_exp_abs (ν * u)).2.trans ?_
  rw [Real.exp_le_exp, abs_mul, abs_of_pos hu]
  gcongr
  exact le_add_of_nonneg_right zero_le_one

/-- Integration by parts for the two `sinh` factors in the Bessel recurrence. -/
private lemma mul_integral_besselK_sinh_sinh {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    x * (∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) *
      (Real.sinh u * Real.sinh (ν * u))) = ν * besselK ν x := by
  let A (u : ℝ) := Real.exp (-x * Real.cosh u)
  let F (u : ℝ) := A u * Real.sinh (ν * u)
  let H (u : ℝ) := A u * (Real.sinh u * Real.sinh (ν * u))
  let G (u : ℝ) := A u * Real.cosh (ν * u)
  have hF : IntegrableOn F (Ioi 0) := by
    refine integrableOn_exp_cosh_mul hx hν (by fun_prop) fun u hu ↦ ?_
    simpa only [abs_of_pos (mul_pos hν hu)] using (norm_hyperbolic_le_exp_abs (ν * u)).1
  have hG : IntegrableOn G (Ioi 0) := integrableOn_besselK ν hx
  have hH : IntegrableOn H (Ioi 0) := by
    refine integrableOn_exp_cosh_mul hx (add_pos one_pos hν) (by fun_prop) fun u hu ↦ ?_
    rw [norm_mul, add_mul, one_mul, Real.exp_add]
    have h1 := (norm_hyperbolic_le_exp_abs u).1
    have h2 := (norm_hyperbolic_le_exp_abs (ν * u)).1
    rw [abs_of_pos hu] at h1
    rw [abs_of_pos (mul_pos hν hu)] at h2
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
  have hd (u : ℝ) : HasDerivAt F (ν * G u - x * H u) u := by
    have hA := ((hasDerivAt_id u).cosh.const_mul (-x)).exp
    have hB := ((hasDerivAt_id u).const_mul ν).sinh
    convert hA.mul hB using 1
    · funext v
      simp only [F, A, id_eq, Pi.mul_apply]
    · simp only [A, G, H, id_eq, mul_one]
      ring
  have hI := (hG.const_mul ν).sub (hH.const_mul x)
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun u _ ↦ hd u) hI hF
  -- The integrable derivative and vanishing boundary values give the recurrence.
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ ↦ hd u) hI hlim
  rw [integral_sub (hG.const_mul ν) (hH.const_mul x), integral_const_mul,
    integral_const_mul] at hFTC
  have hzero : F 0 = 0 := by simp [F]
  rw [hzero, sub_zero, sub_eq_zero] at hFTC
  rw [besselK_def]
  exact hFTC.symm

/-- The modified Bessel recurrence in the order parameter. -/
private lemma besselK_add_one {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    besselK (ν + 1) x = besselK (ν - 1) x + (2 * ν / x) * besselK ν x := by
  have hfun (u : ℝ) :
      Real.cosh ((ν + 1) * u) - Real.cosh ((ν - 1) * u) =
        2 * (Real.sinh u * Real.sinh (ν * u)) := by
    rw [add_mul, sub_mul, one_mul, Real.cosh_add, Real.cosh_sub]
    ring
  have hdiff : besselK (ν + 1) x - besselK (ν - 1) x =
      2 * (∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) *
        (Real.sinh u * Real.sinh (ν * u))) := by
    rw [besselK_def, besselK_def, ← integral_sub (integrableOn_besselK _ hx)
      (integrableOn_besselK _ hx), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    rw [← mul_sub, hfun]
    ring
  have h := mul_integral_besselK_sinh_sinh hν hx
  have hI := (eq_div_iff hx.ne').2 (by simpa only [mul_comm] using h)
  calc
    _ = besselK (ν - 1) x + 2 * (∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) *
          (Real.sinh u * Real.sinh (ν * u))) := by linarith only [hdiff]
    _ = _ := by rw [hI]; ring

/-- The order recurrence for the normalized Matérn correlation. -/
private lemma maternCorrelation_add_one {ν θ t : ℝ} (hν : 1 < ν) (hθ : 0 < θ)
    (ht : 0 ≤ t) : maternCorrelation (ν + 1) θ t =
      maternCorrelation ν θ t + ((t / θ) ^ 2 / (4 * ν * (ν - 1))) *
        maternCorrelation (ν - 1) θ t := by
  have hν₀ : 0 < ν := lt_trans zero_lt_one hν
  have hν₁ : 0 < ν - 1 := sub_pos.mpr hν
  rcases ht.eq_or_lt with rfl | ht
  · simp [maternCorrelation_def]
  let x := t / θ
  have hx : 0 < x := div_pos ht hθ
  have hd : 1 - (ν + 1) = (1 - ν) - 1 := by ring
  have hdm : 1 - (ν - 1) = (1 - ν) + 1 := by ring
  have hΓ : Real.Gamma ν = (ν - 1) * Real.Gamma (ν - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one hν₁.ne'
  have hnorm : 0 < Real.Gamma (ν - 1) := Real.Gamma_pos_of_pos hν₁
  simp only [maternCorrelation_def, ite_eq_right ht.ne']
  -- Write the normalized terms at the common argument `x = t / θ`.
  change 2 ^ (1 - (ν + 1)) / Real.Gamma (ν + 1) * x ^ (ν + 1) *
      besselK (ν + 1) x = 2 ^ (1 - ν) / Real.Gamma ν * x ^ ν * besselK ν x +
        x ^ 2 / (4 * ν * (ν - 1)) *
          (2 ^ (1 - (ν - 1)) / Real.Gamma (ν - 1) * x ^ (ν - 1) * besselK (ν - 1) x)
  rw [besselK_add_one hν₀ hx, Real.Gamma_add_one hν₀.ne', hΓ, hd, hdm,
    Real.rpow_sub two_pos, Real.rpow_add two_pos, Real.rpow_add hx, Real.rpow_sub hx,
    Real.rpow_one, Real.rpow_one]
  field_simp [hν₀.ne', hν₁.ne', hnorm.ne', hx.ne']
  ring

/-- The Gamma value needed for the second Gaussian moment and the Matérn normalization. -/
lemma gamma_threeHalves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  ring

/-- The second Gaussian moment on the positive half-line. -/
lemma integral_sq_mul_gaussian_Ioi {b : ℝ} (hb : 0 < b) :
    ∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-b * v ^ 2) =
      Real.sqrt (Real.pi / b) / (4 * b) := by
  rw [← integral_congr_ae (μ := volume.restrict (Ioi 0)) (f := fun v : ℝ ↦
      v ^ (2 : ℝ) * Real.exp (-b * v ^ (2 : ℝ))) (g := fun v ↦ v ^ 2 * Real.exp (-b * v ^ 2))
      (ae_of_all _ fun _ ↦ by simp only [Real.rpow_two])]
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (-1 : ℝ) < 2) hb]
  norm_num only
  rw [gamma_threeHalves, show (-(3 / 2 : ℝ)) = -(1 / 2) - 1 by ring,
    Real.rpow_sub hb, Real.rpow_one, Real.rpow_neg hb.le, Real.sqrt_div Real.pi_pos.le,
    ← Real.sqrt_eq_rpow]
  field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos.2 hb)]
  ring

/-- The integral defining `K_{3/2}` reduces to the zeroth and second Gaussian moments. -/
private lemma besselK_threeHalves {x : ℝ} (hx : 0 < x) :
    besselK (3 / 2) x = Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) * (1 + x⁻¹) := by
  have hb : 0 < 2 * x := mul_pos two_pos hx
  have h0 : IntegrableOn (fun v : ℝ ↦ Real.exp (-(2 * x) * v ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have h2 : IntegrableOn (fun v : ℝ ↦ v ^ 2 * Real.exp (-(2 * x) * v ^ 2)) (Ioi 0) := by
    simpa only [Real.rpow_two] using
      integrableOn_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
  rw [besselK_def]
  calc
    _ = ∫ u in Ioi (0 : ℝ),
        (Real.exp (-x) * (Real.exp (-(2 * x) * Real.sinh (u / 2) ^ 2) +
          4 * (Real.sinh (u / 2) ^ 2 * Real.exp (-(2 * x) * Real.sinh (u / 2) ^ 2)))) *
          Real.cosh (u / 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only
      have harg : (3 / 2 : ℝ) * u = 3 * (u / 2) := by ring
      have hexp : -x * (1 + 2 * Real.sinh (u / 2) ^ 2) =
          -x + -(2 * x) * Real.sinh (u / 2) ^ 2 := by ring
      rw [harg, Real.cosh_three_mul, pow_succ, Real.cosh_sq,
        cosh_eq_one_add_two_mul_sinh_half_sq u, hexp, Real.exp_add]
      ring
    _ = _ := by
      rw [integral_Ioi_comp_sinh_half (fun v ↦ Real.exp (-x) *
        (Real.exp (-(2 * x) * v ^ 2) + 4 * (v ^ 2 * Real.exp (-(2 * x) * v ^ 2)))),
        integral_const_mul, integral_add h0 (h2.const_mul 4), integral_const_mul,
        integral_gaussian_Ioi, integral_sq_mul_gaussian_Ioi hb]
      field_simp [hx.ne']

/-- SYNOPSIS item 12: for `ν = 3/2` the Matérn correlation is `(1 + t/θ) e^{-t/θ}`. -/
theorem maternCorrelation_threeHalves {θ : ℝ} (hθ : 0 < θ) {t : ℝ} (ht : 0 ≤ t) :
    maternCorrelation (3 / 2) θ t = (1 + t / θ) * Real.exp (-t / θ) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [maternCorrelation_def]
  · have hx : 0 < t / θ := div_pos ht hθ
    rw [maternCorrelation_def, ite_eq_right ht.ne', besselK_threeHalves hx, gamma_threeHalves,
      Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul zero_le_two, neg_div]
    set x := t / θ
    have hp : x ^ (3 / 2 : ℝ) = Real.sqrt x * x := by
      calc
        _ = x ^ (1 / 2 + 1 : ℝ) := by norm_num
        _ = _ := by rw [Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg zero_le_two,
      ← Real.sqrt_eq_rpow, hp]
    have htwo : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
    field_simp [hx.ne', Real.sqrt_ne_zero'.2 hx, Real.sqrt_ne_zero'.2 Real.pi_pos,
      Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)]
    linear_combination -(x + 1) * htwo

/-- SYNOPSIS item 12: for `ν = m + 1/2` the Matérn correlation is `e^{-t/θ}` times a polynomial
of degree `m` in `t/θ`. -/
theorem maternCorrelation_halfInteger {θ : ℝ} (hθ : 0 < θ) (m : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree = m ∧ ∀ t, 0 ≤ t →
      maternCorrelation (m + 1 / 2) θ t = Real.exp (-t / θ) * p.eval (t / θ) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    refine ⟨1, Polynomial.natDegree_one, fun t ht ↦ ?_⟩
    simpa only [Nat.cast_zero, zero_add, Polynomial.eval_one, mul_one] using
      maternCorrelation_half hθ ht
  | one =>
    refine ⟨Polynomial.X + 1, ?_, fun t ht ↦ ?_⟩
    · rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]
    · rw [Nat.cast_one, show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num,
        maternCorrelation_threeHalves hθ ht, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one]
      ring
  | more n hn hsucc =>
    obtain ⟨p, hp, hpval⟩ := hn
    obtain ⟨q, hq, hqval⟩ := hsucc
    let ν := (n : ℝ) + 3 / 2
    have hν : 1 < ν := by dsimp only [ν]; linarith [Nat.cast_nonneg (α := ℝ) n]
    let c := (4 * ν * (ν - 1))⁻¹
    have hc : 0 < c := by dsimp only [c]; positivity
    let R : Polynomial ℝ := Polynomial.C c * (Polynomial.X ^ 2 * p)
    have hpnz : p ≠ 0 := by
      intro h
      have hzero := hpval 0 le_rfl
      simp [h, maternCorrelation_def] at hzero
    have hRdeg : R.natDegree = n + 2 := by
      dsimp only [R]
      rw [Polynomial.natDegree_C_mul hc.ne',
        Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hpnz,
        Polynomial.natDegree_X_pow, hp, Nat.add_comm]
    have hdeg : q.natDegree < R.natDegree := by rw [hq, hRdeg]; omega
    refine ⟨q + R, (Polynomial.natDegree_add_eq_right_of_natDegree_lt hdeg).trans hRdeg,
      fun t ht ↦ ?_⟩
    have hzero : ν - 1 = (n : ℝ) + 1 / 2 := by dsimp only [ν]; ring
    have hone : ν = ((n + 1 : ℕ) : ℝ) + 1 / 2 := by dsimp only [ν]; push_cast; ring
    have htwo : ν + 1 = ((n + 2 : ℕ) : ℝ) + 1 / 2 := by dsimp only [ν]; push_cast; ring
    have hp' : maternCorrelation (ν - 1) θ t = Real.exp (-t / θ) * p.eval (t / θ) := by
      rw [hzero, hpval t ht]
    have hq' : maternCorrelation ν θ t = Real.exp (-t / θ) * q.eval (t / θ) := by
      rw [hone, hqval t ht]
    rw [← htwo, maternCorrelation_add_one hν hθ ht, hp', hq']
    simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, c, div_eq_mul_inv]
    ring

/-- The rate-`ν` gamma laws concentrate at one as the common shape and rate `ν` grow. -/
lemma tendsto_integral_gammaMeasure_of_continuousAt_one {f : ℝ → ℝ}
    (hfm : Measurable f) (hfc : ContinuousAt f 1) (hf : ∀ x, f x ∈ Icc 0 1) :
    Tendsto (fun ν ↦ ∫ x, f x ∂gammaMeasure ν ν) atTop (𝓝 (f 1)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hc : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hfc (ε / 2) hc
  have hlim : Tendsto (fun ν : ℝ ↦ ν⁻¹ / δ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).div_const (δ ^ 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hc)] with ν hν htail
  let μ := gammaMeasure ν ν
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure hν hν
  have hint : Integrable f μ := (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hf x).1]; exact (hf x).2)
  -- The gamma concentration estimate uses its first two moments.
  have hcenter : ∫ x, x ∂μ = 1 := by
    simpa only [id_eq, div_self hν.ne'] using TauCeti.Probability.integral_id_gammaMeasure hν hν
  have hvar : ∫ x, (x - 1) ^ 2 ∂μ = ν⁻¹ := calc
    _ = variance id μ := by
      symm
      simpa only [id_eq, hcenter] using
        (variance_eq_integral (μ := μ) (X := id) measurable_id.aemeasurable)
    _ = _ := by
      dsimp only [μ]
      rw [TauCeti.Probability.variance_id_gammaMeasure hν hν]
      field_simp
  have hint₂ : Integrable (fun x : ℝ ↦ ((x - 1) ^ 2)) μ :=
    ((TauCeti.Probability.memLp_id_gammaMeasure hν hν).sub (memLp_const 1)).integrable_sq
  have hbound (x : ℝ) : ‖f x - f 1‖ ≤ ε / 2 + (x - 1) ^ 2 / δ ^ 2 := by
    by_cases hx : dist x 1 < δ
    · have hclose : ‖f x - f 1‖ ≤ ε / 2 := by
        simpa only [Real.norm_eq_abs, ← Real.dist_eq] using (hδf hx).le
      exact hclose.trans (le_add_of_nonneg_right (by positivity))
    · have htail' : 1 ≤ (x - 1) ^ 2 / δ ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hδ), one_mul, ← sq_abs (x - 1)]
        rw [Real.dist_eq] at hx
        exact pow_le_pow_left₀ hδ.le (le_of_not_gt hx) _
      have hc' : ‖f x - f 1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hf x).1, (hf 1).2], by linarith [(hf x).2, (hf 1).1]⟩
      exact hc'.trans (htail'.trans (le_add_of_nonneg_left hc.le))
  have hconst : (∫ _ : ℝ, f 1 ∂μ) = f 1 := by
    rw [integral_const, probReal_univ, one_smul]
  rw [Real.dist_eq, ← Real.norm_eq_abs, ← hconst, ← integral_sub hint (integrable_const (f 1))]
  apply (norm_integral_le_of_norm_le ((integrable_const (ε / 2)).add (hint₂.div_const _))
    (ae_of_all _ hbound)).trans_lt
  rw [integral_add' (integrable_const _) (hint₂.div_const _), integral_const,
    integral_div, hvar, probReal_univ, one_smul]
  linarith

/-- SYNOPSIS item 12: under the rescaling `θ = 1/(2√ν)`, the Matérn correlations converge
pointwise to the squared-exponential correlation. -/
theorem tendsto_maternCorrelation_gaussian {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun ν ↦ maternCorrelation ν (1 / (2 * Real.sqrt ν)) t) atTop
      (𝓝 (Real.exp (-t ^ 2))) := by
  let f (x : ℝ) := if 0 < x then Real.exp (-(t ^ 2 / x)) else 0
  have hfm : Measurable f :=
    Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  have hfc : ContinuousAt f 1 := by
    have hconst : ContinuousAt (fun _ : ℝ ↦ t ^ 2) 1 := continuousAt_const
    have h : ContinuousAt (fun x : ℝ ↦ Real.exp (-(t ^ 2 / x))) 1 :=
      (hconst.div continuousAt_id one_ne_zero).neg.rexp
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)] with x hx
    exact ite_eq_left (show 0 < x from hx)
  have hf (x : ℝ) : f x ∈ Icc 0 1 := by
    by_cases hx : 0 < x
    · simp only [f, ite_eq_left hx]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))⟩
    · simp only [f, ite_eq_right hx]
      exact ⟨le_rfl, zero_le_one⟩
  have heq : f 1 = Real.exp (-t ^ 2) := by simp [f]
  rw [← heq]
  refine (tendsto_integral_gammaMeasure_of_continuousAt_one hfm hfc hf).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ν hν
  have hθ : 0 < 1 / (2 * Real.sqrt ν) := by positivity
  have hscale := TauCeti.Probability.gammaMeasure_map_const_mul
    (a := ν) (r := 1) (inv_pos.mpr hν)
  rw [div_inv_eq_mul, one_mul] at hscale
  rw [maternCorrelation_eq_integral_gammaMeasure hν hθ ht, ← hscale,
    integral_map (measurable_const_mul _).aemeasurable hfm.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with x hx
  have hx' : 0 < ν⁻¹ * x := mul_pos (inv_pos.mpr hν) hx
  have hdenom : 4 * (1 / (2 * Real.sqrt ν)) ^ 2 * x = ν⁻¹ * x := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hν.le]
    field_simp
    norm_num
  simp only [f, ite_eq_left hx', hdenom]

/-- The gamma variable of shape `ν < 1/2` is the product of an independent gamma variable
of shape `1/2` and a beta variable of shapes `ν, 1/2 - ν`. -/
private lemma gammaMeasure_eq_map_mul_betaMeasure_prod_gammaMeasure_half {ν : ℝ}
    (hν : 0 < ν) (hν' : ν < 1 / 2) :
    ((betaMeasure ν (1 / 2 - ν)).prod (gammaMeasure (1 / 2) 1)).map
      (fun z : ℝ × ℝ ↦ z.1 * z.2) = gammaMeasure ν 1 := by
  have hβ : 0 < 1 / 2 - ν := sub_pos.mpr hν'
  have hsum : ν + (1 / 2 - ν) = 1 / 2 := by ring
  let μ₁ := gammaMeasure ν 1
  let μ₂ := gammaMeasure (1 / 2 - ν) 1
  let _ : IsProbabilityMeasure μ₂ := isProbabilityMeasure_gammaMeasure hβ one_pos
  let f (z : ℝ × ℝ) := (z.1 / (z.1 + z.2), z.1 + z.2)
  have hm : Measurable f := by fun_prop
  -- Invert TauCeti's gamma–beta factorization by multiplying the ratio by the sum.
  have hprod := TauCeti.Probability.map_div_add_prod_gammaMeasure hν hβ one_pos
  rw [hsum] at hprod
  rw [← hprod, Measure.map_map (by fun_prop) hm]
  have hae : ∀ᵐ z ∂μ₁.prod μ₂, z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
    TauCeti.Probability.ae_mem_prod_Ioi_gammaMeasure
  have heq : (fun z : ℝ × ℝ ↦ z.1 * z.2) ∘ f =ᵐ[μ₁.prod μ₂] Prod.fst := by
    filter_upwards [hae] with z hz
    have hp : 0 < z.1 + z.2 := add_pos hz.1 hz.2
    simp only [Function.comp_apply, f, div_mul_cancel₀ _ hp.ne']
  rw [Measure.map_congr heq, Measure.map_fst_prod, measure_univ, one_smul]

/-- Shape parameters below one-half express Matérn correlations as exponential mixtures. -/
private lemma maternCorrelation_eq_integral_betaMeasure {ν θ t : ℝ}
    (hν : 0 < ν) (hν' : ν < 1 / 2) (hθ : 0 < θ) (ht : 0 ≤ t) :
    maternCorrelation ν θ t =
      ∫ u, Real.exp (-(t / (θ * Real.sqrt u))) ∂betaMeasure ν (1 / 2 - ν) := by
  let μ := betaMeasure ν (1 / 2 - ν)
  let γ := gammaMeasure (1 / 2 : ℝ) 1
  let _ : IsProbabilityMeasure μ := isProbabilityMeasureBeta hν (sub_pos.mpr hν')
  let _ : IsProbabilityMeasure γ := isProbabilityMeasure_gammaMeasure (by norm_num) one_pos
  let f (z : ℝ × ℝ) := Real.exp (-(t ^ 2 / (4 * θ ^ 2 * (z.1 * z.2))))
  have hf : Integrable f (μ.prod γ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    have hpos : ∀ᵐ z ∂μ.prod γ, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioi)]
      filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure ν (1 / 2 - ν)] with u hu
      filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure (1 / 2 : ℝ) 1] with v hv
      exact ⟨hu, hv⟩
    filter_upwards [hpos] with z hz
    have hz₀ : 0 < z.1 := hz.1.1
    have hz₁ : 0 < z.2 := hz.2
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity)
  have hkernel : Measurable (fun x : ℝ ↦ Real.exp (-(t ^ 2 / (4 * θ ^ 2 * x)))) := by fun_prop
  rw [maternCorrelation_eq_integral_gammaMeasure hν hθ ht,
    ← gammaMeasure_eq_map_mul_betaMeasure_prod_gammaMeasure_half hν hν',
    integral_map (by fun_prop : Measurable (fun z : ℝ × ℝ ↦ z.1 * z.2)).aemeasurable
      hkernel.aestronglyMeasurable]
  calc
    _ = ∫ u, (∫ v, f (u, v) ∂γ) ∂μ := integral_prod _ hf
    _ = _ := by
      refine integral_congr_ae ?_
      filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure ν (1 / 2 - ν)] with u hu
      have hs : 0 < θ * Real.sqrt u := mul_pos hθ (Real.sqrt_pos.2 hu.1)
      rw [← neg_div, ← maternCorrelation_half hs ht, maternCorrelation_eq_integral_gammaMeasure
        (by norm_num) hs ht]
      apply integral_congr_ae <| ae_of_all _ fun v ↦ ?_
      simp only [f, mul_pow, Real.sq_sqrt hu.1.le, mul_assoc]

/-- Below shape one-half the exponential mixture gives complete monotonicity. -/
private lemma isContinuousCompletelyMonotoneOnIoi_maternCorrelation_of_lt_half
    {ν θ : ℝ} (hν : 0 < ν) (hν' : ν < 1 / 2) (hθ : 0 < θ) :
    TauCeti.IsContinuousCompletelyMonotoneOnIoi (maternCorrelation ν θ) := by
  let μ := betaMeasure ν (1 / 2 - ν)
  let rate (u : ℝ) := Real.toNNReal ((θ * Real.sqrt u)⁻¹)
  have hr : Measurable rate := by fun_prop
  let _ : IsProbabilityMeasure μ := isProbabilityMeasureBeta hν (sub_pos.mpr hν')
  have _ : IsProbabilityMeasure (μ.map rate) :=
    (Measure.isProbabilityMeasure_map_iff hr.aemeasurable).2 inferInstance
  refine (TauCeti.isContinuousCompletelyMonotoneOnIoi_laplaceTransform (μ.map rate)).congr
    fun t ht ↦ ?_
  rw [maternCorrelation_eq_integral_betaMeasure hν hν' hθ ht,
    TauCeti.laplaceTransform_apply,
    integral_map hr.aemeasurable ((by fun_prop : Continuous
      (fun r : ℝ≥0 ↦ Real.exp (-(t * (r : ℝ))))).aestronglyMeasurable)]
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure ν (1 / 2 - ν)] with u hu
  have hp : 0 < θ * Real.sqrt u := mul_pos hθ (Real.sqrt_pos.2 hu.1)
  simp only [rate, Real.coe_toNNReal _ (inv_nonneg_of_nonneg hp.le), div_eq_mul_inv]

/-- A Gaussian profile at an inverse gamma scale is integrable under the gamma law. -/
lemma integrable_exp_neg_div_gammaMeasure {ν θ : ℝ} (hν : 0 < ν) (t : ℝ) :
    Integrable (fun u : ℝ ↦ Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u)))) (gammaMeasure ν 1) := by
  let _ := isProbabilityMeasure_gammaMeasure hν one_pos
  apply (integrable_const (1 : ℝ)).mono' (by
    exact (by fun_prop : Measurable (fun u : ℝ ↦
      Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u))))).aestronglyMeasurable)
  filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (by positivity)

/-- A Matérn correlation is strictly less than one at a positive lag. -/
lemma maternCorrelation_lt_one {ν θ t : ℝ} (hν : 0 < ν) (hθ : 0 < θ) (ht : 0 < t) :
    maternCorrelation ν θ t < 1 := by
  let μ := gammaMeasure ν 1
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure hν one_pos
  let f (u : ℝ) := Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u)))
  have hlt : ∀ᵐ u ∂μ, f u < 1 := by
    filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  have hle := hlt.mono (fun _ h ↦ h.le)
  have hf : Integrable f μ := integrable_exp_neg_div_gammaMeasure (θ := θ) hν t
  have heq : (∫ u : ℝ, (1 : ℝ) ∂μ) = 1 := by simp
  rw [maternCorrelation_eq_integral_gammaMeasure hν hθ ht.le]
  refine (lt_of_le_of_ne (integral_mono_ae hf (integrable_const 1) hle) ?_).trans_eq heq
  intro h
  have hzero := (integral_eq_iff_of_ae_le hf (integrable_const 1) hle).mp h
  obtain ⟨u, hu, hu'⟩ := (hlt.and hzero).exists
  exact hu.ne hu'

/-- For exponents between zero and one, a power dominates the deficit of a decaying exponential. -/
lemma one_sub_exp_neg_le_rpow {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    1 - Real.exp (-x) ≤ x ^ p := by
  by_cases hx' : x ≤ 1
  · calc
      _ ≤ x := by linarith [Real.add_one_le_exp (-x)]
      _ = x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' hx hx' hp hp'
  · exact (sub_le_self _ (Real.exp_pos _).le).trans (Real.one_le_rpow (le_of_not_ge hx') hp)

/-- The deficit of the Matérn correlation is bounded by a fractional power of the lag whenever
the corresponding negative gamma moment is finite. -/
lemma one_sub_maternCorrelation_le_mul_rpow {ν θ t p : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    (ht : 0 ≤ t) (hp : 0 ≤ p) (hp' : p ≤ 1) (hνp : p < ν) :
    1 - maternCorrelation ν θ t ≤
      ((4 * θ ^ 2) ^ (-p) * ∫ u, u ^ (-p) ∂gammaMeasure ν 1) * t ^ (2 * p) := by
  let μ := gammaMeasure ν 1
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure hν one_pos
  let C := (4 * θ ^ 2) ^ (-p) * t ^ (2 * p)
  have hpos : 0 < 4 * θ ^ 2 := by positivity
  have hm : Integrable (fun u : ℝ ↦ u ^ (-p)) μ :=
    (TauCeti.Probability.integrable_rpow_gammaMeasure_iff hν one_pos _).mpr (by linarith)
  have hf : Integrable (fun u : ℝ ↦ Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u)))) μ :=
    integrable_exp_neg_div_gammaMeasure hν t
  have hbound : ∀ᵐ u ∂μ, 1 - Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u))) ≤ C * u ^ (-p) := by
    filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
    apply (one_sub_exp_neg_le_rpow (by positivity) hp hp').trans_eq
    dsimp only [C]
    rw [Real.div_rpow (sq_nonneg t) (mul_nonneg hpos.le hu.le),
      Real.mul_rpow hpos.le hu.le, Real.rpow_neg hpos.le, Real.rpow_neg hu.le,
      ← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
    push_cast
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hconst : (∫ u : ℝ, (1 : ℝ) ∂μ) = 1 := by simp
  have heq : 1 - maternCorrelation ν θ t =
      ∫ u, (1 - Real.exp (-(t ^ 2 / (4 * θ ^ 2 * u)))) ∂μ := by
    rw [integral_sub (integrable_const 1) hf, hconst,
      maternCorrelation_eq_integral_gammaMeasure hν hθ ht]
  rw [heq]
  exact (integral_mono_ae ((integrable_const _).sub hf) (hm.const_mul _) hbound).trans_eq <|
    by rw [integral_const_mul]; dsimp only [C]; ring

/-- Complete monotonicity with continuity at zero implies convexity on the closed half-line. -/
lemma convexOn_of_isContinuousCompletelyMonotoneOnIoi {f : ℝ → ℝ}
    (hf : TauCeti.IsContinuousCompletelyMonotoneOnIoi f) : ConvexOn ℝ (Ici 0) f := by
  have hd := hf.isCompletelyMonotoneOnIoi.contDiffOn
  refine convexOn_of_deriv2_nonneg (convex_Ici 0) hf.continuousOn ?_ ?_ ?_
  · rw [interior_Ici]
    exact hd.differentiableOn (by simp)
  · rw [interior_Ici]
    exact (hd.deriv_of_isOpen isOpen_Ioi (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiableOn
      (by simp)
  · rw [interior_Ici]
    intro x hx
    simpa [iteratedDeriv_eq_iterate] using
      hf.isCompletelyMonotoneOnIoi.neg_one_pow_mul_iteratedDeriv_nonneg 2 hx

/-- The fractional-power bound precludes complete monotonicity above shape one-half. -/
private lemma not_isContinuousCompletelyMonotoneOnIoi_maternCorrelation {ν θ : ℝ}
    (hν : 1 / 2 < ν) (hθ : 0 < θ) :
    ¬ TauCeti.IsContinuousCompletelyMonotoneOnIoi (maternCorrelation ν θ) := by
  intro h
  let p := (1 / 2 + min 1 ν) / 2
  have hp : 1 / 2 < p := by
    dsimp only [p]
    linarith [lt_min (by norm_num : (1 / 2 : ℝ) < 1) hν]
  have hp' : p ≤ 1 := by dsimp only [p]; linarith [min_le_left 1 ν]
  have hpν : p < ν := by dsimp only [p]; linarith [min_le_right 1 ν]
  have hp0 : 0 ≤ p := by linarith
  have hν0 : 0 < ν := by linarith
  let C := (4 * θ ^ 2) ^ (-p) * ∫ u, u ^ (-p) ∂gammaMeasure ν 1
  have hconv := convexOn_of_isContinuousCompletelyMonotoneOnIoi h
  have hratio (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) :
      1 - maternCorrelation ν θ 1 ≤ C * t ^ (2 * p - 1) := by
    have hzero : (0 : ℝ) ∈ Ici 0 := le_rfl
    have hone : (1 : ℝ) ∈ Ici 0 := zero_le_one
    have hchord := hconv.2 hzero hone (sub_nonneg.mpr ht₁.le) ht₀.le (by ring)
    have h0 : maternCorrelation ν θ 0 = 1 := by simp [maternCorrelation_def]
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, h0] at hchord
    have hpow := one_sub_maternCorrelation_le_mul_rpow hν0 hθ ht₀.le hp0 hp' hpν
    have hs : t * (1 - maternCorrelation ν θ 1) ≤ C * t ^ (2 * p) := by
      dsimp only [C]
      nlinarith only [hchord, hpow]
    have hpdiv : t * (C * t ^ (2 * p - 1)) = C * t ^ (2 * p) := by
      rw [Real.rpow_sub ht₀, Real.rpow_one]
      field_simp [ht₀.ne']
    exact le_of_mul_le_mul_left (hs.trans_eq hpdiv.symm) ht₀
  have hp_exp : 0 < 2 * p - 1 := by linarith
  have htend : Tendsto (fun t : ℝ ↦ C * t ^ (2 * p - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hcont := (Real.continuous_rpow_const hp_exp.le).continuousAt (x := (0 : ℝ))
    simpa only [Real.zero_rpow hp_exp.ne', mul_zero] using
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).const_mul C
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, 1 - maternCorrelation ν θ 1 ≤ C * t ^ (2 * p - 1) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with
      t ht₀ ht₁
    exact hratio t ht₀ ht₁
  have hn := le_of_tendsto_of_tendsto tendsto_const_nhds htend hh
  have hstrict := maternCorrelation_lt_one hν0 hθ zero_lt_one
  linarith

/-- SYNOPSIS item 12: the Matérn correlation is completely monotone in the lag precisely when
`ν ≤ 1/2`. -/
theorem maternCorrelation_completelyMonotone_iff {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    TauCeti.IsContinuousCompletelyMonotoneOnIoi (maternCorrelation ν θ) ↔ ν ≤ 1 / 2 := by
  constructor
  · intro hf
    exact le_of_not_gt fun h ↦ not_isContinuousCompletelyMonotoneOnIoi_maternCorrelation h hθ hf
  · intro h
    rcases h.eq_or_lt with rfl | h
    · have he := TauCeti.IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone
        (TauCeti.isCompletelyMonotone_exp_neg_mul (inv_pos.mpr hθ).le)
      refine he.congr fun t ht ↦ ?_
      rw [maternCorrelation_half hθ ht, neg_div, div_eq_mul_inv]
      apply congrArg Real.exp
      ring
    · exact isContinuousCompletelyMonotoneOnIoi_maternCorrelation_of_lt_half hν h hθ

end MSSS
