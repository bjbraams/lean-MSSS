module

public import MSSS.RandomFields.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Probability.Distributions.Cauchy

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.Distributions.Cauchy.Basic

/-!
# Spectral representation and mean-square calculus of stationary fields

SYNOPSIS items 5 and 7. The spectral measure `F` of a stationary field on a finite-dimensional
real inner-product space `E` is the finite measure with `C(h) = ∫ e^{i⟨ω, h⟩} F(dω)`
(`charFun F h`, the angular convention of the synopsis).

The stochastic integral against a complex random measure `W` with orthogonal increments and
`E |W(A)|² = F(A)` is the linear isometry `I : L²(F) → L²(P)` with `I 1_A = W(A)`; conversely
every linear isometry `I : L²(F) → L²(P)` defines such a random measure by `W(A) = I 1_A`,
since `E (W(A) conj W(B)) = ⟪1_B, 1_A⟫ = F(A ∩ B)`. Item 5 is therefore stated with the
isometry `I`, and `Z(t) = ∫ e^{i⟨t, ω⟩} W(dω)` reads `I (e_t) = Z t`.

## Main definitions

* `MSSS.expLp F t`: the character `ω ↦ e^{i⟨ω, t⟩}` as an element of `L²(F)`.
* `MSSS.HasMeanSquareDeriv Z Z' P`: `Z'` is the mean-square derivative of a process on `ℝ`.
* `MSSS.IsMeanSquareDifferentiable m Z P`: `Z` is `m` times mean-square differentiable.
* `MSSS.HasFiniteIteratedDerivAt n K x`: the `n`th derivative of `K` exists at `x`.

The exponential characters are dense by Mathlib's characteristic-function uniqueness
and Radon–Nikodým derivative. TauCeti's Gram identity for finite linear combinations
and Mathlib's extension from a dense domain give the spectral isometry. The covariance
of the spectral integrals uses Mathlib's `L²` inner product. The covariance of mean-square
derivatives follows by differentiating the real `L²` Gram kernel using Mathlib's inner-product
calculus, and using continuity of a uniform limit for the differentiated field. The Cauchy example
uses Mathlib's trigonometric integrals and independence of the phase, and TauCeti's characteristic
function of a Cauchy law.

## Main results

* `MSSS.exists_spectralRepresentation`, `MSSS.integral_spectralIntegral_mul_conj`:
  SYNOPSIS item 5.
* `MSSS.isMeanSquareDifferentiable_tfae`: SYNOPSIS item 7, equivalence (admitted).
* `MSSS.IsMeanSquareDifferentiable.derivative`: SYNOPSIS item 7, covariance regularity
  and stationarity of the mean-square derivatives.
* `MSSS.not_isMeanSquareDifferentiable_cos_cauchy`: the analytic Cauchy-phase example of item 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ComplexConjugate RealInnerProductSpace InnerProductSpace

namespace MSSS

variable {Ω : Type*} [MeasurableSpace Ω]

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma memLp_exp_inner_mul_I (F : Measure E) [IsFiniteMeasure F] (t : E) :
    MemLp (fun ω : E ↦ exp ((⟪ω, t⟫ : ℂ) * I)) 2 F := by
  refine (memLp_top_of_bound (by fun_prop : Continuous fun ω : E ↦
    exp ((⟪ω, t⟫ : ℂ) * I)).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)).mono_exponent
    le_top
  rw [Complex.norm_exp_ofReal_mul_I]

omit [FiniteDimensional ℝ E] in
/-- The character `ω ↦ e^{i⟨ω, t⟩}` as an element of `L²(F)` for a finite measure `F`. -/
def expLp (F : Measure E) [IsFiniteMeasure F] (t : E) : Lp ℂ 2 F :=
  (memLp_exp_inner_mul_I F t).toLp _

omit [FiniteDimensional ℝ E] in
lemma expLp_ae_eq (F : Measure E) [IsFiniteMeasure F] (t : E) :
    expLp F t =ᵐ[F] fun ω ↦ exp ((⟪ω, t⟫ : ℂ) * I) := by
  rw [expLp]
  exact MemLp.coeFn_toLp _

omit [FiniteDimensional ℝ E] in
/-- Multiplication by an exponential character preserves integrability. -/
lemma integrable_mul_exp_inner_mul_I {F : Measure E} {g : E → ℂ} (hg : Integrable g F) (t : E) :
    Integrable (fun w ↦ g w * exp ((⟪w, t⟫ : ℂ) * I)) F := by
  have hc : Continuous (fun w : E ↦ exp ((⟪w, t⟫ : ℂ) * I)) := by fun_prop
  apply hg.mul_bdd hc.aestronglyMeasurable
  exact ae_of_all _ fun w ↦ (norm_exp_ofReal_mul_I _).le

/-- A real integrable weight whose Fourier integrals vanish is zero almost everywhere.
This follows from characteristic-function uniqueness for its positive and negative parts. -/
lemma ae_eq_zero_of_integral_ofReal_mul_exp_inner_mul_I
    (F : Measure E) [IsFiniteMeasure F] {g : E → ℝ} (hg : Integrable g F)
    (h : ∀ t : E, ∫ w, (g w : ℂ) * exp ((⟪w, t⟫ : ℂ) * I) ∂F = 0) :
    g =ᵐ[F] 0 := by
  let p (w : E) := max (g w) 0
  let n (w : E) := max (-g w) 0
  let μ := F.withDensity fun w ↦ ENNReal.ofReal (p w)
  let ν := F.withDensity fun w ↦ ENNReal.ofReal (n w)
  have hp : Integrable p F := hg.sup (integrable_const 0)
  have hn : Integrable n F := hg.neg.sup (integrable_const 0)
  let _ : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hp.hasFiniteIntegral
  let _ : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hn.hasFiniteIntegral
  have hpn (w : E) : p w - n w = g w := by
    dsimp only [p, n]
    rcases le_total 0 (g w) with hw | hw
    · simp only [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw), sub_zero]
    · simp only [max_eq_right hw, max_eq_left (neg_nonneg.mpr hw), zero_sub, neg_neg]
  have hchar (k : E → ℝ) (hk : Integrable k F) (hk0 : ∀ w, 0 ≤ k w) (t : E) :
      charFun (F.withDensity fun w ↦ ENNReal.ofReal (k w)) t =
        ∫ w, (k w : ℂ) * exp ((⟪w, t⟫ : ℂ) * I) ∂F := by
    rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul₀
      hk.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hk0 _), Complex.real_smul]
  -- Uniqueness for finite measures identifies the positive and negative spectral weights.
  have heq : μ = ν := by
    apply Measure.ext_of_charFun
    funext t
    apply sub_eq_zero.mp
    rw [hchar p hp (fun w ↦ le_max_right _ _) t, hchar n hn (fun w ↦ le_max_right _ _) t]
    calc
      _ = ∫ w, ((p w : ℂ) * exp ((⟪w, t⟫ : ℂ) * I) -
          (n w : ℂ) * exp ((⟪w, t⟫ : ℂ) * I)) ∂F :=
        (integral_sub (integrable_mul_exp_inner_mul_I hp.ofReal t)
          (integrable_mul_exp_inner_mul_I hn.ofReal t)).symm
      _ = ∫ w, (g w : ℂ) * exp ((⟪w, t⟫ : ℂ) * I) ∂F := by
        apply integral_congr_ae <| ae_of_all _ fun w ↦ ?_
        rw [← sub_mul, ← ofReal_sub, hpn]
      _ = 0 := h t
  have hrn : (fun w ↦ ENNReal.ofReal (p w)) =ᵐ[F] fun w ↦ ENNReal.ofReal (n w) := by
    have hμ : μ.rnDeriv F =ᵐ[F] fun w ↦ ENNReal.ofReal (p w) :=
      Measure.rnDeriv_withDensity₀ F hp.aemeasurable.ennreal_ofReal
    have hν : ν.rnDeriv F =ᵐ[F] fun w ↦ ENNReal.ofReal (n w) :=
      Measure.rnDeriv_withDensity₀ F hn.aemeasurable.ennreal_ofReal
    rw [heq] at hμ
    exact hμ.symm.trans hν
  filter_upwards [hrn] with w hw
  have hpw : 0 ≤ p w := le_max_right _ _
  have hnw : 0 ≤ n w := le_max_right _ _
  have hw' : p w = n w := by
    simpa only [ENNReal.toReal_ofReal hpw, ENNReal.toReal_ofReal hnw] using
      congrArg ENNReal.toReal hw
  rw [← hpn, hw', sub_self, Pi.zero_apply]

/-- A complex integrable weight whose Fourier integrals vanish is zero almost everywhere. -/
lemma ae_eq_zero_of_integral_mul_exp_inner_mul_I
    (F : Measure E) [IsFiniteMeasure F] {g : E → ℂ} (hg : Integrable g F)
    (h : ∀ t : E, ∫ w, g w * exp ((⟪w, t⟫ : ℂ) * I) ∂F = 0) :
    g =ᵐ[F] 0 := by
  let χ (s w : E) := exp ((⟪w, s⟫ : ℂ) * I)
  have hχ (s w : E) : conj (χ (-s) w) = χ s w := by
    dsimp only [χ]
    rw [← exp_conj, map_mul, inner_neg_right, ofReal_neg, map_neg, conj_ofReal, conj_I]
    simp only [neg_mul_neg]
  have hgin : Integrable (fun w ↦ conj (g w)) F :=
    hg.mono (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
      (ae_of_all _ fun w ↦ (Complex.norm_conj (g w)).le)
  have hconj (t : E) : ∫ w, conj (g w) * χ t w ∂F = 0 := by
    calc
      _ = conj (∫ w, g w * χ (-t) w ∂F) := by
        rw [← integral_conj]
        exact integral_congr_ae <| ae_of_all _ fun w ↦ by
          dsimp only
          rw [map_mul, hχ]
      _ = 0 := by rw [h (-t), map_zero]
  have hre (t : E) : ∫ w, ((g w).re : ℂ) * χ t w ∂F = 0 := by
    have hs : (2 : ℂ) * (∫ w, ((g w).re : ℂ) * χ t w ∂F) = 0 := by
      rw [← integral_const_mul]
      have heq (w : E) : (2 : ℂ) * (((g w).re : ℂ) * χ t w) =
          g w * χ t w + conj (g w) * χ t w := by
        rw [← add_mul, ← mul_assoc, Complex.add_conj, ofReal_mul, ofReal_ofNat]
      rw [integral_congr_ae (ae_of_all _ heq),
        integral_add (integrable_mul_exp_inner_mul_I hg t)
          (integrable_mul_exp_inner_mul_I hgin t), h t, hconj t, add_zero]
    exact (mul_eq_zero.mp hs).resolve_left two_ne_zero
  have him (t : E) : ∫ w, ((g w).im : ℂ) * χ t w ∂F = 0 := by
    have hs : (2 * I : ℂ) * (∫ w, ((g w).im : ℂ) * χ t w ∂F) = 0 := by
      rw [← integral_const_mul]
      have heq (w : E) : (2 * I : ℂ) * (((g w).im : ℂ) * χ t w) =
          g w * χ t w - conj (g w) * χ t w := by
        rw [← sub_mul, ← mul_assoc, Complex.sub_conj, ofReal_mul, ofReal_ofNat]
        ring
      rw [integral_congr_ae (ae_of_all _ heq),
        integral_sub (integrable_mul_exp_inner_mul_I hg t)
          (integrable_mul_exp_inner_mul_I hgin t), h t, hconj t, sub_zero]
    exact (mul_eq_zero.mp hs).resolve_left (mul_ne_zero two_ne_zero I_ne_zero)
  have hr₀ := ae_eq_zero_of_integral_ofReal_mul_exp_inner_mul_I F hg.re hre
  have hi₀ := ae_eq_zero_of_integral_ofReal_mul_exp_inner_mul_I F hg.im him
  filter_upwards [hr₀, hi₀] with w hw₀ hw₁
  exact Complex.ext hw₀ hw₁

/-- The exponential characters span a dense subspace of the spectral `L²`. -/
lemma dense_span_expLp (F : Measure E) [IsFiniteMeasure F] :
    Dense (Submodule.span ℂ (Set.range (expLp F)) : Set (Lp ℂ 2 F)) := by
  let S := Submodule.span ℂ (Set.range (expLp F))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm ?_ bot_le
  intro g hg
  have hg₁ : Integrable (fun w ↦ g w) F := (Lp.memLp g).integrable (by norm_num)
  have h (t : E) : ∫ w, g w * exp ((⟪w, t⟫ : ℂ) * I) ∂F = 0 := calc
    _ = ⟪expLp F (-t), g⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [expLp_ae_eq F (-t)] with w hw
      rw [RCLike.inner_apply, hw, ← exp_conj, map_mul, inner_neg_right, ofReal_neg,
        map_neg, conj_ofReal, conj_I, neg_mul_neg]
    _ = 0 := (Submodule.mem_orthogonal S g).mp hg _
      (Submodule.subset_span (Set.mem_range_self (-t)))
  apply (Submodule.mem_bot (R := ℂ) (M := Lp ℂ 2 F)).mpr
  have hzero : ((0 : Lp ℂ 2 F) : E → ℂ) =ᵐ[F] 0 := Lp.coeFn_zero ℂ 2 F
  exact Lp.ext <| (ae_eq_zero_of_integral_mul_exp_inner_mul_I F hg₁ h).trans hzero.symm

section LinearIsometry

variable {𝕜 H K T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Families with equal Gram kernels and a dense first span induce a linear isometry. -/
lemma exists_linearIsometry_apply_of_inner_eq {v : T → H} {w : T → K}
    (hd : Dense (Submodule.span 𝕜 (Set.range v) : Set H))
    (h : ∀ s t, ⟪v s, v t⟫_𝕜 = ⟪w s, w t⟫_𝕜) :
    ∃ I : H →ₗᵢ[𝕜] K, ∀ t, I (v t) = w t := by
  let e := Finsupp.linearCombination 𝕜 v
  let J := Finsupp.linearCombination 𝕜 w
  have hdense : DenseRange e := by
    dsimp only [DenseRange, e]
    rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact hd
  -- TauCeti's Gram identity gives equal norms for every finite combination.
  have hnorm (a : T →₀ 𝕜) : ‖J a‖ = ‖e a‖ :=
    Finsupp.norm_linearCombination_eq_of_inner_eq a (fun s t ↦ (h s t).symm)
  have hbound : ∃ C, ∀ a, ‖J a‖ ≤ C * ‖e a‖ :=
    ⟨1, fun a ↦ by rw [one_mul, hnorm]⟩
  let L := J.extendOfNorm e
  have hL (a : T →₀ 𝕜) : L (e a) = J a := LinearMap.extendOfNorm_eq hdense hbound a
  have hnormL (x : H) : ‖L x‖ = ‖x‖ := by
    refine hdense.induction_on x (isClosed_eq L.continuous.norm continuous_norm) ?_
    intro a
    rw [hL, hnorm]
  refine ⟨LinearIsometry.mk L.toLinearMap hnormL, fun t ↦ ?_⟩
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe]
  simpa only [e, J, Finsupp.linearCombination_single, one_smul] using
    hL (Finsupp.single t 1)

end LinearIsometry

omit [FiniteDimensional ℝ E] in
/-- The (L²) inner product of two exponential characters is a characteristic function
at their frequency difference. -/
lemma inner_expLp_expLp (F : Measure E) [IsFiniteMeasure F] (s t : E) :
    ⟪expLp F s, expLp F t⟫_ℂ = charFun F (t - s) := by
  rw [L2.inner_def, charFun_apply]
  apply integral_congr_ae
  filter_upwards [expLp_ae_eq F s, expLp_ae_eq F t] with w hs ht
  rw [hs, ht, RCLike.inner_apply, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_add,
    inner_sub_right, ofReal_sub]
  congr 1
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The L² inner products of complexified field values are the centered covariances. -/
private lemma inner_fieldLp_eq_stationaryCov {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : E → Ω → ℝ} (hZ : IsSecondOrderStationary Z P) (hcent : ∀ t, P[Z t] = 0) (s t : E) :
    ⟪(isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 s).ofReal.toLp
        (fun w ↦ (Z s w : ℂ)),
      (isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 t).ofReal.toLp
        (fun w ↦ (Z t w : ℂ))⟫_ℂ =
      (stationaryCov Z P (t - s) : ℂ) := by
  have htrans := (isSecondOrderStationary_iff.mp hZ).2.2 t s (-s)
  rw [← sub_eq_add_neg, add_neg_cancel] at htrans
  rw [stationaryCov_def, htrans, covariance, hcent, hcent, ← integral_complex_ofReal,
    L2.inner_def]
  simp only [sub_zero]
  apply integral_congr_ae
  have hsp : MemLp (fun w ↦ (Z s w : ℂ)) 2 P :=
    (isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 s).ofReal
  have htp : MemLp (fun w ↦ (Z t w : ℂ)) 2 P :=
    (isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 t).ofReal
  filter_upwards [hsp.coeFn_toLp, htp.coeFn_toLp] with w hs ht
  rw [RCLike.inner_apply, hs, ht, conj_ofReal, ofReal_mul]

/-- Integration on a finite-measure (L²) space is the inner product with the constant one. -/
lemma integral_L2_eq_inner_one (P : Measure Ω) [IsFiniteMeasure P] (f : Lp ℂ 2 P) :
    ∫ w, f w ∂P = ⟪(memLp_const (μ := P) (p := 2) (1 : ℂ)).toLp (fun _ ↦ 1), f⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (μ := P) (p := 2) (1 : ℂ)).coeFn_toLp] with w hw
  rw [RCLike.inner_apply, hw, map_one, mul_one]

-- The spectral hypothesis already supplies the regularity needed for the isometry.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 5: a centred, mean-square continuous, second-order stationary field with
spectral measure `F` is the stochastic integral `Z(t) = ∫ e^{i⟨t, ω⟩} W(dω)` against a centred
complex random measure with orthogonal increments and control measure `F`, encoded by the
linear isometry `I : L²(F) → L²(P)`, `W(A) = I 1_A`. -/
theorem exists_spectralRepresentation {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : E → Ω → ℝ} (hZ : IsSecondOrderStationary Z P) (hcent : ∀ t, P[Z t] = 0)
    (hms : IsMeanSquareContinuous Z P) (F : Measure E) [IsFiniteMeasure F]
    (hF : ∀ h, (stationaryCov Z P h : ℂ) = charFun F h) :
    ∃ I : Lp ℂ 2 F →ₗᵢ[ℂ] Lp ℂ 2 P, (∀ f, ∫ ω, I f ω ∂P = 0) ∧
      ∀ t, I (expLp F t) =ᵐ[P] fun ω ↦ (Z t ω : ℂ) := by
  have hw (t : E) : MemLp (fun ω ↦ (Z t ω : ℂ)) 2 P :=
    (isSecondOrderField_iff.mp (isSecondOrderStationary_iff.mp hZ).1 t).ofReal
  let w (t : E) := (hw t).toLp (fun ω ↦ (Z t ω : ℂ))
  have hGram (s t : E) : ⟪expLp F s, expLp F t⟫_ℂ = ⟪w s, w t⟫_ℂ := by
    rw [inner_expLp_expLp, inner_fieldLp_eq_stationaryCov hZ hcent, hF]
  have hDense := dense_span_expLp F
  obtain ⟨I, hI⟩ := exists_linearIsometry_apply_of_inner_eq hDense hGram
  have hrep (t : E) : I (expLp F t) =ᵐ[P] fun ω ↦ (Z t ω : ℂ) := by
    rw [hI]
    exact (hw t).coeFn_toLp
  refine ⟨I, fun f ↦ ?_, hrep⟩
  let u := (memLp_const (μ := P) (p := 2) (1 : ℂ)).toLp (fun _ ↦ 1)
  let L := (innerSL ℂ u).comp I.toContinuousLinearMap
  have hL (x : Lp ℂ 2 F) : (∫ ω, I x ω ∂P) = L x := integral_L2_eq_inner_one P (I x)
  rw [hL]
  have hz (t : E) : L (expLp F t) = 0 := by
    rw [← hL, integral_congr_ae (hrep t), integral_complex_ofReal, hcent t, ofReal_zero]
  have hspan : Submodule.span ℂ (Set.range (expLp F)) ≤ LinearMap.ker L.toLinearMap :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun t ↦ LinearMap.mem_ker.2 (hz t)
  have hclosed : IsClosed {x | L x = 0} := isClosed_eq L.continuous continuous_const
  have hincl : (Submodule.span ℂ (Set.range (expLp F)) : Set (Lp ℂ 2 F)) ⊆
      {x | L x = 0} := fun _ hx ↦ LinearMap.mem_ker.1 (hspan hx)
  exact closure_minimal hincl hclosed (hDense f)

-- Keep the finite-dimensional instance used in the spectral representation section.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 5, converse: a stochastic integral `Y(t) = ∫ e^{i⟨t, ω⟩} W(dω)` against an
orthogonally scattered random measure with control measure `F` is a second-order stationary
complex field with covariance `E (Y(s) conj Y(t)) = ∫ e^{i⟨s - t, ω⟩} F(dω)`; it is centred
when `W` is. -/
theorem integral_spectralIntegral_mul_conj {P : Measure Ω} (F : Measure E) [IsFiniteMeasure F]
    (I : Lp ℂ 2 F →ₗᵢ[ℂ] Lp ℂ 2 P) (s t : E) :
    ∫ ω, I (expLp F s) ω * conj (I (expLp F t) ω) ∂P = charFun F (s - t) := by
  calc
    ∫ ω, I (expLp F s) ω * conj (I (expLp F t) ω) ∂P =
        ⟪I (expLp F t), I (expLp F s)⟫_ℂ := by
      simp only [L2.inner_def, RCLike.inner_apply]
    _ = ⟪expLp F t, expLp F s⟫_ℂ := I.inner_map_map _ _
    _ = charFun F (s - t) := inner_expLp_expLp F t s

end Spectral

/-! ### Mean-square differentiability (SYNOPSIS item 7) -/

/-- `Z'` is the **mean-square derivative** of the process `Z` on `ℝ`:
`E ((Z(t + h) - Z(t)) / h - Z'(t))² → 0` as `h → 0`, for every `t`. -/
def HasMeanSquareDeriv (Z Z' : ℝ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ t, Tendsto (fun h ↦ ∫ ω, ((Z (t + h) ω - Z t ω) / h - Z' t ω) ^ 2 ∂P) (𝓝[≠] 0) (𝓝 0)

/-- `Z` is **`m` times mean-square differentiable** when there are square-integrable processes
`D 0 = Z, D 1, …, D m`, each the mean-square derivative of the previous one. -/
def IsMeanSquareDifferentiable (m : ℕ) (Z : ℝ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ D : ℕ → ℝ → Ω → ℝ, D 0 = Z ∧ ∀ k < m, IsSecondOrderField (D (k + 1)) P ∧
    HasMeanSquareDeriv (D k) (D (k + 1)) P

/-- The `n`th derivative of `K` exists (and is finite) at `x`: for `n ≥ 1`, `K` is `n - 1` times
continuously differentiable near `x` and its `(n - 1)`th derivative is differentiable at `x`. -/
def HasFiniteIteratedDerivAt (n : ℕ) (K : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ U ∈ 𝓝 x, ContDiffOn ℝ (n - 1) K U ∧ DifferentiableAt ℝ (iteratedDeriv (n - 1) K) x

lemma hasMeanSquareDeriv_iff {Z Z' : ℝ → Ω → ℝ} {P : Measure Ω} :
    HasMeanSquareDeriv Z Z' P ↔ ∀ t,
      Tendsto (fun h ↦ ∫ ω, ((Z (t + h) ω - Z t ω) / h - Z' t ω) ^ 2 ∂P) (𝓝[≠] 0) (𝓝 0) :=
  Iff.rfl

lemma isMeanSquareDifferentiable_iff {m : ℕ} {Z : ℝ → Ω → ℝ} {P : Measure Ω} :
    IsMeanSquareDifferentiable m Z P ↔ ∃ D : ℕ → ℝ → Ω → ℝ, D 0 = Z ∧ ∀ k < m,
      IsSecondOrderField (D (k + 1)) P ∧ HasMeanSquareDeriv (D k) (D (k + 1)) P := Iff.rfl

lemma hasFiniteIteratedDerivAt_iff {n : ℕ} {K : ℝ → ℝ} {x : ℝ} :
    HasFiniteIteratedDerivAt n K x ↔ ∃ U ∈ 𝓝 x, ContDiffOn ℝ (n - 1) K U ∧
      DifferentiableAt ℝ (iteratedDeriv (n - 1) K) x := Iff.rfl

/-- SYNOPSIS item 7, equivalence: for a centred second-order stationary process on `ℝ` with
covariance `K` and spectral measure `F`, and `m ≥ 1`, the following are equivalent: `Z` is `m`
times mean-square differentiable; `∫ ω^{2m} F(dω) < ∞`; `K^{(2m)}(0)` exists and is finite. -/
theorem isMeanSquareDifferentiable_tfae {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℝ → Ω → ℝ} (hZ : IsSecondOrderStationary Z P) (hcent : ∀ t, P[Z t] = 0)
    (F : Measure ℝ) [IsFiniteMeasure F]
    (hF : ∀ h, (stationaryCov Z P h : ℂ) = charFun F h) {m : ℕ} (hm : 1 ≤ m) :
    List.TFAE [IsMeanSquareDifferentiable m Z P,
      Integrable (fun ω : ℝ ↦ ω ^ (2 * m)) F,
      HasFiniteIteratedDerivAt (2 * m) (stationaryCov Z P) 0] := by
  sorry

/-- Represent the values of a second-order field as a curve in real `L²`. -/
private def fieldLp {P : Measure Ω} {Z : ℝ → Ω → ℝ} (hZ : IsSecondOrderField Z P)
    (t : ℝ) : Lp ℝ 2 P :=
  (isSecondOrderField_iff.mp hZ t).toLp (Z t)

/-- The `L²` representative agrees almost everywhere with the field value. -/
private lemma fieldLp_ae {P : Measure Ω} {Z : ℝ → Ω → ℝ} (hZ : IsSecondOrderField Z P)
    (t : ℝ) : fieldLp hZ t =ᵐ[P] Z t :=
  (isSecondOrderField_iff.mp hZ t).coeFn_toLp

/-- Mean-square derivatives are derivatives of the corresponding `L²` curves. -/
private lemma fieldLp_hasDerivAt {P : Measure Ω} {Z Z' : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderField Z P) (hZ' : IsSecondOrderField Z' P)
    (hdiff : HasMeanSquareDeriv Z Z' P) (t : ℝ) :
    HasDerivAt (fieldLp hZ) (fieldLp hZ' t) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  let e (h : ℝ) : Lp ℝ 2 P := h⁻¹ • (fieldLp hZ (t + h) - fieldLp hZ t) - fieldLp hZ' t
  have he (h : ℝ) : e h =ᵐ[P] fun w ↦ (Z (t + h) w - Z t w) / h - Z' t w := by
    filter_upwards [Lp.coeFn_sub (h⁻¹ • (fieldLp hZ (t + h) - fieldLp hZ t)) (fieldLp hZ' t),
      Lp.coeFn_smul h⁻¹ (fieldLp hZ (t + h) - fieldLp hZ t),
      Lp.coeFn_sub (fieldLp hZ (t + h)) (fieldLp hZ t), fieldLp_ae hZ (t + h),
      fieldLp_ae hZ t, fieldLp_ae hZ' t] with w h₁ h₂ h₃ h₄ h₅ h₆
    simpa only [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h₂, h₃, h₄, h₅, h₆,
      div_eq_inv_mul] using h₁
  have heq (h : ℝ) : ‖e h‖ = Real.sqrt (∫ w, ((Z (t + h) w - Z t w) / h - Z' t w) ^ 2 ∂P) := by
    rw [← Real.sqrt_sq (norm_nonneg (e h)), ← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [he h] with w hw
    simp [hw, Real.norm_eq_abs, sq_abs]
  have hnorm :
      (fun h : ℝ ↦ ‖h⁻¹ • (fieldLp hZ (t + h) - fieldLp hZ t) - fieldLp hZ' t‖) =
        fun h ↦ ‖e h‖ := rfl
  simp_rw [hnorm, heq]
  simpa only [Function.comp_def, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp (hdiff t)

/-- The inner product of real field values in `L²` is their mixed second moment. -/
private lemma fieldLp_inner {P : Measure Ω} {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderField Z P) (s t : ℝ) :
    ⟪fieldLp hZ s, fieldLp hZ t⟫_ℝ = ∫ w, Z t w * Z s w ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldLp_ae hZ s, fieldLp_ae hZ t] with w hs ht
  rw [RCLike.inner_apply, hs, ht, RCLike.conj_to_real]

/-- Pairing a field value with one in `L²` gives its expectation. -/
private lemma inner_one_fieldLp {P : Measure Ω} [IsFiniteMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderField Z P) (t : ℝ) :
    ⟪Lp.const 2 P (1 : ℝ), fieldLp hZ t⟫_ℝ = P[Z t] := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 P (1 : ℝ), fieldLp_ae hZ t] with w hw ht
  rw [RCLike.inner_apply, ht, RCLike.conj_to_real, hw, Function.const_apply, mul_one]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Differentiate the stationary Gram kernel in its second variable. -/
private lemma stationaryInner_right_deriv {X Y : ℝ → H} {K : ℝ → ℝ}
    (hgram : ∀ s t, ⟪X s, X t⟫_ℝ = K (t - s))
    (h : ∀ t, HasDerivAt X (Y t) t) (u : ℝ) :
    HasDerivAt K ⟪X 0, Y u⟫_ℝ u := by
  have hinner : HasDerivAt (fun t ↦ ⟪X 0, X t⟫_ℝ) ⟪X 0, Y u⟫_ℝ u :=
    (innerSL ℝ (X 0)).hasFDerivAt.comp_hasDerivAt u (h u)
  convert hinner using 1
  funext t
  rw [hgram, sub_zero]

/-- Differentiate the stationary Gram kernel in its first variable. -/
private lemma stationaryInner_derivative_left {X Y : ℝ → H} {K : ℝ → ℝ}
    (hgram : ∀ s t, ⟪X s, X t⟫_ℝ = K (t - s))
    (h : ∀ t, HasDerivAt X (Y t) t) (s t : ℝ) :
    ⟪Y s, X t⟫_ℝ = -deriv K (t - s) := by
  have hs : HasDerivAt (fun v ↦ K (t - v)) (-deriv K (t - s)) s := by
    have hd := (stationaryInner_right_deriv hgram h (t - s)).differentiableAt.hasDerivAt
    simpa only [Function.comp_def, mul_neg, mul_one] using
      hd.comp s ((hasDerivAt_id s).const_sub t)
  have hgram' : (fun v ↦ ⟪X v, X t⟫_ℝ) = fun v ↦ K (t - v) := funext fun v ↦ hgram v t
  have hpartial : HasDerivAt (fun v ↦ ⟪X v, X t⟫_ℝ) ⟪Y s, X t⟫_ℝ s := by
    simpa only [inner_zero_right, zero_add] using (h s).inner ℝ (hasDerivAt_const s (X t))
  rw [hgram'] at hpartial
  exact hpartial.unique hs

/-- A mixed derivative of the Gram kernel gives the second derivative of `K`. -/
private lemma stationaryInner_deriv_deriv {X Y : ℝ → H} {K : ℝ → ℝ}
    (hgram : ∀ s t, ⟪X s, X t⟫_ℝ = K (t - s))
    (h : ∀ t, HasDerivAt X (Y t) t) (u : ℝ) :
    HasDerivAt (deriv K) (-⟪Y 0, Y u⟫_ℝ) u := by
  have hgram' : (fun t ↦ -⟪Y 0, X t⟫_ℝ) = deriv K := by
    funext t
    simp only [stationaryInner_derivative_left hgram h, sub_zero, neg_neg]
  rw [← hgram']
  exact ((innerSL ℝ (Y 0)).hasFDerivAt.comp_hasDerivAt u (h u)).neg

/-- The differentiated curve has stationary Gram kernel `-K″`. -/
private lemma stationaryInner_derivative_self {X Y : ℝ → H} {K : ℝ → ℝ}
    (hgram : ∀ s t, ⟪X s, X t⟫_ℝ = K (t - s))
    (h : ∀ t, HasDerivAt X (Y t) t) (s t : ℝ) :
    ⟪Y s, Y t⟫_ℝ = -deriv (deriv K) (t - s) := by
  have hs : HasDerivAt (fun v ↦ -deriv K (v - s)) (-deriv (deriv K) (t - s)) t := by
    have hd := (stationaryInner_deriv_deriv hgram h (t - s)).differentiableAt.hasDerivAt
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, mul_one] using
      hd.neg.comp t ((hasDerivAt_id t).sub_const s)
  have hgram' : (fun v ↦ ⟪Y s, X v⟫_ℝ) = fun v ↦ -deriv K (v - s) :=
    funext (stationaryInner_derivative_left hgram h s)
  have hpartial : HasDerivAt (fun v ↦ ⟪Y s, X v⟫_ℝ) ⟪Y s, Y t⟫_ℝ t :=
    (innerSL ℝ (Y s)).hasFDerivAt.comp_hasDerivAt t (h t)
  rw [hgram'] at hpartial
  exact hpartial.unique hs

/-- Stationarity makes the difference quotient error independent of the evaluation point.
The derivative is therefore a uniform limit of continuous curves. -/
private lemma stationaryInner_continuous_derivative {X Y : ℝ → H} {K : ℝ → ℝ}
    (hgram : ∀ s t, ⟪X s, X t⟫_ℝ = K (t - s))
    (h : ∀ t, HasDerivAt X (Y t) t) :
    Continuous Y := by
  let Q (u t : ℝ) : H := u⁻¹ • (X (t + u) - X t)
  -- Expand the squared error using the stationary Gram and mixed derivative identities.
  have hQ (u t : ℝ) : ‖Q u t - Y t‖ = ‖Q u 0 - Y 0‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [← real_inner_self_eq_norm_sq, Q, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hgram, stationaryInner_derivative_left hgram h,
      stationaryInner_derivative_self hgram h, zero_add, sub_self, sub_zero]
    rw [real_inner_comm (Y t) (X (t + u)), real_inner_comm (Y t) (X t),
      real_inner_comm (Y 0) (X u), real_inner_comm (Y 0) (X 0)]
    simp only [stationaryInner_derivative_left hgram h, sub_self, sub_zero, add_sub_cancel_left,
      sub_add_cancel_left, zero_sub]
  apply TendstoUniformly.continuous (F := Q) (p := 𝓝[≠] (0 : ℝ))
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hnorm := tendsto_iff_norm_sub_tendsto_zero.1 (h 0).tendsto_slope_zero
    filter_upwards [hnorm.eventually_lt_const hε] with u hu t
    simpa only [dist_comm (Y t) (Q u t), dist_eq_norm, hQ, Q] using hu
  · exact (Eventually.of_forall fun u ↦ by
      have hX : Continuous X := continuous_iff_continuousAt.mpr fun t ↦ (h t).continuousAt
      dsimp only [Q]
      fun_prop).frequently


open scoped ContDiff in
/-- Iterating the differentiated Gram identity gives the covariance at every order. -/
private lemma stationaryInner_iteratedDeriv (m : ℕ) {X : ℕ → ℝ → H} {K : ℝ → ℝ}
    (hcont : Continuous (X 0)) (hgram : ∀ s t, ⟪X 0 s, X 0 t⟫_ℝ = K (t - s))
    (h : ∀ k < m, ∀ t, HasDerivAt (X k) (X (k + 1) t) t) :
    ContDiff ℝ ((2 * m : ℕ) : ℕ∞ω) K ∧
      ∀ s t, ⟪X m s, X m t⟫_ℝ = (-1) ^ m * iteratedDeriv (2 * m) K (t - s) := by
  induction m generalizing X K with
  | zero =>
    have hK : K = fun t ↦ ⟪X 0 0, X 0 t⟫_ℝ := by
      funext t
      rw [hgram, sub_zero]
    have hc : Continuous K := hK ▸ (continuous_const.inner hcont : Continuous _)
    simpa using And.intro hc hgram
  | succ m ih =>
    let X' (k : ℕ) : ℝ → H := X (k + 1)
    let K' (t : ℝ) := -deriv (deriv K) t
    have h0 := h 0 (by omega)
    have hrest (k : ℕ) (hk : k < m) (t : ℝ) : HasDerivAt (X' k) (X' (k + 1) t) t :=
      h (k + 1) (by omega) t
    have hcont' : Continuous (X' 0) := stationaryInner_continuous_derivative hgram h0
    have hgram' : ∀ s t, ⟪X' 0 s, X' 0 t⟫_ℝ = K' (t - s) :=
      stationaryInner_derivative_self hgram h0
    obtain ⟨hK', hgramm⟩ := ih hcont' hgram' hrest
    have hk : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    constructor
    · have hfinite : ((2 * m : ℕ) : ℕ∞ω) ≠ ⊤ := WithTop.natCast_ne_top _
      have hfinite' : ((2 * m : ℕ) : ℕ∞ω) + 1 ≠ ⊤ := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact WithTop.natCast_ne_top _
      rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv,
        contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (stationaryInner_right_deriv hgram h0 t).differentiableAt,
        fun ht ↦ (hfinite' ht).elim,
        fun t ↦ (stationaryInner_deriv_deriv hgram h0 t).differentiableAt,
        fun ht ↦ (hfinite ht).elim, ?_⟩
      simpa [K'] using hK'.neg
    · intro s t
      have hXm : X (m + 1) = X' m := rfl
      rw [hXm, hgramm, hk, iteratedDeriv_succ', iteratedDeriv_succ']
      simp only [K', iteratedDeriv_fun_neg, pow_succ]
      ring

end Hilbert

/-- For a centered field, covariance equals the inner product of field values in `L²`. -/
private lemma covariance_fieldLp {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℝ → Ω → ℝ} (hZ : IsSecondOrderField Z P) (hcent : ∀ t, P[Z t] = 0)
    (s t : ℝ) : cov[Z t, Z s; P] = ⟪fieldLp hZ s, fieldLp hZ t⟫_ℝ := by
  simp only [covariance, hcent, sub_zero, fieldLp_inner]

/-- SYNOPSIS item 7, consequences: if a centred second-order stationary process on `ℝ` is `m`
times mean-square differentiable for `m ≥ 1`, its covariance `K` is `2m` times continuously
differentiable on `ℝ`. The `m`th mean-square derivative is second-order stationary with
covariance `(-1)^m K^{(2m)}`. -/
theorem IsMeanSquareDifferentiable.derivative {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℝ → Ω → ℝ} (hZ : IsSecondOrderStationary Z P) (hcent : ∀ t, P[Z t] = 0) {m : ℕ}
    (hm : 1 ≤ m) (hdiff : IsMeanSquareDifferentiable m Z P) :
    ContDiff ℝ (2 * m) (stationaryCov Z P) ∧
      ∃ D : ℕ → ℝ → Ω → ℝ, D 0 = Z ∧
        (∀ k < m, IsSecondOrderField (D (k + 1)) P ∧ HasMeanSquareDeriv (D k) (D (k + 1)) P) ∧
        IsSecondOrderStationary (D m) P ∧
        ∀ h, stationaryCov (D m) P h = (-1) ^ m * iteratedDeriv (2 * m) (stationaryCov Z P) h := by
  classical
  obtain ⟨D, rfl, hD⟩ := hdiff
  have hstationary := isSecondOrderStationary_iff.mp hZ
  have hfields (k : ℕ) (hk : k ≤ m) : IsSecondOrderField (D k) P := by
    cases k with
    | zero => exact hstationary.1
    | succ k => exact (hD k (by omega)).1
  let X (k : ℕ) : ℝ → Lp ℝ 2 P :=
    if hk : k ≤ m then fieldLp (hfields k hk) else 0
  have hX (k : ℕ) (hk : k ≤ m) : X k = fieldLp (hfields k hk) := dite_eq_left hk
  have hderiv (k : ℕ) (hk : k < m) (t : ℝ) :
      HasDerivAt (X k) (X (k + 1) t) t := by
    rw [hX k hk.le, hX (k + 1) (by omega)]
    exact fieldLp_hasDerivAt _ _ (hD k hk).2 t
  have hzero (k : ℕ) (hk : k ≤ m) (t : ℝ) : ⟪Lp.const 2 P (1 : ℝ), X k t⟫_ℝ = 0 := by
    induction k generalizing t with
    | zero => rw [hX 0 hk, inner_one_fieldLp, hcent]
    | succ k ih =>
      have hconst : (fun t ↦ ⟪Lp.const 2 P (1 : ℝ), X k t⟫_ℝ) = (fun _ ↦ 0) :=
        funext (ih (by omega))
      have hd : HasDerivAt (fun v ↦ ⟪Lp.const 2 P (1 : ℝ), X k v⟫_ℝ)
          ⟪Lp.const 2 P (1 : ℝ), X (k + 1) t⟫_ℝ t :=
        (innerSL ℝ (Lp.const 2 P (1 : ℝ))).hasFDerivAt.comp_hasDerivAt t (hderiv k (by omega) t)
      rw [hconst] at hd
      exact hd.unique (hasDerivAt_const t 0)
  have hgram (s t : ℝ) : ⟪X 0 s, X 0 t⟫_ℝ = stationaryCov (D 0) P (t - s) := by
    have ht := hstationary.2.2 t s (-s)
    rw [← sub_eq_add_neg, add_neg_cancel] at ht
    rw [hX 0 (Nat.zero_le m), stationaryCov_def, ht, covariance_fieldLp hstationary.1 hcent]
  have hc : Continuous (X 0) :=
    continuous_iff_continuousAt.mpr fun t ↦ (hderiv 0 (by omega) t).continuousAt
  obtain ⟨hK, hgramm⟩ := stationaryInner_iteratedDeriv m hc hgram hderiv
  have hmzero (t : ℝ) : P[D m t] = 0 := by
    rw [← inner_one_fieldLp (hfields m le_rfl), ← hX m le_rfl]
    exact hzero m le_rfl t
  have hcov (s t : ℝ) : cov[D m t, D m s; P] =
      (-1) ^ m * iteratedDeriv (2 * m) (stationaryCov (D 0) P) (t - s) := by
    rw [covariance_fieldLp (hfields m le_rfl) hmzero, ← hX m le_rfl, hgramm]
  refine ⟨by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hK, D, rfl, hD,
    isSecondOrderStationary_iff.mpr
      ⟨hfields m le_rfl, fun s t ↦ (hmzero s).trans (hmzero t).symm, ?_⟩, ?_⟩
  · intro s t h
    rw [hcov, hcov, add_sub_add_right_eq_sub]
  · intro h
    rw [stationaryCov_def, hcov, sub_zero]

/-- The cosine of a nonzero integer multiple of a uniform phase has mean zero. -/
private lemma integral_cos_uniform_mul {P : Measure Ω} {Y : Ω → ℝ}
    (hY : HasLaw Y ((ENNReal.ofReal (2 * Real.pi))⁻¹ •
      volume.restrict (Set.Ico 0 (2 * Real.pi))) P) {k : ℕ} (hk : k ≠ 0) :
    (∫ ω, Real.cos ((k : ℝ) * Y ω) ∂P) = 0 := by
  have h := hY.integral_comp (f := fun y ↦ Real.cos ((k : ℝ) * y))
    (by fun_prop : Continuous fun y : ℝ ↦ Real.cos ((k : ℝ) * y)).aestronglyMeasurable
  rw [Function.comp_def, integral_smul_measure,
    Measure.restrict_congr_set (μ := volume) Ico_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (mul_nonneg zero_le_two Real.pi_pos.le),
    intervalIntegral.integral_comp_mul_left Real.cos (Nat.cast_ne_zero.2 hk), integral_cos] at h
  have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 k
  simpa only [hsin, mul_zero, Real.sin_zero, sub_zero, smul_zero] using h

/-- The sine of a nonzero integer multiple of a uniform phase has mean zero. -/
private lemma integral_sin_uniform_mul {P : Measure Ω} {Y : Ω → ℝ}
    (hY : HasLaw Y ((ENNReal.ofReal (2 * Real.pi))⁻¹ •
      volume.restrict (Set.Ico 0 (2 * Real.pi))) P) {k : ℕ} (hk : k ≠ 0) :
    (∫ ω, Real.sin ((k : ℝ) * Y ω) ∂P) = 0 := by
  have h := hY.integral_comp (f := fun y ↦ Real.sin ((k : ℝ) * y))
    (by fun_prop : Continuous fun y : ℝ ↦ Real.sin ((k : ℝ) * y)).aestronglyMeasurable
  rw [Function.comp_def, integral_smul_measure,
    Measure.restrict_congr_set (μ := volume) Ico_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (mul_nonneg zero_le_two Real.pi_pos.le),
    intervalIntegral.integral_comp_mul_left Real.sin (Nat.cast_ne_zero.2 hk), integral_sin] at h
  have hcos : Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
    exact Real.cos_nat_mul_two_pi k
  simpa only [hcos, mul_zero, Real.cos_zero, sub_self, smul_zero] using h

/-- The real part of the standard Cauchy characteristic function. -/
private lemma integral_cos_cauchy_mul {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : HasLaw X (cauchyMeasure 0 1) P) (s : ℝ) :
    (∫ ω, Real.cos (X ω * s) ∂P) = Real.exp (-|s|) := by
  let e (x : ℝ) : ℂ := Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)
  have hE := hX.integral_comp (f := e) (by fun_prop : Continuous e).aestronglyMeasurable
  have hB : Integrable (e ∘ X) P := Integrable.of_bound
    ((by fun_prop : Continuous e).measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    1 (ae_of_all _ fun ω ↦ by
      simp only [Function.comp_apply, e, ← Complex.ofReal_mul, norm_exp_ofReal_mul_I, le_rfl])
  have hR : (∫ ω, (e (X ω)).re ∂P) = (∫ ω, e (X ω) ∂P).re := integral_re hB
  have hc (ω : Ω) : (e (X ω)).re = Real.cos (X ω * s) := by
    dsimp only [e]
    rw [← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_comm]
  simp only [hc] at hR
  rw [hR]
  have hE' : (∫ ω, e (X ω) ∂P) = charFun (cauchyMeasure 0 1) s := by
    rw [charFun_apply_real]
    exact hE
  -- Use TauCeti's characteristic function to compute the Cauchy cosine expectation.
  rw [hE', TauCeti.Probability.charFun_cauchyMeasure]
  norm_num [← Complex.ofReal_neg, ← Complex.ofReal_exp]

/-- An independent uniform phase cancels a nonzero integer-frequency cosine. -/
private lemma integral_cos_cauchy_phase {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P)
    (hY : HasLaw Y ((ENNReal.ofReal (2 * Real.pi))⁻¹ •
      volume.restrict (Set.Ico 0 (2 * Real.pi))) P) (hXY : IndepFun X Y P)
    (s : ℝ) {k : ℕ} (hk : k ≠ 0) :
    (∫ ω, Real.cos (X ω * s + (k : ℝ) * Y ω) ∂P) = 0 := by
  let f (x : ℝ) := Real.cos (x * s)
  let g (x : ℝ) := Real.sin (x * s)
  let u (y : ℝ) := Real.cos ((k : ℝ) * y)
  let v (y : ℝ) := Real.sin ((k : ℝ) * y)
  have hmF : Measurable f := by fun_prop
  have hmG : Measurable g := by fun_prop
  have hmU : Measurable u := by fun_prop
  have hmV : Measurable v := by fun_prop
  have hp₁ : Integrable (fun ω => f (X ω) * u (Y ω)) P := by
    refine Integrable.of_bound ((hmF.comp_aemeasurable hX).mul
      (hmU.comp_aemeasurable hY.aemeasurable)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using Real.abs_cos_le_one _)
  have hp₂ : Integrable (fun ω => g (X ω) * v (Y ω)) P := by
    refine Integrable.of_bound ((hmG.comp_aemeasurable hX).mul
      (hmV.comp_aemeasurable hY.aemeasurable)).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using Real.abs_sin_le_one _)
  have hcos_add (ω : Ω) : Real.cos (X ω * s + (k : ℝ) * Y ω) =
      f (X ω) * u (Y ω) - g (X ω) * v (Y ω) := Real.cos_add _ _
  simp_rw [hcos_add]
  -- Mathlib factors the expectation of each product by independence.
  have hprod₁ : (∫ ω, f (X ω) * u (Y ω) ∂P) =
      (∫ ω, f (X ω) ∂P) * ∫ ω, u (Y ω) ∂P :=
    (hXY.comp hmF hmU).integral_fun_mul_eq_mul_integral
      (hmF.comp_aemeasurable hX).aestronglyMeasurable
      (hmU.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable
  have hprod₂ : (∫ ω, g (X ω) * v (Y ω) ∂P) =
      (∫ ω, g (X ω) ∂P) * ∫ ω, v (Y ω) ∂P :=
    (hXY.comp hmG hmV).integral_fun_mul_eq_mul_integral
      (hmG.comp_aemeasurable hX).aestronglyMeasurable
      (hmV.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable
  rw [integral_sub hp₁ hp₂, hprod₁, hprod₂]
  have h₁ : (∫ ω, u (Y ω) ∂P) = 0 := integral_cos_uniform_mul hY hk
  have h₂ : (∫ ω, v (Y ω) ∂P) = 0 := integral_sin_uniform_mul hY hk
  rw [h₁, h₂, mul_zero, mul_zero, sub_zero]

/-- The product of two cosines with a shared uniform phase averages to half the Cauchy kernel. -/
private lemma integral_cauchy_cos_product {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : HasLaw X (cauchyMeasure 0 1) P)
    (hY : HasLaw Y ((ENNReal.ofReal (2 * Real.pi))⁻¹ •
      volume.restrict (Set.Ico 0 (2 * Real.pi))) P) (hXY : IndepFun X Y P) (s t : ℝ) :
    (∫ ω, Real.cos (X ω * s + Y ω) * Real.cos (X ω * t + Y ω) ∂P) =
      Real.exp (-|s - t|) / 2 := by
  let A (ω : Ω) := X ω * (s - t)
  let B (ω : Ω) := X ω * (s + t) + 2 * Y ω
  have hA : Integrable (fun ω ↦ Real.cos (A ω)) P := by
    have hAm : AEMeasurable A P := hX.aemeasurable.mul_const _
    refine Integrable.of_bound (Real.continuous_cos.measurable.comp_aemeasurable
      hAm).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
    exact Real.abs_cos_le_one _
  have hB : Integrable (fun ω ↦ Real.cos (B ω)) P := by
    have hBm : AEMeasurable B P :=
      (hX.aemeasurable.mul_const _).add (hY.aemeasurable.const_mul 2)
    refine Integrable.of_bound (Real.continuous_cos.measurable.comp_aemeasurable
      hBm).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
    exact Real.abs_cos_le_one _
  have hterm (ω : Ω) : Real.cos (X ω * s + Y ω) * Real.cos (X ω * t + Y ω) =
      (Real.cos (A ω) + Real.cos (B ω)) / 2 := by
    have h₁ : X ω * s + Y ω - (X ω * t + Y ω) = A ω := by dsimp only [A]; ring
    have h₂ : X ω * s + Y ω + (X ω * t + Y ω) = B ω := by dsimp only [B]; ring
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    rw [← h₁, ← h₂, mul_comm _ 2, ← mul_assoc, Real.two_mul_cos_mul_cos]
  simp_rw [hterm]
  rw [integral_div, integral_add hA hB, integral_cos_cauchy_mul hX]
  have hm : (∫ ω, Real.cos (B ω) ∂P) = 0 :=
    integral_cos_cauchy_phase hX.aemeasurable hY hXY _ (by decide : (2 : ℕ) ≠ 0)
  rw [hm, add_zero]

/-- The Cauchy increment variance makes the second moments of difference quotients unbounded. -/
private lemma not_isMeanSquareDifferentiable_of_cauchy_increments {P : Measure Ω} {Z : ℝ → Ω → ℝ}
    (hLp : ∀ t, MemLp (Z t) 2 P)
    (hinc : ∀ h, (∫ ω, (Z h ω - Z 0 ω) ^ 2 ∂P) = 1 - Real.exp (-|h|)) :
    ¬ IsMeanSquareDifferentiable 1 Z P := by
  rintro ⟨D, rfl, hD⟩
  obtain ⟨hD₀, hDeriv⟩ := hD 0 (by decide)
  let d := D 1 0
  let S (h : ℝ) (ω : Ω) := (D 0 h ω - D 0 0 ω) / h
  have hSD : Tendsto (fun h ↦ ∫ ω, (S h ω - d ω) ^ 2 ∂P) (𝓝[>] 0) (𝓝 0) :=
    (by simpa only [zero_add] using hDeriv 0 : Tendsto
      (fun h ↦ ∫ ω, (S h ω - d ω) ^ 2 ∂P) (𝓝[≠] 0) (𝓝 0)).mono_left (nhdsGT_le_nhdsNE 0)
  have hd : MemLp d 2 P := isSecondOrderField_iff.mp hD₀ 0
  -- An L² derivative would bound the second moments of nearby right difference quotients.
  let B := 2 + 2 * ∫ ω, d ω ^ 2 ∂P
  have hbound : ∀ᶠ h in 𝓝[>] 0, (1 - Real.exp (-h)) / h ≤ B * h := by
    filter_upwards [self_mem_nhdsWithin, hSD.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
      with h hh hsmall
    have hh' : 0 < h := hh
    have hS : MemLp (S h) 2 P := by
      simpa only [S, div_eq_inv_mul, Pi.sub_apply] using ((hLp h).sub (hLp 0)).const_mul h⁻¹
    have hle : (∫ ω, S h ω ^ 2 ∂P) ≤ B := calc
      _ ≤ ∫ ω, 2 * ((S h ω - d ω) ^ 2 + d ω ^ 2) ∂P := by
        apply integral_mono hS.integrable_sq
          (((hS.sub hd).integrable_sq.add hd.integrable_sq).const_mul 2)
        intro ω
        simp only [Pi.add_apply, Pi.sub_apply]
        nlinarith [sq_nonneg (S h ω - 2 * d ω)]
      _ ≤ B := by
        have hsd : Integrable (fun ω ↦ (S h ω - d ω) ^ 2) P :=
          (hS.sub hd).integrable_sq
        rw [integral_const_mul, integral_add hsd hd.integrable_sq]
        dsimp only [B]
        linarith
    have hchange : (∫ ω, S h ω ^ 2 ∂P) = (1 - Real.exp (-h)) / h ^ 2 := by
      simp_rw [S, div_pow, integral_div, hinc, abs_of_pos hh']
    rw [hchange, div_le_iff₀ (sq_pos_of_pos hh')] at hle
    exact (div_le_iff₀ hh').2 (by convert hle using 1; ring)
  have hdiff : HasDerivAt (fun h : ℝ ↦ 1 - Real.exp (-h)) 1 0 := by
    simpa using (((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_id (0 : ℝ)).neg).const_sub 1)
  have hright : Tendsto (fun h : ℝ ↦ (1 - Real.exp (-h)) / h) (𝓝[>] 0) (𝓝 1) := by
    simpa [smul_eq_mul, div_eq_inv_mul] using hdiff.tendsto_slope_zero_right
  have hlim : Tendsto (fun h : ℝ ↦ B * h) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ ↦ B * h) := by fun_prop
    have hc' : Tendsto (fun h : ℝ ↦ B * h) (𝓝[>] 0) (𝓝 (B * 0)) :=
      (hc.continuousAt (x := (0 : ℝ))).continuousWithinAt (s := Set.Ioi 0)
    rwa [mul_zero] at hc'
  exact (by norm_num : ¬ ((1 : ℝ) ≤ 0)) (le_of_tendsto_of_tendsto hright hlim hbound)

/-- SYNOPSIS item 7, example: `Z(t) = cos(X t + Y)` with `X` standard Cauchy and `Y` uniform on
`[0, 2π)`, independent, has analytic sample paths and is second-order stationary, but it is not
mean-square differentiable. -/
theorem not_isMeanSquareDifferentiable_cos_cauchy {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : HasLaw X (cauchyMeasure 0 1) P)
    (hY : HasLaw Y ((ENNReal.ofReal (2 * Real.pi))⁻¹ •
      volume.restrict (Set.Ico 0 (2 * Real.pi))) P)
    (hXY : IndepFun X Y P) :
    let Z : ℝ → Ω → ℝ := fun t ω ↦ Real.cos (X ω * t + Y ω)
    IsSecondOrderStationary Z P ∧ (∀ ω, AnalyticOnNhd ℝ (fun t ↦ Z t ω) Set.univ) ∧
      ¬ IsMeanSquareDifferentiable 1 Z P := by
  let Z : ℝ → Ω → ℝ := fun t ω ↦ Real.cos (X ω * t + Y ω)
  -- Name the process from the statement for its moment and regularity calculations.
  change IsSecondOrderStationary Z P ∧ (∀ ω, AnalyticOnNhd ℝ (fun t ↦ Z t ω) Set.univ) ∧
      ¬ IsMeanSquareDifferentiable 1 Z P
  have hLp (t : ℝ) : MemLp (Z t) 2 P := by
    have hz : AEMeasurable (Z t) P := Real.continuous_cos.measurable.comp_aemeasurable
      ((hX.aemeasurable.mul_const t).add hY.aemeasurable)
    exact (memLp_top_of_bound hz.aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ Real.abs_cos_le_one _)).mono_exponent le_top
  have hmean (t : ℝ) : P[Z t] = 0 := by
    simpa only [Z, Nat.cast_one, one_mul] using
      integral_cos_cauchy_phase hX.aemeasurable hY hXY t (by decide : (1 : ℕ) ≠ 0)
  have hprod (s t : ℝ) : (∫ ω, Z s ω * Z t ω ∂P) = Real.exp (-|s - t|) / 2 :=
    integral_cauchy_cos_product hX hY hXY s t
  have hcov (s t : ℝ) : cov[Z s, Z t; P] = Real.exp (-|s - t|) / 2 := by
    simp only [covariance_eq_sub (hLp s) (hLp t), Pi.mul_apply, hprod, hmean, zero_mul,
      sub_zero]
  refine ⟨isSecondOrderStationary_iff.mpr ⟨isSecondOrderField_iff.mpr hLp, ?_, ?_⟩, ?_,
    not_isMeanSquareDifferentiable_of_cauchy_increments hLp ?_⟩
  · intro s t
    simp only [hmean]
  · intro s t h
    simp only [hcov, add_sub_add_right_eq_sub]
  · intro ω t _
    exact Real.analyticAt_cos.comp (by fun_prop)
  · intro h
    have hsquare (ω : Ω) : (Z h ω - Z 0 ω) ^ 2 =
        Z h ω * Z h ω + Z 0 ω * Z 0 ω - 2 * (Z h ω * Z 0 ω) := by ring
    have hmul (s t : ℝ) : Integrable (fun ω ↦ Z s ω * Z t ω) P :=
      MemLp.integrable_mul (p := 2) (q := 2) (hLp s) (hLp t)
    simp_rw [hsquare]
    have hadd : Integrable (fun ω ↦ Z h ω * Z h ω + Z 0 ω * Z 0 ω) P :=
      (hmul h h).add (hmul 0 0)
    rw [integral_sub hadd ((hmul h 0).const_mul 2), integral_add (hmul h h) (hmul 0 0),
      integral_const_mul, hprod, hprod, hprod]
    simp only [sub_self, abs_zero, neg_zero, Real.exp_zero, sub_zero]
    ring

end MSSS
