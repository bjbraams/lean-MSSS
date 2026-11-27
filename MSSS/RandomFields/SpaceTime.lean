module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.CompletelyMonotone.Basic

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Bochner.Fourier.Nonneg
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.PositiveDefinite.FourierAtom
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import MSSS.RandomFields.Isotropic
import TauCeti.Analysis.Bochner.CharFun.PositiveDefinite
import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
import TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Power

/-!
# Space–time covariance functions

SYNOPSIS items 16 and 17: the Cressie–Huang criterion and Gneiting's nonseparable space–time
covariances. Space–time is `ℝ^d × ℝ`, identified with `ℝ^{d+1}`.

The Cressie–Huang criterion uses Mathlib's product integration and Gaussian Fourier
inversion approximation, with TauCeti's Fourier transform results for positive definite
functions and its almost-everywhere inversion through tempered distributions.
The damping criterion uses TauCeti's closure of positive definite functions under pointwise
products, addition-monoid homomorphisms, and pointwise limits. Gneiting's construction uses
Mathlib's Gaussian Fourier integral and TauCeti's Laplace representation of completely
monotone functions and composition rules for Bernstein functions.

## Main results

* `MSSS.isPositiveDefiniteSub_iff_ae_spatialFourier`,
  `MSSS.isPositiveDefiniteSub_iff_forall_exp_mul`: SYNOPSIS item 16.
* `MSSS.isPositiveDefiniteSub_gneiting`, `MSSS.isPositiveDefiniteSub_gneiting_family`:
  SYNOPSIS item 17.
-/

public section

noncomputable section

open MeasureTheory Set Complex Filter Topology
open scoped ComplexConjugate ComplexOrder ContDiff FourierTransform NNReal
  RealInnerProductSpace SchwartzMap

namespace MSSS

variable {d : ℕ}

-- Keep the regularity hypotheses of the existing interface.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 16: a continuous, bounded, symmetric `C` on `ℝ^d × ℝ` is positive definite if
and only if `e^{-a‖h‖ - b|u|} C(h, u)` is positive definite for all `a, b > 0`. -/
theorem isPositiveDefiniteSub_iff_forall_exp_mul
    {C : EuclideanSpace ℝ (Fin d) × ℝ → ℝ} (hc : Continuous C) (hb : ∃ M, ∀ z, |C z| ≤ M)
    (hs : ∀ z, C (-z) = C z) :
    TauCeti.IsPositiveDefiniteSub (fun z ↦ (C z : ℂ)) ↔
      ∀ a b : ℝ, 0 < a → 0 < b → TauCeti.IsPositiveDefiniteSub fun z ↦
        ((Real.exp (-a * ‖z.1‖ - b * |z.2|) * C z : ℝ) : ℂ) := by
  constructor
  · intro h a b ha hb
    have hpd {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ℝ)
        (hc : 0 ≤ c) : TauCeti.IsPositiveDefiniteSub fun x : E ↦ (Real.exp (-c * ‖x‖) : ℂ) := by
      have hcm := TauCeti.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul_rpow hc
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa only [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)] using
        (isPositiveDefiniteSub_sq_norm_of_completelyMonotone (E := E) hcm)
    have hsp := (hpd (E := EuclideanSpace ℝ (Fin d)) a ha.le).comp_addMonoidHom
      (AddMonoidHom.fst (EuclideanSpace ℝ (Fin d)) ℝ)
    have htm := (hpd (E := ℝ) b hb.le).comp_addMonoidHom
      (AddMonoidHom.snd (EuclideanSpace ℝ (Fin d)) ℝ)
    simpa only [AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, Real.norm_eq_abs,
      sub_eq_add_neg, neg_mul, Real.exp_add, ofReal_mul] using (hsp.mul htm).mul h
  · intro h
    -- Use TauCeti's pointwise-limit theorem as both damping parameters tend to zero.
    apply TauCeti.IsPositiveDefiniteSub.of_tendsto (l := 𝓝[>] (0 : ℝ)) (F := fun a z ↦
      (Real.exp (-a * ‖z.1‖ - a * |z.2|) * C z : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact h a a ha ha
    · intro z
      have hcont : Continuous fun a : ℝ ↦
          ((Real.exp (-a * ‖z.1‖ - a * |z.2|) * C z : ℝ) : ℂ) := by fun_prop
      simpa only [neg_zero, zero_mul, sub_zero, Real.exp_zero, one_mul] using
        (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- An integrable mixture of positive definite functions is positive definite. -/
theorem isPositiveDefiniteSub_integral {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
    {μ : Measure X} {F : X → G → ℂ} (hp : ∀ x, TauCeti.IsPositiveDefiniteSub (F x))
    (hi : ∀ z, Integrable (fun x ↦ F x z) μ) :
    TauCeti.IsPositiveDefiniteSub fun z ↦ ∫ x, F x z ∂μ := by
  refine TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg.mpr fun n c v ↦ ?_
  let f (i j : Fin n) (x : X) := c i * conj (c j) * F x (v i - v j)
  have hf (i j : Fin n) : Integrable (f i j) μ := (hi _).const_mul _
  have heq (i j : Fin n) :
      c i * conj (c j) * (∫ x, F x (v i - v j) ∂μ) = ∫ x, f i j x ∂μ :=
    (integral_const_mul _ _).symm
  simp_rw [heq]
  have hrow (i : Fin n) : (∑ j, ∫ x, f i j x ∂μ) = ∫ x, ∑ j, f i j x ∂μ :=
    (integral_finsetSum _ fun j _ ↦ hf i j).symm
  simp_rw [hrow]
  have hsum : Integrable (fun x ↦ ∑ i, ∑ j, f i j x) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hf i j
  have hre : (∫ x, (∑ i, ∑ j, f i j x).re ∂μ) =
      (∫ x, ∑ i, ∑ j, f i j x ∂μ).re := integral_re hsum
  have him : (∫ x, (∑ i, ∑ j, f i j x).im ∂μ) =
      (∫ x, ∑ i, ∑ j, f i j x ∂μ).im := integral_im hsum
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hf i j,
    Complex.nonneg_iff, ← hre, ← him]
  have hval (x : X) : 0 ≤ ∑ i, ∑ j, f i j x := (hp x).sum_nonneg c v
  exact ⟨integral_nonneg fun x ↦ (Complex.nonneg_iff.mp (hval x)).1, by
    simp only [(fun x ↦ (Complex.nonneg_iff.mp (hval x)).2.symm), integral_zero]⟩

section FourierCriterion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A continuous positive definite function has nonnegative Fourier transform. -/
lemma fourier_nonneg_of_isPositiveDefiniteSub {F : V → ℂ} (hc : Continuous F)
    (hp : TauCeti.IsPositiveDefiniteSub F) : ∀ x, 0 ≤ 𝓕 F x := by
  intro x
  exact Complex.nonneg_iff.mpr ⟨TauCeti.fourier_re_nonneg_of_posSemidef F hp.posSemidef hc x,
    (TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj F hp.map_neg x).symm⟩

/-- The inverse Fourier transform of an integrable nonnegative function is positive definite. -/
lemma isPositiveDefiniteSub_fourierInv_of_nonneg {f : V → ℂ} (hi : Integrable f)
    (hn : ∀ x, 0 ≤ f x) : TauCeti.IsPositiveDefiniteSub (𝓕⁻ f) := by
  have heq (v : V) : 𝓕⁻ f v = ∫ x, f x * TauCeti.fourierAtom (-x) v := by
    rw [Real.fourierInv_eq_fourier_neg, TauCeti.fourier_eq_integral_fourierAtom_mul]
    congr 1
    funext x
    rw [mul_comm, TauCeti.fourierAtom_apply, TauCeti.fourierAtom_apply,
      inner_neg_right, inner_neg_right, real_inner_comm x v]
  rw [funext heq]
  apply isPositiveDefiniteSub_integral
  · intro x
    have hp := (TauCeti.continuous_and_isPositiveDefiniteSub_fourierAtom (-x)).2
    have hswap (v : V) : TauCeti.fourierAtom v (-x) = TauCeti.fourierAtom (-x) v := by
      rw [TauCeti.fourierAtom_apply, TauCeti.fourierAtom_apply, real_inner_comm v (-x)]
    simpa only [hswap] using hp.const_mul (hn x)
  · intro v
    have hc : Continuous fun x : V ↦ TauCeti.fourierAtom (-x) v :=
      (TauCeti.continuous_and_isPositiveDefiniteSub_fourierAtom v).1.comp continuous_neg
    apply hi.norm.mono' (hi.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    exact ae_of_all _ fun x ↦ by
      simp only [Pi.mul_apply, norm_mul, TauCeti.norm_fourierAtom, mul_one, le_refl]

/-- A Fourier transform multiplied by a positive Gaussian is integrable. -/
lemma integrable_fourier_mul_gaussian {f : V → ℂ} (hf : Integrable f) {c : ℝ} (hc : 0 < c) :
    Integrable (fun w ↦ 𝓕 f w * Complex.exp ((-c * ‖w‖ ^ 2 : ℝ) : ℂ)) := by
  have hg : Integrable (fun w : V ↦ Complex.exp ((-c * ‖w‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
      zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (c : ℂ))
        (by simpa only [Complex.ofReal_re] using hc) 0 (0 : V)
  exact hg.bdd_mul (hf.continuous_fourier.aestronglyMeasurable)
    (ae_of_all _ (Real.norm_fourier_le_integral_norm f))

/-- Fourier-side Gaussian damping is convolution with the reciprocal-scale Gaussian. -/
lemma fourierInv_fourier_mul_gaussian {f : V → ℂ} (hf : Integrable f) {c : ℝ} (hc : 0 < c) (v : V) :
    𝓕⁻ (fun w ↦ 𝓕 f w * Complex.exp ((-c⁻¹ * ‖w‖ ^ 2 : ℝ) : ℂ)) v =
      ∫ w : V, ((Real.pi * c : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ) *
        exp (-Real.pi ^ 2 * c * ‖v - w‖ ^ 2)) • f w := by
  let g (w : V) := exp (-(c⁻¹ : ℝ) * ‖w‖ ^ 2 + 2 * Real.pi * I * ⟪v, w⟫)
  have hg : Integrable g :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := ((c⁻¹ : ℝ) : ℂ)) (by simpa only [ofReal_re] using inv_pos.mpr hc) _ _
  calc
    _ = ∫ w, g w * 𝓕 f w := by
      rw [Real.fourierInv_eq_fourier_neg, TauCeti.fourier_eq_integral_fourierAtom_mul]
      congr 1
      funext w
      rw [TauCeti.fourierAtom_apply, inner_neg_right]
      simp only [g, ofReal_mul, ofReal_neg, ofReal_pow, exp_add, real_inner_comm w v]
      have hs : (-2 : ℂ) * Real.pi * I * - (⟪w, v⟫ : ℂ) =
          2 * Real.pi * I * (⟪w, v⟫ : ℂ) := by ring
      rw [hs]
      ring
    _ = ∫ w, 𝓕 g w * f w := by
      have hL : Continuous fun p : V × V ↦ (innerₗ V) p.1 p.2 := by
        simp only [innerₗ_apply_apply]
        fun_prop
      have h := (VectorFourier.integral_fourierIntegral_smul_eq_flip
        Real.continuous_fourierChar hL hg hf).symm
      rw [flip_innerₗ] at h
      exact h
    _ = _ := by
      apply integral_congr_ae <| ae_of_all _ fun w ↦ ?_
      simp only [g, smul_eq_mul]
      rw [fourier_gaussian_innerProductSpace'
        (b := ((c⁻¹ : ℝ) : ℂ)) (by simpa only [ofReal_re] using inv_pos.mpr hc)]
      simp only [ofReal_inv, div_inv_eq_mul, neg_mul]
      ring_nf

/-- A continuous integrable function with nonnegative Fourier transform is positive definite. -/
lemma isPositiveDefiniteSub_of_fourier_nonneg {f : V → ℂ} (hf : Integrable f) (hc : Continuous f)
    (hn : ∀ x, 0 ≤ 𝓕 f x) : TauCeti.IsPositiveDefiniteSub f := by
  let F (c : ℝ) (v : V) :=
    𝓕⁻ (fun w ↦ 𝓕 f w * Complex.exp ((-c⁻¹ * ‖w‖ ^ 2 : ℝ) : ℂ)) v
  refine TauCeti.IsPositiveDefiniteSub.of_tendsto (F := F) (l := atTop) ?_ fun v ↦ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hcp
    exact isPositiveDefiniteSub_fourierInv_of_nonneg
      (integrable_fourier_mul_gaussian hf (inv_pos.mpr hcp)) fun w ↦ by
      rw [← Complex.ofReal_exp]
      exact mul_nonneg (hn w) (Complex.zero_le_real.mpr (Real.exp_pos _).le)
  · -- Mathlib's Gaussian approximation recovers the original function pointwise.
    apply (Real.tendsto_integral_gaussian_smul' hf hc.continuousAt).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hcp
    exact (fourierInv_fourier_mul_gaussian hf hcp v).symm

/-- If a function and its Fourier transform are integrable, Fourier inversion holds almost
everywhere. -/
lemma ae_eq_fourierInv_fourier {f : V → ℂ} (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    f =ᵐ[volume] 𝓕⁻ (𝓕 f) := by
  let u := hf.toL1 f
  let v := hF.toL1 (𝓕 f)
  have hv : (v : V → ℂ) =ᵐ[volume] 𝓕 f := hF.coeFn_toL1
  have huv : 𝓕 (u : 𝓢'(V, ℂ)) = (v : 𝓢'(V, ℂ)) := by
    ext φ
    rw [Lp.fourier_toTemperedDistribution_apply u hf hf.coeFn_toL1,
      Lp.toTemperedDistribution_apply]
    exact integral_congr_ae <| hv.mono fun x hx ↦ by dsimp only; rw [hx]
  -- TauCeti's tempered-distribution inversion gives an almost-everywhere identity.
  have h := hf.coeFn_toL1.symm.trans (Lp.ae_eq_fourierInv_of_fourier_eq huv)
  refine h.trans (ae_of_all _ fun x ↦ ?_)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
    TauCeti.fourier_eq_integral_fourierAtom_mul, TauCeti.fourier_eq_integral_fourierAtom_mul]
  exact integral_congr_ae <| hv.mono fun y hy ↦ by dsimp only; rw [hy]

end FourierCriterion

section SpatialFourier

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- The spatial Fourier transform of an integrable function on a product is integrable
as a function of the temporal variable at each spatial frequency. -/
lemma integrable_fourier_fst {C : V × W → ℂ} (hi : Integrable C) (ξ : V) :
    Integrable (fun u ↦ 𝓕 (fun h ↦ C (h, u)) ξ) := by
  have hint : Integrable (fun z : V × W ↦ TauCeti.fourierAtom ξ z.1 * C z)
      ((volume : Measure V).prod (volume : Measure W)) := by
    rw [Measure.volume_eq_prod] at hi
    apply hi.norm.mono'
      (((TauCeti.continuous_fourierAtom ξ).comp continuous_fst).aestronglyMeasurable.mul
        hi.aestronglyMeasurable)
    exact ae_of_all _ fun x ↦ by
      simp only [Pi.mul_apply, Function.comp_apply, norm_mul, TauCeti.norm_fourierAtom,
        one_mul, le_refl]
  simpa only [TauCeti.fourier_eq_integral_fourierAtom_mul] using hint.integral_prod_right

/-- The Fourier transform on a Hilbert product is the iterated Fourier transform in
the two factors. -/
lemma fourier_prod_apply {C : V × W → ℂ} (hC : Integrable C) (ξ : V) (τ : W) :
    𝓕 (C ∘ WithLp.ofLp (p := 2)) (WithLp.toLp 2 (ξ, τ)) =
      𝓕 (fun u ↦ 𝓕 (fun h ↦ C (h, u)) ξ) τ := by
  let e := MeasurableEquiv.toLp 2 (V × W)
  have hmul (z : V × W) :
      TauCeti.fourierAtom (WithLp.toLp 2 (ξ, τ)) (WithLp.toLp 2 z) =
        TauCeti.fourierAtom ξ z.1 * TauCeti.fourierAtom τ z.2 := by
    rw [TauCeti.fourierAtom_apply, TauCeti.fourierAtom_apply, TauCeti.fourierAtom_apply,
      ← Complex.exp_add]
    congr 1
    simp only [WithLp.prod_inner_apply, ofReal_add]
    ring
  rw [TauCeti.fourier_eq_integral_fourierAtom_mul,
    ← (WithLp.volume_preserving_toLp V W).integral_comp e.measurableEmbedding]
  have hi : Integrable
      (fun z : V × W ↦ TauCeti.fourierAtom τ z.2 * (TauCeti.fourierAtom ξ z.1 * C z))
      ((volume : Measure V).prod (volume : Measure W)) := by
    have hc : Continuous (fun z : V × W ↦ TauCeti.fourierAtom τ z.2) :=
      (TauCeti.continuous_fourierAtom τ).comp continuous_snd
    have hs : Continuous (fun z : V × W ↦ TauCeti.fourierAtom ξ z.1) :=
      (TauCeti.continuous_fourierAtom ξ).comp continuous_fst
    rw [Measure.volume_eq_prod] at hC
    apply hC.norm.mono' (hc.aestronglyMeasurable.mul
      (hs.aestronglyMeasurable.mul hC.aestronglyMeasurable))
    exact ae_of_all _ fun x ↦ by
      simp only [Pi.mul_apply, norm_mul, TauCeti.norm_fourierAtom, one_mul, le_refl]
  rw [Measure.volume_eq_prod]
  calc
    _ = ∫ z : V × W, TauCeti.fourierAtom τ z.2 * (TauCeti.fourierAtom ξ z.1 * C z)
        ∂((volume : Measure V).prod (volume : Measure W)) := by
      apply integral_congr_ae <| ae_of_all _ fun z ↦ ?_
      dsimp only [Function.comp_apply]
      rw [hmul, mul_comm (TauCeti.fourierAtom ξ z.1), mul_assoc]
    _ = _ := by
      rw [integral_prod_symm _ hi, TauCeti.fourier_eq_integral_fourierAtom_mul]
      simp_rw [TauCeti.fourier_eq_integral_fourierAtom_mul, integral_const_mul]

/-- A continuous complex-valued function that is nonnegative almost everywhere
under a measure positive on nonempty open sets is nonnegative everywhere. -/
lemma nonneg_of_ae_nonneg_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → ℂ} (hc : Continuous f)
    (h : ∀ᵐ x ∂μ, 0 ≤ f x) (x : X) : 0 ≤ f x := by
  have hclosed : IsClosed {x | 0 ≤ f x} := by
    have hz : Continuous (fun _ : X ↦ (0 : ℝ)) := continuous_const
    have hcl := (isClosed_le hz (continuous_re.comp hc)).inter
      (isClosed_eq hz (continuous_im.comp hc))
    convert hcl using 1
    ext
    simp only [mem_ofPred_eq, mem_inter_iff, Complex.nonneg_iff, Function.comp_apply]
  have hfull : {x | 0 ≤ f x} =ᵐ[μ] univ := by
    filter_upwards [h] with y hy
    simp only [hy, mem_univ]
  exact eq_univ_iff_forall.mp ((hclosed.ae_eq_univ_iff_eq).mp hfull) x

/-- Positive definiteness on a product is equivalent to almost every spatial Fourier
slice having a continuous positive definite representative. -/
lemma isPositiveDefiniteSub_iff_ae_exists_fourier_fst
    {C : V × W → ℂ} (hc : Continuous C) (hi : Integrable C) :
    TauCeti.IsPositiveDefiniteSub C ↔
      ∀ᵐ ξ : V, ∃ F : W → ℂ, Continuous F ∧ TauCeti.IsPositiveDefiniteSub F ∧
        (fun u ↦ 𝓕 (fun h ↦ C (h, u)) ξ) =ᵐ[volume] F := by
  let e := WithLp.addEquiv 2 (V × W)
  let G : WithLp 2 (V × W) → ℂ := C ∘ e
  let P (ξ : V) (u : W) := 𝓕 (fun h ↦ C (h, u)) ξ
  have hGc : Continuous G := hc.comp (WithLp.prod_continuous_ofLp 2 V W)
  have hGi : Integrable G := (WithLp.volume_preserving_ofLp V W).integrable_comp_of_integrable hi
  have hPi (ξ : V) : Integrable (P ξ) := integrable_fourier_fst hi ξ
  have hG (ξ : V) (τ : W) : 𝓕 G (e.symm (ξ, τ)) = 𝓕 (P ξ) τ := fourier_prod_apply hi ξ τ
  constructor
  · intro h
    have hpd : TauCeti.IsPositiveDefiniteSub G := h.comp_addMonoidHom e.toAddMonoidHom
    have hint := TauCeti.integrable_fourier_of_posSemidef G hpd.posSemidef hGi hGc
    have hprod : Integrable (fun q : V × W ↦ 𝓕 G (e.symm q))
        ((volume : Measure V).prod (volume : Measure W)) :=
      by
        rw [← Measure.volume_eq_prod]
        exact (WithLp.volume_preserving_toLp V W).integrable_comp_of_integrable hint
    filter_upwards [hprod.prod_right_ae] with ξ hξ
    have hfft : Integrable (𝓕 (P ξ)) := hξ.congr <| ae_of_all _ (hG ξ)
    have hn (τ : W) : 0 ≤ 𝓕 (P ξ) τ := by
      rw [← hG]
      exact fourier_nonneg_of_isPositiveDefiniteSub hGc hpd _
    exact ⟨𝓕⁻ (𝓕 (P ξ)), hfft.continuous_fourierInv,
      isPositiveDefiniteSub_fourierInv_of_nonneg hfft hn,
      ae_eq_fourierInv_fourier (hPi ξ) hfft⟩
  · intro h
    have hneg (τ : W) : ∀ᵐ ξ : V, 0 ≤ 𝓕 G (e.symm (ξ, τ)) := by
      filter_upwards [h] with ξ hξ
      obtain ⟨F, hFc, hF, heq⟩ := hξ
      rw [hG, Real.fourier_congr_ae heq]
      exact fourier_nonneg_of_isPositiveDefiniteSub hFc hF τ
    have hpt (τ : W) (ξ : V) : 0 ≤ 𝓕 G (e.symm (ξ, τ)) := by
      have hcont : Continuous (fun ξ : V ↦ 𝓕 G (e.symm (ξ, τ))) :=
        hGi.continuous_fourier.comp ((WithLp.prod_continuous_toLp 2 V W).comp
          (continuous_id.prodMk continuous_const))
      exact nonneg_of_ae_nonneg_of_continuous hcont (hneg τ) ξ
    have hGpd : TauCeti.IsPositiveDefiniteSub G := by
      apply isPositiveDefiniteSub_of_fourier_nonneg hGi hGc
      intro w
      exact (e.symm_apply_apply w) ▸ hpt (e w).2 (e w).1
    convert hGpd.comp_addMonoidHom e.symm.toAddMonoidHom using 1
    funext x
    simp only [G, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, e.apply_symm_apply]

end SpatialFourier

/-- Convert the spatial Fourier integral from angular to ordinary frequency. -/
private lemma angularSpatialFourier_eq_fourier {C : EuclideanSpace ℝ (Fin d) × ℝ → ℝ}
    (ξ : EuclideanSpace ℝ (Fin d)) (u : ℝ) :
    (∫ h : EuclideanSpace ℝ (Fin d), exp (-(⟪h, (2 * Real.pi) • ξ⟫ : ℂ) * I) * C (h, u)) =
      𝓕 (fun h : EuclideanSpace ℝ (Fin d) ↦ (C (h, u) : ℂ)) ξ := by
  rw [TauCeti.fourier_eq_integral_fourierAtom_mul]
  apply integral_congr_ae <| ae_of_all _ fun h ↦ ?_
  rw [TauCeti.fourierAtom_apply, real_inner_smul_right, ofReal_mul]
  push_cast
  congr 2
  ring

-- The boundedness and symmetry hypotheses preserve the original real-valued interface.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 16, Cressie–Huang criterion: a continuous integrable covariance on
`ℝ^d × ℝ` is positive definite exactly when almost every spatial Fourier transform in the
time variable agrees almost everywhere with a continuous positive definite function. -/
theorem isPositiveDefiniteSub_iff_ae_spatialFourier
    {C : EuclideanSpace ℝ (Fin d) × ℝ → ℝ} (hc : Continuous C) (hb : ∃ M, ∀ z, |C z| ≤ M)
    (hi : Integrable C) (hs : ∀ z, C (-z) = C z) :
    TauCeti.IsPositiveDefiniteSub (fun z ↦ (C z : ℂ)) ↔
      ∀ᵐ ξ : EuclideanSpace ℝ (Fin d), ∃ F : ℝ → ℂ, Continuous F ∧
        TauCeti.IsPositiveDefiniteSub F ∧
        (fun u : ℝ ↦ ∫ h : EuclideanSpace ℝ (Fin d), exp (-(⟪h, ξ⟫ : ℂ) * I) * C (h, u))
          =ᵐ[volume] F := by
  have hpos : 0 < 2 * Real.pi := Real.two_pi_pos
  rw [isPositiveDefiniteSub_iff_ae_exists_fourier_fst (C := fun z ↦ (C z : ℂ))
    (continuous_ofReal.comp hc) hi.ofReal]
  constructor
  · intro h
    have hscale := Measure.quasiMeasurePreserving_smul
      (volume : Measure (EuclideanSpace ℝ (Fin d))) (inv_ne_zero hpos.ne')
    filter_upwards [hscale.ae h] with ξ hξ
    rcases hξ with ⟨F, hFc, hFpd, hF⟩
    refine ⟨F, hFc, hFpd, ?_⟩
    filter_upwards [hF] with u hu
    have he : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [← he, angularSpatialFourier_eq_fourier]
    exact hu
  · intro h
    have hscale := Measure.quasiMeasurePreserving_smul
      (volume : Measure (EuclideanSpace ℝ (Fin d))) hpos.ne'
    filter_upwards [hscale.ae h] with ξ hξ
    rcases hξ with ⟨F, hFc, hFpd, hF⟩
    refine ⟨F, hFc, hFpd, ?_⟩
    filter_upwards [hF] with u hu
    rw [← angularSpatialFourier_eq_fourier]
    exact hu

/-- The spatial Gaussian Fourier integral with a Bernstein function in the temporal factor. -/
private lemma isPositiveDefiniteSub_integral_gaussian {ψ : ℝ → ℝ}
    (hψ : TauCeti.IsBernsteinFunction ψ) (r : ℝ≥0)
    (hψpos : ∀ t, 0 ≤ t → 0 < ψ t) :
    TauCeti.IsPositiveDefiniteSub fun z : EuclideanSpace ℝ (Fin d) × ℝ ↦
      ∫ ξ : EuclideanSpace ℝ (Fin d),
        exp (-((ψ (z.2 ^ 2) : ℝ) : ℂ) * ‖ξ‖ ^ 2 +
          (2 * Real.sqrt r * I) * ⟪z.1, ξ⟫) := by
  apply isPositiveDefiniteSub_integral
  · intro ξ
    have hsp : TauCeti.IsPositiveDefiniteSub fun h : EuclideanSpace ℝ (Fin d) ↦
        exp ((2 * Real.sqrt r * I) * ⟪h, ξ⟫) := by
      have hp := TauCeti.isPositiveDefiniteSub_charFun
        (μ := Measure.dirac ((2 * Real.sqrt r : ℝ) • ξ))
      convert hp using 1
      funext h
      rw [charFun_dirac, real_inner_smul_left, real_inner_comm ξ h]
      push_cast
      ring_nf
    have hcm := (TauCeti.IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone
      (TauCeti.isCompletelyMonotone_exp_neg_mul (sq_nonneg ‖ξ‖))).comp_isBernsteinFunction hψ
    have htm : TauCeti.IsPositiveDefiniteSub fun u : ℝ ↦
        exp (-((ψ (u ^ 2) : ℝ) : ℂ) * ‖ξ‖ ^ 2) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, sq_abs, ofReal_exp, ofReal_mul, ofReal_neg,
        ofReal_pow, neg_mul, mul_neg, mul_comm] using
        (isPositiveDefiniteSub_sq_norm_of_completelyMonotone (E := ℝ) hcm)
    simpa only [exp_add, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd] using
      (htm.comp_addMonoidHom (AddMonoidHom.snd (EuclideanSpace ℝ (Fin d)) ℝ)).mul
        (hsp.comp_addMonoidHom (AddMonoidHom.fst (EuclideanSpace ℝ (Fin d)) ℝ))
  · intro z
    exact GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa only [ofReal_re] using hψpos (z.2 ^ 2) (sq_nonneg z.2)) _ _

/-- A Gaussian spatial profile with Bernstein temporal scaling gives a positive definite kernel. -/
private lemma isPositiveDefiniteSub_gneiting_gaussian {ψ : ℝ → ℝ}
    (hψ : TauCeti.IsBernsteinFunction ψ) (hψpos : ∀ t, 0 ≤ t → 0 < ψ t) (r : ℝ≥0) :
    TauCeti.IsPositiveDefiniteSub fun z : EuclideanSpace ℝ (Fin d) × ℝ ↦
      ((ψ (z.2 ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-(‖z.1‖ ^ 2 / ψ (z.2 ^ 2) * r)) : ℝ) : ℂ) := by
  have hp := (isPositiveDefiniteSub_integral_gaussian (d := d) hψ r hψpos).real_smul
    (r := Real.pi ^ (-(d : ℝ) / 2)) (by positivity)
  convert hp using 1
  funext z
  let b := ψ (z.2 ^ 2)
  have hb : 0 < b := hψpos _ (sq_nonneg _)
  dsimp only [Pi.smul_apply, real_smul]
  -- Mathlib's Gaussian Fourier integral leaves a real Gaussian profile.
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace (b := (b : ℂ))
    (by simpa only [ofReal_re] using hb), Fintype.card_fin]
  have he : (2 * Real.sqrt r * I : ℂ) ^ 2 * ‖z.1‖ ^ 2 / (4 * (b : ℂ)) =
      ((-(‖z.1‖ ^ 2 / b * (r : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, I_sq, mul_pow, ← ofReal_pow, Real.sq_sqrt r.coe_nonneg]
    ring
  have hc : (Real.pi / (b : ℂ)) ^ ((d : ℂ) / 2) =
      ((Real.pi / b) ^ ((d : ℝ) / 2) : ℝ) := by
    rw [ofReal_cpow (by positivity : 0 ≤ Real.pi / b), ofReal_div, ofReal_div, ofReal_natCast]
    norm_num
  rw [he, hc, ← ofReal_exp, ← ofReal_mul, ← ofReal_mul]
  apply congrArg Complex.ofReal
  have hnum : b ^ (-(d : ℝ) / 2) =
      Real.pi ^ (-(d : ℝ) / 2) * (Real.pi / b) ^ ((d : ℝ) / 2) := by
    rw [neg_div, Real.div_rpow Real.pi_pos.le hb.le, Real.rpow_neg Real.pi_pos.le,
      Real.rpow_neg hb.le]
    field_simp [(Real.rpow_pos_of_pos Real.pi_pos ((d : ℝ) / 2)).ne',
      (Real.rpow_pos_of_pos hb ((d : ℝ) / 2)).ne']
  rw [← mul_assoc]
  exact congrArg (· * Real.exp (-(‖z.1‖ ^ 2 / b * r))) hnum

/-- SYNOPSIS item 17, Gneiting's construction: for `φ` completely monotone, `ψ` positive on
`[0, ∞)` with completely monotone derivative, and `σ² > 0`,
`C(h, u) = σ² ψ(u²)^{-d/2} φ(‖h‖² / ψ(u²))` is positive definite on `ℝ^d × ℝ`. -/
theorem isPositiveDefiniteSub_gneiting {φ ψ : ℝ → ℝ}
    (hφ : TauCeti.IsContinuousCompletelyMonotoneOnIoi φ) (hψc : ContinuousOn ψ (Ici 0))
    (hψpos : ∀ t, 0 ≤ t → 0 < ψ t) (hψd : DifferentiableOn ℝ ψ (Ioi 0))
    (hψ' : TauCeti.IsCompletelyMonotoneOnIoi (deriv ψ)) {σsq : ℝ} (hσ : 0 < σsq) :
    TauCeti.IsPositiveDefiniteSub fun z : EuclideanSpace ℝ (Fin d) × ℝ ↦
      ((σsq / ψ (z.2 ^ 2) ^ ((d : ℝ) / 2) * φ (‖z.1‖ ^ 2 / ψ (z.2 ^ 2)) : ℝ) : ℂ) := by
  have hψ : TauCeti.IsBernsteinFunction ψ := TauCeti.isBernsteinFunction_iff.mpr
    ⟨hψc, (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr ⟨hψd, hψ'.contDiffOn⟩,
      fun t ht ↦ (hψpos t ht).le, hψ'⟩
  -- Decompose the spatial profile into Gaussian profiles using the Laplace representation.
  obtain ⟨μ, hμ⟩ := TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi hφ
  let := hμ.isFiniteMeasure
  have hp := (isPositiveDefiniteSub_integral
    (μ := μ) (isPositiveDefiniteSub_gneiting_gaussian (d := d) hψ hψpos)
    (fun z ↦ ((TauCeti.integrable_exp_neg_mul μ (div_nonneg (sq_nonneg ‖z.1‖)
      (hψpos _ (sq_nonneg z.2)).le)).const_mul _).ofReal)).real_smul hσ.le
  convert hp using 1
  funext z
  rw [hμ.eq_laplaceTransform (div_nonneg (sq_nonneg ‖z.1‖) (hψpos _ (sq_nonneg _)).le),
    TauCeti.laplaceTransform_apply]
  dsimp only [Pi.smul_apply, real_smul]
  rw [neg_div, Real.rpow_neg (hψpos _ (sq_nonneg _)).le]
  simp only [ofReal_mul, integral_const_mul, integral_complex_ofReal, div_eq_mul_inv,
    ofReal_inv, mul_assoc]

/-- SYNOPSIS item 17, the family `φ(t) = e^{-c t^γ}`, `ψ(t) = (a t^α + 1)^β` with `a, c ≥ 0`,
`α, γ ∈ (0, 1]` and `β ∈ [0, 1]`; `β = 0` gives a separable covariance and `β` measures
space–time interaction. -/
theorem isPositiveDefiniteSub_gneiting_family {a c α β γ σsq : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hσ : 0 < σsq) :
    TauCeti.IsPositiveDefiniteSub fun z : EuclideanSpace ℝ (Fin d) × ℝ ↦
      ((σsq / ((a * (z.2 ^ 2) ^ α + 1) ^ β) ^ ((d : ℝ) / 2) *
        Real.exp (-c * (‖z.1‖ ^ 2 / (a * (z.2 ^ 2) ^ α + 1) ^ β) ^ γ) : ℝ) : ℂ) := by
  have hφ := TauCeti.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul_rpow hc hγ₀.le hγ₁
  have hψ : TauCeti.IsBernsteinFunction (fun t : ℝ ↦ (a * t ^ α + 1) ^ β) := by
    refine ((TauCeti.isBernsteinFunction_rpow hβ₀ hβ₁).comp
      (((TauCeti.isBernsteinFunction_rpow hα₀.le hα₁).smul ha).const_add zero_le_one)).congr ?_
    intro t _
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, add_comm]
  have hψpos (t : ℝ) (ht : 0 ≤ t) : 0 < (a * t ^ α + 1) ^ β :=
    Real.rpow_pos_of_pos (by positivity) _
  exact isPositiveDefiniteSub_gneiting hφ hψ.continuousOn hψpos hψ.differentiableOn
    hψ.deriv_isCompletelyMonotoneOnIoi hσ

end MSSS
