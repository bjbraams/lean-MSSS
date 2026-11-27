module

public import MSSS.RandomFields.Matern.Basic
public import MSSS.RandomFields.Spectral
public import Mathlib.Analysis.Asymptotics.Defs

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Smoothness of Matérn fields

SYNOPSIS item 13. The small-lag bounds use the gamma mixture, with Mathlib's power and
reciprocal integrals controlling the contribution near zero and the tail. The principal
irregular terms use TauCeti's gamma moments and Mathlib's Lagrange remainder, change of
variables, and dominated convergence. At integer shape the reciprocal tail contributes
the logarithm.

## Main results

* `MSSS.isMeanSquareDifferentiable_matern_iff`: the mean-square smoothness threshold.
* `MSSS.one_sub_maternCorrelation_isBigO`, `MSSS.one_sub_maternCorrelation_not_isLittleO`:
  small-lag orders of the Matérn correlation deficit.
* `MSSS.maternCorrelation_principalIrregularTerm`,
  `MSSS.maternCorrelation_principalIrregularTerm_natCast`: the principal irregular term.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics
open scoped Interval Nat

namespace MSSS


/-- SYNOPSIS item 13: a second-order stationary process on `ℝ` with Matérn covariance
`σ² φ_{ν,θ}(|h|)` is `m` times mean-square differentiable if and only if `ν > m`. -/
theorem isMeanSquareDifferentiable_matern_iff {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : IsSecondOrderStationary Z P) (hcent : ∀ t, P[Z t] = 0) {ν θ σsq : ℝ} (hν : 0 < ν)
    (hθ : 0 < θ) (hσ : 0 < σsq) (hK : ∀ h, stationaryCov Z P h = σsq * maternCorrelation ν θ |h|)
    (m : ℕ) : IsMeanSquareDifferentiable m Z P ↔ (m : ℝ) < ν := by
  sorry

/-- The gamma density without its normalizing factor, times the exponential deficit. -/
private def maternDeficitKernel (ν s u : ℝ) : ℝ :=
  u ^ (ν - 1) * Real.exp (-u) * (1 - Real.exp (-(s / u)))

private lemma maternDeficitKernel_nonneg {ν s u : ℝ} (hs : 0 ≤ s) (hu : 0 < u) :
    0 ≤ maternDeficitKernel ν s u := by
  unfold maternDeficitKernel
  apply mul_nonneg (by positivity)
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hs hu.le)))

private lemma integrableOn_maternDeficitKernel {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    IntegrableOn (maternDeficitKernel ν s) (Ioi 0) := by
  have hgam : IntegrableOn (fun u : ℝ ↦ u ^ (ν - 1) * Real.exp (-u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_rpow (p := (1 : ℝ)) (s := ν - 1) (by linarith) one_pos
  refine hgam.mono' (by unfold maternDeficitKernel; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  rw [Real.norm_of_nonneg (maternDeficitKernel_nonneg hs hu'), maternDeficitKernel]
  exact mul_le_of_le_one_right (by positivity) (by linarith [Real.exp_pos (-(s / u))])

private lemma one_sub_maternCorrelation_eq_integral_maternDeficitKernel {ν θ t : ℝ}
    (hν : 0 < ν) (hθ : 0 < θ) (ht : 0 ≤ t) :
    1 - maternCorrelation ν θ t =
      (∫ u in Ioi 0, maternDeficitKernel ν (t ^ 2 / (4 * θ ^ 2)) u) / Real.Gamma ν := by
  let _ := isProbabilityMeasure_gammaMeasure hν (r := 1) one_pos
  rw [maternCorrelation_eq_integral_gammaMeasure hν hθ ht]
  nth_rw 1 [← show (∫ _ : ℝ, (1 : ℝ) ∂gammaMeasure ν 1) = 1 by simp]
  rw [← integral_sub (integrable_const _) (integrable_exp_neg_div_gammaMeasure (θ := θ) hν t),
    TauCeti.Probability.integral_gammaMeasure_eq_integral_Ioi hν one_pos,
    ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  simp only [Real.one_rpow, one_mul, smul_eq_mul, maternDeficitKernel, div_div]
  ring

/-- Split a half-line integral at a point to the right of its endpoint. -/
private lemma integral_Ioi_eq_Ioc_add_Ioi {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioi a)) :
    (∫ u in Ioi a, f u) = (∫ u in Ioc a b, f u) + ∫ u in Ioi b, f u := by
  rw [← intervalIntegral.integral_of_le hab]
  exact (intervalIntegral.integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm

private lemma integral_maternDeficitKernel_small_le {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    (∫ u in Ioc 0 s, maternDeficitKernel ν s u) ≤ s ^ ν / ν := by
  have hf : IntegrableOn (maternDeficitKernel ν s) (Ioc 0 s) :=
    (integrableOn_maternDeficitKernel hν hs.le).mono_set Ioc_subset_Ioi_self
  have hg := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s)
    (r := ν - 1) (by linarith)).1
  calc
    _ ≤ ∫ u in Ioc 0 s, u ^ (ν - 1) := by
      refine setIntegral_mono_on hf hg measurableSet_Ioc fun u hu ↦ ?_
      have hu₀ : 0 < u := hu.1
      unfold maternDeficitKernel
      have h₁ : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1.le)
      have h₂ : 1 - Real.exp (-(s / u)) ≤ 1 := by linarith [Real.exp_pos (-(s / u))]
      exact (mul_le_of_le_one_right (by positivity) h₂).trans
        (mul_le_of_le_one_right (by positivity) h₁)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hs.le, integral_rpow (Or.inl (by linarith)),
        sub_add_cancel, Real.zero_rpow hν.ne', sub_zero]

/-- Drop the exponential density factor on the tail and use the linear bound for the deficit. -/
private lemma maternDeficitKernel_le_mul_rpow {ν s u : ℝ} (hs : 0 ≤ s) (hu : 0 < u) :
    maternDeficitKernel ν s u ≤ s * u ^ (ν - 2) := by
  have h₁ : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.le)
  have h₂ : 1 - Real.exp (-(s / u)) ≤ s / u := by
    linarith [Real.add_one_le_exp (-(s / u))]
  unfold maternDeficitKernel
  calc
    _ ≤ (u ^ (ν - 1) * Real.exp (-u)) * (s / u) := by gcongr
    _ ≤ u ^ (ν - 1) * (s / u) := by
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) h₁) (by positivity)
    _ = _ := by
      rw [show ν - 2 = (ν - 1) - 1 by ring, Real.rpow_sub_one hu.ne' (ν - 1)]
      ring

private lemma integral_maternDeficitKernel_le_of_lt_one {ν s : ℝ} (hν : 0 < ν)
    (hν₁ : ν < 1) (hs : 0 < s) :
    (∫ u in Ioi 0, maternDeficitKernel ν s u) ≤ (ν⁻¹ + (1 - ν)⁻¹) * s ^ ν := by
  have hf := integrableOn_maternDeficitKernel hν hs.le
  have hg := (integrableOn_Ioi_rpow_of_lt (a := ν - 2) (by linarith) hs).const_mul s
  rw [integral_Ioi_eq_Ioc_add_Ioi hs.le hf]
  calc
    _ ≤ s ^ ν / ν + ∫ u in Ioi s, s * u ^ (ν - 2) := by
      refine add_le_add (integral_maternDeficitKernel_small_le hν hs) ?_
      exact setIntegral_mono_on (hf.mono_set (Ioi_subset_Ioi hs.le)) hg measurableSet_Ioi
        fun u hu ↦ maternDeficitKernel_le_mul_rpow hs.le (hs.trans hu)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hs,
        show ν - 2 + 1 = ν - 1 by ring, Real.rpow_sub_one hs.ne' ν,
        show ν - 1 = -(1 - ν) by ring, div_neg]
      field_simp [hs.ne', hν.ne', ne_of_gt (sub_pos.mpr hν₁)]

private lemma integrableOn_inv_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u : ℝ ↦ u⁻¹) (Ioc a b) := by
  have h := intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := a) (b := b)
    (r := -1) (Or.inr (by rw [uIcc_of_le hab]; exact fun h ↦ ha.not_ge h.1))
  simpa only [Real.rpow_neg_one] using h.1

private lemma integral_maternDeficitKernel_le_of_eq_one {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) :
    (∫ u in Ioi 0, maternDeficitKernel 1 s u) ≤ s * (2 + |Real.log s|) := by
  have hf := integrableOn_maternDeficitKernel one_pos hs.le
  have hf' := hf.mono_set (Ioi_subset_Ioi hs.le)
  have hg := (integrableOn_inv_Ioc hs hs₁).const_mul s
  rw [integral_Ioi_eq_Ioc_add_Ioi hs.le hf, integral_Ioi_eq_Ioc_add_Ioi hs₁ hf']
  calc
    _ ≤ s + (∫ u in Ioc s 1, s * u⁻¹) + ∫ u in Ioi 1, s * Real.exp (-u) := by
      rw [add_assoc]
      refine add_le_add (by simpa using integral_maternDeficitKernel_small_le one_pos hs) ?_
      refine add_le_add ?_ ?_
      · refine setIntegral_mono_on (hf'.mono_set fun _ h ↦ h.1) hg measurableSet_Ioc ?_
        intro u hu
        simpa only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one] using
          maternDeficitKernel_le_mul_rpow (ν := 1) hs.le (hs.trans hu.1)
      · refine setIntegral_mono_on (hf'.mono_set (Ioi_subset_Ioi hs₁))
          ((integrableOn_exp_neg_Ioi 1).const_mul s) measurableSet_Ioi fun u hu ↦ ?_
        have hu' : 1 < u := hu
        have h : 1 - Real.exp (-(s / u)) ≤ s := by
          have hlin : 1 - Real.exp (-(s / u)) ≤ s / u := by
            linarith [Real.add_one_le_exp (-(s / u))]
          exact hlin.trans (div_le_self hs.le hu'.le)
        simpa only [maternDeficitKernel, sub_self, Real.rpow_zero, one_mul, mul_comm s] using
          mul_le_mul_of_nonneg_left h (Real.exp_pos (-u)).le
    _ ≤ _ := by
      rw [integral_const_mul, integral_const_mul, integral_exp_neg_Ioi,
        ← intervalIntegral.integral_of_le hs₁, integral_inv_of_pos hs one_pos,
        one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hs.le hs₁)]
      have h : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left h hs.le]

private lemma half_le_one_sub_exp_neg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h : Real.exp (-x) * (1 + x) ≤ 1 := by
    calc
      _ ≤ Real.exp (-x) * Real.exp x := by gcongr; simpa [add_comm] using Real.add_one_le_exp x
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h' : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ (by positivity)).2 h
  calc
    x / 2 ≤ x / (1 + x) := by gcongr; linarith
    _ = 1 - (1 + x)⁻¹ := by field_simp [show 1 + x ≠ 0 by positivity]; ring
    _ ≤ _ := sub_le_sub_left h' _

private lemma integral_maternDeficitKernel_ge_const_mul_rpow_of_le_one {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (hs₁ : s ≤ 1) :
    (Real.exp (-1) * (1 - Real.exp (-1)) / ν) * s ^ ν ≤
      ∫ u in Ioi 0, maternDeficitKernel ν s u := by
  let C := Real.exp (-1) * (1 - Real.exp (-1))
  have hInt := integrableOn_maternDeficitKernel hν hs.le
  have hbase := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s)
    (r := ν - 1) (by linarith)).1
  calc
    _ = ∫ u in Ioc 0 s, C * u ^ (ν - 1) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hs.le,
        integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow hν.ne', sub_zero]
      dsimp only [C]
      ring
    _ ≤ ∫ u in Ioc 0 s, maternDeficitKernel ν s u := by
      refine setIntegral_mono_on (hbase.const_mul _) (hInt.mono_set Ioc_subset_Ioi_self)
        measurableSet_Ioc fun u hu ↦ ?_
      have h₁ : Real.exp (-1) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (neg_le_neg (hu.2.trans hs₁))
      have h₂ : 1 - Real.exp (-1) ≤ 1 - Real.exp (-(s / u)) := by
        apply sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg _))
        exact (le_div_iff₀ hu.1).mpr (by simpa using hu.2)
      have h₀ : 0 ≤ 1 - Real.exp (-1) := by
        exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
      simpa only [C, maternDeficitKernel, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ h₀ (Real.exp_pos _).le)
          (Real.rpow_nonneg hu.1.le (ν - 1))
    _ ≤ _ := by
      refine setIntegral_mono_set hInt ?_ (ae_of_all _ fun _ hu ↦ hu.1)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact maternDeficitKernel_nonneg hs.le hu

private lemma integral_maternDeficitKernel_ge_const_mul_of_one_le {ν s : ℝ} (hν : 1 ≤ ν)
    (hs : 0 < s) (hs₁ : s ≤ 1) :
    Real.exp (-2) / 4 * s ≤ ∫ u in Ioi 0, maternDeficitKernel ν s u := by
  have hInt := integrableOn_maternDeficitKernel (zero_lt_one.trans_le hν) hs.le
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioi 0 := Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)
  calc
    _ = ∫ _u in Ioc (1 : ℝ) 2, Real.exp (-2) / 4 * s := by
      rw [← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const]
      norm_num
    _ ≤ ∫ u in Ioc (1 : ℝ) 2, maternDeficitKernel ν s u := by
      refine setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioc]))
        (hInt.mono_set hsub) measurableSet_Ioc fun u hu ↦ ?_
      have hu₀ : 0 < u := zero_lt_one.trans hu.1
      have hx₀ : 0 ≤ s / u := by positivity
      have hx₁ : s / u ≤ 1 := (div_le_iff₀ hu₀).mpr (by linarith [hu.1])
      have h₁ : 1 ≤ u ^ (ν - 1) := Real.one_le_rpow hu.1.le (sub_nonneg.mpr hν)
      have h₂ : Real.exp (-2) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (neg_le_neg hu.2)
      have h₃ : s / 4 ≤ 1 - Real.exp (-(s / u)) := by
        refine le_trans ?_ (half_le_one_sub_exp_neg hx₀ hx₁)
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        apply (le_div_iff₀ hu₀).mpr
        nlinarith [mul_le_mul_of_nonneg_left hu.2 hs.le]
      unfold maternDeficitKernel
      calc
        _ = 1 * Real.exp (-2) * (s / 4) := by ring
        _ ≤ _ := by gcongr
    _ ≤ _ := by
      refine setIntegral_mono_set hInt ?_ (ae_of_all _ fun u hu ↦ hsub hu)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact maternDeficitKernel_nonneg hs.le hu

private lemma tendsto_maternLagParam (θ : ℝ) :
    Tendsto (fun t : ℝ ↦ t ^ 2 / (4 * θ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous fun t : ℝ ↦ t ^ 2 / (4 * θ ^ 2) := by fun_prop
  simpa using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

private lemma maternLagParam_rpow {θ t p : ℝ} (ht : 0 ≤ t) :
    (t ^ 2 / (4 * θ ^ 2)) ^ p = (4 * θ ^ 2)⁻¹ ^ p * t ^ (2 * p) := by
  rw [Real.div_rpow (sq_nonneg _) (by positivity), Real.inv_rpow (by positivity),
    ← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
  push_cast
  ring

/-- SYNOPSIS item 13: the small-lag Matérn deficit has the power bound `t ^ min (2 * ν) 2`,
with a factor of `|log t|` at the critical shape `ν = 1`. -/
theorem one_sub_maternCorrelation_isBigO {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    (fun t ↦ 1 - maternCorrelation ν θ t) =O[𝓝[>] 0]
      fun t ↦ if ν = 1 then t ^ 2 * |Real.log t| else t ^ min (2 * ν) 2 := by
  have hgam := Real.Gamma_pos_of_pos hν
  let B : ℝ := 4 * θ ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  rcases lt_trichotomy ν 1 with h | rfl | h
  · simp only [ite_eq_right h.ne, min_eq_left (by linarith : 2 * ν ≤ 2)]
    refine IsBigO.of_bound ((ν⁻¹ + (1 - ν)⁻¹) * B⁻¹ ^ ν / Real.Gamma ν) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hs : 0 < t ^ 2 / B := by positivity
    have hbound := integral_maternDeficitKernel_le_of_lt_one hν h hs
    change ‖1 - maternCorrelation ν θ t‖ ≤ _ * ‖t ^ (2 * ν)‖
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
      Real.norm_of_nonneg (sub_nonneg.mpr (maternCorrelation_lt_one hν hθ ht).le),
      one_sub_maternCorrelation_eq_integral_maternDeficitKernel hν hθ ht.le]
    calc
      _ ≤ (ν⁻¹ + (1 - ν)⁻¹) * (t ^ 2 / B) ^ ν / Real.Gamma ν :=
        div_le_div_of_nonneg_right hbound hgam.le
      _ = _ := by
        dsimp only [B]
        rw [maternLagParam_rpow ht.le]
        ring
  · simp only
    refine IsBigO.of_bound ((4 + |Real.log B|) / B) ?_
    have hs₁ : ∀ᶠ t : ℝ in 𝓝[>] 0, t ^ 2 / B < 1 :=
      (tendsto_maternLagParam θ).eventually (Iio_mem_nhds zero_lt_one)
    have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, Real.log t ≤ -1 :=
      Real.tendsto_log_nhdsGT_zero.eventually (eventually_le_atBot (-1 : ℝ))
    filter_upwards [self_mem_nhdsWithin, hs₁, hl] with t (ht : 0 < t) hs₁ hl
    have hs : 0 < t ^ 2 / B := by positivity
    have hb := integral_maternDeficitKernel_le_of_eq_one hs hs₁.le
    have hl₁ : 1 ≤ |Real.log t| := by rw [abs_of_nonpos (by linarith)]; linarith
    have hlog : |Real.log (t ^ 2 / B)| ≤ 2 * |Real.log t| + |Real.log B| := by
      rw [Real.log_div (pow_ne_zero _ ht.ne') hB.ne', Real.log_pow, Nat.cast_ofNat]
      exact (abs_sub_le (2 * Real.log t) 0 (Real.log B)).trans_eq (by simp [abs_mul])
    have hlog' : 2 + |Real.log (t ^ 2 / B)| ≤ (4 + |Real.log B|) * |Real.log t| := by
      nlinarith [mul_le_mul_of_nonneg_left hl₁ (abs_nonneg (Real.log B))]
    change ‖1 - maternCorrelation 1 θ t‖ ≤ _ * ‖t ^ 2 * |Real.log t|‖
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg t) (abs_nonneg _)),
      Real.norm_of_nonneg (sub_nonneg.mpr (maternCorrelation_lt_one one_pos hθ ht).le),
      one_sub_maternCorrelation_eq_integral_maternDeficitKernel one_pos hθ ht.le,
      Real.Gamma_one, div_one]
    calc
      _ ≤ (t ^ 2 / B) * ((4 + |Real.log B|) * |Real.log t|) :=
        hb.trans (mul_le_mul_of_nonneg_left hlog' hs.le)
      _ = _ := by ring
  · simp only [ite_eq_right h.ne', min_eq_right (by linarith : 2 ≤ 2 * ν)]
    refine IsBigO.of_bound (B⁻¹ * ∫ u, u ^ (-(1 : ℝ)) ∂gammaMeasure ν 1) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
      Real.norm_of_nonneg (sub_nonneg.mpr (maternCorrelation_lt_one hν hθ ht).le)]
    simpa only [B, mul_one, Real.rpow_neg_one] using
      one_sub_maternCorrelation_le_mul_rpow (p := 1) hν hθ ht.le zero_le_one le_rfl h

/-- SYNOPSIS item 13: the Matérn deficit does not vanish faster than `t ^ min (2 * ν) 2`. -/
theorem one_sub_maternCorrelation_not_isLittleO {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    ¬ (fun t ↦ 1 - maternCorrelation ν θ t) =o[𝓝[>] 0] fun t ↦ t ^ min (2 * ν) 2 := by
  have hgam := Real.Gamma_pos_of_pos hν
  let B : ℝ := 4 * θ ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hs₁ : ∀ᶠ t : ℝ in 𝓝[>] 0, t ^ 2 / B < 1 :=
    (tendsto_maternLagParam θ).eventually (Iio_mem_nhds zero_lt_one)
  have hbound : ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      c * t ^ min (2 * ν) 2 ≤ 1 - maternCorrelation ν θ t := by
    by_cases h : ν < 1
    · let C := (Real.exp (-1) * (1 - Real.exp (-1)) / ν)
      have hC : 0 < C := by
        have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        dsimp only [C]
        positivity
      refine ⟨C * B⁻¹ ^ ν / Real.Gamma ν, by positivity, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hs₁] with t (ht : 0 < t) hs₁
      have hs : 0 < t ^ 2 / B := by positivity
      rw [min_eq_left (by linarith : 2 * ν ≤ 2),
        one_sub_maternCorrelation_eq_integral_maternDeficitKernel hν hθ ht.le]
      calc
        _ = C * (t ^ 2 / B) ^ ν / Real.Gamma ν := by
          dsimp only [B]
          rw [maternLagParam_rpow ht.le]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (integral_maternDeficitKernel_ge_const_mul_rpow_of_le_one hν hs hs₁.le) hgam.le
    · let C := Real.exp (-2) / 4
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨C / Real.Gamma ν / B, by positivity, ?_⟩
      have hν₁ := le_of_not_gt h
      filter_upwards [self_mem_nhdsWithin, hs₁] with t (ht : 0 < t) hs₁
      have hs : 0 < t ^ 2 / B := by positivity
      rw [min_eq_right (by linarith : 2 ≤ 2 * ν), Real.rpow_two,
        one_sub_maternCorrelation_eq_integral_maternDeficitKernel hν hθ ht.le]
      calc
        _ = C * (t ^ 2 / B) / Real.Gamma ν := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (integral_maternDeficitKernel_ge_const_mul_of_one_le hν₁ hs hs₁.le) hgam.le
  obtain ⟨c, hc, hb⟩ := hbound
  intro ho
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0 := self_mem_nhdsWithin
  obtain ⟨t, ht, hlow, hhi⟩ := (hpos.and (hb.and (ho.def (half_pos hc)))).exists
  have ht' : 0 < t := ht
  have hp : 0 < t ^ min (2 * ν) 2 := Real.rpow_pos_of_pos ht' _
  change ‖1 - maternCorrelation ν θ t‖ ≤ (c / 2) * ‖t ^ min (2 * ν) 2‖ at hhi
  rw [Real.norm_of_nonneg (sub_nonneg.mpr (maternCorrelation_lt_one hν hθ ht').le),
    Real.norm_of_nonneg hp.le] at hhi
  linarith [mul_pos hc hp]

/-- The degree `n` exponential Taylor remainder, evaluated on the negative axis. -/
private def expNegRemainder (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) - ∑ k ∈ Finset.range (n + 1), (-x) ^ k / (k ! : ℝ)

private lemma continuous_expNegRemainder (n : ℕ) : Continuous (expNegRemainder n) := by
  unfold expNegRemainder
  fun_prop

private lemma expNegRemainder_eq_exp_mul_pow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ∃ y ∈ Ioo (-x) 0, expNegRemainder n x = Real.exp y * (-x) ^ (n + 1) / (n + 1)! := by
  have hx' : (0 : ℝ) ≠ -x := by linarith
  obtain ⟨y, hy, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx'
    (f := Real.exp) Real.contDiff_exp.contDiffOn
  use y
  refine ⟨by simpa only [uIoo_of_ge (neg_nonpos.mpr hx.le)] using hy, ?_⟩
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, sub_zero] at h
  rw [← h, expNegRemainder, taylor_within_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx')
      Real.contDiff_exp.contDiffAt (left_mem_uIcc),
    iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero, smul_eq_mul, mul_one, sub_zero]
  ring

private lemma expNegRemainder_signed_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ (n + 1) * expNegRemainder n x := by
  obtain ⟨y, _, hy⟩ := expNegRemainder_eq_exp_mul_pow n hx
  rw [hy, show -x = (-1) * x by ring, mul_pow]
  rw [show (-1 : ℝ) ^ (n + 1) * (Real.exp y * ((-1 : ℝ) ^ (n + 1) * x ^ (n + 1)) /
      ((n + 1)! : ℝ)) = ((-1 : ℝ) ^ (n + 1)) ^ 2 *
        (Real.exp y * x ^ (n + 1) / ((n + 1)! : ℝ)) by ring]
  positivity

private lemma abs_expNegRemainder_le_pow_succ (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |expNegRemainder n x| ≤ x ^ (n + 1) := by
  obtain ⟨y, hy, he⟩ := expNegRemainder_eq_exp_mul_pow n hx
  have h₁ : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy.2.le
  have h₂ : (1 : ℝ) ≤ (n + 1)! := by exact_mod_cast Nat.factorial_pos (n + 1)
  rw [he, abs_div, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_pow, abs_neg,
    abs_of_pos hx, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1)!)]
  exact (div_le_self (by positivity) h₂).trans (mul_le_of_le_one_left (by positivity) h₁)

private lemma abs_expNegRemainder_le_pow (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    |expNegRemainder n x| ≤ (n + 2) * x ^ n := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have he : |Real.exp (-x)| ≤ x ^ n := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx₀.le)).trans (one_le_pow₀ hx)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      |(-x) ^ k / (k ! : ℝ)| ≤ x ^ n := by
    rw [abs_div, abs_pow, abs_neg, abs_of_pos hx₀, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k !)]
    exact (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos k)).trans
      (pow_le_pow_right₀ hx (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  calc
    _ ≤ |Real.exp (-x)| + |∑ k ∈ Finset.range (n + 1), (-x) ^ k / (k ! : ℝ)| := abs_sub _ _
    _ ≤ x ^ n + ∑ k ∈ Finset.range (n + 1), x ^ n := by
      exact add_le_add he ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

/-- The scale-normalized remainder kernel at gamma shape `ν`. -/
private def maternRemainderKernel (ν : ℝ) (n : ℕ) (u : ℝ) :=
  u ^ (ν - 1) * expNegRemainder n (1 / u)

private lemma measurable_maternRemainderKernel (ν : ℝ) (n : ℕ) :
    Measurable (maternRemainderKernel ν n) := by
  unfold maternRemainderKernel
  exact (by fun_prop : Measurable (fun u : ℝ ↦ u ^ (ν - 1))).mul
    ((continuous_expNegRemainder n).measurable.comp (by fun_prop))

private lemma norm_maternRemainderKernel_le {ν u : ℝ} (n : ℕ) (hu : 0 < u) {k : ℕ}
    {C : ℝ} (h : |expNegRemainder n (1 / u)| ≤ C * (1 / u) ^ k) :
    ‖maternRemainderKernel ν n u‖ ≤ C * u ^ (ν - 1 - k) := by
  rw [maternRemainderKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hu.le _), Real.rpow_sub_natCast hu.ne']
  calc
    _ ≤ u ^ (ν - 1) * (C * (1 / u) ^ k) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hu.le _)
    _ = _ := by rw [div_pow, one_pow]; ring

private lemma integrableOn_maternRemainderKernel {ν : ℝ} {n : ℕ} (hn : (n : ℝ) < ν)
    (hn' : ν < n + 1) : IntegrableOn (maternRemainderKernel ν n) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one, integrableOn_union]
  constructor
  · have hpow := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := ν - 1 - n) (by linarith)).1.const_mul (n + 2 : ℝ)
    refine hpow.mono' (measurable_maternRemainderKernel ν n).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact norm_maternRemainderKernel_le n hu.1
      (abs_expNegRemainder_le_pow n ((le_div_iff₀ hu.1).mpr (by simpa using hu.2)))
  · have hpow := integrableOn_Ioi_rpow_of_lt (a := ν - 1 - (n + 1 : ℕ))
        (by push_cast; linarith) (c := (1 : ℝ)) one_pos
    refine hpow.mono' (measurable_maternRemainderKernel ν n).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [one_mul] using norm_maternRemainderKernel_le n (zero_lt_one.trans hu)
      (C := 1) (k := n + 1) (by simpa only [one_mul] using
        abs_expNegRemainder_le_pow_succ n (one_div_pos.mpr (zero_lt_one.trans hu)))

/-- Integrate the Taylor coefficients under the inverse-gamma Gaussian mixture. -/
private def maternTaylor (ν B : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k
    (((-B⁻¹) ^ k / (k ! : ℝ)) * (Real.Gamma (ν - k) / Real.Gamma ν))

private lemma natDegree_maternTaylor_le (ν B : ℝ) (n : ℕ) : (maternTaylor ν B n).natDegree ≤ n := by
  unfold maternTaylor
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

private lemma integral_expNegTaylor_gammaMeasure {ν B t : ℝ} {n : ℕ} (hn : (n : ℝ) < ν) :
    (∫ u, ∑ k ∈ Finset.range (n + 1), (-(t ^ 2 / (B * u))) ^ k / (k ! : ℝ)
        ∂gammaMeasure ν 1) = (maternTaylor ν B n).eval (t ^ 2) := by
  have hν : 0 < ν := (Nat.cast_nonneg n).trans_lt hn
  let c (k : ℕ) : ℝ := (-(B⁻¹)) ^ k / (k ! : ℝ) * (t ^ 2) ^ k
  have hpoint (k : ℕ) {u : ℝ} (hu : 0 < u) :
      (-(t ^ 2 / (B * u))) ^ k / (k ! : ℝ) = c k * u ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg hu.le, Real.rpow_natCast]
    simp only [c, div_eq_mul_inv, mul_inv_rev]
    ring
  have hdegree (k : ℕ) (hk : k ∈ Finset.range (n + 1)) : -ν < -(k : ℝ) := by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    linarith
  have hint (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Integrable (fun u : ℝ ↦ (-(t ^ 2 / (B * u))) ^ k / (k ! : ℝ)) (gammaMeasure ν 1) := by
    have hi := (TauCeti.Probability.integrable_rpow_gammaMeasure_iff hν one_pos _).mpr
      (hdegree k hk)
    refine (hi.const_mul (c k)).congr ?_
    filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
    exact (hpoint k hu).symm
  rw [integral_finsetSum _ hint, maternTaylor, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_monomial, show
      (∫ u, (-(t ^ 2 / (B * u))) ^ k / (k ! : ℝ) ∂gammaMeasure ν 1) =
        ∫ u, c k * u ^ (-(k : ℝ)) ∂gammaMeasure ν 1 by
          refine integral_congr_ae ?_
          filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
          exact hpoint k hu]
  rw [integral_const_mul, TauCeti.Probability.integral_rpow_gammaMeasure hν one_pos (hdegree k hk),
    Real.one_rpow, one_mul, ← sub_eq_add_neg]
  dsimp only [c]
  ring

private lemma maternCorrelation_sub_taylor_eq_scaled_remainder {ν θ t : ℝ} {n : ℕ}
    (hn : (n : ℝ) < ν) (hθ : 0 < θ) (ht : 0 < t) :
    let B := 4 * θ ^ 2
    let s := t ^ 2 / B
    maternCorrelation ν θ t - (maternTaylor ν B n).eval (t ^ 2) =
      (s ^ ν / Real.Gamma ν) *
        ∫ u in Ioi 0, Real.exp (-(s * u)) * maternRemainderKernel ν n u := by
  intro B s
  have hν : 0 < ν := (Nat.cast_nonneg n).trans_lt hn
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hint : Integrable (fun u : ℝ ↦ ∑ k ∈ Finset.range (n + 1),
        (-(t ^ 2 / (B * u))) ^ k / (k ! : ℝ)) (gammaMeasure ν 1) := by
    apply integrable_finsetSum
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hi := (TauCeti.Probability.integrable_rpow_gammaMeasure_iff hν one_pos (-(k : ℝ))).mpr
      (by linarith)
    refine (hi.const_mul ((-s) ^ k / (k ! : ℝ))).congr ?_
    filter_upwards [TauCeti.Probability.ae_pos_gammaMeasure ν 1] with u hu
    rw [Real.rpow_neg hu.le, Real.rpow_natCast]
    dsimp only [s]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [maternCorrelation_eq_integral_gammaMeasure hν hθ ht.le,
    ← integral_expNegTaylor_gammaMeasure (t := t) hn,
    ← integral_sub (integrable_exp_neg_div_gammaMeasure hν t) hint]
  change (∫ u, expNegRemainder n (t ^ 2 / (B * u)) ∂gammaMeasure ν 1) = _
  rw [TauCeti.Probability.integral_gammaMeasure_eq_integral_Ioi hν one_pos]
  let f (u : ℝ) := (1 ^ ν / Real.Gamma ν * u ^ (ν - 1) * Real.exp (-(1 * u))) *
    expNegRemainder n (t ^ 2 / (B * u))
  change (∫ u in Ioi 0, f u) = _
  rw [← show (∫ u in Ioi 0, s * f (s * u)) = ∫ u in Ioi 0, f u by
    rw [integral_const_mul]
    simpa only [smul_eq_mul, mul_zero] using integral_comp_mul_left_Ioi' f 0 hs,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  have hu₀ : 0 < u := hu
  have harg : t ^ 2 / (B * (s * u)) = 1 / u := by
    dsimp only [s]
    field_simp [hB.ne', ht.ne', hu₀.ne']
  dsimp only [f, maternRemainderKernel]
  rw [harg, Real.one_rpow, one_mul, Real.mul_rpow hs.le hu₀.le, Real.rpow_sub_one hs.ne']
  field_simp [hs.ne']

private lemma integral_maternRemainderKernel_ne_zero {ν : ℝ} {n : ℕ}
    (h : IntegrableOn (maternRemainderKernel ν n) (Ioi 0)) :
    (∫ u in Ioi 0, maternRemainderKernel ν n u) ≠ 0 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hμ : μ ≠ 0 := by
    intro hz
    have hz' := congrArg (fun m : Measure ℝ ↦ m univ) hz
    simp [μ, Real.volume_Ioi] at hz'
  have : NeZero μ := ⟨hμ⟩
  let c : ℝ := (-1) ^ (n + 1)
  have hpos : ∀ᵐ u ∂μ, 0 < c * maternRemainderKernel ν n u := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    rw [maternRemainderKernel, mul_left_comm]
    exact mul_pos (Real.rpow_pos_of_pos hu' _) (expNegRemainder_signed_pos n (one_div_pos.mpr hu'))
  intro hz
  have hint : ∫ u, c * maternRemainderKernel ν n u ∂μ = 0 := by
    rw [integral_const_mul, hz, mul_zero]
  have haez := (integral_eq_zero_iff_of_nonneg_ae (hpos.mono fun u hu ↦ hu.le)
    (h.const_mul c)).mp hint
  obtain ⟨u, hu, hz⟩ := (hpos.and haez).exists
  exact hu.ne' hz

private lemma tendsto_integral_exp_mul_maternRemainderKernel {ν θ : ℝ} {n : ℕ}
    (h : IntegrableOn (maternRemainderKernel ν n) (Ioi 0)) :
    Tendsto (fun t : ℝ ↦ ∫ u in Ioi 0,
      Real.exp (-(t ^ 2 / (4 * θ ^ 2) * u)) * maternRemainderKernel ν n u) (𝓝[>] 0)
      (𝓝 (∫ u in Ioi 0, maternRemainderKernel ν n u)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun u ↦ ‖maternRemainderKernel ν n u‖)
  · refine Eventually.of_forall fun t ↦ ?_
    have he : Measurable (fun u : ℝ ↦ Real.exp (-(t ^ 2 / (4 * θ ^ 2) * u))) := by fun_prop
    exact (he.mul (measurable_maternRemainderKernel ν n)).aestronglyMeasurable
  · filter_upwards with t
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (by positivity) hu'.le)))
  · exact h.norm
  · refine ae_of_all _ fun u ↦ ?_
    have ht := Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_maternLagParam θ).mul_const u).neg
    simpa only [Function.comp_apply, zero_mul, neg_zero, Real.exp_zero, one_mul] using
      ht.mul_const (maternRemainderKernel ν n u)

/-- SYNOPSIS item 13: for noninteger `ν`, the principal irregular term of `φ_{ν,θ}` is a nonzero
multiple of `t^{2ν}` after subtracting a polynomial in `t²` of degree at most `⌊ν⌋`. -/
theorem maternCorrelation_principalIrregularTerm {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    (hνn : ∀ n : ℕ, ν ≠ n) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ p : Polynomial ℝ, p.natDegree ≤ ⌊ν⌋₊ ∧
      (fun t ↦ maternCorrelation ν θ t - p.eval (t ^ 2) - c * t ^ (2 * ν)) =o[𝓝[>] 0]
        fun t ↦ t ^ (2 * ν) := by
  let n := ⌊ν⌋₊
  let B := 4 * θ ^ 2
  let A := B⁻¹ ^ ν / Real.Gamma ν
  let J := ∫ u in Ioi 0, maternRemainderKernel ν n u
  have hn : (n : ℝ) < ν := (Nat.floor_le hν.le).lt_of_ne (hνn n).symm
  have hI := integrableOn_maternRemainderKernel hn (Nat.lt_floor_add_one ν)
  have hA : 0 < A := by
    have hΓ := Real.Gamma_pos_of_pos hν
    dsimp [A, B]
    positivity
  refine ⟨A * J, mul_ne_zero hA.ne' (integral_maternRemainderKernel_ne_zero hI), maternTaylor ν B n,
    natDegree_maternTaylor_le ν B n, ?_⟩
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact fun hz ↦ ((Real.rpow_pos_of_pos ht _).ne' hz).elim
  · have hD := tendsto_integral_exp_mul_maternRemainderKernel (θ := θ) hI
    have hL : Tendsto (fun t : ℝ ↦ A * (∫ u in Ioi 0,
        Real.exp (-(t ^ 2 / B * u)) * maternRemainderKernel ν n u) - A * J) (𝓝[>] 0) (𝓝 0) := by
      simpa only [J, sub_self] using (hD.const_mul A).sub_const (A * J)
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hpow : t ^ (2 * ν) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    rw [maternCorrelation_sub_taylor_eq_scaled_remainder hn hθ ht]
    dsimp only [A, B]
    rw [maternLagParam_rpow ht.le]
    field_simp [hpow]

private lemma integrableOn_exp_neg_mul_inv_Ioi {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-u) * u⁻¹) (Ioi s) := by
  refine ((integrableOn_exp_neg_Ioi s).const_mul s⁻¹).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : s < u := hu
  have h₀ := hs.trans hu'
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg (by positivity)]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (inv_anti₀ hs hu'.le) (Real.exp_nonneg (-u))

/-- The tail integral of `exp(-u)/u` differs from `-log s` by a bounded amount at zero. -/
private lemma abs_integral_exp_neg_mul_inv_add_log_le {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) :
    |(∫ u in Ioi s, Real.exp (-u) * u⁻¹) + Real.log s| ≤ 2 := by
  have hf := integrableOn_exp_neg_mul_inv_Ioi hs
  have h₁ := hf.mono_set (show Ioc s 1 ⊆ Ioi s from Ioc_subset_Ioi_self)
  have h₂ := integrableOn_inv_Ioc hs hs₁
  have hlow : (∫ u in Ioc s 1, Real.exp (-u) * u⁻¹) + Real.log s =
      ∫ u in Ioc s 1, (Real.exp (-u) - 1) * u⁻¹ := by
    have hlog : (∫ u in Ioc s 1, u⁻¹) = -Real.log s := by
      rw [← intervalIntegral.integral_of_le hs₁, integral_inv_of_pos hs one_pos,
        one_div, Real.log_inv]
    simp_rw [sub_mul, one_mul]
    rw [integral_sub h₁ h₂, hlog, sub_neg_eq_add]
  have hlow' : |∫ u in Ioc s 1, (Real.exp (-u) - 1) * u⁻¹| ≤ 1 := by
    have h : ∀ᵐ u ∂volume.restrict (Ioc s 1), ‖(Real.exp (-u) - 1) * u⁻¹‖ ≤ (1 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu' : 0 < u := hs.trans hu.1
      have hex : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu'.le)
      have hlin : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr hex), neg_sub,
        abs_of_nonneg (by positivity : 0 ≤ u⁻¹)]
      simpa [hu'.ne'] using mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr hu'.le)
    have hbound := norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) h
    rw [Real.norm_eq_abs, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs₁)] at hbound
    exact hbound.trans (by linarith)
  have htail : |∫ u in Ioi 1, Real.exp (-u) * u⁻¹| ≤ 1 := by
    have hnon : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun u ↦ Real.exp (-u) * u⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := zero_lt_one.trans hu
      positivity
    rw [abs_of_nonneg (integral_nonneg_of_ae hnon)]
    calc
      _ ≤ ∫ u in Ioi 1, Real.exp (-u) := by
        refine setIntegral_mono_on (integrableOn_exp_neg_mul_inv_Ioi one_pos)
          (integrableOn_exp_neg_Ioi 1) measurableSet_Ioi fun u hu ↦ ?_
        exact mul_le_of_le_one_right (Real.exp_nonneg _)
          (inv_le_one_of_one_le₀ (show 1 ≤ u from hu.le))
      _ ≤ _ := by rw [integral_exp_neg_Ioi]; exact Real.exp_le_one_iff.mpr (by norm_num)
  rw [integral_Ioi_eq_Ioc_add_Ioi hs₁ hf, add_right_comm, hlow]
  exact (abs_add_le _ _).trans (by linarith)

private lemma integral_exp_neg_mul_mul_inv_Ioi {s : ℝ} (hs : 0 < s) :
    (∫ u in Ioi 1, Real.exp (-(s * u)) * u⁻¹) = ∫ u in Ioi s, Real.exp (-u) * u⁻¹ := by
  let f (u : ℝ) := Real.exp (-u) * u⁻¹
  have h := integral_comp_mul_left_Ioi' f 1 hs
  rw [mul_one] at h
  change _ = ∫ u in Ioi s, f u
  rw [← h, smul_eq_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only [f]
  field_simp [hs.ne']

/-- The coefficient of `u⁻¹` in the rescaled Taylor remainder at integer shape `n`. -/
private def maternLogCoeff (n : ℕ) : ℝ := (-1 : ℝ) ^ n / (n ! : ℝ)

private def maternLogError (m : ℕ) (u : ℝ) : ℝ :=
  if 1 < u then maternRemainderKernel (m + 1 : ℕ) (m + 1) u
  else maternRemainderKernel (m + 1 : ℕ) m u

private lemma measurable_maternLogError (m : ℕ) : Measurable (maternLogError m) :=
  (measurable_maternRemainderKernel _ _).ite measurableSet_Ioi
    (measurable_maternRemainderKernel _ _)

private lemma integrableOn_maternLogError (m : ℕ) : IntegrableOn (maternLogError m) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one, integrableOn_union]
  constructor
  · have hc : IntegrableOn (fun _ : ℝ ↦ (m : ℝ) + 2) (Ioc 0 1) :=
      integrableOn_const (by simp [Real.volume_Ioc])
    refine hc.mono' (measurable_maternLogError m).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [maternLogError, ite_eq_right (not_lt_of_ge hu.2)]
    have h := norm_maternRemainderKernel_le (ν := (m + 1 : ℕ)) m hu.1
      (abs_expNegRemainder_le_pow m ((le_div_iff₀ hu.1).mpr (by simpa using hu.2)))
    rw [show (((m + 1 : ℕ) : ℝ) - 1 - m) = 0 by push_cast; ring, Real.rpow_zero, mul_one] at h
    exact h
  · have ht := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := (1 : ℝ)) one_pos
    refine ht.mono' (measurable_maternLogError m).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 1 < u := hu
    have h₀ : 0 < u := zero_lt_one.trans hu'
    rw [maternLogError, ite_eq_left hu']
    have h := norm_maternRemainderKernel_le (ν := (m + 1 : ℕ)) (m + 1) h₀
      (C := 1) (k := (m + 1) + 1)
      (by simpa only [one_mul] using abs_expNegRemainder_le_pow_succ (m + 1) (one_div_pos.mpr h₀))
    rw [show (((m + 1 : ℕ) : ℝ) - 1 - (((m + 1) + 1 : ℕ) : ℝ)) = -2 by push_cast; ring,
      one_mul] at h
    exact h

private lemma maternRemainderKernel_succ_eq_add {m : ℕ} {u : ℝ} (hu : 0 < u) :
    maternRemainderKernel (m + 1 : ℕ) m u = maternLogError m u +
      (Ioi (1 : ℝ)).indicator (fun u ↦ maternLogCoeff (m + 1) * u⁻¹) u := by
  by_cases h : 1 < u
  · rw [maternLogError, ite_eq_left h, indicator_of_mem h]
    unfold maternRemainderKernel expNegRemainder maternLogCoeff
    rw [Finset.sum_range_succ (fun k ↦ (-(1 / u)) ^ k / (k ! : ℝ)) (m + 1)]
    have hpow : u ^ (((m + 1 : ℕ) : ℝ) - 1) = u ^ m := by
      rw [show (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hpow]
    have he : u ^ m * (-(1 / u)) ^ (m + 1) = (-1 : ℝ) ^ (m + 1) * u⁻¹ := by
      rw [← neg_div, div_pow, pow_succ u m]
      field_simp [hu.ne']
    rw [← sub_sub]
    simp only [mul_sub]
    rw [← mul_div_assoc, he]
    ring
  · have h' : u ∉ Ioi (1 : ℝ) := h
    rw [maternLogError, ite_eq_right h, indicator_of_notMem h', add_zero]

private lemma integral_exp_mul_maternRemainderKernel_succ {m : ℕ} {s : ℝ} (hs : 0 < s) :
    (∫ u in Ioi 0, Real.exp (-(s * u)) * maternRemainderKernel (m + 1 : ℕ) m u) =
      (∫ u in Ioi 0, Real.exp (-(s * u)) * maternLogError m u) +
        maternLogCoeff (m + 1) * ∫ u in Ioi s, Real.exp (-u) * u⁻¹ := by
  let f (u : ℝ) := Real.exp (-(s * u)) * maternLogError m u
  let g (u : ℝ) := Real.exp (-(s * u)) * u⁻¹
  let c := maternLogCoeff (m + 1)
  have hfg : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_maternLogError m).norm.mono' ?_ ?_
    · exact ((by fun_prop : Measurable fun u : ℝ ↦ Real.exp (-(s * u))).mul
        (measurable_maternLogError m)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h₀ : 0 < u := hu
      dsimp only [f]
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hs.le h₀.le)))
  have hg : IntegrableOn g (Ioi 1) := by
    have hex : IntegrableOn (fun u : ℝ ↦ Real.exp (-(s * u))) (Ioi 1) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := 0) (b := s)
        (by norm_num) one_pos hs
      exact (show IntegrableOn (fun u : ℝ ↦ Real.exp (-(s * u))) (Ioi 0) by
        simpa only [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul] using h).mono_set
          (Ioi_subset_Ioi zero_le_one)
    refine hex.mono' (by dsimp only [g]; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 1 < u := hu
    have h₀ : 0 < u := zero_lt_one.trans hu'
    dsimp only [g]
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (inv_nonneg.mpr h₀.le)]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) (inv_le_one_of_one_le₀ hu'.le)
  have h_g : Integrable ((Ioi (1 : ℝ)).indicator (fun u ↦ c * g u))
      (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.2 (Ioi_subset_Ioi zero_le_one)]
    exact hg.const_mul c
  rw [← integral_exp_neg_mul_mul_inv_Ioi hs]
  change _ = (∫ u in Ioi 0, f u) + c * ∫ u in Ioi 1, g u
  rw [← integral_const_mul, ← show
    (∫ u in Ioi 0, (Ioi (1 : ℝ)).indicator (fun u ↦ c * g u) u) =
      ∫ u in Ioi 1, c * g u by
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi zero_le_one)], ← integral_add hfg h_g]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  rw [maternRemainderKernel_succ_eq_add hu]
  by_cases h : u ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h, f, g, c]
    ring
  · simp only [indicator_of_notMem h, add_zero, f]

private lemma abs_integral_exp_mul_maternLogError_le (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |∫ u in Ioi 0, Real.exp (-(s * u)) * maternLogError m u| ≤
      ∫ u in Ioi 0, ‖maternLogError m u‖ := by
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (integrableOn_maternLogError m).norm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have h₀ : 0 < u := hu
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg hs h₀.le)))

/-- SYNOPSIS item 13: at positive integer shape `n`, the principal irregular term of `φ_{n,θ}`
is a nonzero multiple of `t^{2n} log t`. -/
theorem maternCorrelation_principalIrregularTerm_natCast {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧
      (fun t ↦ maternCorrelation n θ t - p.eval (t ^ 2) - c * t ^ (2 * n) * Real.log t)
        =o[𝓝[>] 0] fun t ↦ t ^ (2 * n) * Real.log t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let B := 4 * θ ^ 2
  let s (t : ℝ) := t ^ 2 / B
  let A : ℝ := B⁻¹ ^ (m + 1) / Real.Gamma (m + 1)
  let d := maternLogCoeff (m + 1)
  let L (t : ℝ) := ∫ u in Ioi 0,
    Real.exp (-(s t * u)) * maternRemainderKernel (m + 1 : ℕ) m u
  let W (t : ℝ) := L t + d * Real.log (s t) + d * Real.log B
  have hB : 0 < B := by dsimp only [B]; positivity
  have hΓ : 0 < Real.Gamma (m + 1 : ℝ) := Real.Gamma_pos_of_pos (by positivity)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hd : d ≠ 0 := div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  have hm : (m : ℝ) < (m + 1 : ℕ) := by push_cast; linarith
  refine ⟨-2 * A * d, mul_ne_zero (mul_ne_zero (by norm_num) hA.ne') hd,
    maternTaylor (m + 1 : ℕ) B m, (natDegree_maternTaylor_le _ _ _).trans (Nat.le_succ _), ?_⟩
  have ht₀ : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, Real.log t < 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot (0 : ℝ))
  have hs₁ : ∀ᶠ t : ℝ in 𝓝[>] 0, s t < 1 :=
    (tendsto_maternLagParam θ).eventually (Iio_mem_nhds zero_lt_one)
  have hW : W =O[𝓝[>] 0] fun _ ↦ (1 : ℝ) := by
    refine IsBigO.of_bound ((∫ u in Ioi 0, ‖maternLogError m u‖) + 2 * |d| +
      |d * Real.log B|) ?_
    filter_upwards [ht₀, hs₁] with t ht hs₁
    have hs : 0 < s t := by dsimp only [s]; positivity
    let e := ∫ u in Ioi 0, Real.exp (-(s t * u)) * maternLogError m u
    let J := ∫ u in Ioi (s t), Real.exp (-u) * u⁻¹
    have he := abs_integral_exp_mul_maternLogError_le m hs.le
    have hJ := abs_integral_exp_neg_mul_inv_add_log_le hs hs₁.le
    change ‖W t‖ ≤ _ * ‖(1 : ℝ)‖
    rw [Real.norm_eq_abs, norm_one, mul_one]
    calc
      |W t| = |(e + d * (J + Real.log (s t))) + d * Real.log B| := by
        dsimp only [W, L, e, J, d]
        rw [integral_exp_mul_maternRemainderKernel_succ hs]
        congr 1
        ring
      _ ≤ |e| + |d| * |J + Real.log (s t)| + |d * Real.log B| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ _ := by
        refine add_le_add (add_le_add he ?_) le_rfl
        rw [mul_comm (2 : ℝ)]
        exact mul_le_mul_of_nonneg_left hJ (abs_nonneg d)
  have hLog : (fun _ : ℝ ↦ (1 : ℝ)) =o[𝓝[>] 0] Real.log := by
    refine (isLittleO_iff_tendsto' (hl.mono fun _ ht h ↦ (ht.ne h).elim)).mpr ?_
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [ht₀, hl] with t ht hlt
    exact fun hz ↦ ((mul_ne_zero (pow_ne_zero _ ht.ne') hlt.ne) hz).elim
  · have hlim := ((hW.trans_isLittleO hLog).tendsto_div_nhds_zero).const_mul A
    rw [mul_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [ht₀, hl] with t ht hlt
    have hpow : t ^ (2 * (m + 1)) ≠ 0 := pow_ne_zero _ ht.ne'
    have hscale : (s t) ^ (((m + 1 : ℕ) : ℝ)) / Real.Gamma (m + 1 : ℕ) =
        A * t ^ (2 * (m + 1)) := by
      rw [Real.rpow_natCast]
      dsimp only [s, A]
      rw [Nat.cast_add, Nat.cast_one, div_pow, ← pow_mul, inv_pow]
      ring
    have hEq : maternCorrelation (m + 1 : ℕ) θ t -
        (maternTaylor (m + 1 : ℕ) B m).eval (t ^ 2) = A * t ^ (2 * (m + 1)) * L t := by
      rw [maternCorrelation_sub_taylor_eq_scaled_remainder hm hθ ht]
      change (s t) ^ (((m + 1 : ℕ) : ℝ)) / Real.Gamma (m + 1 : ℕ) * L t = _
      rw [hscale]
    have hl' : Real.log (s t) = 2 * Real.log t - Real.log B := by
      dsimp only [s]
      rw [Real.log_div (pow_ne_zero _ ht.ne') hB.ne', Real.log_pow, Nat.cast_ofNat]
    change A * (W t / Real.log t) =
      (maternCorrelation (m + 1 : ℕ) θ t - (maternTaylor (m + 1 : ℕ) B m).eval (t ^ 2) -
        (-2 * A * d) * t ^ (2 * (m + 1)) * Real.log t) / (t ^ (2 * (m + 1)) * Real.log t)
    rw [hEq]
    dsimp only [W]
    rw [hl']
    field_simp [hpow, hlt.ne]
    ring

end MSSS
