module

public import MSSS.GibbsPointProcesses.InfiniteVolume
public import MSSS.PointProcesses.Palm
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Summary statistics of stationary point processes

SYNOPSIS items 103 and 104: estimation of the intensity and of the `K`-function, and the
empty-space, nearest-neighbour, and `J`-functions of Poisson and Gibbs processes.

A point process is `∑_{n : I n} δ_{x_n}` as in `MSSS.PointProcesses.Basic`. For the Poisson
ratio estimator of `K` with Ripley's isotropic edge correction, conditioning a Poisson process
on `X(W) = N` gives `N` independent uniform points in `W`; the statement is made for such
points. The almost sure convergence of edge-corrected estimators is stated for the
translation-corrected ratio estimator. The intensity estimator uses TauCeti’s transport
of densities through a measurable embedding and Mathlib’s second-moment formula for variance.
The Poisson void and nearest-neighbour probabilities follow from the count law and the
finite-intensity Mecke identity on a bounded window.

## Main definitions

* `MSSS.kFunctional α₂ ρ A B`, `MSSS.IsReweightedStationary α₂ ρ`, `MSSS.translationK`.
* `MSSS.circleFraction W ξ r`, `MSSS.ripleyK W t u`.
* `MSSS.IsErgodicPointProcess P η`.
* `MSSS.IsPalmDistribution P η P₀`, `MSSS.emptySpace`, `MSSS.nearestNeighbour`, `MSSS.jFunction`.

## Main results

* `MSSS.intensity_estimator`, `MSSS.integral_translationK`, `MSSS.integral_ripleyK`,
  `MSSS.tendstoUniformlyOn_translationK`: SYNOPSIS item 103.
* `MSSS.emptySpace_poisson`, `MSSS.jFunction_gibbs`, `MSSS.jFunction_gibbs_of_range_le`:
  SYNOPSIS item 104.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Function Filter Metric TauCeti.Probability
open scoped ENNReal Topology

namespace MSSS

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-! ### Intensity and `K`-function estimation (SYNOPSIS item 103) -/

private lemma lintegral_factorialCount_of_pairDensity
    {P : Measure Ω} {α : Ω → Measure (Fin 2 → EuclideanSpace ℝ (Fin d))}
    (hαm : AEMeasurable α P)
    {w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ}
    (hw₀ : ∀ z, 0 ≤ w z)
    (hα₂ : P.bind α = volume.withDensity fun z ↦ ENNReal.ofReal (w (z 0, z 1)))
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWm : MeasurableSet W)
    (hwm : IntegrableOn w (W ×ˢ W)) :
    let e : (Fin 2 → EuclideanSpace ℝ (Fin d)) ≃ᵐ
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) := MeasurableEquiv.finTwoArrow
    ∫⁻ ω, (α ω |>.map e) (W ×ˢ W) ∂P = ENNReal.ofReal (∫ z in W ×ˢ W, w z) := by
  let Y := EuclideanSpace ℝ (Fin d)
  intro e
  have he : e = (MeasurableEquiv.finTwoArrow : (Fin 2 → Y) ≃ᵐ Y × Y) := rfl
  have hPush : (P.bind α).map e =
      (volume : Measure (Y × Y)).withDensity (fun z ↦ ENNReal.ofReal (w z)) := by
    rw [hα₂]
    calc
      _ = (volume.withDensity ((fun z ↦ ENNReal.ofReal (w z)) ∘ e)).map e := rfl
      _ = _ := by rw [e.measurableEmbedding.map_withDensity_comp, he,
        (volume_preserving_finTwoArrow Y).map_eq]
  have hbox := hWm.prod hWm
  calc
    _ = ((P.bind α).map e) (W ×ˢ W) := by
      simp_rw [Measure.map_apply e.measurable hbox]
      exact (Measure.bind_apply (e.measurable hbox) hαm).symm
    _ = _ := by
      rw [hPush, withDensity_apply _ hbox, ofReal_integral_eq_lintegral_ofReal hwm
        (ae_of_all _ hw₀)]

/-- The first two raw count moments come from the mean intensity and the second factorial
moment measure. -/
private theorem intensity_count_lintegrals {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Ω → ℕ → Bool) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (hm : Measurable fun ω ↦ pointSum (I ω) (x ω))
    (hst : IsStationary P fun ω ↦ pointSum (I ω) (x ω)) {lam : ℝ}
    (hlam : intensity P (fun ω ↦ pointSum (I ω) (x ω)) = ENNReal.ofReal lam)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} (hg0 : ∀ y z, 0 ≤ g y z)
    (hα₂ : P.bind (fun ω ↦ factorialPointSum 2 (I ω) (x ω)) =
      volume.withDensity fun z ↦ ENNReal.ofReal (lam ^ 2 * g (z 0) (z 1)))
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWm : MeasurableSet W)
    (hgi : IntegrableOn (fun z ↦ g z.1 z.2) (W ×ˢ W)) :
    let η (ω : Ω) := pointSum (I ω) (x ω)
    (∫⁻ ω, η ω W ∂P = ENNReal.ofReal lam * volume W) ∧
    (∫⁻ ω, (η ω W) ^ 2 ∂P =
      ENNReal.ofReal (lam ^ 2 * (∫ z in W ×ˢ W, g z.1 z.2)) +
        ENNReal.ofReal lam * volume W) := by
  let Y := EuclideanSpace ℝ (Fin d)
  let Q : Measure Y := volume
  let η (ω : Ω) := pointSum (I ω) (x ω)
  let α (ω : Ω) := factorialPointSum 2 (I ω) (x ω)
  have hMean : P.bind η = ENNReal.ofReal lam • Q := by
    rw [intensityMeasure_stationary hm hst (by rw [hlam]; exact ENNReal.ofReal_lt_top), hlam]
  have hEval (B : Set Y) (hBm : MeasurableSet B) :
      ∫⁻ ω, η ω B ∂P = ENNReal.ofReal lam * Q B := by
    rw [← Measure.bind_apply hBm hm.aemeasurable, hMean, smul_apply, smul_eq_mul]
  have hEvalfinite (B : Set Y) (hBm : MeasurableSet B) (hBf : Q B < ⊤) :
      ∀ᵐ ω ∂P, η ω B < ⊤ :=
    ae_lt_top ((Measure.measurable_coe hBm).comp hm)
      (by rw [hEval B hBm]; exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBf).ne)
  have hαm : AEMeasurable α P := aemeasurable_factorialPointSum_two_of_cover I x hm
    (measurableSet_spanningSets Q) (fun _ _ h ↦ spanningSets_mono h) (iUnion_spanningSets Q)
    (ae_all_iff.2 fun n ↦ hEvalfinite _ (measurableSet_spanningSets Q n)
      (measure_spanningSets_lt_top Q n))
  let e : (Fin 2 → Y) ≃ᵐ Y × Y := MeasurableEquiv.finTwoArrow
  let w : Y × Y → ℝ := fun z ↦ lam ^ 2 * g z.1 z.2
  have hSecond := lintegral_factorialCount_of_pairDensity hαm
    (fun z ↦ mul_nonneg (sq_nonneg lam) (hg0 z.1 z.2)) hα₂ hWm (hgi.const_mul _)
  have hSqEN :
      (∫⁻ ω, (η ω W) ^ 2 ∂P) =
        ENNReal.ofReal (∫ z in W ×ˢ W, w z) + ENNReal.ofReal lam * Q W := by
    have heq (ω : Ω) : (η ω W) ^ 2 = (α ω |>.map e) (W ×ˢ W) + η ω W := by
      rw [pow_two]
      simpa only [Set.inter_self] using
        (factorialPointSum_two_apply_prod_add (I ω) (x ω) hWm hWm).symm
    have hrect := e.measurable (hWm.prod hWm)
    have hboxed : AEMeasurable (fun ω ↦ (α ω |>.map e) (W ×ˢ W)) P :=
      ((Measure.measurable_coe hrect).comp_aemeasurable hαm).congr
        (ae_of_all _ (fun ω ↦ (Measure.map_apply e.measurable (hWm.prod hWm)).symm))
    simp_rw [heq]
    rw [lintegral_add_left' hboxed, hSecond, hEval W hWm]
  refine ⟨hEval W hWm, ?_⟩
  simpa only [w, integral_const_mul] using hSqEN

/-- Integrating the centred pair correlation subtracts the square of the window volume. -/
private lemma integral_sub_one_window
    {W : Set (EuclideanSpace ℝ (Fin d))} (hW : volume W < ∞)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ}
    (hgi : IntegrableOn (fun z ↦ g z.1 z.2) (W ×ˢ W)) :
    (∫ z in W ×ˢ W, (g z.1 z.2 - 1)) =
      (∫ z in W ×ˢ W, g z.1 z.2) - (volume W).toReal ^ 2 := by
  let Y := EuclideanSpace ℝ (Fin d)
  let Q : Measure Y := volume
  have hVol : (volume : Measure (Y × Y)) (W ×ˢ W) = Q W * Q W := Measure.prod_prod _ _
  have : IsFiniteMeasure ((volume : Measure (Y × Y)).restrict (W ×ˢ W)) :=
    isFiniteMeasure_restrict.mpr (by rw [hVol]; exact ENNReal.mul_ne_top hW.ne hW.ne)
  rw [integral_sub hgi (integrable_const _), integral_const, smul_eq_mul, mul_one,
    Measure.real_def, Measure.restrict_apply_univ, hVol, ENNReal.toReal_mul, pow_two]

/-- SYNOPSIS item 103: the count per unit volume of a stationary point process is unbiased,
and its variance is given by the second factorial moment density. -/
theorem intensity_estimator {P : Measure Ω} [IsProbabilityMeasure P] (I : Ω → ℕ → Bool)
    (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (hm : Measurable fun ω ↦ pointSum (I ω) (x ω))
    (hst : IsStationary P fun ω ↦ pointSum (I ω) (x ω)) {lam : ℝ}
    (hlam : intensity P (fun ω ↦ pointSum (I ω) (x ω)) = ENNReal.ofReal lam) (hlam0 : 0 ≤ lam)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} (hg0 : ∀ y z, 0 ≤ g y z)
    (hα₂ : P.bind (fun ω ↦ factorialPointSum 2 (I ω) (x ω)) =
      volume.withDensity fun z ↦ ENNReal.ofReal (lam ^ 2 * g (z 0) (z 1)))
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWm : MeasurableSet W) (hW0 : 0 < volume W)
    (hW : volume W < ∞) (hgi : IntegrableOn (fun z ↦ g z.1 z.2) (W ×ˢ W)) :
    ∫ ω, (pointSum (I ω) (x ω) W).toReal / (volume W).toReal ∂P = lam ∧
      Var[fun ω ↦ (pointSum (I ω) (x ω) W).toReal / (volume W).toReal; P] =
        lam / (volume W).toReal +
          lam ^ 2 / (volume W).toReal ^ 2 * ∫ z in W ×ˢ W, (g z.1 z.2 - 1) := by
  let η (ω : Ω) := pointSum (I ω) (x ω)
  let Q : Measure (EuclideanSpace ℝ (Fin d)) := volume
  obtain ⟨hEval, hSqEN⟩ := intensity_count_lintegrals I x hm hst hlam hg0 hα₂ hWm hgi
  have hCountFinite : (∫⁻ ω, η ω W ∂P) < ⊤ := by
    rw [hEval]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW
  let N (ω : Ω) := (η ω W).toReal
  have hηWm : Measurable (fun ω ↦ η ω W) := (Measure.measurable_coe hWm).comp hm
  have hNm : Measurable N := hηWm.ennreal_toReal
  have hNfin := ae_lt_top hηWm hCountFinite.ne
  have hv : 0 < (Q W).toReal := ENNReal.toReal_pos hW0.ne' hW.ne
  have hCount : (∫ ω, N ω ∂P) = lam * (Q W).toReal := by
    dsimp only [N]
    rw [integral_toReal hηWm.aemeasurable hNfin,
      hEval, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam0]
  have hsfinite : (∫⁻ ω, η ω W ^ 2 ∂P) < ⊤ := by
    rw [hSqEN]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW⟩
  have hnsq : Integrable (fun ω ↦ N ω ^ 2) P := by
    have hmeasSq : AEMeasurable (fun ω ↦ η ω W ^ 2) P :=
      (hηWm.pow_const 2).aemeasurable
    simpa only [N, ENNReal.toReal_pow] using
      integrable_toReal_of_lintegral_ne_top hmeasSq hsfinite.ne
  have hLp : MemLp N 2 P := (memLp_two_iff_integrable_sq hNm.aestronglyMeasurable).mpr hnsq
  have hCountSq :
      (∫ ω, N ω ^ 2 ∂P) = lam ^ 2 * (∫ z in W ×ˢ W, g z.1 z.2) + lam * (Q W).toReal := by
    simp only [N, ← ENNReal.toReal_pow]
    rw [integral_toReal (hηWm.pow_const 2).aemeasurable
      (hNfin.mono fun _ hw ↦ ENNReal.pow_lt_top hw),
      hSqEN, ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam0,
      ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
        (integral_nonneg (f := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
          g z.1 z.2) (fun z ↦ hg0 z.1 z.2)))]
  refine ⟨?_, ?_⟩
  · rw [integral_div, hCount, mul_div_cancel_right₀ _ hv.ne']
  · simp only [div_eq_mul_inv]
    rw [variance_mul_const, variance_eq_sub hLp]
    simp only [Pi.pow_apply]
    rw [hCount, hCountSq, integral_sub_one_window hW hgi]
    field_simp [hv.ne']
    ring

/-- The functional
`𝒦_A(B) = |A|⁻¹ ∫ 𝟙[x ∈ A, y - x ∈ B] / (ρ(x) ρ(y)) α₂(d(x, y))`, with `a / 0 = 0`. -/
def kFunctional (α₂ : Measure (Fin 2 → EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (A B : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  (volume A)⁻¹ * ∫⁻ z, {z : Fin 2 → EuclideanSpace ℝ (Fin d) | z 0 ∈ A ∧ z 1 - z 0 ∈ B}.indicator
    (fun z ↦ ENNReal.ofReal (ρ (z 0) * ρ (z 1))⁻¹) z ∂α₂

/-- **Second-order intensity-reweighted stationarity**: `𝒦_A(B)` does not depend on `A`. -/
def IsReweightedStationary (α₂ : Measure (Fin 2 → EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ K : Set (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞, ∀ A, MeasurableSet A → 0 < volume A →
    volume A < ∞ → ∀ B, MeasurableSet B → kFunctional α₂ ρ A B = K B

/-- The translation-corrected estimator
`𝒦̂(B) = ∑^{≠}_{ξ, η ∈ X ∩ W} 𝟙[η - ξ ∈ B] / (ρ(ξ) ρ(η) |W ∩ (W + η - ξ)|)`. -/
def translationK (W : Set (EuclideanSpace ℝ (Fin d))) (ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (I : ℕ → Bool) (x : ℕ → EuclideanSpace ℝ (Fin d)) :
    ℝ≥0∞ :=
  ∫⁻ z, {z : Fin 2 → EuclideanSpace ℝ (Fin d) | z 0 ∈ W ∧ z 1 ∈ W ∧ z 1 - z 0 ∈ B}.indicator
    (fun z ↦ ENNReal.ofReal (ρ (z 0) * ρ (z 1) *
      (volume (W ∩ (· + (z 1 - z 0)) '' W)).toReal)⁻¹) z ∂factorialPointSum 2 I x

lemma kFunctional_def (α₂ : Measure (Fin 2 → EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (A B : Set (EuclideanSpace ℝ (Fin d))) :
    kFunctional α₂ ρ A B = (volume A)⁻¹ * ∫⁻ z,
      {z : Fin 2 → EuclideanSpace ℝ (Fin d) | z 0 ∈ A ∧ z 1 - z 0 ∈ B}.indicator
        (fun z ↦ ENNReal.ofReal (ρ (z 0) * ρ (z 1))⁻¹) z ∂α₂ := by
  rw [kFunctional]

lemma isReweightedStationary_def {α₂ : Measure (Fin 2 → EuclideanSpace ℝ (Fin d))}
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} : IsReweightedStationary α₂ ρ ↔
      ∃ K : Set (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞, ∀ A, MeasurableSet A → 0 < volume A →
        volume A < ∞ → ∀ B, MeasurableSet B → kFunctional α₂ ρ A B = K B := Iff.rfl

lemma translationK_def (W : Set (EuclideanSpace ℝ (Fin d))) (ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (I : ℕ → Bool) (x : ℕ → EuclideanSpace ℝ (Fin d)) :
    translationK W ρ B I x = ∫⁻ z,
      {z : Fin 2 → EuclideanSpace ℝ (Fin d) | z 0 ∈ W ∧ z 1 ∈ W ∧ z 1 - z 0 ∈ B}.indicator
        (fun z ↦ ENNReal.ofReal (ρ (z 0) * ρ (z 1) *
          (volume (W ∩ (· + (z 1 - z 0)) '' W)).toReal)⁻¹) z ∂factorialPointSum 2 I x := by
  rw [translationK]

/-- SYNOPSIS item 103: for a second-order intensity-reweighted stationary process with known
intensity `ρ > 0`, the translation-corrected estimator is unbiased when
`|W ∩ (W + ξ)| > 0` for `ξ ∈ B`. -/
theorem integral_translationK {P : Measure Ω} [IsProbabilityMeasure P] (I : Ω → ℕ → Bool)
    (x : Ω → ℕ → EuclideanSpace ℝ (Fin d)) {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ : ∀ y, 0 < ρ y)
    (hint : P.bind (fun ω ↦ pointSum (I ω) (x ω)) = volume.withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (hrs : IsReweightedStationary (P.bind fun ω ↦ factorialPointSum 2 (I ω) (x ω)) ρ)
    {W B : Set (EuclideanSpace ℝ (Fin d))} (hWm : MeasurableSet W) (hW0 : 0 < volume W)
    (hW : volume W < ∞) (hBm : MeasurableSet B)
    (hWB : ∀ ξ ∈ B, 0 < volume (W ∩ (· + ξ) '' W)) :
    ∫⁻ ω, translationK W ρ B (I ω) (x ω) ∂P =
      kFunctional (P.bind fun ω ↦ factorialPointSum 2 (I ω) (x ω)) ρ W B := by
  sorry

/-- The fraction of the circle of radius `r` about `ξ` that lies in `W ⊆ ℝ²`. -/
def circleFraction (W : Set (EuclideanSpace ℝ (Fin 2))) (ξ : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ℝ :=
  (volume {θ ∈ Ico 0 (2 * Real.pi) |
    ξ + WithLp.toLp 2 ![r * Real.cos θ, r * Real.sin θ] ∈ W}).toReal / (2 * Real.pi)

/-- Ripley's ratio estimator of `K(t)` from `N` points `u_1, …, u_N` in `W ⊆ ℝ²`, with
isotropic edge correction: `|W| / N² ∑_{i ≠ j} 𝟙[‖u_i - u_j‖ ≤ t] / f(u_i, ‖u_i - u_j‖)`, with
`f` the circle fraction. -/
def ripleyK {N : ℕ} (W : Set (EuclideanSpace ℝ (Fin 2))) (t : ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (volume W).toReal / N ^ 2 * ∑ i, ∑ j,
    if i ≠ j ∧ dist (u i) (u j) ≤ t then (circleFraction W (u i) (dist (u i) (u j)))⁻¹ else 0

lemma circleFraction_def (W : Set (EuclideanSpace ℝ (Fin 2))) (ξ : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) : circleFraction W ξ r = (volume {θ ∈ Ico 0 (2 * Real.pi) |
      ξ + WithLp.toLp 2 ![r * Real.cos θ, r * Real.sin θ] ∈ W}).toReal / (2 * Real.pi) := by
  rw [circleFraction]

lemma ripleyK_def {N : ℕ} (W : Set (EuclideanSpace ℝ (Fin 2))) (t : ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin 2)) : ripleyK W t u =
      (volume W).toReal / N ^ 2 * ∑ i, ∑ j, if i ≠ j ∧ dist (u i) (u j) ≤ t then
        (circleFraction W (u i) (dist (u i) (u j)))⁻¹ else 0 := by
  rw [ripleyK]

/-- SYNOPSIS item 103: for `N ≥ 1` independent uniform points in `W ⊆ ℝ²` (a Poisson process
conditioned on `X(W) = N`), the mean of Ripley's isotropically corrected ratio estimator is
`π t² (N - 1) / N`, for `t` such that the correction is defined, that is, every circle of radius
`r ∈ (0, t]` about a point of `W` meets `W` in positive length. -/
theorem integral_ripleyK {W : Set (EuclideanSpace ℝ (Fin 2))} (hWm : MeasurableSet W)
    (hW0 : 0 < volume W) (hW : volume W < ∞) {t : ℝ} (ht : 0 < t)
    (hcorr : ∀ ξ ∈ W, ∀ r ∈ Ioc 0 t, 0 < circleFraction W ξ r) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u, ripleyK W t u ∂(Measure.pi fun _ : Fin N ↦ (volume W)⁻¹ • volume.restrict W) =
      Real.pi * t ^ 2 * (N - 1) / N := by
  sorry

/-- A stationary point process is **ergodic** when its law gives every shift-invariant
measurable set of configurations probability `0` or `1`. -/
def IsErgodicPointProcess (P : Measure Ω) (η : Ω → Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ A, MeasurableSet[invariantSigma] A → P.map η A = 0 ∨ P.map η A = 1

lemma isErgodicPointProcess_def {P : Measure Ω} {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} :
    IsErgodicPointProcess P η ↔
      ∀ A, MeasurableSet[invariantSigma] A → P.map η A = 0 ∨ P.map η A = 1 := Iff.rfl

/-- SYNOPSIS item 103: for a stationary ergodic point process with intensity `λ ∈ (0, ∞)` and
locally finite second factorial moment measure, and increasing compact convex windows `W_n`
whose inradius tends to infinity, the translation-corrected ratio estimator
`K̂_n(r) = |W_n|² / X(W_n)² ∑^{≠}_{ξ, η ∈ X ∩ W_n} 𝟙[‖η - ξ‖ ≤ r] / |W_n ∩ (W_n + η - ξ)|`
converges almost surely to `K(r) = λ⁻² α₂^!(B(0, r))`, uniformly on `[0, r₀]`. -/
theorem tendstoUniformlyOn_translationK {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Ω → ℕ → Bool) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (hm : Measurable fun ω ↦ pointSum (I ω) (x ω))
    (hst : IsStationary P fun ω ↦ pointSum (I ω) (x ω))
    (herg : IsErgodicPointProcess P fun ω ↦ pointSum (I ω) (x ω))
    (hlam0 : 0 < intensity P fun ω ↦ pointSum (I ω) (x ω))
    (hlam : intensity P (fun ω ↦ pointSum (I ω) (x ω)) < ∞)
    (hα₂ : IsLocallyFiniteMeasure (P.bind fun ω ↦ factorialPointSum 2 (I ω) (x ω)))
    {W : ℕ → Set (EuclideanSpace ℝ (Fin d))} (hWc : ∀ n, IsCompact (W n))
    (hWconv : ∀ n, Convex ℝ (W n)) (hWmono : Monotone W)
    (hWin : ∀ r : ℝ, ∀ᶠ n in atTop, ∃ c, closedBall c r ⊆ W n) (r₀ : ℝ) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun n r ↦ ((volume (W n)).toReal / (pointSum (I ω) (x ω) (W n)).toReal) ^ 2 *
        (translationK (W n) (fun _ ↦ 1) (closedBall 0 r) (I ω) (x ω)).toReal)
      (fun r ↦ (reducedSecondMoment (P.bind fun ω ↦ factorialPointSum 2 (I ω) (x ω))
          (closedBall 0 r)).toReal /
        (intensity P fun ω ↦ pointSum (I ω) (x ω)).toReal ^ 2)
      atTop (Icc 0 r₀) := by
  sorry

/-! ### The `F`, `G`, and `J` functions (SYNOPSIS item 104) -/

/-- `P₀` is a **Palm distribution** of the stationary point process `η`:
`E ∫ f(x, θ_x η) η(dx) = γ ∫∫ f(x, μ) P₀(dμ) dx` for measurable `f ≥ 0`. -/
def IsPalmDistribution (P : Measure Ω) (η : Ω → Measure (EuclideanSpace ℝ (Fin d)))
    (P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))) : Prop :=
  IsProbabilityMeasure P₀ ∧
    ∀ f : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞,
      Measurable (Function.uncurry f) →
      ∫⁻ ω, ∫⁻ x, f x (translate x (η ω)) ∂(η ω) ∂P = intensity P η * ∫⁻ x, ∫⁻ μ, f x μ ∂P₀

/-- The **empty-space function** `F(r) = P(X ∩ B(0, r) ≠ ∅)`. -/
def emptySpace (P : Measure Ω) (η : Ω → Measure (EuclideanSpace ℝ (Fin d))) (r : ℝ) : ℝ :=
  (P {ω | η ω (closedBall 0 r) ≠ 0}).toReal

/-- The **nearest-neighbour function** `G(r)`: the Palm probability that the typical point has
another point within distance `r`. -/
def nearestNeighbour (P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))) (r : ℝ) : ℝ :=
  (P₀ {μ | μ (closedBall 0 r \ {0}) ≠ 0}).toReal

/-- The **`J`-function** `J(r) = (1 - G(r)) / (1 - F(r))`. -/
def jFunction (P : Measure Ω) (η : Ω → Measure (EuclideanSpace ℝ (Fin d)))
    (P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))) (r : ℝ) : ℝ :=
  (1 - nearestNeighbour P₀ r) / (1 - emptySpace P η r)

lemma isPalmDistribution_def {P : Measure Ω} {η : Ω → Measure (EuclideanSpace ℝ (Fin d))}
    {P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))} : IsPalmDistribution P η P₀ ↔
      IsProbabilityMeasure P₀ ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞,
        Measurable (Function.uncurry f) →
        ∫⁻ ω, ∫⁻ x, f x (translate x (η ω)) ∂(η ω) ∂P =
          intensity P η * ∫⁻ x, ∫⁻ μ, f x μ ∂P₀ := Iff.rfl

lemma emptySpace_def (P : Measure Ω) (η : Ω → Measure (EuclideanSpace ℝ (Fin d))) (r : ℝ) :
    emptySpace P η r = (P {ω | η ω (closedBall 0 r) ≠ 0}).toReal := by
  rw [emptySpace]

lemma nearestNeighbour_def (P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))) (r : ℝ) :
    nearestNeighbour P₀ r = (P₀ {μ | μ (closedBall 0 r \ {0}) ≠ 0}).toReal := by
  rw [nearestNeighbour]

lemma jFunction_def (P : Measure Ω) (η : Ω → Measure (EuclideanSpace ℝ (Fin d)))
    (P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))) (r : ℝ) :
    jFunction P η P₀ r = (1 - nearestNeighbour P₀ r) / (1 - emptySpace P η r) := by
  rw [jFunction]

private lemma void_compl_toReal {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    [IsProbabilityMeasure μ] {B : Set Y} (hB : MeasurableSet B) :
    1 - (μ Bᶜ).toReal = (μ B).toReal := by
  rw [prob_compl_eq_one_sub hB, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one]
  ring

private lemma lintegral_indicator_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Y} {A : Set X} {C : Set Y} (hC : MeasurableSet C) (x : X) :
    (∫⁻ y, (A ×ˢ C).indicator 1 (x, y) ∂μ) = A.indicator (fun _ ↦ μ C) x := by
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx, ← lintegral_indicator_one hC]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : y ∈ C <;> simp [indicator, hx, hy]
  · rw [indicator_of_notMem hx, ← lintegral_zero]
    exact lintegral_congr fun y ↦ by simp [indicator, hx]

private lemma lintegral_palmVoid_restrict {P : Measure Ω}
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} {A W T : Set (EuclideanSpace ℝ (Fin d))}
    (hTm : MeasurableSet T) (hWm : MeasurableSet W) (hAW : A ⊆ W)
    (hTx_sub : ∀ x ∈ A, (fun y ↦ y - x) ⁻¹' T ⊆ W)
    (hfinηW : ∀ᵐ ω ∂P, (η ω).restrict W univ < ⊤) :
    let C := {μ : Measure (EuclideanSpace ℝ (Fin d)) | μ T = 0}
    let g : EuclideanSpace ℝ (Fin d) × Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ :=
      (A ×ˢ C).indicator 1
    let f (x : EuclideanSpace ℝ (Fin d)) μ := g (x, translateFinitePart x μ)
    let ηW (ω : Ω) := (η ω).restrict W
    (∫⁻ ω, ∫⁻ x, g (x, translate x (η ω)) ∂η ω ∂P) =
      ∫⁻ ω, ∫⁻ x, f x (ηW ω) ∂ηW ω ∂P := by
  intro C g f ηW
  let Tx (x : EuclideanSpace ℝ (Fin d)) := (fun y ↦ y - x) ⁻¹' T
  have hTxm (x : EuclideanSpace ℝ (Fin d)) : MeasurableSet (Tx x) :=
    hTm.preimage (by fun_prop)
  refine lintegral_congr_ae (hfinηW.mono fun ω hω ↦ ?_)
  change (∫⁻ x, g (x, translate x (η ω)) ∂η ω) =
    ∫⁻ x, f x (ηW ω) ∂(η ω).restrict W
  rw [← lintegral_indicator hWm]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ A
  · rw [indicator_of_mem (hAW hx)]
    have hval : translate x (η ω) T = translateFinitePart x (ηW ω) T := by
      rw [translateFinitePart_eq x hω, translate_apply_measurable _ _ hTm,
        translate_apply_measurable _ _ hTm]
      change η ω (Tx x) = ((η ω).restrict W) (Tx x)
      rw [Measure.restrict_apply (hTxm x), inter_eq_left.mpr (hTx_sub x hx)]
    simp [g, f, indicator, hx, C, hval]
  · by_cases hxw : x ∈ W <;> simp [g, f, indicator, hx, hxw]

private lemma lintegral_palmVoid_insert {P : Measure Ω} {Λ : Measure (EuclideanSpace ℝ (Fin d))}
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} (hη : IsPoissonRandomMeasure P η Λ)
    {A W T : Set (EuclideanSpace ℝ (Fin d))} (hTm : MeasurableSet T) (hT₀ : 0 ∉ T)
    (hΛW : Λ W < ⊤) (hTx_sub : ∀ x ∈ A, (fun y ↦ y - x) ⁻¹' T ⊆ W)
    (hTx_eq : ∀ x : EuclideanSpace ℝ (Fin d), Λ ((fun y ↦ y - x) ⁻¹' T) = Λ T)
    (hfinηW : ∀ᵐ ω ∂P, (η ω).restrict W univ < ⊤) (x : EuclideanSpace ℝ (Fin d)) :
    let C := {μ : Measure (EuclideanSpace ℝ (Fin d)) | μ T = 0}
    let g : EuclideanSpace ℝ (Fin d) × Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ :=
      (A ×ˢ C).indicator 1
    let f (x : EuclideanSpace ℝ (Fin d)) μ := g (x, translateFinitePart x μ)
    let ηW (ω : Ω) := (η ω).restrict W
    let p := ENNReal.ofReal (Real.exp (-(Λ T).toReal))
    (∫⁻ ω, f x (ηW ω + Measure.dirac x) ∂P) = A.indicator (fun _ ↦ p) x := by
  intro C g f ηW p
  let Tx (x : EuclideanSpace ℝ (Fin d)) := (fun y ↦ y - x) ⁻¹' T
  have hTxm (x : EuclideanSpace ℝ (Fin d)) : MeasurableSet (Tx x) :=
    hTm.preimage (by fun_prop)
  have horig (x : EuclideanSpace ℝ (Fin d)) : x ∉ Tx x := by
    simpa only [Tx, mem_preimage, sub_self] using hT₀
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
    calc
      _ = ∫⁻ ω, {ω | η ω (Tx x) = 0}.indicator 1 ω ∂P := by
        refine lintegral_congr_ae (hfinηW.mono fun ω hω ↦ ?_)
        have hadd : (ηW ω + Measure.dirac x) univ < ⊤ := by
          rw [add_apply, Measure.dirac_apply_of_mem (mem_univ x)]
          exact ENNReal.add_lt_top.mpr ⟨hω, ENNReal.one_lt_top⟩
        have hval : translateFinitePart x (ηW ω + Measure.dirac x) T = η ω (Tx x) := by
          rw [translateFinitePart_eq x hadd, translate_apply_measurable _ _ hTm]
          change (ηW ω + Measure.dirac x) (Tx x) = _
          rw [add_apply, Measure.dirac_apply' _ (hTxm x),
            indicator_of_notMem (horig x), add_zero]
          change ((η ω).restrict W) (Tx x) = _
          rw [Measure.restrict_apply (hTxm x), inter_eq_left.mpr (hTx_sub x hx)]
        simp [f, g, indicator, C, hx, hval]
      _ = P {ω | η ω (Tx x) = 0} := by
        exact lintegral_indicator_one ((Measure.measurable_coe (hTxm x)).comp hη.measurable
          (measurableSet_singleton 0))
      _ = p := by
        rw [measure_count_eq_zero_of_poisson hη (hTxm x)
          ((measure_mono (hTx_sub x hx)).trans_lt hΛW), hTx_eq x]
  · rw [indicator_of_notMem hx, ← lintegral_zero]
    exact lintegral_congr fun ω ↦ by simp [f, g, indicator, hx]

private lemma intensity_poisson_smul_volume {P : Measure Ω}
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} {a : ℝ≥0∞} (ha : a < ⊤)
    (hη : IsPoissonRandomMeasure P η (a • volume)) : intensity P η = a := by
  have hcube : (a • volume) (unitCube d) < ⊤ := by
    change a * volume (unitCube d) < ⊤
    rwa [volume_unitCube, mul_one]
  rw [intensity_def, lintegral_poisson_count hη (measurableSet_unitCube d) hcube]
  change a * volume (unitCube d) = a
  rw [volume_unitCube, mul_one]

/-- After removing the point at the origin, the Palm void probability agrees with the Poisson
void probability on the same bounded test set. -/
private lemma palm_void_eq_poisson_void {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} {lam : ℝ} (hlam : 0 < lam)
    (hη : IsPoissonRandomMeasure P η (ENNReal.ofReal lam • volume))
    {P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))} (hP₀ : IsPalmDistribution P η P₀)
    {T : Set (EuclideanSpace ℝ (Fin d))} (hTm : MeasurableSet T) (hT₀ : 0 ∉ T)
    {r : ℝ} (hr : 0 ≤ r) (hT : T ⊆ closedBall 0 r) :
    P₀ {μ | μ T = 0} = ENNReal.ofReal (Real.exp (-((ENNReal.ofReal lam • volume) T).toReal)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let Λ : Measure E := ENNReal.ofReal lam • volume
  let A : Set E := closedBall 0 1
  let W : Set E := closedBall 0 (1 + r)
  let C := {μ : Measure E | μ T = 0}
  let p := ENNReal.ofReal (Real.exp (-(Λ T).toReal))
  let g : E × Measure E → ℝ≥0∞ := (A ×ˢ C).indicator 1
  let f (x : E) (μ : Measure E) : ℝ≥0∞ := g (x, translateFinitePart x μ)
  let ηW (ω : Ω) := (η ω).restrict W
  have hAm : MeasurableSet A := measurableSet_closedBall
  have hWm : MeasurableSet W := measurableSet_closedBall
  have hAW : A ⊆ W := closedBall_subset_closedBall (by linarith)
  have hCm : MeasurableSet C := (Measure.measurable_coe hTm) (measurableSet_singleton 0)
  have hg : Measurable g := measurable_const.indicator (hAm.prod hCm)
  have hf : Measurable (Function.uncurry f) :=
    hg.comp (measurable_fst.prodMk measurable_translateFinitePart)
  have hvolW : (volume : Measure E) W < ⊤ := measure_closedBall_lt_top
  have hΛW : Λ W < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvolW
  have : IsFiniteMeasure (Λ.restrict W) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hηW : IsPoissonRandomMeasure P ηW (Λ.restrict W) := hη.restrict hWm
  have hfinηW : ∀ᵐ ω ∂P, ηW ω univ < ⊤ :=
    hηW.ae_lt_top MeasurableSet.univ (measure_lt_top _ _)
  have hA0 : Λ A ≠ 0 := by
    have hpA : 0 < (volume : Measure E) A :=
      (isOpen_ball.measure_pos volume (nonempty_ball.mpr zero_lt_one)).trans_le
        (measure_mono ball_subset_closedBall)
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hlam).ne' hpA.ne'
  have hAfin : Λ A ≠ ⊤ := ((measure_mono hAW).trans_lt hΛW).ne
  have hintensity := intensity_poisson_smul_volume ENNReal.ofReal_lt_top hη
  let Tx (x : E) := (fun z : E ↦ z - x) ⁻¹' T
  have hTx_sub (x : E) (hx : x ∈ A) : Tx x ⊆ W := by
    intro y hy
    have h1 : dist x 0 ≤ 1 := mem_closedBall.mp hx
    have h2 : dist y x ≤ r := by
      have h2 := mem_closedBall.mp (hT hy)
      simpa only [dist_eq_norm, sub_zero] using h2
    exact mem_closedBall.mpr ((dist_triangle y x 0).trans (by linarith))
  have hTx_eq (x : E) : Λ (Tx x) = Λ T := by
    have hm : MeasurePreserving (fun y : E ↦ y - x) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure E) (-x)
    change ENNReal.ofReal lam * volume (Tx x) = ENNReal.ofReal lam * volume T
    rw [hm.measure_preimage hTm.nullMeasurableSet]
  have hleft := lintegral_palmVoid_restrict hTm hWm hAW hTx_sub hfinηW
  have hright (x : E) := lintegral_palmVoid_insert hη hTm hT₀ hΛW hTx_sub hTx_eq hfinηW x
  have hproduct : Λ A * P₀ C = intensity P η * (∫⁻ x, ∫⁻ μ, g (x, μ) ∂P₀) := by
    rw [hintensity, show Λ A = ENNReal.ofReal lam * volume A from rfl]
    have hG (x : E) : (∫⁻ μ, g (x, μ) ∂P₀) = A.indicator (fun _ ↦ P₀ C) x :=
      lintegral_indicator_prod hCm x
    simp_rw [hG]
    rw [lintegral_indicator_const hAm, mul_assoc, mul_comm (volume A)]
  have hpalm := hP₀.2 (fun x μ ↦ g (x, μ)) hg
  have hmecke := lintegral_finitePoissonRandomMeasure_mecke hηW hf
  have hlast : (∫⁻ x, ∫⁻ ω, f x (ηW ω + Measure.dirac x) ∂P ∂Λ.restrict W) =
      Λ A * p := by
    have he (x : E) : (∫⁻ ω, f x (ηW ω + Measure.dirac x) ∂P) =
        A.indicator (fun _ ↦ p) x := hright x
    simp_rw [he]
    rw [lintegral_indicator_const hAm, Measure.restrict_apply hAm,
      inter_eq_left.mpr hAW, mul_comm]
  exact (ENNReal.mul_right_inj hA0 hAfin).mp
    (hproduct.trans (hpalm.symm.trans (hleft.trans (hmecke.trans hlast))))

/-- SYNOPSIS item 104: for a stationary Poisson process of intensity `λ > 0`,
`1 - F(r) = e^{-λ |B(0, r)|}`, `G = F` for its Palm distribution, and so `J ≡ 1`. -/
theorem emptySpace_poisson (hd : 0 < d) {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} {lam : ℝ} (hlam : 0 < lam)
    (hη : IsPoissonRandomMeasure P η (ENNReal.ofReal lam • volume))
    {P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))} (hP₀ : IsPalmDistribution P η P₀) (r : ℝ)
    (hr : 0 ≤ r) :
    1 - emptySpace P η r = Real.exp (-lam * (volume (closedBall (0 : EuclideanSpace ℝ (Fin d))
      r)).toReal) ∧ nearestNeighbour P₀ r = emptySpace P η r ∧ jFunction P η P₀ r = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let B : Set E := closedBall 0 r
  let T : Set E := B \ {0}
  let Λ : Measure E := ENNReal.ofReal lam • volume
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hTm : MeasurableSet T := hBm.diff (measurableSet_singleton 0)
  have h₀ : 0 ∉ T := fun h ↦ h.2 rfl
  have hBfin : Λ B < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hTB : Λ T = Λ B := by
    have hnull : (volume : Measure E) {0} = 0 := measure_singleton _
    change ENNReal.ofReal lam * volume (B \ {0}) = ENNReal.ofReal lam * volume B
    rw [measure_sdiff_null hnull]
  have hFmeas : MeasurableSet {ω | η ω B = 0} :=
    ((Measure.measurable_coe hBm).comp hη.measurable) (measurableSet_singleton 0)
  have hGmeas : MeasurableSet {μ : Measure E | μ T = 0} :=
    Measure.measurable_coe hTm (measurableSet_singleton 0)
  let e := Real.exp (-lam * (volume B).toReal)
  have he : 0 < e := Real.exp_pos _
  have hexp : ENNReal.ofReal (Real.exp (-(Λ B).toReal)) = ENNReal.ofReal e := by
    change ENNReal.ofReal (Real.exp (-(ENNReal.ofReal lam * volume B).toReal)) = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam.le, ← neg_mul]
  have hF : 1 - emptySpace P η r = e := by
    change 1 - (P {ω | η ω B = 0}ᶜ).toReal = e
    rw [void_compl_toReal hFmeas, measure_count_eq_zero_of_poisson hη hBm hBfin, hexp,
      ENNReal.toReal_ofReal he.le]
  have : IsProbabilityMeasure P₀ := hP₀.1
  have hG : 1 - nearestNeighbour P₀ r = e := by
    change 1 - (P₀ {μ | μ T = 0}ᶜ).toReal = e
    rw [void_compl_toReal hGmeas, palm_void_eq_poisson_void hlam hη hP₀ hTm h₀ hr sdiff_subset,
      hTB, hexp, ENNReal.toReal_ofReal he.le]
  exact ⟨hF, by linarith, by rw [jFunction_def, hF, hG, div_self he.ne']⟩

/-- SYNOPSIS item 104: for a stationary infinite-volume Gibbs process with translation-invariant
finite-range energy and intensity `ρ ∈ (0, ∞)`, and `F(r) < 1`,
`J(r) = E[λ*(X, 0) | X ∩ B(0, r) = ∅] / ρ` with `λ*(x, 0) = z e^{-β h(0, x)}`. -/
theorem jFunction_gibbs {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))}
    (hP : IsInfiniteGibbs P z β R H) (hρ0 : 0 < intensity P id) (hρ : intensity P id < ∞)
    {P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))} (hP₀ : IsPalmDistribution P id P₀)
    {r : ℝ} (hr : 0 ≤ r) (hF : emptySpace P id r < 1) :
    jFunction P id P₀ r =
      (∫ x in {x | x (closedBall 0 r) = 0}, z * boltzmann β (infLocalEnergy H R 0 x) ∂P) /
        (P {x | x (closedBall 0 r) = 0}).toReal / (intensity P id).toReal := by
  sorry

/-- SYNOPSIS item 104: for an interaction of finite range `R` and `r ≥ R` with `F(r) < 1`,
`J(r) = λ*(∅, 0) / ρ = z e^{-β h(0, ∅)} / ρ`. -/
theorem jFunction_gibbs_of_range_le {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))}
    (hP : IsInfiniteGibbs P z β R H) (hρ0 : 0 < intensity P id) (hρ : intensity P id < ∞)
    {P₀ : Measure (Measure (EuclideanSpace ℝ (Fin d)))} (hP₀ : IsPalmDistribution P id P₀)
    {r : ℝ} (hRr : R ≤ r) (hF : emptySpace P id r < 1) :
    jFunction P id P₀ r = z * boltzmann β (localEnergy H 0 ∅) / (intensity P id).toReal := by
  sorry

end MSSS
