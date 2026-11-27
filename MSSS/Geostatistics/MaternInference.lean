module

public import MSSS.Geostatistics.Equivalence
public import MSSS.Geostatistics.Likelihood
public import MSSS.RandomFields.Matern
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

/-!
# Fixed-domain inference for the Matérn family

SYNOPSIS items 40 and 41: Zhang's theorem on equivalence of Matérn Gaussian measures, and strong
consistency of the maximum-likelihood estimator of the microergodic parameter.

The isotropic Matérn covariance with variance `σ²`, inverse range `α`, and smoothness `ν` is
`σ² φ_{ν,1/α}(‖h‖) = σ² 2^{1-ν}/Γ(ν) (α‖h‖)^ν 𝒦_ν(α‖h‖)`, with `φ` the Matérn correlation
`MSSS.maternCorrelation`. Its microergodic parameter is `σ² α^{2ν}`.

## Main definitions

* `MSSS.maternLaw ν σsq α D`: the centred Gaussian law with Matérn covariance on `D → ℝ`.

## Main results

All admitted.

* `MSSS.maternLaw_equiv_iff`, `MSSS.not_consistent_maternVariance`,
  `MSSS.not_consistent_maternInverseRange`, `MSSS.tendsto_tvDist_condDistrib_maternLaw`:
  SYNOPSIS item 40.
* `MSSS.tendsto_maternMLE_microergodic`: SYNOPSIS item 41.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MSSS

variable {d : ℕ}

/-- The centred Gaussian law on `D → ℝ`, `D ⊆ ℝ^d`, with isotropic Matérn covariance
`σ² φ_{ν,1/α}(‖s - t‖)`. -/
def maternLaw (ν σsq α : ℝ) (D : Set (EuclideanSpace ℝ (Fin d))) : Measure (D → ℝ) :=
  gaussianFieldLaw 0 fun s t : D ↦
    σsq * maternCorrelation ν (1 / α) ‖(s : EuclideanSpace ℝ (Fin d)) - t‖

lemma maternLaw_def (ν σsq α : ℝ) (D : Set (EuclideanSpace ℝ (Fin d))) :
    maternLaw ν σsq α D = gaussianFieldLaw 0 fun s t : D ↦
      σsq * maternCorrelation ν (1 / α) ‖(s : EuclideanSpace ℝ (Fin d)) - t‖ := by
  rw [maternLaw]

instance (ν σsq α : ℝ) (D : Set (EuclideanSpace ℝ (Fin d))) :
    IsProbabilityMeasure (maternLaw ν σsq α D) := by
  rw [maternLaw]
  infer_instance

/-- SYNOPSIS item 40, Zhang's theorem: for `d ≤ 3`, a common smoothness `ν`, and a bounded
infinite `T ⊆ ℝ^d`, the Matérn laws with parameters `(σ₁², α₁)` and `(σ₂², α₂)` are equivalent
on `T` if `σ₁² α₁^{2ν} = σ₂² α₂^{2ν}` and orthogonal otherwise. -/
theorem maternLaw_equiv_iff (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3) {ν σsq₁ σsq₂ α₁ α₂ : ℝ} (hν : 0 < ν)
    (hσ₁ : 0 < σsq₁) (hσ₂ : 0 < σsq₂) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    {T : Set (EuclideanSpace ℝ (Fin d))} (hT : Bornology.IsBounded T) (hTi : T.Infinite) :
    (σsq₁ * α₁ ^ (2 * ν) = σsq₂ * α₂ ^ (2 * ν) →
        maternLaw ν σsq₁ α₁ T ≪ maternLaw ν σsq₂ α₂ T ∧
          maternLaw ν σsq₂ α₂ T ≪ maternLaw ν σsq₁ α₁ T) ∧
      (σsq₁ * α₁ ^ (2 * ν) ≠ σsq₂ * α₂ ^ (2 * ν) →
        maternLaw ν σsq₁ α₁ T ⟂ₘ maternLaw ν σsq₂ α₂ T) := by
  sorry

/-- SYNOPSIS item 40: under infill sampling in a bounded infinite set, `σ²` has no weakly
consistent estimator. -/
theorem not_consistent_maternVariance (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3) {ν : ℝ} (hν : 0 < ν)
    {T : Set (EuclideanSpace ℝ (Fin d))} (hT : Bornology.IsBounded T) (hTi : T.Infinite)
    (est : ℕ → (T → ℝ) → ℝ) (hm : ∀ n, Measurable (est n)) :
    ¬ ∀ σsq α : ℝ, 0 < σsq → 0 < α →
      TendstoInMeasure (maternLaw ν σsq α T) est atTop fun _ ↦ σsq := by
  sorry

/-- SYNOPSIS item 40: under infill sampling in a bounded infinite set, `α` has no weakly
consistent estimator. -/
theorem not_consistent_maternInverseRange (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3) {ν : ℝ} (hν : 0 < ν)
    {T : Set (EuclideanSpace ℝ (Fin d))} (hT : Bornology.IsBounded T) (hTi : T.Infinite)
    (est : ℕ → (T → ℝ) → ℝ) (hm : ∀ n, Measurable (est n)) :
    ¬ ∀ σsq α : ℝ, 0 < σsq → 0 < α →
      TendstoInMeasure (maternLaw ν σsq α T) est atTop fun _ ↦ α := by
  sorry

/-- SYNOPSIS item 40: under two equivalent Matérn laws, the conditional laws of the future
observations `Z(s_{n+1}), Z(s_{n+2}), …` given `Z(s_1), …, Z(s_n)` merge almost surely in total
variation. -/
theorem tendsto_tvDist_condDistrib_maternLaw (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    {ν σsq₁ σsq₂ α₁ α₂ : ℝ} (hν : 0 < ν) (hσ₁ : 0 < σsq₁) (hσ₂ : 0 < σsq₂) (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂) {T : Set (EuclideanSpace ℝ (Fin d))} (hT : Bornology.IsBounded T)
    (hTi : T.Infinite) (heq : σsq₁ * α₁ ^ (2 * ν) = σsq₂ * α₂ ^ (2 * ν)) (s : ℕ → T) :
    ∀ᵐ z ∂maternLaw ν σsq₁ α₁ T, Tendsto (fun n ↦ tvDist
      (condDistrib (fun z (k : ℕ) ↦ z (s (n + k))) (fun z (i : Fin n) ↦ z (s i))
        (maternLaw ν σsq₁ α₁ T) fun i ↦ z (s i))
      (condDistrib (fun z (k : ℕ) ↦ z (s (n + k))) (fun z (i : Fin n) ↦ z (s i))
        (maternLaw ν σsq₂ α₂ T) fun i ↦ z (s i))) atTop (𝓝 0) := by
  sorry

open Classical in
/-- SYNOPSIS item 41: let `ν` be known, `D_n` an increasing sequence of finite sets with bounded
infinite union, and `α₁ > 0` fixed. If `σ̂_n²` maximises over `σ² > 0` the Gaussian likelihood of
`Z|_{D_n}` with `α = α₁` (for nonzero data), then `σ̂_n² α₁^{2ν} → σ₀² α₀^{2ν}` almost surely
under the true parameters `(σ₀², α₀)`. -/
theorem tendsto_maternMLE_microergodic (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3) {ν σsq₀ α₀ α₁ : ℝ}
    (hν : 0 < ν) (hσ₀ : 0 < σsq₀) (hα₀ : 0 < α₀) (hα₁ : 0 < α₁)
    (D : ℕ → Finset (EuclideanSpace ℝ (Fin d))) (hmono : Monotone D)
    (hbdd : Bornology.IsBounded (⋃ n, (D n : Set (EuclideanSpace ℝ (Fin d)))))
    (hinf : (⋃ n, (D n : Set (EuclideanSpace ℝ (Fin d)))).Infinite)
    (σhat : ℕ → (EuclideanSpace ℝ (Fin d) → ℝ) → ℝ)
    (hmax : ∀ n z, (fun i : D n ↦ z i) ≠ 0 → 0 < σhat n z ∧ ∀ s : ℝ, 0 < s →
      gaussianLogLik (s • Matrix.of fun i j : D n ↦
          maternCorrelation ν (1 / α₁) ‖(i : EuclideanSpace ℝ (Fin d)) - j‖)
        (fun i : D n ↦ z i) ≤
      gaussianLogLik (σhat n z • Matrix.of fun i j : D n ↦
          maternCorrelation ν (1 / α₁) ‖(i : EuclideanSpace ℝ (Fin d)) - j‖)
        (fun i : D n ↦ z i)) :
    ∀ᵐ z ∂maternLaw ν σsq₀ α₀ univ, Tendsto (fun n ↦ σhat n (fun x ↦ z ⟨x, mem_univ x⟩) *
      α₁ ^ (2 * ν)) atTop (𝓝 (σsq₀ * α₀ ^ (2 * ν))) := by
  sorry

end MSSS
