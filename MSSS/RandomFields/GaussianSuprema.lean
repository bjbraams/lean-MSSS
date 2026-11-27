module

public import MSSS.RandomFields.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Suprema of Gaussian fields

SYNOPSIS items 20 and 21: Dudley's entropy bound with its continuity consequences, and the
Borell–TIS inequality.

For a centred Gaussian field `f` on a set `T`, the canonical pseudometric is
`d(s, t) = (E (f s - f t)²)^{1/2}` and `N(ε)` is the least number of closed `d`-balls of radius
`ε`, centred in `T`, that cover `T`. Its entropy `H(ε) = log N(ε)` enters through
`H(ε)^{1/2}`, which is taken to be `∞` when `N(ε) = ∞`.

The expected supremum `E sup_T f` of a possibly uncountable field is the supremum of
`E max_F f` over finite `F ⊆ T`; the bounds of item 20 are stated for every finite `F`, which
is equivalent and avoids measurability of the supremum. For item 21, a separable field has the
same supremum as its restriction to a countable separant, so the inequality is stated for a
countable index set.

## Main definitions

* `MSSS.canonicalDist f P s t`: the canonical pseudometric `d(s, t)`.
* `MSSS.canonicalCoveringNumber f P ε`: the covering number `N(ε)`.
* `MSSS.sqrtEntropy f P ε`: `H(ε)^{1/2} = (log N(ε))^{1/2}` in `[0, ∞]`.
* `MSSS.canonicalDiam f P`: the `d`-diameter of `T` in `[0, ∞]`.
* `MSSS.entropyIntegral f P δ`: `∫_0^δ H(ε)^{1/2} dε`.

## Main results

All admitted.

* `MSSS.dudley_entropy_bound`, `MSSS.exists_continuous_modification_of_entropyIntegral`,
  `MSSS.fernique_stationary_tfae`, `MSSS.exists_continuous_modification_of_logModulus`:
  SYNOPSIS item 20.
* `MSSS.borell_tis`: SYNOPSIS item 21.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace MSSS

variable {Ω T : Type*} [MeasurableSpace Ω]

/-- The **canonical pseudometric** `d(s, t) = (E (f s - f t)²)^{1/2}` of a field. -/
def canonicalDist (f : T → Ω → ℝ) (P : Measure Ω) (s t : T) : ℝ :=
  Real.sqrt (∫ ω, (f s ω - f t ω) ^ 2 ∂P)

/-- The **covering number** `N(ε)`: the least number of closed `d`-balls of radius `ε`,
centred in `T`, that cover `T`. -/
def canonicalCoveringNumber (f : T → Ω → ℝ) (P : Measure Ω) (ε : ℝ) : ℕ∞ :=
  ⨅ (C : Finset T) (_ : ∀ t, ∃ c ∈ C, canonicalDist f P t c ≤ ε), (C.card : ℕ∞)

/-- The square root of the metric entropy, `H(ε)^{1/2} = (log N(ε))^{1/2}`, with value `∞` when
`N(ε) = ∞`. -/
def sqrtEntropy (f : T → Ω → ℝ) (P : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  if canonicalCoveringNumber f P ε = ⊤ then ⊤
  else ENNReal.ofReal (Real.sqrt (Real.log (canonicalCoveringNumber f P ε).toNat))

/-- The diameter of `T` for the canonical pseudometric, in `[0, ∞]`. -/
def canonicalDiam (f : T → Ω → ℝ) (P : Measure Ω) : ℝ≥0∞ :=
  ⨆ (s : T) (t : T), ENNReal.ofReal (canonicalDist f P s t)

/-- The **entropy integral** `∫_0^δ H(ε)^{1/2} dε`, for `δ ∈ [0, ∞]`. -/
def entropyIntegral (f : T → Ω → ℝ) (P : Measure Ω) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ε in {ε : ℝ | 0 < ε ∧ ENNReal.ofReal ε ≤ δ}, sqrtEntropy f P ε

lemma canonicalDist_def (f : T → Ω → ℝ) (P : Measure Ω) (s t : T) :
    canonicalDist f P s t = Real.sqrt (∫ ω, (f s ω - f t ω) ^ 2 ∂P) := by
  rw [canonicalDist]

lemma canonicalCoveringNumber_def (f : T → Ω → ℝ) (P : Measure Ω) (ε : ℝ) :
    canonicalCoveringNumber f P ε =
      ⨅ (C : Finset T) (_ : ∀ t, ∃ c ∈ C, canonicalDist f P t c ≤ ε), (C.card : ℕ∞) := by
  rw [canonicalCoveringNumber]

lemma sqrtEntropy_def (f : T → Ω → ℝ) (P : Measure Ω) (ε : ℝ) : sqrtEntropy f P ε =
    if canonicalCoveringNumber f P ε = ⊤ then ⊤
    else ENNReal.ofReal (Real.sqrt (Real.log (canonicalCoveringNumber f P ε).toNat)) := by
  rw [sqrtEntropy]

lemma canonicalDiam_def (f : T → Ω → ℝ) (P : Measure Ω) :
    canonicalDiam f P = ⨆ (s : T) (t : T), ENNReal.ofReal (canonicalDist f P s t) := by
  rw [canonicalDiam]

lemma entropyIntegral_def (f : T → Ω → ℝ) (P : Measure Ω) (δ : ℝ≥0∞) :
    entropyIntegral f P δ =
      ∫⁻ ε in {ε : ℝ | 0 < ε ∧ ENNReal.ofReal ε ≤ δ}, sqrtEntropy f P ε := by
  rw [entropyIntegral]

/-! ### Dudley's entropy bound (SYNOPSIS item 20) -/

/-- SYNOPSIS item 20, Dudley's entropy bound: there is a universal constant `K` such that, for
every centred Gaussian field, `E sup_T f ≤ K ∫_0^{diam(T)/2} H(ε)^{1/2} dε` and
`E sup_{d(s,t) ≤ δ} |f t - f s| ≤ K ∫_0^δ H(ε)^{1/2} dε`; both suprema are taken over finite
subsets. -/
theorem dudley_entropy_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω T : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (f : T → Ω → ℝ), IsGaussianProcess f P → (∀ t, P[f t] = 0) →
      (∀ (F : Finset T) (hF : F.Nonempty),
        ENNReal.ofReal (∫ ω, F.sup' hF (fun t ↦ f t ω) ∂P) ≤
          ENNReal.ofReal K * entropyIntegral f P (canonicalDiam f P / 2)) ∧
      ∀ (δ : ℝ), 0 < δ → ∀ (F : Finset (T × T)) (hF : F.Nonempty),
        (∀ p ∈ F, canonicalDist f P p.1 p.2 ≤ δ) →
        ENNReal.ofReal (∫ ω, F.sup' hF (fun p ↦ |f p.2 ω - f p.1 ω|) ∂P) ≤
          ENNReal.ofReal K * entropyIntegral f P (ENNReal.ofReal δ) := by
  sorry

/-- SYNOPSIS item 20: if the entropy integral is finite, the centred Gaussian field has a version
with bounded and `d`-uniformly continuous sample paths. -/
theorem exists_continuous_modification_of_entropyIntegral {P : Measure Ω}
    [IsProbabilityMeasure P] {f : T → Ω → ℝ} (hf : IsGaussianProcess f P)
    (hc : ∀ t, P[f t] = 0) (hH : entropyIntegral f P (canonicalDiam f P / 2) < ⊤) :
    ∃ f' : T → Ω → ℝ, (∀ t, Measurable (f' t)) ∧ (∀ t, f' t =ᵐ[P] f t) ∧
      ∀ ω, (∃ M, ∀ t, |f' t ω| ≤ M) ∧
        ∀ η > 0, ∃ δ > 0, ∀ s t, canonicalDist f P s t < δ → |f' s ω - f' t ω| < η := by
  sorry

/-- SYNOPSIS item 20, Fernique's theorem: for a centred, mean-square continuous Gaussian field
on a compact abelian group whose covariance is invariant under translation, sample continuity,
sample boundedness, and finiteness of the entropy integral are equivalent. Mean-square continuity is the
standing assumption of Fernique and of Marcus–Pisier. -/
theorem fernique_stationary_tfae {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : G → Ω → ℝ} (hf : IsGaussianProcess f P) (hc : ∀ t, P[f t] = 0)
    (hms : IsMeanSquareContinuous f P)
    (hstat : ∀ g s t, cov[f (g * s), f (g * t); P] = cov[f s, f t; P]) :
    List.TFAE [∃ f' : G → Ω → ℝ, (∀ t, Measurable (f' t)) ∧ (∀ t, f' t =ᵐ[P] f t) ∧
        ∀ ω, Continuous fun t ↦ f' t ω,
      ∃ f' : G → Ω → ℝ, (∀ t, Measurable (f' t)) ∧ (∀ t, f' t =ᵐ[P] f t) ∧
        ∀ ω, ∃ M, ∀ t, |f' t ω| ≤ M,
      entropyIntegral f P (canonicalDiam f P / 2) < ⊤] := by
  sorry

/-- SYNOPSIS item 20, consequence: a centred Gaussian field on a compact `T ⊆ ℝ^N` with
`E |f s - f t|² ≤ C |log |s - t||^{-1-α}` for `|s - t| < η` has a version with continuous
sample paths on `T`, which are then bounded on `T`. -/
theorem exists_continuous_modification_of_logModulus {N : ℕ}
    {T : Set (EuclideanSpace ℝ (Fin N))} (hT : IsCompact T) {P : Measure Ω}
    [IsProbabilityMeasure P] {f : EuclideanSpace ℝ (Fin N) → Ω → ℝ}
    (hf : IsGaussianProcess f P) (hc : ∀ t, P[f t] = 0) {C α η : ℝ} (hC : 0 < C)
    (hα : 0 < α) (hη : 0 < η)
    (hmod : ∀ s ∈ T, ∀ t ∈ T, dist s t < η →
      ∫ ω, (f s ω - f t ω) ^ 2 ∂P ≤ C * |Real.log (dist s t)| ^ (-1 - α)) :
    ∃ f' : EuclideanSpace ℝ (Fin N) → Ω → ℝ, (∀ t, Measurable (f' t)) ∧
      (∀ t ∈ T, f' t =ᵐ[P] f t) ∧ ∀ ω, ContinuousOn (fun t ↦ f' t ω) T := by
  sorry

/-! ### The Borell–TIS inequality (SYNOPSIS item 21) -/

/-- SYNOPSIS item 21, Borell–TIS inequality: for a centred Gaussian field on a countable set,
almost surely bounded above, `‖f‖ = sup_T f` is integrable, the variances are bounded, and
`P(‖f‖ - E‖f‖ > u) ≤ exp(-u² / (2σ_T²))` with `σ_T² = sup_T E f(t)²`. -/
theorem borell_tis [Countable T] [Nonempty T] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : T → Ω → ℝ} (hf : IsGaussianProcess f P) (hc : ∀ t, P[f t] = 0)
    (hbdd : ∀ᵐ ω ∂P, BddAbove (range fun t ↦ f t ω)) :
    Integrable (fun ω ↦ ⨆ t, f t ω) P ∧ BddAbove (range fun t ↦ ∫ ω, f t ω ^ 2 ∂P) ∧
      ∀ u : ℝ, 0 < u →
        P {ω | (⨆ t, f t ω) - ∫ ω', (⨆ t, f t ω') ∂P > u} ≤
          ENNReal.ofReal (Real.exp (-u ^ 2 / (2 * ⨆ t, ∫ ω, f t ω ^ 2 ∂P))) := by
  sorry

end MSSS
