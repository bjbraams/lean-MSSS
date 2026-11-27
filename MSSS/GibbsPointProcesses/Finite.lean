module

public import MSSS.GibbsPointProcesses.Finite.Reference

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Pi
import all Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Finite Gibbs, Markov, and Strauss point processes

SYNOPSIS items 95, 97–99, and 107. An energy takes values in `ℝ ∪ {+∞}` (`WithTop ℝ`).
Where `H = +∞` the weight `e^{-β H}` is `0` for `β ≠ 0` and `1` for `β = 0`, so that the Gibbs
law at `β = 0` is the Poisson law. The finite Poisson reference, stability, and the forward
Georgii–Nguyen–Zessin formula are in `MSSS.GibbsPointProcesses.Finite.Reference`.

## Main results

* `MSSS.hasConfigDensity_gibbs_iff_gnz`: SYNOPSIS item 95.
* `MSSS.isMarkovFunction_iff`, `MSSS.papangelou_markov`,
  `MSSS.markov_density_factorization`: SYNOPSIS item 97.
* `MSSS.strauss_properties`, `MSSS.strauss_not_normalisable`,
  `MSSS.strauss_fixed_number_integrable`: SYNOPSIS item 98.
* `MSSS.partitionFunction_pos_lt_top`, `MSSS.gibbs_dlr`, `MSSS.gibbs_variational`,
  `MSSS.hasDerivAt_gibbs_meanCount`, `MSSS.hasDerivAt_gibbs_meanEnergy`: SYNOPSIS item 99.
* `MSSS.tendsto_prod_conditionalDensity_pseudolikelihood`,
  `MSSS.pseudolikelihood_score_mean_zero`, `MSSS.concaveOn_log_pseudolikelihood`,
  `MSSS.pseudolikelihood_poisson`: SYNOPSIS item 107.

The Markov factorisation uses Mathlib's finite powerset product identities. The Strauss
divergence proof uses Mathlib's exponential series and the limit of a polynomial divided by an
exponential, together with almost-sure distinctness of the reference tuples. The Gibbs moment
derivatives use Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and
`Real.pow_div_factorial_le_exp`. For the inverse-temperature derivative, the fixed activity
weight is absorbed into the reference measure using a measurable minorant.
-/

public section

noncomputable section

open MeasureTheory Set Finset Topology Filter TopologicalSpace
open scoped Filter
open scoped ENNReal NNReal

namespace MSSS

variable {E : Type*} [MeasureSpace E] [DecidableEq E]

/-! ### Energies and Gibbs measures (SYNOPSIS items 95, 99) -/

/-- The Boltzmann weight `e^{-β H(x)}`. Where `H(x) = +∞` it is `0` for `β ≠ 0` and `1` for
`β = 0` (the convention `e^{-0·∞} = 1`). -/
def gibbsWeight (β : ℝ) (H : Finset E → WithTop ℝ) (x : Finset E) : ℝ :=
  if h : H x = ⊤ then (if β = 0 then 1 else 0) else Real.exp (-β * (H x).untop h)

/-- The partition function `Z = ∫ z^{n(x)} e^{-β H(x)} Π_Λ(dx)`. -/
def partitionFunction (Λ : Set E) (z β : ℝ) (H : Finset E → WithTop ℝ) : ℝ≥0∞ :=
  poissonIntegral Λ fun x ↦ ENNReal.ofReal (z ^ x.card * gibbsWeight β H x)

/-- The density `Z⁻¹ z^{n(x)} e^{-β H(x)}` of the finite-volume Gibbs measure `P^{z,β}_Λ`. -/
def gibbsDensity (Λ : Set E) (z β : ℝ) (H : Finset E → WithTop ℝ) (x : Finset E) : ℝ :=
  z ^ x.card * gibbsWeight β H x / (partitionFunction Λ z β H).toReal

/-- The energy is **non-degenerate**: `H(∅) < ∞`. -/
def IsNonDegenerate (H : Finset E → WithTop ℝ) : Prop := H ∅ ≠ ⊤

/-- The energy is **hereditary**: `H(x) < ∞` implies `H(x ∖ {ξ}) < ∞`. -/
def IsHereditaryEnergy (H : Finset E → WithTop ℝ) : Prop :=
  ∀ x ξ, H x ≠ ⊤ → H (x.erase ξ) ≠ ⊤

/-- The energy is **measurable**: its finite part and the set where it is infinite are
measurable as functions of the points of configurations with `n` points, for every `n`. -/
def IsEnergyMeasurable (H : Finset E → WithTop ℝ) : Prop :=
  IsConfigMeasurable (fun x ↦ (H x).untopD 0) ∧
    ∀ n, MeasurableSet {x : Fin n → E | H (toConfig x) = ⊤}

lemma isEnergyMeasurable_def {H : Finset E → WithTop ℝ} : IsEnergyMeasurable H ↔
    IsConfigMeasurable (fun x ↦ (H x).untopD 0) ∧
      ∀ n, MeasurableSet {x : Fin n → E | H (toConfig x) = ⊤} := Iff.rfl

/-- The energy is **stable**: `H(x) ≥ A n(x)` for a constant `A`. -/
def IsStableEnergy (H : Finset E → WithTop ℝ) : Prop :=
  ∃ A : ℝ, ∀ x, ((A * x.card : ℝ) : WithTop ℝ) ≤ H x

omit [MeasureSpace E] [DecidableEq E] in
lemma gibbsWeight_def (β : ℝ) (H : Finset E → WithTop ℝ) (x : Finset E) :
    gibbsWeight β H x =
      if h : H x = ⊤ then (if β = 0 then 1 else 0) else Real.exp (-β * (H x).untop h) := by
  rw [gibbsWeight]

lemma partitionFunction_def (Λ : Set E) (z β : ℝ) (H : Finset E → WithTop ℝ) :
    partitionFunction Λ z β H =
      poissonIntegral Λ fun x ↦ ENNReal.ofReal (z ^ x.card * gibbsWeight β H x) := by
  rw [partitionFunction]

lemma gibbsDensity_def (Λ : Set E) (z β : ℝ) (H : Finset E → WithTop ℝ) (x : Finset E) :
    gibbsDensity Λ z β H x =
      z ^ x.card * gibbsWeight β H x / (partitionFunction Λ z β H).toReal := by
  rw [gibbsDensity]

/-- SYNOPSIS item 95, converse: for a non-degenerate, hereditary, stable energy, `z > 0`,
`β ≥ 0`, and a diffuse finite-volume window `Λ` with `|Λ| > 0`, a random configuration satisfies the
Georgii–Nguyen–Zessin formula with `λ*(x, ξ) = z e^{-β(H(x ∪ {ξ}) - H(x))}` (with
`(+∞) - (+∞) = 0`) for all `h` if and only if it has the Gibbs density `P^{z,β}_Λ`. -/
theorem hasConfigDensity_gibbs_iff_gnz [MeasurableEq E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Finset E} {Λ : Set E}
    [NullSingletonClass ((volume : Measure E).restrict Λ)] (hΛ : volume Λ < ∞)
    (hΛ0 : 0 < volume Λ) (hXΛ : ∀ ω, (X ω : Set E) ⊆ Λ)
    (hXm : ∀ h : Finset E → ℝ≥0∞, IsConfigMeasurable h → Measurable fun ω ↦ h (X ω))
    {H : Finset E → WithTop ℝ} (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H)
    (hst : IsStableEnergy H) (hHm : IsEnergyMeasurable H) {z β : ℝ} (hz : 0 < z)
    (hβ : 0 ≤ β) :
    HasConfigDensity P X Λ (gibbsDensity Λ z β H) ↔
      ∀ h : E → Finset E → ℝ≥0∞,
        (∀ n, Measurable fun w : E × (Fin n → E) ↦ h w.1 (toConfig w.2)) →
        ∫⁻ ω, ∑ ξ ∈ X ω, h ξ ((X ω).erase ξ) ∂P =
          ∫⁻ ξ in Λ, ∫⁻ ω, h ξ (X ω) * ENNReal.ofReal
            (if H (X ω) = ⊤ then z
              else z * gibbsWeight β H (insert ξ (X ω)) / gibbsWeight β H (X ω)) ∂P := by
  sorry

-- Keep the hypotheses of the finite-volume Gibbs model in the statement.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 99: for a non-degenerate, hereditary, stable energy, `0 < Z < ∞`. -/
theorem partitionFunction_pos_lt_top {Λ : Set E} (hΛ : volume Λ < ∞)
    {H : Finset E → WithTop ℝ} (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H)
    (hst : IsStableEnergy H) (hHm : IsEnergyMeasurable H) {z β : ℝ} (hz : 0 < z)
    (hβ : 0 ≤ β) :
    0 < partitionFunction Λ z β H ∧ partitionFunction Λ z β H < ∞ := by
  rw [partitionFunction_def]
  refine ⟨poissonIntegral_pos_of_empty ?_, ?_⟩
  · rw [Finset.card_empty, pow_zero, one_mul, gibbsWeight_def, dite_eq_right hnd]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  obtain ⟨A, hA⟩ := hst
  let C := max 1 (z * Real.exp (-β * A))
  have hC : 1 ≤ C := le_max_left _ _
  refine poissonIntegral_lt_top_of_pow hΛ (C := ENNReal.ofReal C) ENNReal.ofReal_lt_top
    fun n x _ ↦ ?_
  rw [← ENNReal.ofReal_pow (zero_le_one.trans hC)]
  apply ENNReal.ofReal_le_ofReal
  have hk : (toConfig x).card ≤ n := by
    simpa only [toConfig_def, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := x))
  apply le_trans _ (pow_le_pow_right₀ hC hk)
  rw [gibbsWeight_def]
  split_ifs with htop hβ0
  · rw [mul_one]
    exact pow_le_pow_left₀ hz.le ((by simp [hβ0] : z ≤ z * Real.exp (-β * A)).trans
      (le_max_right _ _)) _
  · rw [mul_zero]
    exact pow_nonneg (zero_le_one.trans hC) _
  · have hle : A * ((toConfig x).card : ℝ) ≤ (H (toConfig x)).untop htop :=
      (WithTop.le_untop_iff htop).mpr (hA _)
    calc
      _ ≤ z ^ (toConfig x).card * Real.exp (-β * (A * (toConfig x).card)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hle (neg_nonpos.mpr hβ)))
          (pow_nonneg hz.le _)
      _ = (z * Real.exp (-β * A)) ^ (toConfig x).card := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
      _ ≤ C ^ (toConfig x).card := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _

/-- SYNOPSIS item 99, DLR equation: for `Δ ⊆ Λ` with `|Δ| > 0`, the conditional law of `X ∩ Δ`
given `X ∖ Δ` under `P^{z,β}_Λ` has density
`Z_Δ(x_{Δᶜ})⁻¹ z^{n(x_Δ)} e^{-β H_Δ(x)}` with respect to `Π_Δ`,
`H_Δ(x) = H(x) - H(x ∖ Δ)`. -/
theorem gibbs_dlr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Finset E} {Λ Δ : Set E} (hΛ : volume Λ < ∞) (hΔΛ : Δ ⊆ Λ) (hΔ : 0 < volume Δ)
    (hΔm : MeasurableSet Δ) [DecidablePred (· ∈ Δ)] {H : Finset E → WithTop ℝ}
    (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β)
    (hX : HasConfigDensity P X Λ (gibbsDensity Λ z β H)) (h : Finset E → ℝ≥0∞)
    (hh : IsConfigMeasurable h) :
    let w : Finset E → Finset E → ℝ := fun y c ↦
      z ^ y.card * gibbsWeight β H (y ∪ c) / gibbsWeight β H c
    ∫⁻ ω, h (X ω) ∂P = ∫⁻ ω,
      poissonIntegral Δ (fun y ↦ h (y ∪ (X ω).filter (· ∉ Δ)) *
          ENNReal.ofReal (w y ((X ω).filter (· ∉ Δ)))) /
        poissonIntegral Δ (fun y ↦ ENNReal.ofReal (w y ((X ω).filter (· ∉ Δ)))) ∂P := by
  sorry

/-- SYNOPSIS item 99, variational principle: among probability densities `g` on `Λ` with respect
to `Π_Λ` with finite mean number of points and finite mean energy, the functional
`β E_g H - log z E_g n + ∫ g log g dΠ_Λ` is at least `-log Z`, with equality exactly for the
Gibbs density (up to `Π_Λ`-null sets). -/
theorem gibbs_variational {Λ : Set E} (hΛ : volume Λ < ∞) {H : Finset E → ℝ}
    (hst : ∃ A : ℝ, ∀ x, A * x.card ≤ H x) (hHm : IsConfigMeasurable H) {z β : ℝ} (hz : 0 < z)
    (hβ : 0 ≤ β) (g : Finset E → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgm : IsConfigMeasurable g)
    (hg1 : poissonIntegral Λ (fun x ↦ ENNReal.ofReal (g x)) = 1)
    (hgn : poissonIntegral Λ (fun x ↦ ENNReal.ofReal (x.card * g x)) < ∞)
    (hgH : poissonIntegral Λ (fun x ↦ ‖H x * g x‖ₑ) < ∞)
    (hglog : poissonIntegral Λ (fun x ↦ ‖g x * Real.log (g x)‖ₑ) < ∞) :
    let Hw : Finset E → WithTop ℝ := fun x ↦ (H x : WithTop ℝ)
    let F : (Finset E → ℝ) → ℝ := fun g ↦
      (poissonIntegral Λ (fun x ↦ ENNReal.ofReal (β * H x * g x - Real.log z * x.card * g x +
          g x * Real.log (g x)))).toReal -
        (poissonIntegral Λ (fun x ↦ ENNReal.ofReal (-(β * H x * g x - Real.log z * x.card * g x +
          g x * Real.log (g x))))).toReal;
    -Real.log (partitionFunction Λ z β Hw).toReal ≤ F g ∧
      (F g = -Real.log (partitionFunction Λ z β Hw).toReal ↔
        poissonIntegral Λ (fun x ↦ if g x = gibbsDensity Λ z β Hw x then 0 else 1) = 0) := by
  sorry

section Tilt

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

/-- The exponential weight with coefficient `t` and its powers of the nonnegative statistic. -/
private def tiltKernel (a v : S → ℝ) (t : ℝ) (k : ℕ) (x : S) : ℝ :=
  v x ^ k * Real.exp (a x + t * v x)

omit [MeasurableSpace S] in
/-- Any fixed power of the statistic is bounded by a constant times a faster exponential. -/
private lemma tiltKernel_le (a v : S → ℝ) {d : ℝ} (hd : 0 < d) {b u : ℝ}
    (hu : u + d ≤ b) (k : ℕ) (x : S) (hv : 0 ≤ v x) :
    tiltKernel a v u k x ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (a x + b * v x) := by
  have hpow : v x ^ k ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (d * v x) := by
    have hn : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    have hp := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp _ (mul_nonneg hd.le hv) k)
    rw [div_mul_eq_mul_div, le_div_iff₀' (pow_pos hd k), ← mul_pow, mul_comm _ (Real.exp _)]
    exact hp
  unfold tiltKernel
  calc
    _ ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (d * v x) *
        Real.exp (a x + u * v x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_right hu hv]

/-- A finite exponential moment with larger coefficient controls all polynomial moments. -/
private lemma integrable_tiltKernel {a v : S → ℝ} (ha : Measurable a) (hv : Measurable v)
    (hv0 : ∀ x, 0 ≤ v x) {b u : ℝ} (hu : u < b)
    (hb : Integrable (fun x ↦ Real.exp (a x + b * v x)) μ) (k : ℕ) :
    Integrable (tiltKernel a v u k) μ := by
  have hd : 0 < b - u := sub_pos.mpr hu
  refine (hb.const_mul ((k.factorial : ℝ) / (b - u) ^ k)).mono'
    ((hv.pow_const _).mul (ha.add (measurable_const.mul hv)).exp).aestronglyMeasurable ?_
  filter_upwards with x
  have hn : 0 ≤ tiltKernel a v u k x :=
    mul_nonneg (pow_nonneg (hv0 x) _) (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact tiltKernel_le a v hd (by linarith) k x (hv0 x)

/-- Dominated differentiation of an unnormalized moment of an exponential tilt. -/
private lemma hasDerivAt_integral_tiltKernel {a v : S → ℝ} (ha : Measurable a)
    (hv : Measurable v) (hv0 : ∀ x, 0 ≤ v x) {t b : ℝ} (ht : t < b)
    (hb : Integrable (fun x ↦ Real.exp (a x + b * v x)) μ) (k : ℕ) :
    HasDerivAt (fun u ↦ ∫ x, tiltKernel a v u k x ∂μ)
      (∫ x, tiltKernel a v t (k + 1) x ∂μ) t := by
  let d := (b - t) / 2
  have hd : 0 < d := half_pos (sub_pos.mpr ht)
  have hm (u : ℝ) (j : ℕ) : AEStronglyMeasurable (tiltKernel a v u j) μ :=
    ((hv.pow_const _).mul (ha.add (measurable_const.mul hv)).exp).aestronglyMeasurable
  have hx (x : S) (u : ℝ) :
      HasDerivAt (fun u ↦ tiltKernel a v u k x) (tiltKernel a v u (k + 1) x) u := by
    have he := ((hasDerivAt_const u (a x)).add ((hasDerivAt_id u).mul_const (v x))).exp
    have hdv : v x ^ k * (Real.exp (a x + u * v x) * (0 + 1 * v x)) =
        v x ^ (k + 1) * Real.exp (a x + u * v x) := by rw [pow_succ]; ring
    simpa only [Pi.add_apply, id_eq, hdv, tiltKernel] using he.const_mul (v x ^ k)
  have hd' : t ∈ Iio (t + d) := lt_add_of_pos_right _ hd
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Iio_mem_nhds hd')
    (Eventually.of_forall fun u ↦ hm u k) (integrable_tiltKernel ha hv hv0 ht hb k)
    (hm t (k + 1)) ?_ (hb.const_mul (((k + 1).factorial : ℝ) / d ^ (k + 1)))
    (Eventually.of_forall fun x u _ ↦ hx x u)).2
  filter_upwards with x
  intro u hu
  have hn : 0 ≤ tiltKernel a v u (k + 1) x :=
    mul_nonneg (pow_nonneg (hv0 x) _) (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have hlt : u < t + d := mem_Iio.mp hu
  have he : t + d + d = b := by dsimp only [d]; ring
  exact tiltKernel_le a v hd ((add_le_add hlt.le le_rfl).trans_eq he) _ x (hv0 x)

/-- Differentiating the normalized first moment of an exponential tilt gives its variance. -/
private lemma hasDerivAt_tilt_mean {a v : S → ℝ} (ha : Measurable a) (hv : Measurable v)
    (hv0 : ∀ x, 0 ≤ v x) {t b : ℝ} (ht : t < b)
    (hb : Integrable (fun x ↦ Real.exp (a x + b * v x)) μ)
    (h0 : (∫ x, tiltKernel a v t 0 x ∂μ) ≠ 0) :
    let M (t : ℝ) (k : ℕ) := ∫ x, tiltKernel a v t k x ∂μ
    HasDerivAt (fun u ↦ M u 1 / M u 0) (M t 2 / M t 0 - (M t 1 / M t 0) ^ 2) t := by
  dsimp only
  convert (hasDerivAt_integral_tiltKernel ha hv hv0 ht hb 1).fun_div
    (hasDerivAt_integral_tiltKernel ha hv hv0 ht hb 0) h0 using 1
  field_simp

end Tilt

/-- Disjoint union of the finite tuple spaces used by the Poisson reference. -/
private abbrev ConfigTuples (E : Type*) := Σ n : ℕ, Fin n → E

/-- A tuple determines a finite configuration by taking its image. -/
private def tupleConfig (x : ConfigTuples E) : Finset E := toConfig x.2

/-- Tuplewise measurability induces measurability on the disjoint union. -/
private lemma measurable_tupleConfig {Y : Type*} [MeasurableSpace Y] {g : Finset E → Y}
    (hg : IsConfigMeasurable g) : Measurable (fun x : ConfigTuples E ↦ g (tupleConfig x)) := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr fun n ↦ (isConfigMeasurable_def _).mp hg n hs

omit [DecidableEq E] in
/-- Each tuple space is a measurable subspace of the disjoint union. -/
private lemma measurableEmbedding_tuple_mk (n : ℕ) :
    MeasurableEmbedding (Sigma.mk (β := fun k : ℕ ↦ Fin k → E) n) where
  injective := fun _ _ h ↦ by cases h; rfl
  measurable := fun _ hs ↦ MeasurableSpace.measurableSet_iInf.mp hs n
  measurableSet_image' s hs := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro m
    by_cases hm : m = n
    · subst m
      have hi : Function.Injective (Sigma.mk (β := fun k : ℕ ↦ Fin k → E) n) := by
        intro x y h
        cases h
        rfl
      -- On its own fibre, the map pulls its image back to the original measurable set.
      change MeasurableSet (Sigma.mk n ⁻¹' (Sigma.mk n '' s : Set (ConfigTuples E)))
      rwa [Set.preimage_image_eq _ hi]
    · have he : Sigma.mk m ⁻¹' (Sigma.mk n '' s : Set (ConfigTuples E)) = ∅ := by
        ext x
        refine iff_false_intro fun hx ↦ ?_
        obtain ⟨y, _, hy⟩ := hx
        exact hm (congrArg Sigma.fst hy).symm
      -- On every other fibre, this preimage is empty.
      change MeasurableSet (Sigma.mk m ⁻¹' (Sigma.mk n '' s : Set (ConfigTuples E)))
      rw [he]
      exact MeasurableSet.empty

/-- The finite Poisson tuple measure has weight `e^{-|W|}/n!` on each tuple space. -/
private def poissonTupleMeasure (W : Set E) : Measure (ConfigTuples E) :=
  Measure.sum fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-(volume W).toReal) / n.factorial) •
    Measure.map (Sigma.mk n) (volume.restrict (Set.pi univ fun _ : Fin n ↦ W))

/-- The Poisson series is the lower integral over the disjoint union of tuple spaces. -/
private lemma lintegral_poissonTupleMeasure (W : Set E) (g : Finset E → ℝ≥0∞) :
    (∫⁻ x, g (tupleConfig x) ∂poissonTupleMeasure W) = poissonIntegral W g := by
  rw [poissonTupleMeasure, lintegral_sum_measure, poissonIntegral_def]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, (measurableEmbedding_tuple_mk (E := E) n).lintegral_map]
  rfl

/-- The cardinality is measurable on tuple spaces with a measurable diagonal. -/
private lemma isConfigMeasurable_card_real [MeasurableEq E] :
    IsConfigMeasurable (fun x : Finset E ↦ (x.card : ℝ)) := by
  rw [isConfigMeasurable_def]
  intro n
  have h := (isConfigMeasurable_def _).mp (isConfigMeasurable_sum_erase
    (E := E) (g := fun _ _ ↦ 1) (fun _ ↦ measurable_const)) n
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, ENNReal.toReal_natCast]
    using h.ennreal_toReal

/-- Finite stable energies have a strictly positive and finite partition function. -/
private lemma partitionFunction_of_real_pos_lt_top {W : Set E} (hW : volume W < ∞)
    {H : Finset E → ℝ} (hs : ∃ A : ℝ, ∀ x, A * x.card ≤ H x)
    (hm : IsConfigMeasurable H) {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) :
    0 < partitionFunction W z β (fun x ↦ (H x : WithTop ℝ)) ∧
      partitionFunction W z β (fun x ↦ (H x : WithTop ℝ)) < ∞ := by
  apply partitionFunction_pos_lt_top hW _ _ _ _ hz hβ
  · exact WithTop.coe_ne_top
  · exact fun _ _ _ ↦ WithTop.coe_ne_top
  · obtain ⟨A, hA⟩ := hs
    exact ⟨A, fun x ↦ WithTop.coe_le_coe.mpr (hA x)⟩
  · refine ⟨(isConfigMeasurable_def _).mpr ?_, fun n ↦ by simp⟩
    intro n
    simpa using (isConfigMeasurable_def _).mp hm n

omit [MeasureSpace E] [DecidableEq E] in
/-- A real energy gives the usual exponential Gibbs factor. -/
private lemma gibbsWeight_of_real (β : ℝ) (H : Finset E → ℝ) (x : Finset E) :
    gibbsWeight β (fun y ↦ (H y : WithTop ℝ)) x = Real.exp (-β * H x) := by
  simp [gibbsWeight_def]

/-- Dividing the integrand by a positive real constant divides its Poisson integral. -/
private lemma poissonIntegral_ofReal_div (W : Set E) (g : Finset E → ℝ) {c : ℝ} (hc : 0 < c) :
    (poissonIntegral W (fun x ↦ ENNReal.ofReal (g x / c))).toReal =
      (poissonIntegral W (fun x ↦ ENNReal.ofReal (g x))).toReal / c := by
  rw [← lintegral_poissonTupleMeasure, ← lintegral_poissonTupleMeasure]
  simp_rw [ENNReal.ofReal_div_of_pos hc, ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne'),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le, div_eq_inv_mul]

/-- Configuration moments under the Gibbs density divide the unnormalized moments by
the partition function. -/
private lemma poissonIntegral_gibbsDensity (W : Set E) (z β : ℝ) (H : Finset E → WithTop ℝ)
    (g : Finset E → ℝ) (hZ : 0 < (partitionFunction W z β H).toReal) :
    (poissonIntegral W (fun x ↦ ENNReal.ofReal (g x * gibbsDensity W z β H x))).toReal =
      (poissonIntegral W (fun x ↦ ENNReal.ofReal (g x * (z ^ x.card * gibbsWeight β H x)))).toReal /
        (partitionFunction W z β H).toReal := by
  simp_rw [gibbsDensity_def, mul_div_assoc']
  exact poissonIntegral_ofReal_div W _ hZ

omit [MeasureSpace E] in
/-- The activity enters the Gibbs weight as an exponential tilt by the count. -/
private lemma tiltKernel_count (β u : ℝ) (H : Finset E → ℝ) (k : ℕ) (x : ConfigTuples E) :
    tiltKernel (fun y ↦ -β * H (tupleConfig y)) (fun y ↦ (tupleConfig y).card)
      u k x =
      ((tupleConfig x).card : ℝ) ^ k * (Real.exp u ^ (tupleConfig x).card *
        gibbsWeight β (fun y ↦ (H y : WithTop ℝ)) (tupleConfig x)) := by
  rw [tiltKernel, gibbsWeight_of_real, Real.exp_add, ← Real.exp_nat_mul, mul_comm u, mul_comm
    (Real.exp (-β * H (tupleConfig x)))]

/-- Integrating an unnormalized moment over tuple space realizes the finite Gibbs series. -/
private lemma integral_count_tilt {W : Set E} [MeasurableEq E] {H : Finset E → ℝ}
    (hm : IsConfigMeasurable H) (β u : ℝ) (k : ℕ) :
    (∫ x, tiltKernel (fun y ↦ -β * H (tupleConfig y)) (fun y ↦ (tupleConfig y).card)
      u k x ∂poissonTupleMeasure W) =
      (poissonIntegral W (fun x ↦ ENNReal.ofReal ((x.card : ℝ) ^ k *
        (Real.exp u ^ x.card * gibbsWeight β (fun y ↦ (H y : WithTop ℝ)) x)))).toReal := by
  have ha := (measurable_const (a := -β)).mul (measurable_tupleConfig hm)
  have hv := measurable_tupleConfig (E := E) isConfigMeasurable_card_real
  have hmeas : Measurable
      (tiltKernel (fun y ↦ -β * H (tupleConfig y)) (fun y ↦ (tupleConfig y).card) u k) :=
    (hv.pow_const k).mul (ha.add ((measurable_const (a := u)).mul hv)).exp
  have hn : 0 ≤ᵐ[poissonTupleMeasure W] tiltKernel
      (fun y ↦ -β * H (tupleConfig y)) (fun y ↦ (tupleConfig y).card) u k :=
    Eventually.of_forall fun x ↦ mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae hn hmeas.aestronglyMeasurable]
  simp_rw [tiltKernel_count]
  rw [lintegral_poissonTupleMeasure W (fun x ↦ ENNReal.ofReal ((x.card : ℝ) ^ k *
    (Real.exp u ^ x.card * gibbsWeight β (fun y ↦ (H y : WithTop ℝ)) x)))]

/-- The exponential tilt by the count is integrable at every real coefficient. -/
private lemma integrable_count_tilt {W : Set E} [MeasurableEq E] (hW : volume W < ∞)
    {H : Finset E → ℝ} (hs : ∃ A : ℝ, ∀ x, A * x.card ≤ H x)
    (hm : IsConfigMeasurable H) {β : ℝ} (hβ : 0 ≤ β) (u : ℝ) :
    Integrable (fun x : ConfigTuples E ↦ Real.exp (-β * H (tupleConfig x) +
      u * (tupleConfig x).card)) (poissonTupleMeasure W) := by
  have hv := measurable_tupleConfig (E := E) isConfigMeasurable_card_real
  have hmexp : Measurable (fun x : ConfigTuples E ↦ Real.exp (-β * H (tupleConfig x) +
      u * (tupleConfig x).card)) :=
    (((measurable_const (a := -β)).mul (measurable_tupleConfig hm)).add
      ((measurable_const (a := u)).mul hv)).exp
  apply (lintegral_ofReal_ne_top_iff_integrable hmexp.aestronglyMeasurable
    (Eventually.of_forall fun _ ↦ Real.exp_nonneg _)).mp
  have he (x : ConfigTuples E) : Real.exp (-β * H (tupleConfig x) + u * (tupleConfig x).card) =
      tiltKernel (fun y ↦ -β * H (tupleConfig y)) (fun y ↦ (tupleConfig y).card) u 0 x := by
    simp only [tiltKernel, pow_zero, one_mul]
  simp_rw [he, tiltKernel_count, pow_zero, one_mul]
  rw [lintegral_poissonTupleMeasure W (fun x ↦ ENNReal.ofReal
    (Real.exp u ^ x.card * gibbsWeight β (fun y ↦ (H y : WithTop ℝ)) x)),
    ← partitionFunction_def]
  exact (partitionFunction_of_real_pos_lt_top hW hs hm (Real.exp_pos u) hβ).2.ne

/-- SYNOPSIS item 99: `d/dz E n = Var(n) / z` under `P^{z,β}_Λ`, for a finite stable energy
and a measurable diagonal, so that configuration cardinality is measurable. -/
theorem hasDerivAt_gibbs_meanCount [MeasurableEq E] {Λ : Set E} (hΛ : volume Λ < ∞)
    {H : Finset E → ℝ} (hst : ∃ A : ℝ, ∀ x, A * x.card ≤ H x) (hHm : IsConfigMeasurable H)
    {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) :
    let Hw : Finset E → WithTop ℝ := fun x ↦ (H x : WithTop ℝ)
    let moment : ℝ → (Finset E → ℝ) → ℝ := fun z k ↦
      (poissonIntegral Λ (fun x ↦ ENNReal.ofReal (k x * gibbsDensity Λ z β Hw x))).toReal
    HasDerivAt (fun z ↦ moment z fun x ↦ x.card)
      ((moment z (fun x ↦ (x.card : ℝ) ^ 2) - (moment z fun x ↦ x.card) ^ 2) / z) z := by
  dsimp only
  let M u k := ∫ x, tiltKernel (fun y ↦ -β * H (tupleConfig y)) (fun y ↦ (tupleConfig y).card)
    u k x ∂poissonTupleMeasure Λ
  have hZ (u : ℝ) :
      M u 0 = (partitionFunction Λ (Real.exp u) β (fun y ↦ (H y : WithTop ℝ))).toReal := by
    dsimp only [M]
    rw [integral_count_tilt hHm]
    simp [partitionFunction_def]
  have hpos (u : ℝ) : 0 < M u 0 := by
    rw [hZ]
    obtain ⟨h0, hfin⟩ := partitionFunction_of_real_pos_lt_top hΛ hst hHm (Real.exp_pos u) hβ
    exact ENNReal.toReal_pos h0.ne' hfin.ne
  have hmom {q : ℝ} (hq : 0 < q) (k : ℕ) :
      (poissonIntegral Λ (fun x ↦ ENNReal.ofReal ((x.card : ℝ) ^ k *
        gibbsDensity Λ q β (fun y ↦ (H y : WithTop ℝ)) x))).toReal =
          M (Real.log q) k / M (Real.log q) 0 := by
    have hq0 := hpos (Real.log q)
    rw [hZ, Real.exp_log hq] at hq0
    conv_rhs => arg 1; dsimp only [M]
    rw [integral_count_tilt hHm, poissonIntegral_gibbsDensity _ _ _ _ _ hq0,
      hZ, Real.exp_log hq]
  have hder : HasDerivAt (fun u ↦ M u 1 / M u 0)
      (M (Real.log z) 2 / M (Real.log z) 0 -
        (M (Real.log z) 1 / M (Real.log z) 0) ^ 2) (Real.log z) :=
    hasDerivAt_tilt_mean
    ((measurable_const (a := -β)).mul (measurable_tupleConfig hHm))
    (measurable_tupleConfig (E := E) isConfigMeasurable_card_real)
    (fun x ↦ Nat.cast_nonneg (tupleConfig x).card) (lt_add_one (Real.log z))
    (integrable_count_tilt hΛ hst hHm hβ (Real.log z + 1)) (hpos (Real.log z)).ne'
  have he := (hder.comp z (Real.hasDerivAt_log hz.ne'))
  rw [← div_eq_mul_inv, ← hmom hz 2, ← hmom hz 1] at he
  simp only [pow_one] at he
  refine he.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hz] with q hq
  simpa only [Function.comp_apply, pow_one] using hmom hq 1

/-- A fixed positive activity weight has finite lower integral over the tuple reference. -/
private lemma lintegral_activity_lt_top {W : Set E} (hW : volume W < ∞) {z : ℝ}
    (hz : 0 < z) :
    (∫⁻ x : ConfigTuples E, ENNReal.ofReal (z ^ (tupleConfig x).card) ∂poissonTupleMeasure W)
      < ∞ := by
  rw [lintegral_poissonTupleMeasure W (fun x ↦ ENNReal.ofReal (z ^ x.card))]
  let C := max 1 z
  have hC : 1 ≤ C := le_max_left _ _
  refine poissonIntegral_lt_top_of_pow hW (C := ENNReal.ofReal C) ENNReal.ofReal_lt_top
    fun n x _ ↦ ?_
  rw [← ENNReal.ofReal_pow (zero_le_one.trans hC)]
  apply ENNReal.ofReal_le_ofReal
  have hx : (toConfig x).card ≤ n := by
    simpa only [toConfig_def, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := x))
  exact (pow_le_pow_left₀ hz.le (le_max_right _ _) _).trans (pow_le_pow_right₀ hC hx)

/-- With a measurable minorant of the activity weight as reference density, the moments
of the exponential energy tilt give the unnormalized Gibbs moments. -/
private lemma lintegral_energy_tilt {W : Set E} {H : Finset E → ℝ} (hHm : IsConfigMeasurable H)
    (hH0 : ∀ x, 0 ≤ H x) {z : ℝ} {ρ : ConfigTuples E → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : ∀ a : ConfigTuples E → ℝ≥0∞, Measurable a → (∀ x, a x ≠ ∞) →
      (∫⁻ x, a x * ρ x ∂poissonTupleMeasure W) =
        ∫⁻ x, a x * ENNReal.ofReal (z ^ (tupleConfig x).card) ∂poissonTupleMeasure W)
    (t : ℝ) (k : ℕ) :
    (∫⁻ x, ENNReal.ofReal (tiltKernel (fun _ ↦ 0) (fun y ↦ H (tupleConfig y)) t k x)
      ∂(poissonTupleMeasure W).withDensity ρ) =
      poissonIntegral W (fun x ↦ ENNReal.ofReal (H x ^ k *
        (z ^ x.card * gibbsWeight (-t) (fun y ↦ (H y : WithTop ℝ)) x))) := by
  have hv := measurable_tupleConfig hHm
  let a x := ENNReal.ofReal (tiltKernel (fun _ ↦ 0) (fun y ↦ H (tupleConfig y)) t k x)
  have hm : Measurable a :=
    ((hv.pow_const k).mul ((measurable_const.add
      ((measurable_const (a := t)).mul hv)).exp)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hρm hm]
  have he := hρ a hm fun _ ↦ ENNReal.ofReal_ne_top
  simp only [Pi.mul_apply, mul_comm (ρ _)]
  rw [he]
  have hprod (x : ConfigTuples E) : a x * ENNReal.ofReal (z ^ (tupleConfig x).card) =
      ENNReal.ofReal (H (tupleConfig x) ^ k * (z ^ (tupleConfig x).card *
        gibbsWeight (-t) (fun y ↦ (H y : WithTop ℝ)) (tupleConfig x))) := by
    simp only [a, tiltKernel, zero_add, ← ENNReal.ofReal_mul
      (mul_nonneg (pow_nonneg (hH0 _) _) (Real.exp_nonneg _)), gibbsWeight_of_real, neg_neg]
    congr 1
    ring
  simp_rw [hprod]
  exact lintegral_poissonTupleMeasure W (fun x ↦ ENNReal.ofReal
    (H x ^ k * (z ^ x.card * gibbsWeight (-t) (fun y ↦ (H y : WithTop ℝ)) x)))

/-- SYNOPSIS item 99: `d/dβ E H = -Var(H)` under `P^{z,β}_Λ`, for a nonnegative energy. -/
theorem hasDerivAt_gibbs_meanEnergy {Λ : Set E} (hΛ : volume Λ < ∞) {H : Finset E → ℝ}
    (hH0 : ∀ x, 0 ≤ H x) (hHm : IsConfigMeasurable H) {z β : ℝ} (hz : 0 < z) (hβ : 0 < β) :
    let Hw : Finset E → WithTop ℝ := fun x ↦ (H x : WithTop ℝ)
    let moment : ℝ → (Finset E → ℝ) → ℝ := fun β k ↦
      (poissonIntegral Λ (fun x ↦ ENNReal.ofReal (k x * gibbsDensity Λ z β Hw x))).toReal
    HasDerivAt (fun β ↦ moment β H) (-(moment β (fun x ↦ H x ^ 2) - (moment β H) ^ 2)) β := by
  dsimp only
  obtain ⟨ρ, hρm, hρ⟩ := exists_measurable_minorant_lintegral_mul_eq
    (fun x : ConfigTuples E ↦ ENNReal.ofReal (z ^ (tupleConfig x).card))
    (lintegral_activity_lt_top hΛ hz).ne
  let ν := (poissonTupleMeasure Λ).withDensity ρ
  let a : ConfigTuples E → ℝ := fun _ ↦ 0
  let v : ConfigTuples E → ℝ := fun x ↦ H (tupleConfig x)
  let M t k := ∫ x, tiltKernel a v t k x ∂ν
  have hv : Measurable v := measurable_tupleConfig hHm
  have hvs : ∀ x, 0 ≤ v x := fun x ↦ hH0 (tupleConfig x)
  have hs : ∃ A : ℝ, ∀ x, A * x.card ≤ H x := ⟨0, by simpa using hH0⟩
  have hlin := lintegral_energy_tilt hHm hH0 hρm hρ
  have hMoment (t : ℝ) (k : ℕ) :
      M t k = (poissonIntegral Λ (fun x ↦ ENNReal.ofReal
        (H x ^ k * (z ^ x.card * gibbsWeight (-t) (fun y ↦ (H y : WithTop ℝ)) x)))).toReal := by
    have hm : Measurable (tiltKernel a v t k) :=
      (hv.pow_const k).mul ((measurable_const.add ((measurable_const (a := t)).mul hv)).exp)
    dsimp only [M]
    have hn : 0 ≤ᵐ[ν] tiltKernel a v t k := Eventually.of_forall fun x ↦
      mul_nonneg (pow_nonneg (hvs x) _) (Real.exp_nonneg _)
    rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
    exact congrArg ENNReal.toReal (hlin t k)
  have hZ (t : ℝ) :
      M t 0 = (partitionFunction Λ z (-t) (fun y ↦ (H y : WithTop ℝ))).toReal := by
    simp only [hMoment, pow_zero, one_mul, partitionFunction_def]
  have hpos {q : ℝ} (hq : 0 < q) : 0 < M (-q) 0 := by
    rw [hZ, neg_neg]
    obtain ⟨h0, hfin⟩ := partitionFunction_of_real_pos_lt_top hΛ hs hHm hz hq.le
    exact ENNReal.toReal_pos h0.ne' hfin.ne
  have hmom {q : ℝ} (hq : 0 < q) (k : ℕ) :
      (poissonIntegral Λ (fun x ↦ ENNReal.ofReal (H x ^ k *
        gibbsDensity Λ z q (fun y ↦ (H y : WithTop ℝ)) x))).toReal = M (-q) k / M (-q) 0 := by
    have hq0 := hpos hq
    rw [hZ, neg_neg] at hq0
    simp_rw [hMoment (-q) k, hZ, neg_neg, poissonIntegral_gibbsDensity _ _ _ _ _ hq0]
  let b := -β / 2
  have hb : Integrable (fun x ↦ Real.exp (a x + b * v x)) ν := by
    have hm : Measurable (fun x ↦ Real.exp (a x + b * v x)) :=
      (measurable_const.add ((measurable_const (a := b)).mul hv)).exp
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall fun _ ↦ Real.exp_nonneg _)).mp
    have he := hlin b 0
    simp only [tiltKernel, pow_zero, one_mul, ← partitionFunction_def] at he
    have hfin := (partitionFunction_of_real_pos_lt_top hΛ hs hHm hz (show 0 ≤ -b by
      dsimp only [b]; linarith)).2.ne
    exact he.trans_ne hfin
  have hd : HasDerivAt (fun t ↦ M t 1 / M t 0)
      (M (-β) 2 / M (-β) 0 - (M (-β) 1 / M (-β) 0) ^ 2) (-β) :=
    hasDerivAt_tilt_mean measurable_const hv hvs (show -β < b by dsimp only [b]; linarith) hb
      (hpos hβ).ne'
  have he := hd.comp β (hasDerivAt_id β).neg
  simp only [mul_neg_one, ← hmom hβ 2, ← hmom hβ 1, pow_one] at he
  refine he.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hβ] with q hq
  simpa only [Function.comp_apply, id_eq, pow_one] using hmom hq 1

/-! ### Markov point processes (SYNOPSIS item 97) -/

section Markov

variable {W : Type*} [DecidableEq W]

/-- A **clique** for the relation `r`: its points are pairwise related. -/
def IsConfigClique (r : W → W → Prop) (y : Finset W) : Prop :=
  ∀ ξ ∈ y, ∀ η ∈ y, r ξ η

/-- A hereditary `h ≥ 0` is a **Markov function** for `r` when, for `h(x) > 0` and `ξ ∉ x`, the
ratio `h(x ∪ {ξ}) / h(x)` depends on `x` only through its points related to `ξ`. -/
def IsMarkovFunction (r : W → W → Prop) [DecidableRel r] (h : Finset W → ℝ) : Prop :=
  (∀ x y, y ⊆ x → 0 < h x → 0 < h y) ∧
    ∀ x ξ, 0 < h x → ξ ∉ x →
      h (insert ξ x) / h x = h (insert ξ (x.filter (r ξ))) / h (x.filter (r ξ))

omit [DecidableEq W] in
lemma isConfigClique_def {r : W → W → Prop} {y : Finset W} :
    IsConfigClique r y ↔ ∀ ξ ∈ y, ∀ η ∈ y, r ξ η := Iff.rfl

lemma isMarkovFunction_def {r : W → W → Prop} [DecidableRel r] {h : Finset W → ℝ} :
    IsMarkovFunction r h ↔ (∀ x y, y ⊆ x → 0 < h x → 0 < h y) ∧
      ∀ x ξ, 0 < h x → ξ ∉ x →
        h (insert ξ x) / h x = h (insert ξ (x.filter (r ξ))) / h (x.filter (r ξ)) := Iff.rfl

/-- Adding a site leaves only the factors supported by its neighbours in the insertion product. -/
private lemma clique_prod_filter {r : W → W → Prop} [DecidableRel r] {φ : Finset W → ℝ}
    (hφ : ∀ y, ¬ IsConfigClique r y → φ y = 1) (x : Finset W) (ξ : W) :
    (∏ y ∈ x.powerset, φ (insert ξ y)) = ∏ y ∈ (x.filter (r ξ)).powerset, φ (insert ξ y) := by
  classical
  refine (Finset.prod_subset (Finset.powerset_mono.mpr (Finset.filter_subset _ _))
    (fun y hy hnf ↦ hφ _ fun hc ↦ ?_)).symm
  apply hnf
  refine Finset.mem_powerset.2 fun z hz ↦ Finset.mem_filter.2 ⟨Finset.mem_powerset.mp hy hz, ?_⟩
  exact hc ξ (Finset.mem_insert_self _ _) z (Finset.mem_insert_of_mem hz)

/-- On a clique the potential is the ratio to the product of the potentials of proper subsets.
If a proper subset already has zero potential, its supersets need no further zero factor. -/
private def markovPotential (r : W → W → Prop) (f : Finset W → ℝ) (x : Finset W) : ℝ := by
  classical
  exact x.strongInductionOn fun s rec ↦
    if IsConfigClique r s then
      let q := ∏ y ∈ (s.powerset.erase s).attach, rec y.1 (ssubset_of_subset_of_ne
        (Finset.mem_powerset.mp (Finset.mem_erase.mp y.2).2) (Finset.mem_erase.mp y.2).1)
      if q = 0 then 1 else f s / q
    else 1

open scoped Classical in
/-- The potential depends on the density and the factors of proper subsets. -/
private lemma markovPotential_def (r : W → W → Prop) (f : Finset W → ℝ) (x : Finset W) :
    markovPotential r f x =
      if IsConfigClique r x then
        let q := ∏ y ∈ x.powerset.erase x, markovPotential r f y
        if q = 0 then 1 else f x / q
      else 1 := by
  classical
  nth_rw 1 [markovPotential, Finset.strongInductionOn_eq]
  -- Each recursion value is the potential of the attached proper subset.
  change (if IsConfigClique r x then
    let q := ∏ y ∈ (x.powerset.erase x).attach, markovPotential r f y.1
    if q = 0 then 1 else f x / q
    else 1) = _
  rw [Finset.prod_attach]

/-- The recursively constructed potential is trivial away from cliques. -/
private lemma markovPotential_eq_one {r : W → W → Prop} (f : Finset W → ℝ)
    {x : Finset W} (hx : ¬ IsConfigClique r x) : markovPotential r f x = 1 := by
  rw [markovPotential_def, ite_eq_right hx]

/-- The recursive quotient of nonnegative weights gives nonnegative potentials. -/
private lemma markovPotential_nonneg (r : W → W → Prop) {f : Finset W → ℝ}
    (h0 : ∀ x, 0 ≤ f x) (x : Finset W) : 0 ≤ markovPotential r f x := by
  classical
  induction x using Finset.strongInductionOn with
  | _ x ih =>
    rw [markovPotential_def]
    by_cases hc : IsConfigClique r x
    · rw [ite_eq_left hc]
      dsimp only
      split_ifs
      · exact zero_le_one
      · apply div_nonneg (h0 x)
        apply Finset.prod_nonneg fun y hy ↦ ih y ?_
        obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
        exact ssubset_of_subset_of_ne (Finset.mem_powerset.mp hy) hne
    · rw [ite_eq_right hc]
      exact zero_le_one

/-- If a nonclique's proper subconfigurations have positive densities, the Markov property
recovers its density from the factors already determined on those subconfigurations. -/
private lemma markovPotential_nonclique_prod {r : W → W → Prop} [DecidableRel r]
    (hrefl : ∀ ξ, r ξ ξ) {f : Finset W → ℝ} (hf : IsMarkovFunction r f) (x : Finset W)
    (hcl : ¬ IsConfigClique r x) (hpos : ∀ y ⊂ x, 0 < f y)
    (ih : ∀ y ⊂ x, f y = ∏ z ∈ y.powerset, markovPotential r f z) :
    f x = ∏ z ∈ x.powerset, markovPotential r f z := by
  have hn := hcl
  rw [isConfigClique_def] at hn
  push Not at hn
  obtain ⟨ξ, hξ, η, hη, hrel⟩ := hn
  have hne : η ≠ ξ := fun h ↦ hrel (h ▸ hrefl ξ)
  let a := x.erase ξ
  let b := a.filter (r ξ)
  have ha : a ⊂ x := Finset.erase_ssubset hξ
  have hb : b ⊂ x := lt_of_le_of_lt (Finset.filter_subset _ _) ha
  have hξa : ξ ∉ a := Finset.notMem_erase _ _
  have hξb : ξ ∉ b := fun h ↦ hξa (Finset.filter_subset _ _ h)
  have hxa : insert ξ a = x := Finset.insert_erase hξ
  have hxb : insert ξ b ⊂ x := by
    refine ssubset_of_subset_of_ne (hxa ▸ Finset.insert_subset_insert ξ (Finset.filter_subset _ _))
      fun h ↦ ?_
    have hηb : η ∈ insert ξ b := h.symm ▸ hη
    exact hrel (Finset.mem_filter.mp ((Finset.mem_insert.mp hηb).resolve_left hne)).2
  have hA := hpos a ha
  have hB := hpos b hb
  have hr := hf.2 a ξ hA hξa
  have hprod :
      (∏ z ∈ x.powerset, markovPotential r f z) = f a * (f (insert ξ b) / f b) := by
    calc
      _ = (∏ z ∈ a.powerset, markovPotential r f z) *
          ∏ z ∈ a.powerset, markovPotential r f (insert ξ z) := by
        rw [← hxa, Finset.prod_powerset_insert hξa]
      _ = f a * ∏ z ∈ b.powerset, markovPotential r f (insert ξ z) := by
        rw [← ih a ha, clique_prod_filter (fun y ↦ markovPotential_eq_one f) a ξ]
      _ = _ := by
        congr 1
        rw [ih (insert ξ b) hxb, Finset.prod_powerset_insert hξb, ← ih b hb]
        exact (mul_div_cancel_left₀ _ hB.ne').symm
  rw [hprod, ← hr, hxa]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hA.ne']

/-- The product of the recursive potentials equals the original Markov weight. -/
private lemma markovPotential_prod {r : W → W → Prop} [DecidableRel r] (hrefl : ∀ ξ, r ξ ξ)
    {f : Finset W → ℝ} (h0 : ∀ x, 0 ≤ f x) (hf : IsMarkovFunction r f) (x : Finset W) :
    f x = ∏ z ∈ x.powerset, markovPotential r f z := by
  classical
  induction x using Finset.strongInductionOn with
  | _ x ih =>
    let φ := markovPotential r f
    let q := ∏ y ∈ x.powerset.erase x, φ y
    have hprod : q * φ x = ∏ y ∈ x.powerset, φ y :=
      Finset.prod_erase_mul _ _ (Finset.mem_powerset.mpr (Finset.Subset.refl x))
    by_cases hq : q = 0
    · obtain ⟨y, hy, hy0⟩ := Finset.prod_eq_zero_iff.mp hq
      obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hy
      have hypos : ¬ 0 < f y := by
        rw [ih y (ssubset_of_subset_of_ne (Finset.mem_powerset.mp hsub) hne)]
        rw [Finset.prod_eq_zero (Finset.mem_powerset.mpr (Finset.Subset.refl y)) hy0]
        exact lt_irrefl _
      rw [← hprod, hq, zero_mul]
      exact le_antisymm (le_of_not_gt fun hp ↦ hypos (hf.1 _ _ (Finset.mem_powerset.mp hsub) hp))
        (h0 x)
    by_cases hc : IsConfigClique r x
    · rw [← hprod]
      have hφx : φ x = f x / q := by
        dsimp only [φ]
        rw [markovPotential_def, ite_eq_left hc, ite_eq_right hq]
      rw [hφx, ← mul_div_assoc, mul_div_cancel_left₀ _ hq]
    apply markovPotential_nonclique_prod hrefl hf x hc _ ih
    intro y hy
    have hfy : f y ≠ 0 := by
      rw [ih y hy]
      apply Finset.prod_ne_zero_iff.mpr
      intro z hz hz0
      have hzx := lt_of_le_of_lt (Finset.mem_powerset.mp hz) hy
      exact hq (Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨ne_of_lt hzx, Finset.mem_powerset.mpr hzx.le⟩) hz0)
    exact (h0 y).lt_of_ne hfy.symm

/-- SYNOPSIS item 97: for such a factorisation and `h(x) > 0`,
`λ*(x, ξ) = ∏_{y ⊆ x} φ(y ∪ {ξ})`. -/
theorem papangelou_markov (r : W → W → Prop) [DecidableRel r] {h φ : Finset W → ℝ}
    (hφ : ∀ x, h x = ∏ y ∈ x.powerset, φ y) {x : Finset W} {ξ : W} (hx : 0 < h x)
    (hξ : ξ ∉ x) : h (insert ξ x) / h x = ∏ y ∈ x.powerset, φ (insert ξ y) := by
  calc
    h (insert ξ x) / h x =
        ((∏ y ∈ x.powerset, φ y) * ∏ y ∈ x.powerset, φ (insert ξ y)) / h x := by
      rw [hφ (insert ξ x), Finset.prod_powerset_insert hξ]
    _ = ∏ y ∈ x.powerset, φ (insert ξ y) := by
      rw [← hφ x]
      exact mul_div_cancel_left₀ _ hx.ne'

-- Retain the symmetric neighbourhood assumption of the Markov point-process model.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 97, Hammersley–Clifford–Ripley–Kelly theorem: for a reflexive symmetric
relation, a hereditary `h ≥ 0` is a Markov function if and only if
`h(x) = ∏_{y ⊆ x} φ(y)` for some `φ ≥ 0` with `φ(y) = 1` whenever `y` is not a clique. -/
theorem isMarkovFunction_iff (r : W → W → Prop) [DecidableRel r] (hrefl : ∀ ξ, r ξ ξ)
    (hsymm : ∀ ξ η, r ξ η → r η ξ) {h : Finset W → ℝ} (h0 : ∀ x, 0 ≤ h x)
    (hher : ∀ x y, y ⊆ x → 0 < h x → 0 < h y) :
    IsMarkovFunction r h ↔ ∃ φ : Finset W → ℝ, (∀ y, 0 ≤ φ y) ∧
      (∀ y, ¬ IsConfigClique r y → φ y = 1) ∧ ∀ x, h x = ∏ y ∈ x.powerset, φ y := by
  constructor
  · intro hf
    exact ⟨markovPotential r h, markovPotential_nonneg r h0, fun _ ↦ markovPotential_eq_one h,
      markovPotential_prod hrefl h0 hf⟩
  · rintro ⟨φ, _, hcl, hφ⟩
    refine ⟨hher, fun x ξ hx hξ ↦ ?_⟩
    have hxf : 0 < h (x.filter (r ξ)) := hher _ _ (Finset.filter_subset _ _) hx
    have hξf : ξ ∉ x.filter (r ξ) := fun h ↦ hξ (Finset.filter_subset _ _ h)
    rw [papangelou_markov r hφ hx hξ, papangelou_markov r hφ hxf hξf, clique_prod_filter hcl]

/-- Two sets of unrelated points can be inserted independently over a common configuration. -/
private lemma markov_separated_product {r : W → W → Prop} [DecidableRel r]
    {f : Finset W → ℝ} (h0 : ∀ x, 0 ≤ f x) (hf : IsMarkovFunction r f)
    (a b c : Finset W) (hd : Disjoint b (a ∪ c))
    (hrel : ∀ ξ ∈ b, ∀ η ∈ a, ¬ r ξ η) :
    f (a ∪ (b ∪ c)) * f c = f (a ∪ c) * f (b ∪ c) := by
  induction b using Finset.induction_on with
  | empty => simp
  | @insert ξ b hξ ih =>
    have hd' : Disjoint b (a ∪ c) := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hd
    have he : ξ ∉ a ∪ (b ∪ c) := by
      intro hh
      have hh' : ξ ∈ a ∪ c := by simpa only [Finset.mem_union, hξ, false_or] using hh
      exact Finset.disjoint_left.mp hd (Finset.mem_insert_self _ _) hh'
    have hes : ξ ∉ b ∪ c := fun h ↦ he (Finset.mem_union_right _ h)
    have hn : (a ∪ (b ∪ c)).filter (r ξ) = (b ∪ c).filter (r ξ) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨ha | hb, hr⟩
        · exact (hrel ξ (Finset.mem_insert_self _ _) z ha hr).elim
        · exact ⟨hb, hr⟩
      · exact fun ⟨hb, hr⟩ ↦ ⟨Or.inr hb, hr⟩
    have hi := ih hd' (fun z hz ↦ hrel z (Finset.mem_insert_of_mem hz))
    simp only [Finset.insert_union, Finset.union_insert]
    by_cases hp : 0 < f (a ∪ (b ∪ c))
    · have hs : 0 < f (b ∪ c) := hf.1 _ _ Finset.subset_union_right hp
      have hr := (hf.2 _ ξ hp he).trans (by rw [hn, ← hf.2 _ ξ hs hes])
      calc
        f (insert ξ (a ∪ (b ∪ c))) * f c =
            (f (insert ξ (a ∪ (b ∪ c))) / f (a ∪ (b ∪ c))) *
              (f (a ∪ (b ∪ c)) * f c) := by field_simp
        _ = (f (insert ξ (b ∪ c)) / f (b ∪ c)) * (f (a ∪ c) * f (b ∪ c)) := by
          rw [hi, hr]
        _ = _ := by field_simp
    · have hz : f (a ∪ (b ∪ c)) = 0 := le_antisymm (le_of_not_gt hp) (h0 _)
      have hz' : f (insert ξ (a ∪ (b ∪ c))) = 0 := by
        refine le_antisymm (le_of_not_gt fun h ↦ hp ?_) (h0 _)
        exact hf.1 _ _ (Finset.subset_insert _ _) h
      rw [hz, zero_mul, eq_comm, mul_eq_zero] at hi
      rw [hz', zero_mul, eq_comm, mul_eq_zero]
      refine hi.imp id fun h ↦ le_antisymm (le_of_not_gt fun h' ↦ ?_) (h0 _)
      exact (hf.1 _ _ (Finset.subset_insert _ _) h').ne' h

-- The separator identity uses the same reflexive symmetric relation as the clique theorem.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 97: if no point of `A` is related to a point of `B`, a Markov density
factorises as `f(x) = g(x ∩ (A ∪ C)) k(x ∩ (B ∪ C))` with `C` the complement of `A ∪ B`; for
densities with respect to the Poisson process this is the conditional independence of `X_A` and
`X_B` given `X_C`. -/
theorem markov_density_factorization (r : W → W → Prop) [DecidableRel r] (hrefl : ∀ ξ, r ξ ξ)
    (hsymm : ∀ ξ η, r ξ η → r η ξ) {f : Finset W → ℝ} (h0 : ∀ x, 0 ≤ f x)
    (hf : IsMarkovFunction r f) {A B : Set W} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hAB : Disjoint A B) (hrel : ∀ a ∈ A, ∀ b ∈ B, ¬ r a b) :
    ∃ g k : Finset W → ℝ, ∀ x, f x = g (x.filter (· ∉ B)) * k (x.filter (· ∉ A)) := by
  refine ⟨f, fun y ↦ f y / f (y.filter (· ∉ B)), fun x ↦ ?_⟩
  dsimp only
  let a := x.filter (· ∈ A)
  let b := x.filter (· ∈ B)
  let c := (x.filter (· ∉ A)).filter (· ∉ B)
  have ha : a ∪ c = x.filter (· ∉ B) := by
    ext z
    simp only [a, c, Finset.mem_union, Finset.mem_filter]
    by_cases hz : z ∈ A
    · simp only [hz, and_true, not_true_eq_false, and_false, false_and, or_false]
      exact ⟨fun hx ↦ ⟨hx, Set.disjoint_left.mp hAB hz⟩, And.left⟩
    · simp only [hz, and_false, not_false_eq_true, and_true, false_or]
  have hb : b ∪ c = x.filter (· ∉ A) := by
    ext z
    simp only [b, c, Finset.mem_union, Finset.mem_filter]
    by_cases hz : z ∈ B
    · simp only [hz, and_true, not_true_eq_false, and_false, or_false]
      exact ⟨fun hx ↦ ⟨hx, fun h ↦ Set.disjoint_left.mp hAB h hz⟩, And.left⟩
    · simp only [hz, and_false, not_false_eq_true, and_true, false_or]
  have hx : a ∪ (b ∪ c) = x := by
    rw [hb]
    exact Finset.filter_union_filter_not_eq _ _
  have hd : Disjoint b (a ∪ c) := by
    rw [ha]
    exact Finset.disjoint_filter_filter_not _ _ _
  have hbc : ∀ ξ ∈ b, ∀ η ∈ a, ¬ r ξ η :=
    fun ξ hξ η hη hr ↦
      hrel η (Finset.mem_filter.mp hη).2 ξ (Finset.mem_filter.mp hξ).2 (hsymm _ _ hr)
  have hp := markov_separated_product h0 hf a b c hd hbc
  rw [hx, ha, hb] at hp
  by_cases hc : f c = 0
  · have hsub : c ⊆ x := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hzero : f x = 0 :=
      le_antisymm (le_of_not_gt fun hf' ↦ (hf.1 _ _ hsub hf').ne' hc) (h0 _)
    rw [hzero, hc, div_zero, mul_zero]
  · calc
      _ = (f x * f c) / f c := (mul_div_cancel_right₀ _ hc).symm
      _ = _ := by rw [hp, mul_div_assoc]

end Markov

/-! ### The Strauss process (SYNOPSIS item 98) -/

section Strauss

variable {F : Type*} [NormedAddCommGroup F] [MeasureSpace F] [DecidableEq F]

/-- The **Strauss** function `h(x) = β^{n(x)} γ^{s_R(x)}`, with `s_R(x)` the number of pairs of
points at distance at most `R` and `0⁰ = 1`. -/
def straussDensity (β γ R : ℝ) (x : Finset F) : ℝ :=
  β ^ x.card * γ ^ ((x.offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R).card / 2)

omit [MeasureSpace F] [DecidableEq F] in
lemma straussDensity_def (β γ R : ℝ) (x : Finset F) : straussDensity β γ R x =
    β ^ x.card * γ ^ ((x.offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R).card / 2) := by
  rw [straussDensity]

omit [MeasureSpace F] in
/-- Adding a site increases the number of unordered neighbouring pairs by its neighbours. -/
private lemma strauss_pairCount_insert (R : ℝ) (x : Finset F) {ξ : F} (hξ : ξ ∉ x) :
    ((insert ξ x).offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R).card / 2 =
      (x.offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R).card / 2 +
        (x.filter fun η ↦ ‖ξ - η‖ ≤ R).card := by
  classical
  let p : F × F → Prop := fun q ↦ ‖q.1 - q.2‖ ≤ R
  let s := x.filter fun η ↦ ‖ξ - η‖ ≤ R
  let l : F ↪ F × F := ⟨fun η ↦ (ξ, η), fun _ _ h ↦ congrArg Prod.snd h⟩
  let r : F ↪ F × F := ⟨fun η ↦ (η, ξ), fun _ _ h ↦ congrArg Prod.fst h⟩
  have hL : (({ξ} : Finset F) ×ˢ x).filter p = s.map l := by
    ext q
    rcases q with ⟨a, b⟩
    simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_map]
    constructor
    · rintro ⟨⟨rfl, hb⟩, hab⟩
      exact ⟨b, ⟨hb, hab⟩, rfl⟩
    · rintro ⟨c, hc, he⟩
      have ha : ξ = a := congrArg Prod.fst he
      have hb : c = b := congrArg Prod.snd he
      subst a b
      exact ⟨⟨rfl, hc.1⟩, hc.2⟩
  have hR : (x ×ˢ ({ξ} : Finset F)).filter p = s.map r := by
    ext q
    rcases q with ⟨a, b⟩
    simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_map]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      subst b
      have hp' : ‖a - ξ‖ ≤ R := hab
      rw [norm_sub_rev] at hp'
      exact ⟨a, ⟨ha, hp'⟩, rfl⟩
    · rintro ⟨c, hc, he⟩
      have ha : c = a := congrArg Prod.fst he
      have hb : ξ = b := congrArg Prod.snd he
      subst a b
      have hp' : ‖ξ - c‖ ≤ R := hc.2
      rw [norm_sub_rev] at hp'
      exact ⟨⟨hc.1, rfl⟩, hp'⟩
  have hdL : Disjoint (x.offDiag.filter p) ((({ξ} : Finset F) ×ˢ x).filter p) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
      Finset.mem_singleton]
    rintro ⟨a, b⟩ ⟨⟨ha, _, _⟩, _⟩ ⟨⟨he, _⟩, _⟩
    exact hξ (he ▸ ha)
  have hdR : Disjoint (x.offDiag.filter p ∪ (({ξ} : Finset F) ×ˢ x).filter p)
      ((x ×ˢ ({ξ} : Finset F)).filter p) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_union]
    rintro ⟨a, b⟩ (⟨⟨_, hb, _⟩, _⟩ | ⟨⟨he, _⟩, _⟩) ⟨⟨ha, hb'⟩, _⟩
    · exact hξ (hb' ▸ hb)
    · exact hξ (he ▸ ha)
  have hcard :
      ((insert ξ x).offDiag.filter fun q ↦ ‖q.1 - q.2‖ ≤ R).card =
        (x.offDiag.filter p).card + s.card + s.card := by
    rw [Finset.offDiag_insert hξ, Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint hdR, Finset.card_union_of_disjoint hdL, hL, hR,
      Finset.card_map, Finset.card_map]
  dsimp only [p, s] at hcard
  rw [hcard]
  omega

omit [MeasureSpace F] in
/-- Adding a site multiplies the Strauss weight by the birth factor. -/
private lemma straussDensity_insert (β γ R : ℝ) (x : Finset F) {ξ : F} (hξ : ξ ∉ x) :
    straussDensity β γ R (insert ξ x) =
      β * γ ^ (x.filter fun η ↦ ‖ξ - η‖ ≤ R).card * straussDensity β γ R x := by
  rw [straussDensity_def, straussDensity_def, Finset.card_insert_of_notMem hξ,
    strauss_pairCount_insert R x hξ, pow_succ, pow_add]
  ring

-- Retain the positive interaction range of the Strauss model.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 98: for `γ ≤ 1` the Strauss function is locally stable with `φ* ≡ β`, hence
normalisable, and Markov for `‖ξ - η‖ ≤ R` with
`λ*(x, ξ) = β γ^{#{η ∈ x : ‖ξ - η‖ ≤ R}}`. -/
theorem strauss_properties {W : Set F} (hW : volume W < ∞) {β γ R : ℝ} (hβ : 0 < β)
    (hR : 0 < R) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsLocallyStable W (fun _ ↦ β) (straussDensity β γ R) ∧
      poissonIntegral W (fun x ↦ ENNReal.ofReal (straussDensity β γ R x)) < ∞ ∧
      IsMarkovFunction (fun ξ η : F ↦ ‖ξ - η‖ ≤ R) (straussDensity β γ R) ∧
      ∀ x : Finset F, ∀ ξ ∉ x, 0 < straussDensity β γ R x →
        papangelou (straussDensity β γ R) x ξ =
          β * γ ^ (x.filter fun η ↦ ‖ξ - η‖ ≤ R).card := by
  let f : Finset F → ℝ := straussDensity β γ R
  have h0 (x : Finset F) : 0 ≤ f x := by
    dsimp only [f]
    rw [straussDensity_def]
    positivity
  have hls (U : Set F) : IsLocallyStable U (fun _ ↦ β) f := by
    rw [isLocallyStable_def]
    intro x _ ξ _ hξ
    dsimp only [f]
    rw [straussDensity_insert β γ R x hξ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hβ.le (pow_le_one₀ hγ0 hγ1)) (h0 x)
  have hint : IntegrableOn (fun _ : F ↦ β) W := by
    let : IsFiniteMeasure ((volume : Measure F).restrict W) :=
      ⟨by rwa [Measure.restrict_apply_univ]⟩
    exact integrable_const _
  have hEmpty : 0 < f ∅ := by simp [f, straussDensity_def]
  have hher := (isLocallyStable_consequences (fun _ : F ↦ hβ.le) h0 (hls univ)).2.1
  have hp (x : Finset F) (ξ : F) (hx : 0 < f x) (hξ : ξ ∉ x) :
      papangelou f x ξ = β * γ ^ (x.filter fun y ↦ ‖ξ - y‖ ≤ R).card := by
    dsimp only [f] at hx ⊢
    rw [papangelou_def, ite_eq_right hx.ne', straussDensity_insert β γ R x hξ,
      mul_div_cancel_right₀ _ hx.ne']
  refine ⟨hls W, (normalisable_of_locallyStable hW (fun _ ↦ hβ.le) hint h0 (hls W) hEmpty).2,
    ⟨fun x y hxy hx ↦ hher x y (subset_univ _) hxy hx, ?_⟩,
    fun x ξ hξ hx ↦ hp x ξ hx hξ⟩
  intro x ξ hx hξ
  let y := x.filter fun η ↦ ‖ξ - η‖ ≤ R
  have hsub : y ⊆ x := Finset.filter_subset _ _
  have hy : 0 < f y := hher x y (subset_univ _) hsub hx
  have hξ' : ξ ∉ y := fun h ↦ hξ (hsub h)
  have hratio x ξ (hx : 0 < f x) : f (insert ξ x) / f x = papangelou f x ξ := by
    rw [papangelou_def, ite_eq_right hx.ne']
  rw [hratio x ξ hx, hratio y ξ hy, hp x ξ hx hξ, hp y ξ hy hξ']
  simp only [y, Finset.filter_filter, and_self]

/-- A positive-volume measurable set in a separable metric space contains a positive-volume
part inside an arbitrarily small ball. -/
lemma exists_pos_measure_inter_ball {X : Type*} [MetricSpace X] [SeparableSpace X]
    [MeasurableSpace X] {μ : Measure X} {W : Set X} (hW : 0 < μ W)
    {r : ℝ} (hr : 0 < r) :
    ∃ a : X, 0 < μ (W ∩ Metric.ball a r) := by
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense X
  have : Countable D := hD.to_subtype
  have hcov : W = ⋃ a : D, W ∩ Metric.ball (a : X) r := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun _ ↦ inter_subset_left)
    intro x hx
    obtain ⟨a, ha, hdist⟩ := hd.exists_dist_lt x hr
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hx, hdist⟩
  by_contra! h
  apply hW.ne'
  rw [hcov, measure_iUnion_null_iff]
  exact fun a ↦ le_antisymm (h a) zero_le

/-- A weight with a quadratic exponent of base greater than one outgrows the Poisson factorial
term, for any positive activity. -/
lemma tsum_ofReal_mul_pow_quadratic_div_factorial_eq_top {C a γ : ℝ}
    (hC : 0 < C) (ha : 0 < a) (hγ : 1 < γ) :
    ∑' n : ℕ, ENNReal.ofReal (C * a ^ n * γ ^ ((n * n - n) / 2) / n.factorial) = ⊤ := by
  let f (n : ℕ) := C * a ^ n * γ ^ ((n * n - n) / 2) / n.factorial
  have hγ0 : 0 < γ := zero_lt_one.trans hγ
  have hpos (n : ℕ) : 0 < f n :=
    div_pos (mul_pos (mul_pos hC (pow_pos ha _)) (pow_pos hγ0 _))
      (Nat.cast_pos.mpr (Nat.factorial_pos _))
  have hstep (n : ℕ) : f (n + 1) * (↑n + 1) = (a * γ ^ n) * f n := by
    have he : ((n + 1) * (n + 1) - (n + 1)) / 2 = (n * n - n) / 2 + n := by
      have hn : n ≤ n * n := Nat.le_mul_self n
      have hh : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
      omega
    have hfac : (n.factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
    dsimp only [f]
    rw [he, pow_add, pow_succ a, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring
  have hlim : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / γ ^ n) atTop (𝓝 0) := by
    have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hγ
    have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hγ
    simpa only [pow_one, pow_zero, ← add_div, add_zero] using h₁.add h₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const ha)
  have hmono (n : ℕ) (hn : N ≤ n) : f n ≤ f (n + 1) := by
    have hr := (div_lt_iff₀ (pow_pos hγ0 n)).mp (hN n hn)
    have hh := mul_le_mul_of_nonneg_right hr.le (hpos n).le
    rw [← hstep] at hh
    exact le_of_mul_le_mul_right ((le_of_eq (mul_comm _ _)).trans hh) (by positivity)
  by_contra hfinite
  have hsum₀ := ENNReal.summable_toReal (f := fun n ↦ ENNReal.ofReal (f n)) hfinite
  have hsum : Summable f := by
    convert hsum₀ using 1
    ext n
    exact (ENNReal.toReal_ofReal (hpos n).le).symm
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hsum.tendsto_atTop_zero.eventually_lt_const (hpos N))
  have hge : ∀ k : ℕ, f N ≤ f (N + k) := by
    intro k
    induction k with
    | zero => simp only [add_zero, le_refl]
    | succ k ih =>
      exact ih.trans (hmono (N + k) (Nat.le_add_right N k))
  exact (hM (N + M) (Nat.le_add_left M N)).not_ge (hge M)

omit [MeasureSpace F] [DecidableEq F] in
/-- On configurations whose points are all at distance at most `R`, every unordered pair
contributes to the Strauss density. -/
lemma straussDensity_eq_of_pairwise_norm_sub_le (β γ R : ℝ) (x : Finset F)
    (h : ∀ u ∈ x, ∀ v ∈ x, ‖u - v‖ ≤ R) :
    straussDensity β γ R x = β ^ x.card * γ ^ ((x.card * x.card - x.card) / 2) := by
  have hfilter : (x.offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R) = x.offDiag := by
    exact Finset.filter_eq_self.mpr fun p hp ↦
      h p.1 (Finset.mem_offDiag.mp hp).1 p.2 (Finset.mem_offDiag.mp hp).2.1
  rw [straussDensity_def, hfilter, Finset.offDiag_card]

/-- SYNOPSIS item 98: for `γ > 1` the Strauss function is not integrable,
`∫ h dΠ_W = ∞`, on a diffuse window `W` of positive volume. -/
theorem strauss_not_normalisable [SeparableSpace F] [BorelSpace F]
    {W : Set F} [NullSingletonClass ((volume : Measure F).restrict W)]
    (hW : 0 < volume W) (hWf : volume W < ∞)
    (hWm : MeasurableSet W) {β γ R : ℝ} (hβ : 0 < β) (hR : 0 < R) (hγ : 1 < γ) :
    poissonIntegral W (fun x ↦ ENNReal.ofReal (straussDensity β γ R x)) = ∞ := by
  obtain ⟨a, ha⟩ := exists_pos_measure_inter_ball hW (half_pos hR)
  let S := W ∩ Metric.ball a (R / 2)
  have hSW : S ⊆ W := Set.inter_subset_left
  have hSf := (measure_mono hSW).trans_lt hWf
  have hSm : MeasurableSet S := hWm.inter Metric.isOpen_ball.measurableSet
  have hclose {u v : F} (hu : u ∈ S) (hv : v ∈ S) : ‖u - v‖ ≤ R := by
    rw [← dist_eq_norm]
    have ht := dist_triangle_right u v a
    have h₁ := Metric.mem_ball.mp hu.2
    have h₂ := Metric.mem_ball.mp hv.2
    linarith only [ht, h₁, h₂]
  let m := (volume S).toReal
  let C := Real.exp (-(volume W).toReal)
  have hm : 0 < m := ENNReal.toReal_pos ha.ne' hSf.ne
  have hC : 0 < C := Real.exp_pos _
  let ν := (volume : Measure F).restrict S
  have : NullSingletonClass ν := ⟨fun u ↦
    le_antisymm ((Measure.restrict_mono_set volume hSW {u}).trans_eq (measure_singleton u))
      zero_le⟩
  have : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hSf⟩
  apply top_unique
  calc
    ∞ = ∑' n : ℕ, ENNReal.ofReal (C * (β * m) ^ n *
        γ ^ ((n * n - n) / 2) / n.factorial) :=
      (tsum_ofReal_mul_pow_quadratic_div_factorial_eq_top hC (mul_pos hβ hm) hγ).symm
    _ ≤ _ := by
      rw [poissonIntegral_def]
      refine tsum_le_tsum fun n ↦ ?_
      let U : Set (Fin n → F) := Set.pi univ (fun _ ↦ S)
      let G : ℝ := β ^ n * γ ^ ((n * n - n) / 2)
      have hG : 0 ≤ G := mul_nonneg (pow_nonneg hβ.le _) (pow_nonneg (zero_lt_one.trans hγ).le _)
      have hval : ∀ᵐ x ∂(volume : Measure (Fin n → F)).restrict U,
          ENNReal.ofReal G = ENNReal.ofReal (straussDensity β γ R (toConfig x)) := by
        refine (ae_toConfig_subset_and_card hSf hSm n).mono fun x ⟨hcfg, hc⟩ ↦ ?_
        rw [straussDensity_eq_of_pairwise_norm_sub_le _ _ _ _
          (fun _ hu _ hv ↦ hclose (hcfg hu) (hcfg hv)), hc]
      have hsub : U ⊆ Set.pi univ (fun _ : Fin n ↦ W) := Set.pi_mono fun _ _ ↦ hSW
      have hmass : Measure.pi (fun _ : Fin n ↦ ν) univ = ENNReal.ofReal m ^ n := by
        rw [Measure.pi_univ]
        simp only [ν, Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, m, ENNReal.ofReal_toReal hSf.ne]
      refine le_trans ?_ (mul_le_mul_right (lintegral_mono_set hsub) _)
      rw [← lintegral_congr_ae hval, restrict_volume_pi_window hSf n, lintegral_const, hmass,
        ← ENNReal.ofReal_pow hm.le, ← ENNReal.ofReal_mul hG,
        ← ENNReal.ofReal_mul (div_nonneg hC.le (Nat.cast_nonneg _))]
      apply le_of_eq
      apply congrArg ENNReal.ofReal
      dsimp only [G]
      rw [mul_pow]
      ring

/-- SYNOPSIS item 98: for a fixed number `n` of points, the Strauss weight is
integrable for every `γ ≥ 0`. -/
theorem strauss_fixed_number_integrable {W : Set F} (hWf : volume W < ∞) {β γ R : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (n : ℕ) :
    ∫⁻ x in Set.pi univ (fun _ : Fin n ↦ W),
      ENNReal.ofReal (straussDensity β γ R (toConfig x)) < ∞ := by
  let b := max β 1
  let g := max γ 1
  have hb : 1 ≤ b := le_max_right _ _
  have hg : 1 ≤ g := le_max_right _ _
  have hbound (x : Fin n → F) :
      straussDensity β γ R (toConfig x) ≤ b ^ n * g ^ (n * n) := by
    have hc : (toConfig x).card ≤ n := by
      simpa only [toConfig_def, Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := Finset.univ) (f := x))
    have hsub : (toConfig x).offDiag ⊆ (toConfig x) ×ˢ (toConfig x) := by
      intro p hp
      obtain ⟨h₁, h₂, _⟩ := Finset.mem_offDiag.mp hp
      exact Finset.mem_product.mpr ⟨h₁, h₂⟩
    have hp : (((toConfig x).offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R).card / 2) ≤ n * n :=
      (Nat.div_le_self _ _).trans <| (Finset.card_filter_le _ _).trans <|
        (Finset.card_le_card hsub).trans <| by
          rw [Finset.card_product]
          exact Nat.mul_le_mul hc hc
    rw [straussDensity]
    have hb' : β ^ (toConfig x).card ≤ b ^ n :=
      (pow_le_pow_left₀ hβ.le (le_max_left _ _) _).trans (pow_le_pow_right₀ hb hc)
    have hg' : γ ^ (((toConfig x).offDiag.filter fun p ↦ ‖p.1 - p.2‖ ≤ R).card / 2) ≤
        g ^ (n * n) :=
      (pow_le_pow_left₀ hγ (le_max_left _ _) _).trans (pow_le_pow_right₀ hg hp)
    exact mul_le_mul_of_nonneg_left hg' (pow_nonneg hβ.le _) |>.trans
      (mul_le_mul_of_nonneg_right hb' (pow_nonneg (zero_le_one.trans hg) _))
  have : IsFiniteMeasure ((volume : Measure F).restrict W) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  rw [restrict_volume_pi_window hWf n]
  refine lt_of_le_of_lt (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hbound x)) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Strauss

/-! ### Pseudolikelihood (SYNOPSIS item 107) -/

/-- The **pseudolikelihood**
`PL_A(x) = exp(-∫_A λ*(x, ξ) dξ) ∏_{ξ ∈ x ∩ A} λ*(x ∖ {ξ}, ξ)`. -/
def pseudolikelihood (lam : Finset E → E → ℝ) (A : Set E) [DecidablePred (· ∈ A)]
    (x : Finset E) : ℝ :=
  Real.exp (-∫ ξ in A, lam x ξ) * ∏ ξ ∈ x.filter (· ∈ A), lam (x.erase ξ) ξ

lemma pseudolikelihood_def (lam : Finset E → E → ℝ) (A : Set E) [DecidablePred (· ∈ A)]
    (x : Finset E) : pseudolikelihood lam A x =
      Real.exp (-∫ ξ in A, lam x ξ) * ∏ ξ ∈ x.filter (· ∈ A), lam (x.erase ξ) ξ := by
  rw [pseudolikelihood]

/-- SYNOPSIS item 107: products of the cell conditional densities, scaled by `e^{-|A|}`,
converge to the pseudolikelihood at a positive-density configuration. The measurable
partitions refine each other and eventually separate the observed points.
See Gaetan and Guyon (2010), Theorem 5.8 and (5.39)–(5.40), p. 220. -/
theorem tendsto_prod_conditionalDensity_pseudolikelihood [NoAtoms (volume : Measure E)]
    {W A : Set E} [DecidablePred (· ∈ A)] (hAW : A ⊆ W)
    (hW : MeasurableSet W) (hWf : volume W < ⊤)
    {f : Finset E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : IsConfigMeasurable f)
    (hf : IsHereditary f) {φ : E → ℝ} (hφ : ∀ ξ, 0 ≤ φ ξ)
    (hφi : IntegrableOn φ W) (hR : IsRuelleStable W φ f)
    {x : Finset E} (hx : (x : Set E) ⊆ W) (hfx : 0 < f x)
    (m : ℕ → ℕ) (cell : (n : ℕ) → Fin (m n) → Set E)
    [∀ n j, DecidablePred (· ∈ cell n j)]
    (hcell : ∀ n j, MeasurableSet (cell n j))
    (hdisj : ∀ n, Pairwise (fun i j ↦ Disjoint (cell n i) (cell n j)))
    (hcover : ∀ n, (⋃ j, cell n j) = A)
    (hrefine : ∀ n j, ∃ i, cell (n + 1) j ⊆ cell n i)
    (hsep : ∀ᶠ n in Filter.atTop, ∀ j, (x.filter (· ∈ cell n j)).card ≤ 1)
    (hmesh : Filter.Tendsto (fun n ↦ (m n : ℝ) *
      (Finset.univ.sup (fun j ↦ volume (cell n j))).toReal ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n ↦ Real.exp (-(volume A).toReal) *
      ∏ j : Fin (m n),
        f x / (poissonIntegral (cell n j) (fun y ↦
          ENNReal.ofReal (f (y ∪ x.filter (· ∉ cell n j))))).toReal) Filter.atTop
      (𝓝 (pseudolikelihood (papangelou f) A x)) := by
  sorry

/-- SYNOPSIS item 107: on a diffuse finite-volume window with a measurable density,
the Georgii–Nguyen–Zessin formula gives mean zero for the pseudolikelihood score
`∑_{ξ ∈ X ∩ A} ψ(X ∖ {ξ}, ξ) - ∫_A ψ(X, ξ) λ*(X, ξ) dξ`, with `ψ = ∇_θ log λ*_θ` at the true
parameter. Here `ψ` is any measurable function with the integrability needed. -/
theorem pseudolikelihood_score_mean_zero [MeasurableEq E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Finset E} {W A : Set E} [DecidablePred (· ∈ A)]
    [NullSingletonClass ((volume : Measure E).restrict W)] (hW : volume W < ∞)
    (hAW : A ⊆ W) (hAm : MeasurableSet A) {f : Finset E → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfm : IsConfigMeasurable f) (hX : HasConfigDensity P X W f)
    (hher : IsHereditary f) (ψ : Finset E → E → ℝ)
    (hψm : ∀ n, Measurable fun z : E × (Fin n → E) ↦ ψ (toConfig z.2) z.1)
    (hint : Integrable (fun ω ↦ ∑ ξ ∈ (X ω).filter (· ∈ A), |ψ ((X ω).erase ξ) ξ|) P) :
    ∫ ω, (∑ ξ ∈ (X ω).filter (· ∈ A), ψ ((X ω).erase ξ) ξ -
      ∫ ξ in A, ψ (X ω) ξ * papangelou f (X ω) ξ) ∂P = 0 := by
  sorry

/-- SYNOPSIS item 107: for an exponential family `λ*_θ(x, ξ) = b(x, ξ) e^{θ ⬝ t(x, ξ)}`,
`θ ↦ log PL_A(θ; x)` is concave. -/
theorem concaveOn_log_pseudolikelihood {p : ℕ} (A : Set E) [DecidablePred (· ∈ A)]
    (b : Finset E → E → ℝ) (hb : ∀ x ξ, 0 < b x ξ) (t : Finset E → E → Fin p → ℝ)
    (x : Finset E) (hint : ∀ θ : Fin p → ℝ,
      IntegrableOn (fun ξ ↦ b x ξ * Real.exp (∑ j, θ j * t x ξ j)) A) :
    ConcaveOn ℝ univ fun θ : Fin p → ℝ ↦
      Real.log (pseudolikelihood (fun y ξ ↦ b y ξ * Real.exp (∑ j, θ j * t y ξ j)) A x) := by
  let L (θ : Fin p → ℝ) (y : Finset E) (ξ : E) := ∑ j, θ j * t y ξ j
  let F (θ : Fin p → ℝ) (y : Finset E) (ξ : E) := b y ξ * Real.exp (L θ y ξ)
  have hFpos (θ : Fin p → ℝ) (y : Finset E) (ξ : E) : 0 < F θ y ξ :=
    mul_pos (hb y ξ) (Real.exp_pos _)
  have hlog (θ : Fin p → ℝ) : Real.log (pseudolikelihood (F θ) A x) =
      -(∫ ξ in A, F θ x ξ) +
        ∑ ξ ∈ x.filter (· ∈ A), (Real.log (b (x.erase ξ) ξ) + L θ (x.erase ξ) ξ) := by
    rw [pseudolikelihood, Real.log_mul (Real.exp_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun ξ _ ↦ (hFpos θ (x.erase ξ) ξ).ne'),
      Real.log_exp, Real.log_prod (fun ξ _ ↦ (hFpos θ (x.erase ξ) ξ).ne')]
    congr 1
    apply Finset.sum_congr rfl
    intro ξ _
    dsimp only [F]
    rw [Real.log_mul (hb _ _).ne' (Real.exp_ne_zero _), Real.log_exp]
  suffices ConcaveOn ℝ univ (fun θ ↦ Real.log (pseudolikelihood (F θ) A x)) from this
  refine ⟨convex_univ, ?_⟩
  intro θ _ η _ a c ha hc hac
  have hmix (y : Finset E) (ξ : E) : L (a • θ + c • η) y ξ = a * L θ y ξ + c * L η y ξ := by
    simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hpoint (ξ : E) : F (a • θ + c • η) x ξ ≤ a * F θ x ξ + c * F η x ξ := by
    have hle : Real.exp (L (a • θ + c • η) x ξ) ≤
        a * Real.exp (L θ x ξ) + c * Real.exp (L η x ξ) := by
      rw [hmix]
      exact convexOn_exp.2 (mem_univ _) (mem_univ _) ha hc hac
    dsimp only [F]
    have hm := mul_le_mul_of_nonneg_left hle (hb x ξ).le
    linarith only [hm]
  have hFi (δ : Fin p → ℝ) : IntegrableOn (fun ξ ↦ F δ x ξ) A := hint δ
  have hle := integral_mono (hFi (a • θ + c • η))
    (((hFi θ).const_mul a).add ((hFi η).const_mul c)) hpoint
  rw [integral_add' ((hFi θ).const_mul a) ((hFi η).const_mul c),
    integral_const_mul, integral_const_mul] at hle
  have hsum : (∑ ξ ∈ x.filter (· ∈ A), (Real.log (b (x.erase ξ) ξ) +
      L (a • θ + c • η) (x.erase ξ) ξ)) =
        a * (∑ ξ ∈ x.filter (· ∈ A), (Real.log (b (x.erase ξ) ξ) + L θ (x.erase ξ) ξ)) +
        c * (∑ ξ ∈ x.filter (· ∈ A), (Real.log (b (x.erase ξ) ξ) + L η (x.erase ξ) ξ)) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [hmix]
    linear_combination -Real.log (b (x.erase ξ) ξ) * hac
  simp only [hlog, hsum, smul_eq_mul]
  linarith

/-- SYNOPSIS item 107: for a Poisson process with intensity `ρ` on `W`, whose density is
`f(x) = e^{|W| - ∫_W ρ} ∏_{ξ ∈ x} ρ(ξ)` and whose conditional intensity is `ρ(ξ)`, the
pseudolikelihood on `W` is the likelihood up to the factor `e^{-|W|}`. -/
theorem pseudolikelihood_poisson {W : Set E} [DecidablePred (· ∈ W)] (_hW : volume W < ∞)
    {ρ : E → ℝ} (x : Finset E) (hx : (x : Set E) ⊆ W) :
    pseudolikelihood (fun _ ξ ↦ ρ ξ) W x = Real.exp (-(volume W).toReal) *
      (Real.exp ((volume W).toReal - ∫ ξ in W, ρ ξ) * ∏ ξ ∈ x, ρ ξ) := by
  have hf : x.filter (· ∈ W) = x := Finset.filter_true_of_mem hx
  rw [pseudolikelihood, hf, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end MSSS
