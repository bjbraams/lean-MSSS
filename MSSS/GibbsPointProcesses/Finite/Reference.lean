module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

import Mathlib.MeasureTheory.Integral.Pi
import all Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# The finite Poisson reference and Georgii–Nguyen–Zessin formula

SYNOPSIS items 94–95. A finite configuration is a `Finset E`. With `Π_W` the unit-rate
Poisson process on `W`, the integral of `h ≥ 0` against `Π_W` is
`∑_n e^{-|W|}/n! ∫_{W^n} h({x_1, …, x_n}) dx` (`MSSS.poissonIntegral`).
A random configuration `X` has density `f` on `W` when
`E h(X) = ∫ h f dΠ_W` for every nonnegative tuple-measurable `h`
(`MSSS.HasConfigDensity`).

## Main results

* `MSSS.isLocallyStable_consequences`, `MSSS.poissonIntegral_lt_top_of_ruelle`,
  `MSSS.poissonIntegral_le_of_locallyStable_const`, `MSSS.normalisable_of_locallyStable`:
  SYNOPSIS item 94.
* `MSSS.poissonIntegral_sum_erase` and `MSSS.georgii_nguyen_zessin`: the finite Mecke identity
  and the forward Georgii–Nguyen–Zessin formula on a diffuse window (SYNOPSIS item 95).

Mathlib's `measurePreserving_piFinSuccAbove` gives the one-coordinate decomposition
in the Mecke proof. Almost-sure distinctness uses TauCeti's
`measurePreserving_piSplitAt` and Mathlib's null-singleton property. The stability
proofs use Mathlib's exponential series and finite product integration. Mathlib's
`exists_measurable_le_lintegral_eq` supplies the measurable minorant used to represent
the fixed activity weight in the Gibbs moment proofs.
-/

public section

noncomputable section

open MeasureTheory Set Finset Topology Filter TopologicalSpace
open scoped Filter
open scoped ENNReal NNReal

namespace MSSS

variable {E : Type*} [MeasureSpace E] [DecidableEq E]

/-- The configuration `{x_1, …, x_n}` of a tuple of points. -/
def toConfig {n : ℕ} (x : Fin n → E) : Finset E :=
  Finset.univ.image x

/-- `h` is measurable as a function of the points of configurations with `n` points, for every
`n`. -/
def IsConfigMeasurable {β : Type*} [MeasurableSpace β] (h : Finset E → β) : Prop :=
  ∀ n, Measurable fun x : Fin n → E ↦ h (toConfig x)

/-- Configuration measurability is measurability on every finite tuple space. -/
lemma isConfigMeasurable_def {β : Type*} [MeasurableSpace β] (h : Finset E → β) :
    IsConfigMeasurable h ↔ ∀ n, Measurable fun x : Fin n → E ↦ h (toConfig x) := Iff.rfl

/-- The integral `∫ h dΠ_W = ∑_n e^{-|W|}/n! ∫_{W^n} h({x_1, …, x_n}) dx` against the
unit-rate Poisson process on `W`. -/
def poissonIntegral (W : Set E) (h : Finset E → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(volume W).toReal) / n.factorial) *
    ∫⁻ x in Set.pi univ (fun _ : Fin n ↦ W), h (toConfig x)

/-- A random finite configuration `X` in `W` has **density** `f` with respect to `Π_W`. -/
def HasConfigDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Finset E)
    (W : Set E) (f : Finset E → ℝ) : Prop :=
  (∀ ω, (X ω : Set E) ⊆ W) ∧ ∀ h : Finset E → ℝ≥0∞, IsConfigMeasurable h →
    ∫⁻ ω, h (X ω) ∂P = poissonIntegral W fun x ↦ h x * ENNReal.ofReal (f x)

/-- `f` is **hereditary**: `f(x) > 0` and `y ⊆ x` imply `f(y) > 0`. -/
def IsHereditary (f : Finset E → ℝ) : Prop :=
  ∀ x y, y ⊆ x → 0 < f x → 0 < f y

/-- The **Papangelou conditional intensity** `λ*(x, ξ) = f(x ∪ {ξ}) / f(x)`, with `λ* = 0` when
`f(x) = 0`. -/
def papangelou (f : Finset E → ℝ) (x : Finset E) (ξ : E) : ℝ :=
  if f x = 0 then 0 else f (insert ξ x) / f x

/-- `h` is **locally stable** on `W` with integrable bound `φ*`. -/
def IsLocallyStable (W : Set E) (φ : E → ℝ) (h : Finset E → ℝ) : Prop :=
  ∀ x : Finset E, (x : Set E) ⊆ W → ∀ ξ ∈ W, ξ ∉ x → h (insert ξ x) ≤ φ ξ * h x

/-- `h` is **Ruelle stable** on `W`: `h(x) ≤ α ∏_{ξ ∈ x} φ*(ξ)`. -/
def IsRuelleStable (W : Set E) (φ : E → ℝ) (h : Finset E → ℝ) : Prop :=
  ∃ α > 0, ∀ x : Finset E, (x : Set E) ⊆ W → h x ≤ α * ∏ ξ ∈ x, φ ξ

omit [MeasureSpace E] in
lemma toConfig_def {n : ℕ} (x : Fin n → E) : toConfig x = Finset.univ.image x := by
  rw [toConfig]

lemma poissonIntegral_def (W : Set E) (h : Finset E → ℝ≥0∞) : poissonIntegral W h =
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(volume W).toReal) / n.factorial) *
      ∫⁻ x in Set.pi univ (fun _ : Fin n ↦ W), h (toConfig x) := by
  rw [poissonIntegral]

omit [MeasureSpace E] in
lemma papangelou_def (f : Finset E → ℝ) (x : Finset E) (ξ : E) :
    papangelou f x ξ = if f x = 0 then 0 else f (insert ξ x) / f x := by
  rw [papangelou]

omit [MeasureSpace E] [DecidableEq E] in
lemma isHereditary_def {f : Finset E → ℝ} :
    IsHereditary f ↔ ∀ x y, y ⊆ x → 0 < f x → 0 < f y := Iff.rfl

omit [MeasureSpace E] in
lemma isLocallyStable_def {W : Set E} {φ : E → ℝ} {h : Finset E → ℝ} :
    IsLocallyStable W φ h ↔ ∀ x : Finset E, (x : Set E) ⊆ W → ∀ ξ ∈ W, ξ ∉ x →
      h (insert ξ x) ≤ φ ξ * h x := Iff.rfl

omit [MeasureSpace E] [DecidableEq E] in
lemma isRuelleStable_def {W : Set E} {φ : E → ℝ} {h : Finset E → ℝ} :
    IsRuelleStable W φ h ↔ ∃ α > 0, ∀ x : Finset E, (x : Set E) ⊆ W →
      h x ≤ α * ∏ ξ ∈ x, φ ξ := Iff.rfl

/-! ### Stability (SYNOPSIS item 94) -/

omit [DecidableEq E] in
/-- For tuple integrals, restricting each factor to a finite-volume window gives the same
measure as restricting the product measure to the tuples in that window. -/
theorem restrict_volume_pi_window {W : Set E} (hW : volume W < ⊤) (n : ℕ) :
    (volume : Measure (Fin n → E)).restrict (Set.pi univ (fun _ ↦ W)) =
      Measure.pi (fun _ : Fin n ↦ (volume : Measure E).restrict W) := by
  let ν := (volume : Measure E).restrict W
  have : IsFiniteMeasure ν := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hmono : Measure.pi (fun _ : Fin n ↦ ν) ≤ volume := by
    rw [volume_pi]
    apply Measure.le_iff.2
    intro U hU
    simp only [Measure.pi, toMeasure_apply _ _ hU]
    refine OuterMeasure.le_pi.2 (fun s _ ↦ ?_) U
    exact (OuterMeasure.pi_pi_le _ _).trans
      (Finset.prod_le_prod fun i _ ↦ Measure.restrict_le_self (s := W) _)
  refine (Measure.pi_eq (μ := fun _ : Fin n ↦ ν) fun s hs ↦ ?_).symm
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib]
  have hprod : (∏ i, ν (s i ∩ W)) = ∏ i, ν (s i) := by
    apply Finset.prod_congr rfl
    intro i _
    refine le_antisymm (measure_mono inter_subset_left) ?_
    dsimp only [ν]
    rw [Measure.restrict_apply (hs i)]
    simpa only [inter_assoc, inter_self] using
      (Measure.le_restrict_apply (μ := (volume : Measure E)) W (s i ∩ W))
  refine le_antisymm ?_ ?_
  · let V i := toMeasurable volume (s i ∩ W)
    have hle : (Set.univ.pi fun i ↦ s i ∩ W) ⊆ Set.univ.pi V :=
      Set.pi_mono fun _ _ ↦ subset_toMeasurable _ _
    apply (measure_mono hle).trans
    rw [volume_pi, Measure.pi, toMeasure_apply _ _
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_toMeasurable _ _)]
    refine (OuterMeasure.pi_pi_le _ _).trans_eq ?_
    exact Finset.prod_congr rfl fun i _ ↦
      (measure_toMeasurable (s i ∩ W)).trans (Measure.restrict_apply (hs i)).symm
  · have h := hmono (Set.univ.pi fun i ↦ s i ∩ W)
    rwa [Measure.pi_pi, hprod] at h

/-- The Poisson integral is finite when its tuple integrals are bounded by a geometric
sequence. The factorial in the Poisson weight makes the resulting series summable. -/
private theorem poissonIntegral_lt_top_of_geometric {W : Set E} {h : Finset E → ℝ≥0∞}
    {B C : ℝ≥0∞} (hB : B < ⊤) (hC : C < ⊤)
    (hbound : ∀ n : ℕ,
      (∫⁻ x in Set.pi univ (fun _ : Fin n ↦ W), h (toConfig x)) ≤ B * C ^ n) :
    poissonIntegral W h < ⊤ := by
  let A := Real.exp (-(volume W).toReal) * B.toReal
  let g (n : ℕ) := A * (C.toReal ^ n / n.factorial)
  have hA : 0 ≤ A := mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  have hnon (n : ℕ) : 0 ≤ g n :=
    mul_nonneg hA (div_nonneg (pow_nonneg ENNReal.toReal_nonneg _) (Nat.cast_nonneg _))
  have hsum : Summable g := (Real.summable_pow_div_factorial C.toReal).mul_left A
  rw [poissonIntegral]
  refine lt_of_le_of_lt (tsum_le_tsum (g := fun n ↦ ENNReal.ofReal (g n)) ?_) ?_
  · intro n
    refine (mul_le_mul_right (hbound n) _).trans_eq ?_
    have hn : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hdiv : ENNReal.ofReal (C.toReal ^ n / n.factorial) = C ^ n / n.factorial := by
      rw [ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]
    dsimp only [g]
    rw [ENNReal.ofReal_mul hA, hdiv]
    dsimp only [A]
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal hB.ne,
      ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_natCast]
    simp only [div_eq_mul_inv]
    ac_rfl
  · rw [← ENNReal.ofReal_tsum_of_nonneg hnon hsum]
    exact ENNReal.ofReal_lt_top

/-- The factorial-weighted tuple integral is finite under a geometric bound on the weight
of every tuple in the window. -/
theorem poissonIntegral_lt_top_of_pow {W : Set E} (hW : volume W < ⊤)
    {h : Finset E → ℝ≥0∞} {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n : ℕ, ∀ x ∈ Set.pi univ (fun _ : Fin n ↦ W), h (toConfig x) ≤ C ^ n) :
    poissonIntegral W h < ⊤ := by
  refine poissonIntegral_lt_top_of_geometric (B := 1) ENNReal.one_lt_top
    (ENNReal.mul_lt_top hC hW) fun n ↦ ?_
  have : IsFiniteMeasure ((volume : Measure E).restrict W) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  calc
    _ ≤ ∫⁻ _ in Set.pi univ (fun _ : Fin n ↦ W), C ^ n :=
      setLIntegral_mono measurable_const (hbound n)
    _ = _ := by
      rw [restrict_volume_pi_window hW n, lintegral_const, Measure.pi_univ, one_mul, mul_pow]
      simp only [Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Positive weight of the empty configuration makes the Poisson integral positive. -/
theorem poissonIntegral_pos_of_empty {W : Set E} {h : Finset E → ℝ≥0∞}
    (h₀ : 0 < h ∅) : 0 < poissonIntegral W h := by
  let u : Fin 0 → E := isEmptyElim
  have hW : Set.pi univ (fun _ : Fin 0 ↦ W) = univ := by
    refine Set.eq_univ_of_forall fun x i _ ↦ ?_
    exact Fin.elim0 i
  have hEmpty (x : Fin 0 → E) : toConfig x = ∅ := by
    simp [toConfig]
  have hmass : (volume : Measure (Fin 0 → E)) univ = 1 := by
    rw [Measure.volume_pi_eq_dirac u, Measure.dirac_apply_of_mem (Set.mem_univ _)]
  rw [poissonIntegral]
  apply lt_of_lt_of_le ?_ (le_tsum _ 0)
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, hW, Measure.restrict_univ,
    hEmpty, lintegral_const, hmass, mul_one]
  exact ENNReal.mul_pos (by positivity) h₀.ne'

-- Preserve the ambient measure-space argument of the existing theorem.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 94: a nonnegative locally stable `h` is Ruelle stable and hereditary on `W`,
and its conditional intensity is bounded by `φ*`. -/
theorem isLocallyStable_consequences {W : Set E} {φ : E → ℝ} (hφ : ∀ ξ, 0 ≤ φ ξ)
    {h : Finset E → ℝ} (h0 : ∀ x, 0 ≤ h x) (hls : IsLocallyStable W φ h) :
    IsRuelleStable W φ h ∧
      (∀ x y : Finset E, (x : Set E) ⊆ W → y ⊆ x → 0 < h x → 0 < h y) ∧
      ∀ x : Finset E, (x : Set E) ⊆ W → ∀ ξ ∈ W, ξ ∉ x → papangelou h x ξ ≤ φ ξ := by
  have hbound {y x : Finset E} (hx : (x : Set E) ⊆ W) (hy : y ⊆ x) :
      h x ≤ h y * ∏ ξ ∈ x \ y, φ ξ := by
    have haux (z : Finset E) (hz : Disjoint z y) (hzy : ((z ∪ y : Finset E) : Set E) ⊆ W) :
        h (z ∪ y) ≤ h y * ∏ ξ ∈ z, φ ξ := by
      induction z using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.disjoint_insert_left] at hz
        rw [Finset.insert_union] at hzy ⊢
        have hsub : ((s ∪ y : Finset E) : Set E) ⊆ W :=
          fun _ hk ↦ hzy (Finset.mem_insert_of_mem hk)
        have haw : a ∈ W := hzy (Finset.mem_insert_self a _)
        have han : a ∉ s ∪ y := by simpa only [Finset.mem_union, not_or] using And.intro ha hz.1
        rw [Finset.prod_insert ha, ← mul_left_comm]
        exact (hls _ hsub a haw han).trans (mul_le_mul_of_nonneg_left (ih hz.2 hsub) (hφ a))
    simpa only [Finset.sdiff_union_of_subset hy] using
      haux (x \ y) Finset.sdiff_disjoint (by simpa only [Finset.sdiff_union_of_subset hy] using hx)
  refine ⟨⟨h ∅ + 1, by linarith [h0 ∅], fun x hx ↦ ?_⟩, ?_, ?_⟩
  · have hprod : 0 ≤ ∏ ξ ∈ x, φ ξ := Finset.prod_nonneg fun ξ _ ↦ hφ ξ
    have hx' := hbound hx (Finset.empty_subset x)
    rw [Finset.sdiff_empty] at hx'
    nlinarith [hx', hprod]
  · intro x y hx hy hpos
    by_contra! hneg
    have hle := hbound hx hy
    rw [le_antisymm hneg (h0 y), zero_mul] at hle
    exact (not_lt_of_ge hle) hpos
  · intro x hx ξ hξ hξx
    rw [papangelou]
    split_ifs with hh
    · exact hφ ξ
    · exact (div_le_iff₀ (lt_of_le_of_ne (h0 x) (Ne.symm hh))).2 (hls x hx ξ hξ hξx)

-- Retain the nonnegativity hypothesis from the statement for density weights.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 94: a Ruelle stable `h` with integrable `φ*` has `∫ h dΠ_W < ∞`. -/
theorem poissonIntegral_lt_top_of_ruelle {W : Set E} (hW : volume W < ∞) {φ : E → ℝ}
    (hφ : ∀ ξ, 0 ≤ φ ξ) (hφi : IntegrableOn φ W) {h : Finset E → ℝ} (h0 : ∀ x, 0 ≤ h x)
    (hR : IsRuelleStable W φ h) : poissonIntegral W (fun x ↦ ENNReal.ofReal (h x)) < ∞ := by
  obtain ⟨α, hα, hh⟩ := hR
  let ν := (volume : Measure E).restrict W
  have : IsFiniteMeasure ν := ⟨by rwa [Measure.restrict_apply_univ]⟩
  let g (u : E) := max 1 (φ u)
  have hg1 (u : E) : 1 ≤ g u := le_max_left _ _
  have hg0 (u : E) : 0 ≤ g u := zero_le_one.trans (hg1 u)
  have hgi : Integrable g ν := (integrable_const 1).sup hφi
  refine poissonIntegral_lt_top_of_geometric (B := ENNReal.ofReal α)
    (C := ENNReal.ofReal (∫ u, g u ∂ν)) ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top fun n ↦ ?_
  let G (x : Fin n → E) := α * ∏ i, g (x i)
  have hG0 (x : Fin n → E) : 0 ≤ G x :=
    mul_nonneg hα.le (Finset.prod_nonneg fun i _ ↦ hg0 (x i))
  have hGi : Integrable G (Measure.pi (fun _ : Fin n ↦ ν)) :=
    (Integrable.fintype_prod fun _ ↦ hgi).const_mul α
  have heq := restrict_volume_pi_window hW n
  have hGm : AEMeasurable (fun x ↦ ENNReal.ofReal (G x))
      ((volume : Measure (Fin n → E)).restrict (Set.pi univ (fun _ ↦ W))) := by
    rw [heq]
    exact hGi.aemeasurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ x in Set.pi univ (fun _ : Fin n ↦ W), ENNReal.ofReal (G x) := by
      refine setLIntegral_mono_ae hGm (ae_of_all _ fun x hx ↦ ENNReal.ofReal_le_ofReal ?_)
      have hWx : (toConfig x : Set E) ⊆ W := by
        intro u hu
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
        exact hx i (Set.mem_univ i)
      apply (hh _ hWx).trans
      apply mul_le_mul_of_nonneg_left _ hα.le
      have hprod : (∏ ξ ∈ toConfig x, φ ξ) ≤ ∏ ξ ∈ toConfig x, g ξ :=
        Finset.prod_le_prod₀ (fun ξ _ ↦ hφ ξ) (fun ξ _ ↦ le_max_right 1 (φ ξ))
      refine hprod.trans ?_
      let gn (u : E) : ℝ≥0 := ⟨g u, hg0 u⟩
      have hi := Finset.prod_image_le_of_one_le (s := Finset.univ) (g := x) (f := gn)
        fun ξ _ ↦ NNReal.coe_le_coe.mp (hg1 ξ)
      have hiReal := NNReal.coe_le_coe.mpr hi
      rw [NNReal.coe_prod, NNReal.coe_prod] at hiReal
      exact hiReal
    _ = ENNReal.ofReal α * ENNReal.ofReal (∫ u, g u ∂ν) ^ n := by
      rw [heq, ← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ hG0)]
      dsimp only [G]
      rw [integral_const_mul, integral_fintype_prod_eq_pow, Fintype.card_fin,
        ENNReal.ofReal_mul hα.le, ENNReal.ofReal_pow (integral_nonneg hg0)]

/-- Tuple coordinates in a diffuse product measure are almost surely distinct. -/
lemma ae_injective_pi_of_nullSingletonClass {X ι : Type*} [MeasurableSpace X] [MeasurableEq X]
    [Fintype ι] {ν : Measure X}
    [SigmaFinite ν] [NullSingletonClass ν] :
    ∀ᵐ x ∂Measure.pi (fun _ : ι ↦ ν), Function.Injective x := by
  classical
  simp only [Function.Injective, ae_all_iff]
  intro i j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ ↦ hij
  let k : {k : ι // k ≠ i} := ⟨j, Ne.symm hij⟩
  let ν' : {k : ι // k ≠ i} → Measure X := fun _ ↦ ν
  -- TauCeti splits off one coordinate before applying Fubini and the null-singleton property.
  have hsplit := TauCeti.measurePreserving_piSplitAt (fun _ : ι ↦ ν) i
  have hpred : MeasurableSet {p : X × ({k : ι // k ≠ i} → X) | p.2 k ≠ p.1} :=
    (measurableSet_eq_fun (f := fun p : X × ({k : ι // k ≠ i} → X) ↦ p.2 k)
      (g := Prod.fst) ((measurable_pi_apply _).comp measurable_snd) measurable_fst).compl
  have hae : ∀ᵐ p ∂ν.prod (Measure.pi ν'), p.2 k ≠ p.1 :=
    (Measure.ae_prod_iff_ae_ae hpred).2
      (Filter.Eventually.of_forall fun a ↦ Measure.ae_eval_ne ν' k a)
  rw [← hsplit.map_eq] at hae
  refine ((ae_map_iff hsplit.aemeasurable hpred).1 hae).mono fun x hx heq ↦ ?_
  exact (hx heq.symm).elim

/-- Tuples in a diffuse window give configurations of the same size almost surely. -/
lemma ae_toConfig_subset_and_card [MeasurableEq E] {W : Set E}
    [NullSingletonClass ((volume : Measure E).restrict W)] (hW : volume W < ∞)
    (hWm : MeasurableSet W) (n : ℕ) :
    ∀ᵐ x : Fin n → E ∂volume.restrict (Set.pi univ (fun _ ↦ W)),
      (toConfig x : Set E) ⊆ W ∧ (toConfig x).card = n := by
  let ν := (volume : Measure E).restrict W
  have : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hW⟩
  have hU : MeasurableSet (Set.pi univ (fun _ : Fin n ↦ W)) :=
    MeasurableSet.univ_pi fun _ ↦ hWm
  have hinj : ∀ᵐ x ∂(volume : Measure (Fin n → E)).restrict
      (Set.pi univ (fun _ ↦ W)), Function.Injective x := by
    rw [restrict_volume_pi_window hW n]
    exact ae_injective_pi_of_nullSingletonClass
  filter_upwards [hinj, ae_restrict_mem hU] with x hxi hxu
  constructor
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hxu i (mem_univ i)
  · rw [toConfig_def, Finset.card_image_of_injective _ hxi, Finset.card_univ, Fintype.card_fin]

/-- SYNOPSIS item 94: for a diffuse reference measure, `φ* ≡ β`, and locally stable `h`,
`∫ h dΠ_W ≤ h(∅) e^{(β - 1)|W|}`. -/
theorem poissonIntegral_le_of_locallyStable_const [MeasurableEq E] {W : Set E}
    [NullSingletonClass ((volume : Measure E).restrict W)] (hW : volume W < ∞)
    (hWm : MeasurableSet W) {β : ℝ} (hβ : 0 ≤ β) {h : Finset E → ℝ}
    (h0 : ∀ x, 0 ≤ h x) (hls : IsLocallyStable W (fun _ ↦ β) h) :
    poissonIntegral W (fun x ↦ ENNReal.ofReal (h x)) ≤
      ENNReal.ofReal (h ∅ * Real.exp ((β - 1) * (volume W).toReal)) := by
  have hbound (s : Finset E) (hs : (s : Set E) ⊆ W) : h s ≤ h ∅ * β ^ s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      have hsub : (s : Set E) ⊆ W := fun _ hu ↦ hs (Finset.mem_insert_of_mem hu)
      have haw : a ∈ W := hs (Finset.mem_insert_self a s)
      rw [Finset.card_insert_of_notMem ha, pow_succ, ← mul_assoc, mul_comm _ β]
      exact (hls s hsub a haw ha).trans (mul_le_mul_of_nonneg_left (ih hsub) hβ)
  let m := (volume W).toReal
  let g (n : ℕ) := (Real.exp (-m) * h ∅) * ((β * m) ^ n / n.factorial)
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hgn (n : ℕ) : 0 ≤ g n :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (h0 ∅))
      (div_nonneg (pow_nonneg (mul_nonneg hβ hm) _) (Nat.cast_nonneg _))
  have hg : Summable g := (Real.summable_pow_div_factorial _).mul_left _
  calc
    _ ≤ ∑' n, ENNReal.ofReal (g n) := by
      rw [poissonIntegral_def]
      refine tsum_le_tsum fun n ↦ ?_
      let ν := (volume : Measure E).restrict W
      let U : Set (Fin n → E) := Set.pi univ (fun _ ↦ W)
      have : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hW⟩
      have ht : ∀ᵐ x ∂(volume : Measure (Fin n → E)).restrict U,
          ENNReal.ofReal (h (toConfig x)) ≤ ENNReal.ofReal (h ∅ * β ^ n) :=
        (ae_toConfig_subset_and_card hW hWm n).mono fun x ⟨hsub, hc⟩ ↦
          ENNReal.ofReal_le_ofReal ((hbound _ hsub).trans_eq (by rw [hc]))
      exact (mul_le_mul_right (lintegral_mono_ae ht) _).trans_eq (by
        have hmass : Measure.pi (fun _ : Fin n ↦ ν) univ = ENNReal.ofReal m ^ n := by
          rw [Measure.pi_univ]
          simp only [ν, Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, m, ENNReal.ofReal_toReal hW.ne]
        rw [restrict_volume_pi_window hW n, lintegral_const, hmass]
        dsimp only [g]
        rw [← ENNReal.ofReal_pow hm,
          ← ENNReal.ofReal_mul (mul_nonneg (h0 ∅) (pow_nonneg hβ _)),
          ← ENNReal.ofReal_mul (div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _))]
        apply congrArg ENNReal.ofReal
        rw [mul_pow]
        ring)
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hgn hg]
      have he : ∑' n : ℕ, ((β * m) ^ n / n.factorial) = Real.exp (β * m) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      dsimp only [g]
      rw [tsum_mul_left, he, mul_assoc, mul_left_comm, ← Real.exp_add]
      have harg : -m + β * m = (β - 1) * (volume W).toReal := by
        dsimp only [m]
        ring
      rw [harg]

/-- SYNOPSIS item 94: a locally stable `h` with `h(∅) > 0` is proportional to a probability
density: `0 < ∫ h dΠ_W < ∞`. -/
theorem normalisable_of_locallyStable {W : Set E} (hW : volume W < ∞) {φ : E → ℝ}
    (hφ : ∀ ξ, 0 ≤ φ ξ) (hφi : IntegrableOn φ W) {h : Finset E → ℝ} (h0 : ∀ x, 0 ≤ h x)
    (hls : IsLocallyStable W φ h) (hpos : 0 < h ∅) :
    0 < poissonIntegral W (fun x ↦ ENNReal.ofReal (h x)) ∧
      poissonIntegral W (fun x ↦ ENNReal.ofReal (h x)) < ∞ := by
  exact ⟨poissonIntegral_pos_of_empty (ENNReal.ofReal_pos.mpr hpos),
    poissonIntegral_lt_top_of_ruelle hW hφ hφi h0 (isLocallyStable_consequences hφ h0 hls).1⟩

/-! ### Mecke and Georgii–Nguyen–Zessin identities (SYNOPSIS item 95) -/

/-- A fixed subset of tuple indices can be reenumerated as a shorter tuple. -/
private lemma measurable_config_image {n : ℕ} {g : E → Finset E → ℝ≥0∞}
    (hg : ∀ k, Measurable fun z : E × (Fin k → E) ↦ g z.1 (toConfig z.2))
    (i : Fin n) (s : Finset (Fin n)) :
    Measurable (fun x : Fin n → E ↦ g (x i) (s.image x)) := by
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
  have hmeas : Measurable (fun x : Fin n → E ↦ (fun j : Fin s.card ↦ x (e j))) :=
    measurable_pi_iff.mpr fun j ↦ measurable_pi_apply (e j : Fin n)
  have hconfig (x : Fin n → E) : toConfig (fun j : Fin s.card ↦ x (e j)) = s.image x := by
    ext a
    simp only [toConfig, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, (e j).property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e.symm ⟨j, hj⟩, by simp⟩
  simpa only [Function.comp_def, hconfig] using
    (hg s.card).comp ((measurable_pi_apply i).prodMk hmeas)

/-- The measurable pieces for deletion are indexed by sets of retained coordinates. -/
private lemma measurable_config_erase [MeasurableEq E] {n : ℕ}
    {g : E → Finset E → ℝ≥0∞}
    (hg : ∀ k, Measurable fun z : E × (Fin k → E) ↦ g z.1 (toConfig z.2))
    (i : Fin n) :
    Measurable (fun x : Fin n → E ↦ g (x i) ((toConfig x).erase (x i))) := by
  classical
  let mask (x : Fin n → E) := Finset.univ.filter fun j ↦ x j ≠ x i
  have hm (s : Finset (Fin n)) : MeasurableSet {x : Fin n → E | mask x = s} := by
    have hset : {x : Fin n → E | mask x = s} =
        ⋂ j : Fin n, {x | (x j ≠ x i) ↔ j ∈ s} := by
      ext x
      simp [mask, Finset.ext_iff]
    rw [hset]
    apply MeasurableSet.iInter
    intro j
    have heq := measurableSet_eq_fun (measurable_pi_apply j : Measurable fun x : Fin n → E ↦ x j)
      (measurable_pi_apply i)
    by_cases hj : j ∈ s
    · simp only [hj, iff_true]
      exact heq.compl
    · simpa only [hj, iff_false, not_not] using heq
  have he (x : Fin n → E) : (mask x).image x = (toConfig x).erase (x i) := by
    ext a
    simp only [mask, toConfig, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨j, hji, rfl⟩
      exact ⟨hji, j, rfl⟩
    · rintro ⟨hai, j, rfl⟩
      exact ⟨j, hai, rfl⟩
  convert (Finset.measurable_sum Finset.univ (fun s _ ↦
    Measurable.ite (hm s) (measurable_config_image hg i s) measurable_const) :
      Measurable (fun x : Fin n → E ↦ ∑ s : Finset (Fin n),
        if mask x = s then g (x i) (s.image x) else 0)) using 1
  funext x
  rw [Finset.sum_eq_single (mask x)]
  · simp [he]
  · intro b _ hb
    exact ite_eq_right (Ne.symm hb)
  · simp

/-- The sum of a jointly measurable test over all points of a configuration and
their remainders is a measurable function of the configuration. -/
lemma isConfigMeasurable_sum_erase [MeasurableEq E] {g : E → Finset E → ℝ≥0∞}
    (hg : ∀ n, Measurable fun z : E × (Fin n → E) ↦ g z.1 (toConfig z.2)) :
    IsConfigMeasurable (fun x ↦ ∑ ξ ∈ x, g ξ (x.erase ξ)) := by
  classical
  intro n
  let first (x : Fin n → E) (i : Fin n) := ∀ j : Fin n, j < i → x j ≠ x i
  have hm (i : Fin n) : MeasurableSet {x | first x i} := by
    rw [show {x | first x i} = ⋂ j : Fin n, {x | j < i → x j ≠ x i} by ext; simp [first]]
    apply MeasurableSet.iInter
    intro j
    by_cases hj : j < i
    · simp only [hj, true_implies]
      exact (measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply i)).compl
    · simp [hj]
  convert (Finset.measurable_sum Finset.univ (fun i _ ↦
    Measurable.ite (hm i) (measurable_config_erase hg i) measurable_const) :
      Measurable (fun x : Fin n → E ↦ ∑ i : Fin n,
        if first x i then g (x i) ((toConfig x).erase (x i)) else 0)) using 1
  funext x
  let s := Finset.univ.filter (first x)
  rw [← Finset.sum_filter]
  have hs : s.image x = toConfig x := by
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image (Finset.subset_univ _)
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      let t := Finset.univ.filter (fun j ↦ x j = x i)
      have ht : t.Nonempty := ⟨i, by simp [t]⟩
      have hk := Finset.min'_mem t ht
      rw [Finset.mem_image]
      refine ⟨t.min' ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        (Finset.mem_filter.mp hk).2⟩
      intro j hj heq
      have hle := Finset.min'_le t j (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, heq.trans (Finset.mem_filter.mp hk).2⟩)
      exact (not_lt_of_ge hle) hj
  dsimp only
  conv_lhs => arg 1; rw [← hs]
  apply Finset.sum_image
  intro i hi j hj he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact ((Finset.mem_filter.mp hj).2 i hij he).elim
  · exact hij
  · exact ((Finset.mem_filter.mp hi).2 j hij he.symm).elim

omit [MeasureSpace E] in
/-- Deleting one value of an injective tuple amounts to dropping its coordinate. -/
private lemma toConfig_erase_of_injective {n : ℕ} {x : Fin (n + 1) → E}
    (hx : Function.Injective x) (i : Fin (n + 1)) :
    (toConfig x).erase (x i) = toConfig (fun j ↦ x (i.succAbove j)) := by
  ext a
  simp only [toConfig, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, j, rfl⟩
    have hji : j ≠ i := fun he ↦ ha (congrArg x he)
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
    exact ⟨k, congrArg x hk⟩
  · rintro ⟨j, rfl⟩
    exact ⟨fun he ↦ i.succAbove_ne j (hx he), i.succAbove j, rfl⟩

/-- Each coordinate contributes the same iterated integral, using Mathlib's
`measurePreserving_piFinSuccAbove` to split the product measure. -/
private lemma lintegral_pi_sum_erase [MeasurableEq E] {ν : Measure E} [IsFiniteMeasure ν]
    [NullSingletonClass ν] {g : E → Finset E → ℝ≥0∞}
    (hg : ∀ n, Measurable fun z : E × (Fin n → E) ↦ g z.1 (toConfig z.2)) (n : ℕ) :
    (∫⁻ x, ∑ ξ ∈ toConfig x, g ξ ((toConfig x).erase ξ) ∂Measure.pi
      (fun _ : Fin (n + 1) ↦ ν)) =
      (n + 1 : ℝ≥0∞) * ∫⁻ a, ∫⁻ x, g a (toConfig x) ∂Measure.pi
        (fun _ : Fin n ↦ ν) ∂ν := by
  classical
  have ha (i : Fin (n + 1)) : Measurable
      (fun x : Fin (n + 1) → E ↦ g (x i) (toConfig fun j ↦ x (i.succAbove j))) :=
    (hg n).comp (MeasurableEquiv.piFinSuccAbove (fun _ ↦ E) i).measurable
  calc
    _ = ∫⁻ x : Fin (n + 1) → E, ∑ i : Fin (n + 1),
        g (x i) (toConfig fun j ↦ x (i.succAbove j)) ∂Measure.pi (fun _ ↦ ν) := by
      apply lintegral_congr_ae
      filter_upwards [ae_injective_pi_of_nullSingletonClass (ν := ν) (ι := Fin (n + 1))]
        with x hx
      conv_lhs => arg 1; rw [toConfig_def]
      rw [Finset.sum_image (fun _ _ _ _ he ↦ hx he)]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (g (x i)) (toConfig_erase_of_injective hx i)
    _ = _ := by
      rw [lintegral_finsetSum _ (fun i _ ↦ ha i)]
      have hcoord (i : Fin (n + 1)) :
          (∫⁻ x, g (x i) (toConfig fun j ↦ x (i.succAbove j)) ∂Measure.pi (fun _ ↦ ν)) =
            ∫⁻ a, ∫⁻ x, g a (toConfig x) ∂Measure.pi (fun _ : Fin n ↦ ν) ∂ν :=
        ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ν) i).lintegral_comp
          (hg n)).trans (lintegral_prod _ (hg n).aemeasurable)
      simp_rw [hcoord]
      simp [nsmul_eq_mul]

/-- Multiplying a successor term's Poisson weight by the number of coordinates
cancels that factor in the factorial. -/
private lemma poissonWeight_mul_succ (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ENNReal.ofReal (a / (n + 1).factorial) * (n + 1 : ℝ≥0∞) =
      ENNReal.ofReal (a / n.factorial) := by
  have hp : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hc : (n : ℝ≥0∞) + 1 = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  rw [hc,
    ← ENNReal.ofReal_mul (div_nonneg ha (Nat.cast_nonneg _)),
    Nat.factorial_succ, Nat.cast_mul]
  congr 1
  rw [mul_comm (↑(n + 1) : ℝ), ← div_div, div_mul_cancel₀ _ hp.ne']

/-- The Mecke identity for the finite Poisson reference on a diffuse window. -/
theorem poissonIntegral_sum_erase [MeasurableEq E] {W : Set E}
    [NullSingletonClass ((volume : Measure E).restrict W)] (hW : volume W < ∞)
    {g : E → Finset E → ℝ≥0∞}
    (hg : ∀ n, Measurable fun z : E × (Fin n → E) ↦ g z.1 (toConfig z.2)) :
    poissonIntegral W (fun x ↦ ∑ ξ ∈ x, g ξ (x.erase ξ)) =
      ∫⁻ ξ in W, poissonIntegral W (g ξ) := by
  let ν := (volume : Measure E).restrict W
  have : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hW⟩
  have hterm (n : ℕ) : Measurable (fun a ↦ ENNReal.ofReal
      (Real.exp (-(volume W).toReal) / n.factorial) *
      ∫⁻ x : Fin n → E, g a (toConfig x) ∂Measure.pi (fun _ ↦ ν)) :=
    measurable_const.mul ((hg n).lintegral_prod_right)
  simp_rw [poissonIntegral_def, restrict_volume_pi_window hW]
  rw [lintegral_tsum (fun n ↦ (hterm n).aemeasurable), tsum_eq_zero_add' CompleteLattice.summable]
  have hzero : (∫⁻ x : Fin 0 → E, ∑ ξ ∈ toConfig x, g ξ ((toConfig x).erase ξ)
      ∂Measure.pi (fun _ ↦ ν)) = 0 := by
    simp [toConfig, Finset.univ_eq_empty]
  rw [hzero, mul_zero, zero_add]
  apply tsum_congr
  intro n
  rw [lintegral_pi_sum_erase hg, ← mul_assoc, poissonWeight_mul_succ _ (Real.exp_nonneg _) n,
    lintegral_const_mul _ (hg n).lintegral_prod_right]

omit [MeasureSpace E] in
/-- Prepending a coordinate inserts that point into the tuple's configuration. -/
lemma toConfig_cons {n : ℕ} (ξ : E) (x : Fin n → E) :
    toConfig (Fin.cons ξ x) = insert ξ (toConfig x) := by
  ext a
  simp [toConfig, Fin.exists_fin_succ, eq_comm]

/-- Inserting a point is measurable on each product of a point and a tuple. -/
private lemma measurable_config_insert {β : Type*} [MeasurableSpace β] {f : Finset E → β}
    (hf : IsConfigMeasurable f) (n : ℕ) :
    Measurable (fun z : E × (Fin n → E) ↦ f (insert z.1 (toConfig z.2))) := by
  let cons (z : E × (Fin n → E)) : Fin (n + 1) → E := Fin.cons z.1 z.2
  have hm : Measurable cons := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases (motive := fun i ↦ Measurable
      (fun z ↦ cons z i)) ?_ (fun j ↦ ?_) i
    · simpa only [cons, Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst :
        E × (Fin n → E) → E))
    · simpa only [cons, Fin.cons_succ, Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_snd :
          Measurable (Prod.snd : E × (Fin n → E) → (Fin n → E)))
  simpa only [Function.comp_def, cons, toConfig_cons] using (hf (n + 1)).comp hm

/-- For a fixed point, the Papangelou intensity is measurable on each tuple space. -/
private lemma isConfigMeasurable_papangelou {f : Finset E → ℝ}
    (hf : IsConfigMeasurable f) (ξ : E) :
    IsConfigMeasurable (fun x ↦ papangelou f x ξ) := by
  intro n
  have hm := (measurable_config_insert hf n).comp ((measurable_const (a := ξ)).prodMk measurable_id)
  have h0 := measurableSet_eq_fun (hf n) (measurable_const (a := (0 : ℝ)))
  simp only [papangelou_def]
  exact Measurable.ite h0 measurable_const (hm.div (hf n))

omit [MeasureSpace E] in
/-- Multiplying the Papangelou intensity by the hereditary density recovers the inserted
configuration's density, including when the original density vanishes. -/
private lemma ofReal_papangelou_mul {f : Finset E → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hher : IsHereditary f) (x : Finset E) (ξ : E) :
    ENNReal.ofReal (papangelou f x ξ) * ENNReal.ofReal (f x) =
      ENNReal.ofReal (f (insert ξ x)) := by
  rw [papangelou_def]
  split_ifs with hx
  · have hnonpos : f (insert ξ x) ≤ 0 := le_of_not_gt (fun hpos ↦
      (not_lt_of_ge hx.le) (hher _ _ (Finset.subset_insert _ _) hpos))
    rw [hx, ENNReal.ofReal_zero, mul_zero, ENNReal.ofReal_eq_zero.mpr hnonpos]
  · rw [← ENNReal.ofReal_mul (div_nonneg (hf0 _) (hf0 _)), div_mul_cancel₀ _ hx]

/-- SYNOPSIS item 95, Georgii–Nguyen–Zessin formula: if `X` has a nonnegative, measurable
hereditary density `f` on a diffuse finite-volume window `W`, then
`E ∑_{ξ ∈ X} h(ξ, X ∖ {ξ}) = ∫_W E[h(ξ, X) λ*(X, ξ)] dξ` for measurable `h ≥ 0`. -/
theorem georgii_nguyen_zessin [MeasurableEq E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Finset E} {W : Set E}
    [NullSingletonClass ((volume : Measure E).restrict W)] (hW : volume W < ∞)
    {f : Finset E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : IsConfigMeasurable f)
    (hX : HasConfigDensity P X W f) (hher : IsHereditary f)
    (h : E → Finset E → ℝ≥0∞)
    (hm : ∀ n, Measurable fun z : E × (Fin n → E) ↦ h z.1 (toConfig z.2)) :
    ∫⁻ ω, ∑ ξ ∈ X ω, h ξ ((X ω).erase ξ) ∂P =
      ∫⁻ ξ in W, ∫⁻ ω, h ξ (X ω) * ENNReal.ofReal (papangelou f (X ω) ξ) ∂P := by
  let g ξ x := h ξ x * ENNReal.ofReal (f (insert ξ x))
  have hg n : Measurable (fun z : E × (Fin n → E) ↦ g z.1 (toConfig z.2)) :=
    (hm n).mul (measurable_config_insert hfm n).ennreal_ofReal
  have he (x : Finset E) :
      (∑ ξ ∈ x, h ξ (x.erase ξ)) * ENNReal.ofReal (f x) = ∑ ξ ∈ x, g ξ (x.erase ξ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ξ hξ ↦ by
      simp only [g, Finset.insert_erase hξ]
  rw [hX.2 _ (isConfigMeasurable_sum_erase hm)]
  simp_rw [he]
  rw [poissonIntegral_sum_erase hW hg]
  apply lintegral_congr
  intro ξ
  have hmξ : IsConfigMeasurable (fun x ↦ h ξ x * ENNReal.ofReal (papangelou f x ξ)) :=
    fun n ↦ ((hm n).comp (measurable_const.prodMk measurable_id)).mul
      ((isConfigMeasurable_papangelou hfm ξ n).ennreal_ofReal)
  rw [hX.2 _ hmξ]
  simp_rw [mul_assoc, ofReal_papangelou_mul hf0 hher]
  rfl

/-- A finite lower integral has a measurable minorant representing all its products
with finite measurable nonnegative factors. -/
lemma exists_measurable_minorant_lintegral_mul_eq {S : Type*} [MeasurableSpace S]
    {μ : Measure S} (g : S → ℝ≥0∞) (hg : (∫⁻ x, g x ∂μ) ≠ ∞) :
    ∃ ρ : S → ℝ≥0∞, Measurable ρ ∧ ∀ a : S → ℝ≥0∞, Measurable a →
      (∀ x, a x ≠ ∞) → (∫⁻ x, a x * ρ x ∂μ) = ∫⁻ x, a x * g x ∂μ := by
  obtain ⟨ρ, hρm, hρle, hρ⟩ := exists_measurable_le_lintegral_eq μ g
  have hmax {φ : S → ℝ≥0∞} (hφm : Measurable φ) (hφ : φ ≤ g) : φ ≤ᵐ[μ] ρ := by
    have hs : (fun x ↦ max (ρ x) (φ x)) ≤ g := fun x ↦ max_le (hρle x) (hφ x)
    have he := ae_eq_of_ae_le_of_lintegral_le
      (Eventually.of_forall fun x ↦ le_max_left (ρ x) (φ x))
      (hρ.symm.trans_ne hg) (hρm.max hφm).aemeasurable ((lintegral_mono hs).trans_eq hρ)
    filter_upwards [he] with x hx
    exact (le_max_right (ρ x) (φ x)).trans_eq hx.symm
  refine ⟨ρ, hρm, fun a ham ha ↦ le_antisymm (lintegral_mono fun x ↦ ?_) ?_⟩
  · exact mul_le_mul_right (hρle x) _
  · obtain ⟨φ, hφm, hφle, hφ⟩ := exists_measurable_le_lintegral_eq μ (fun x ↦ a x * g x)
    have hquot : (fun x ↦ φ x / a x) ≤ g := by
      intro x
      by_cases ha0 : a x = 0
      · have hφ0 : φ x = 0 := le_antisymm (by simpa only [ha0, zero_mul] using hφle x) bot_le
        simp [hφ0]
      · exact (ENNReal.div_le_iff' ha0 (ha x)).mpr (hφle x)
    rw [hφ]
    apply lintegral_mono_ae
    filter_upwards [hmax (hφm.div ham) hquot] with x hx
    by_cases ha0 : a x = 0
    · simpa only [ha0, zero_mul] using hφle x
    · calc
        φ x = a x * (φ x / a x) := (ENNReal.mul_div_cancel ha0 (ha x)).symm
        _ ≤ _ := mul_le_mul_right hx _

end MSSS
