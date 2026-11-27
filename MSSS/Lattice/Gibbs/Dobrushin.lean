module

public import MSSS.Lattice.Gibbs.Basic
import MSSS.Lattice.Gibbs.Existence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.MeasureTheory.Integral.Bind

/-!
# Dobrushin uniqueness for Gibbs measures

Under Dobrushin's bound and quasilocality, repeated single-site integration removes the
oscillation of every bounded local observable. A recurrent deterministic schedule suffices and
uses no measurable selection of couplings.

## Main definitions

* `MSSS.singleSiteLaw`, `MSSS.tvSup`, `MSSS.dobrushinCoeff`, and `MSSS.IsQuasilocal`.

## Main results

* `MSSS.gibbsSet_subsingleton_of_dobrushin` proves uniqueness (SYNOPSIS item 62).
* `MSSS.existsUnique_gibbs_of_dobrushin` and `MSSS.gibbsSet_subsingleton_of_oscillation`
  prove the existence and potential-oscillation parts of item 62.

The argument uses Mathlib's layer-cake formula, dominated convergence for sums, and
Kolmogorov extension and uniqueness of projective limits. The potential criterion uses
Mathlib's logarithm derivative and mean value inequality. TauCeti's formula for the Bochner integral against a
bound measure passes the DLR equation to bounded observables.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MSSS

variable {S E : Type*} [MeasurableSpace E]

/-! ### Dobrushin's uniqueness theorem (SYNOPSIS item 62) -/

/-- The single-site conditional law `γ_i^0(· ∣ ω)`, the image of `γ {i} ω` under `σ ↦ σ_i`. -/
def singleSiteLaw (γ : Finset S → (S → E) → Measure (S → E)) (i : S) (ω : S → E) : Measure E :=
  (γ {i} ω).map fun σ ↦ σ i

/-- The total-variation distance `sup_A |α(A) - β(A)|`. -/
def tvSup (α β : Measure E) : ℝ≥0∞ :=
  ⨆ (A : Set E) (_ : MeasurableSet A), (α A - β A) ⊔ (β A - α A)

/-- **Dobrushin's interaction coefficient**
`C_{ij} = sup {‖γ_i^0(· ∣ ζ) - γ_i^0(· ∣ η)‖ : ζ = η off j}`. -/
def dobrushinCoeff (γ : Finset S → (S → E) → Measure (S → E)) (i j : S) : ℝ≥0∞ :=
  ⨆ (ζ : S → E) (η : S → E) (_ : ∀ k, k ≠ j → ζ k = η k),
    tvSup (singleSiteLaw γ i ζ) (singleSiteLaw γ i η)

/-- `γ` is **quasilocal**: for bounded measurable local `f`, `ω ↦ ∫ f dγ_Λ(· ∣ ω)` is a uniform
limit of local functions. -/
def IsQuasilocal (γ : Finset S → (S → E) → Measure (S → E)) : Prop :=
  ∀ Λ (f : (S → E) → ℝ), IsLocalFunction f → Measurable f → (∃ C, ∀ ω, |f ω| ≤ C) →
    ∀ ε > 0, ∃ Δ : Finset S, ∀ ω ω', (∀ j ∈ Δ, ω j = ω' j) →
      |∫ σ, f σ ∂γ Λ ω - ∫ σ, f σ ∂γ Λ ω'| < ε

/-- The single-site conditional law is the coordinate image of the kernel. -/
lemma singleSiteLaw_def (γ : Finset S → (S → E) → Measure (S → E)) (i : S) (ω : S → E) :
    singleSiteLaw γ i ω = (γ {i} ω).map fun σ ↦ σ i := by
  rw [singleSiteLaw]

/-- Total variation takes the supremum over measurable events. -/
lemma tvSup_def (α β : Measure E) :
    tvSup α β = ⨆ (A : Set E) (_ : MeasurableSet A), (α A - β A) ⊔ (β A - α A) := by
  rw [tvSup]

/-- The influence coefficient takes the supremum over one-site changes. -/
lemma dobrushinCoeff_def (γ : Finset S → (S → E) → Measure (S → E)) (i j : S) :
    dobrushinCoeff γ i j = ⨆ (ζ : S → E) (η : S → E) (_ : ∀ k, k ≠ j → ζ k = η k),
      tvSup (singleSiteLaw γ i ζ) (singleSiteLaw γ i η) := by
  rw [dobrushinCoeff]

/-- Quasilocality is finite-coordinate control of the means of local observables. -/
lemma isQuasilocal_def {γ : Finset S → (S → E) → Measure (S → E)} : IsQuasilocal γ ↔
    ∀ Λ (f : (S → E) → ℝ), IsLocalFunction f → Measurable f → (∃ C, ∀ ω, |f ω| ≤ C) →
      ∀ ε > 0, ∃ Δ : Finset S, ∀ ω ω', (∀ j ∈ Δ, ω j = ω' j) →
        |∫ σ, f σ ∂γ Λ ω - ∫ σ, f σ ∂γ Λ ω'| < ε := Iff.rfl

/-- A coordinate projection of a specification has mass one. -/
private lemma singleSiteLaw_isProbability
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (i : S)
    (ω : S → E) : IsProbabilityMeasure (singleSiteLaw γ i ω) := by
  let _ := hγ.isProbabilityMeasure {i} ω
  rw [singleSiteLaw_def]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply i).aemeasurable).mpr
    inferInstance

/-- Properness identifies a one-site update with sampling just the updated coordinate. -/
private lemma map_singleSiteLaw_update [DecidableEq S]
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (i : S)
    (ω : S → E) : (singleSiteLaw γ i ω).map (Function.update ω i) = γ {i} ω := by
  let _ := hγ.isProbabilityMeasure {i} ω
  let T := {j : S // j ≠ i}
  let out (σ : S → E) (j : T) := σ j.1
  let split (σ : S → E) := (σ i, out σ)
  have hout : Measurable out := Measurable.of_eval fun j ↦ measurable_pi_apply j.1
  have hsplit : Measurable split := (measurable_pi_apply i).prodMk hout
  let _ : IsProbabilityMeasure ((γ {i} ω).map split) :=
    (Measure.isProbabilityMeasure_map_iff hsplit.aemeasurable).mpr inferInstance
  let _ := singleSiteLaw_isProbability hγ i ω
  have hprod : (γ {i} ω).map split = (singleSiteLaw γ i ω).prod (Measure.dirac (out ω)) := by
    apply Measure.ext_prod
    intro A B hA hB
    have hout' : Measurable[outsideSigma ((↑({i} : Finset S)) : Set S)] out :=
      measurable_outsideSigma_of_eq ω hout (fun x y hxy ↦
        funext fun j ↦ hxy j.1 (by simpa using j.2))
    have hB' := hout' hB
    have hprob := hγ.proper {i} (out ⁻¹' B) hB' ω
    rw [Measure.map_apply hsplit (hA.prod hB), Measure.prod_prod, Measure.dirac_apply' _ hB,
      singleSiteLaw_def, Measure.map_apply (measurable_pi_apply i) hA]
    have hs : split ⁻¹' (A ×ˢ B) = (out ⁻¹' B) ∩ ((fun σ : S → E ↦ σ i) ⁻¹' A) := by
      ext σ
      exact and_comm
    rw [hs]
    by_cases h : out ω ∈ B
    · rw [indicator_of_mem h, Pi.one_apply, mul_one]
      have hmem : ω ∈ out ⁻¹' B := h
      rw [indicator_of_mem hmem, Pi.one_apply, ← measure_univ (μ := γ {i} ω)] at hprob
      simpa only [univ_inter] using
        (γ {i} ω).measure_inter_eq_of_measure_eq (measurable_pi_apply i hA) hprob
          (subset_univ _) (measure_ne_top _ _)
    · have hmem : ω ∉ out ⁻¹' B := h
      rw [indicator_of_notMem hmem] at hprob
      rw [indicator_of_notMem h]
      rw [mul_zero]
      exact measure_mono_null inter_subset_left hprob
  let join (z : E × (T → E)) (j : S) := if h : j = i then z.1 else z.2 ⟨j, h⟩
  have hjoin : Measurable join := Measurable.of_eval fun j ↦ by
    by_cases hj : j = i
    · simpa only [join, dite_eq_left hj] using
        (measurable_fst : Measurable (Prod.fst : E × (T → E) → E))
    · simp only [join, dite_eq_right hj]
      exact Measurable.comp (measurable_pi_apply (⟨j, hj⟩ : T)) measurable_snd
  have hjs : join ∘ split = id := by
    funext σ j
    by_cases hj : j = i <;> simp [join, split, out, hj]
  have hjm : join ∘ (fun y ↦ (y, out ω)) = Function.update ω i := by
    funext y j
    by_cases hj : j = i <;> simp [join, out, hj, Function.update_of_ne]
  rw [Measure.prod_dirac] at hprod
  have hp := congrArg (Measure.map join) hprod
  have hins : Measurable (fun y : E ↦ (y, out ω)) := measurable_id.prodMk measurable_const
  rw [Measure.map_map hjoin hsplit, hjs, Measure.map_id, Measure.map_map hjoin hins, hjm] at hp
  exact hp.symm

/-- A bounded measurable observable is integrable for any finite measure. -/
private lemma integrable_of_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : Integrable f μ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hB x

/-- A uniform bound holds for the mean under a probability measure. -/
private lemma abs_integral_le_of_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : |∫ x, f x ∂μ| ≤ B := by
  calc
    |∫ x, f x ∂μ| ≤ ∫ x, B ∂μ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_of_norm_le (f := f) (μ := μ) (integrable_const B)
          (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hB x))
    _ = B := by simp

/-- The total variation distance between probability measures is at most one. -/
private lemma tvSup_le_one {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvSup μ ν ≤ 1 := by
  rw [tvSup_def]
  exact iSup_le fun A ↦ iSup_le fun _ ↦ sup_le
    ((tsub_le_self).trans (prob_le_one (μ := μ))) ((tsub_le_self).trans (prob_le_one (μ := ν)))

/-- The real mass difference of any event is bounded by total variation. -/
private lemma measureReal_sub_le_tvSup {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {A : Set E} (hA : MeasurableSet A) :
    μ.real A - ν.real A ≤ (tvSup μ ν).toReal := by
  by_cases ha : ν A ≤ μ A
  · rw [measureReal_def, measureReal_def,
        ← ENNReal.toReal_sub_of_le ha (measure_ne_top _ _)]
    apply ENNReal.toReal_mono ((tvSup_le_one (μ := μ) (ν := ν)).trans_lt ENNReal.one_lt_top).ne
    rw [tvSup_def]
    exact le_iSup₂_of_le A hA le_sup_left
  · exact (sub_nonpos.mpr (ENNReal.toReal_mono (measure_ne_top _ _) (le_of_not_ge ha))).trans
      ENNReal.toReal_nonneg

/-- The total variation distance is symmetric. -/
private lemma tvSup_comm (μ ν : Measure E) : tvSup μ ν = tvSup ν μ := by
  simp only [tvSup_def, sup_comm]

/-- For probability laws the change of the mean of an observable is bounded by total variation
times the diameter of its range. -/
private lemma abs_integral_sub_le_mul_tvSup {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : E → ℝ} (hf : Measurable f) {B D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hD : ∀ x y, |f x - f y| ≤ D) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ D * (tvSup μ ν).toReal := by
  have hne : Nonempty E := nonempty_of_isProbabilityMeasure μ
  let a := sInf (range f)
  have hbelow : BddBelow (range f) :=
    ⟨-B, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (hB x)).1⟩
  have hfa (x : E) : a ≤ f x := csInf_le hbelow (mem_range_self _)
  let g (x : E) := f x - a
  have hg : Measurable g := hf.sub measurable_const
  have hg₀ (x : E) : 0 ≤ g x := sub_nonneg.mpr (hfa x)
  have hgD (x : E) : g x ≤ D := by
    have h : f x - D ≤ a := by
      refine le_csInf (range_nonempty _) ?_
      rintro _ ⟨y, rfl⟩
      linarith [(abs_le.mp (hD x y)).2]
    dsimp only [g]
    linarith
  have hD₀ : 0 ≤ D := (hg₀ (Classical.choice hne)).trans (hgD _)
  have hgb (x : E) : |g x| ≤ D := by rw [abs_of_nonneg (hg₀ x)]; exact hgD x
  have layer (η : Measure E) [IsProbabilityMeasure η] :
      (∫ x, f x ∂η) - a = ∫ t in Ioc 0 D, η.real {x | t ≤ g x} := by
    have hη : (∫ _ : E, a ∂η) = a := by simp
    rw [← hη, ← integral_sub (integrable_of_bounded hf hB)
      (integrable_const a)]
    exact (integrable_of_bounded hg hgb).integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hg₀) (Eventually.of_forall hgD)
  have hlayerInt (η : Measure E) [IsProbabilityMeasure η] :
      IntegrableOn (fun t ↦ η.real {x | t ≤ g x}) (Ioc 0 D) := by
    apply integrable_of_bounded (B := 1)
    · exact Antitone.measurable (fun s t hst ↦ measureReal_mono fun x hx ↦ hst.trans hx)
    · intro t
      rw [abs_of_nonneg measureReal_nonneg]
      simpa only [measureReal_def, ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := η) (s := {x | t ≤ g x}))
  have hset (t : ℝ) : MeasurableSet {x | t ≤ g x} := hg measurableSet_Ici
  have upstairs (α β : Measure E) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
      (∫ x, f x ∂α) - ∫ x, f x ∂β ≤ D * (tvSup α β).toReal := by
    calc
      _ = ((∫ x, f x ∂α) - a) - ((∫ x, f x ∂β) - a) := by ring
      _ = ∫ t in Ioc 0 D, (α.real {x | t ≤ g x} - β.real {x | t ≤ g x}) := by
        rw [layer α, layer β, integral_sub (hlayerInt α) (hlayerInt β)]
      _ ≤ ∫ _ in Ioc 0 D, (tvSup α β).toReal :=
        integral_mono ((hlayerInt α).sub (hlayerInt β)) (integrable_const _)
          (fun t ↦ measureReal_sub_le_tvSup (hset t))
      _ = _ := by simp [max_eq_left hD₀]
  exact abs_sub_le_iff.mpr ⟨upstairs μ ν, by simpa only [tvSup_comm ν μ] using upstairs ν μ⟩

/-- The mean after resampling one site. -/
private def siteMean (γ : Finset S → (S → E) → Measure (S → E))
    (i : S) (f : (S → E) → ℝ) (ω : S → E) : ℝ :=
  ∫ σ, f σ ∂γ {i} ω

/-- A specification is a measurable kernel for the product sigma algebra. -/
private lemma measurable_specification
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (Λ : Finset S) :
    Measurable (γ Λ) :=
  Measure.measurable_measure.mpr fun A hA ↦
    (hγ.measurable Λ A hA).mono (outsideSigma_le _) le_rfl

/-- Averaging a measurable observable over a single-site kernel is measurable. -/
private lemma measurable_siteMean {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (i : S) {f : (S → E) → ℝ} (hf : Measurable f) :
    Measurable (siteMean γ i f) := by
  let κ : ProbabilityTheory.Kernel (S → E) (S → E) := ⟨γ {i}, measurable_specification hγ {i}⟩
  exact (hf.stronglyMeasurable.integral_kernel (κ := κ)).measurable

/-- A single-site update preserves a uniform bound on the observable. -/
private lemma abs_siteMean_le {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (i : S) {f : (S → E) → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (ω : S → E) : |siteMean γ i f ω| ≤ B := by
  let _ := hγ.isProbabilityMeasure {i} ω
  exact abs_integral_le_of_abs_le hB

/-- A probability law invariant under a site update preserves the mean of every
bounded observable under that update. -/
private lemma integral_siteMean_of_consistent {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (μ : Measure (S → E)) [IsProbabilityMeasure μ] (i : S)
    (hDLR : ∀ A, MeasurableSet A → μ A = ∫⁻ x, γ {i} x A ∂μ)
    {f : (S → E) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫ ω, siteMean γ i f ω ∂μ) = ∫ ω, f ω ∂μ := by
  have hm := measurable_specification hγ {i}
  have hb : μ.bind (γ {i}) = μ := Measure.ext fun A hA ↦
    (Measure.bind_apply hA hm.aemeasurable).trans (hDLR A hA).symm
  have hi : Integrable f (μ.bind (γ {i})) := hb.symm ▸ integrable_of_bounded hf hB
  -- TauCeti's integration formula converts the DLR identity of measures to one of means.
  simpa only [siteMean, hb] using (Measure.integral_bind hm.aemeasurable hi).symm

omit [MeasurableSpace E] in
/-- A uniformly local observable has arbitrarily small oscillation on finite-coordinate fibres. -/
private def IsUniformlyLocal (f : (S → E) → ℝ) : Prop :=
  ∀ ε > 0, ∃ Δ : Finset S, ∀ x y, (∀ j ∈ Δ, x j = y j) → |f x - f y| < ε

omit [MeasurableSpace E] in
/-- A local observable is uniformly local. -/
private lemma IsLocalFunction.isUniformlyLocal {f : (S → E) → ℝ} (hf : IsLocalFunction f) :
    IsUniformlyLocal f := by
  obtain ⟨Δ, hΔ⟩ := isLocalFunction_def.mp hf
  exact fun ε hε ↦ ⟨Δ, fun x y hxy ↦ by simpa only [hΔ x y hxy, sub_self, abs_zero] using hε⟩

/-- Quasilocal updates preserve uniform locality by uniform approximation. -/
private lemma isUniformlyLocal_siteMean {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (hq : IsQuasilocal γ) (i : S) (a : S → E)
    {f : (S → E) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hu : IsUniformlyLocal f) : IsUniformlyLocal (siteMean γ i f) := by
  classical
  intro ε hε
  obtain ⟨Δ, hΔ⟩ := hu (ε / 3) (by positivity)
  let p (ω : S → E) := splice Δ (Δ.restrict ω) a
  let g (ω : S → E) := f (p ω)
  have hp : Measurable p := Measurable.of_eval (fun j ↦ by
    by_cases hj : j ∈ Δ
    · simpa only [p, splice_def, dite_eq_left hj, Finset.restrict_def] using measurable_pi_apply j
    · simp only [p, splice_def, dite_eq_right hj]
      exact measurable_const)
  have hloc : IsLocalFunction g := isLocalFunction_def.mpr ⟨Δ, fun x y hxy ↦ by
    have he : Δ.restrict x = Δ.restrict y := funext fun j ↦ hxy j.1 j.2
    simp only [g, p, he]⟩
  have hdiff (ω : S → E) : |siteMean γ i f ω - siteMean γ i g ω| ≤ ε / 3 := by
    let _ := hγ.isProbabilityMeasure {i} ω
    have hbound (x : S → E) : |f x - g x| ≤ ε / 3 :=
      (hΔ x (p x) (fun j hj ↦ by
        simp only [p, splice_def, dite_eq_left hj, Finset.restrict_def])).le
    simp only [siteMean]
    rw [← integral_sub (integrable_of_bounded hf hB)
      (integrable_of_bounded (f := g) (hf.comp hp) (fun x ↦ hB (p x)))]
    exact abs_integral_le_of_abs_le hbound
  obtain ⟨U, hU⟩ := isQuasilocal_def.mp hq {i} g hloc (hf.comp hp)
    ⟨B, fun x ↦ hB (p x)⟩ (ε / 3) (by positivity)
  refine ⟨U, fun x y hxy ↦ ?_⟩
  calc
    |siteMean γ i f x - siteMean γ i f y| ≤
        |siteMean γ i f x - siteMean γ i g x| + |siteMean γ i g x - siteMean γ i f y| :=
      abs_sub_le _ _ _
    _ ≤ |siteMean γ i f x - siteMean γ i g x| +
        (|siteMean γ i g x - siteMean γ i g y| + |siteMean γ i g y - siteMean γ i f y|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ < ε := by
      have hy := hdiff y
      rw [abs_sub_comm] at hy
      have hz : |siteMean γ i g x - siteMean γ i g y| < ε / 3 := hU x y hxy
      linarith [hdiff x, hz]

omit [MeasurableSpace E] in
/-- The oscillation obtained by varying one coordinate. -/
private def siteOscillation (f : (S → E) → ℝ) (j : S) : ℝ≥0∞ :=
  ⨆ (x : S → E) (y : S → E) (_ : ∀ k, k ≠ j → x k = y k), ENNReal.ofReal |f x - f y|

omit [MeasurableSpace E] in
/-- Changing only one coordinate changes the observable by at most its site oscillation. -/
private lemma ofReal_abs_sub_le_siteOscillation {f : (S → E) → ℝ} {j : S} {x y : S → E}
    (hxy : ∀ k, k ≠ j → x k = y k) : ENNReal.ofReal |f x - f y| ≤ siteOscillation f j :=
  le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))

omit [MeasurableSpace E] in
/-- A bounded observable has finite oscillation at every site. -/
private lemma siteOscillation_le {f : (S → E) → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (j : S) : siteOscillation f j ≤ ENNReal.ofReal (2 * B) := by
  unfold siteOscillation
  refine iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun _ ↦ ENNReal.ofReal_le_ofReal ?_
  have h : |f x - f y| ≤ |f x| + |f y| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x) 0 (f y)
  linarith [hB x, hB y]

omit [MeasurableSpace E] in
/-- The real value of the site oscillation bounds a one-coordinate change. -/
private lemma abs_sub_le_siteOscillation {f : (S → E) → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    {j : S} {x y : S → E} (hxy : ∀ k, k ≠ j → x k = y k) :
    |f x - f y| ≤ (siteOscillation f j).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (siteOscillation_le hB j))).mp
    (ofReal_abs_sub_le_siteOscillation hxy)

/-- The updated mean only depends on the coordinates outside the updated site. -/
private lemma siteMean_eq_of_eqOff {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (i : S) {x y : S → E} (hxy : ∀ k, k ≠ i → x k = y k)
    (f : (S → E) → ℝ) : siteMean γ i f x = siteMean γ i f y := by
  classical
  unfold siteMean
  congr 1
  refine Measure.ext fun A hA ↦ eq_of_measurable_outsideSigma (hγ.measurable {i} A hA) ?_
  intro k hk
  exact hxy k (by simpa using hk)

/-- A single-site update removes the oscillation at its own site. -/
private lemma siteOscillation_siteMean_same {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (i : S) (f : (S → E) → ℝ) :
    siteOscillation (siteMean γ i f) i = 0 := by
  unfold siteOscillation
  refine le_antisymm ?_ (by positivity)
  refine iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun hxy ↦ ?_
  simp only [siteMean_eq_of_eqOff hγ i hxy f, sub_self, abs_zero, ENNReal.ofReal_zero, le_refl]

/-- The change in any site's oscillation is controlled by the influence coefficient. -/
private lemma siteOscillation_siteMean_le {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (i j : S)
    {f : (S → E) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    siteOscillation (siteMean γ i f) j ≤
      siteOscillation f j + siteOscillation f i * dobrushinCoeff γ i j := by
  classical
  change (⨆ (x : S → E) (y : S → E) (_ : ∀ k, k ≠ j → x k = y k),
    ENNReal.ofReal |siteMean γ i f x - siteMean γ i f y|) ≤ _
  refine iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun hxy ↦ ?_
  let μ := singleSiteLaw γ i x
  let ν := singleSiteLaw γ i y
  let _ : IsProbabilityMeasure μ := singleSiteLaw_isProbability hγ i x
  let _ : IsProbabilityMeasure ν := singleSiteLaw_isProbability hγ i y
  let gx : E → ℝ := f ∘ Function.update x i
  let gy : E → ℝ := f ∘ Function.update y i
  have hmx : Measurable gx := hf.comp (measurable_update x)
  have hmy : Measurable gy := hf.comp (measurable_update y)
  have hx : siteMean γ i f x = ∫ t, gx t ∂μ := by
    rw [siteMean, ← map_singleSiteLaw_update hγ i x, integral_map
      (measurable_update x).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hy : siteMean γ i f y = ∫ t, gy t ∂ν := by
    rw [siteMean, ← map_singleSiteLaw_update hγ i y, integral_map
      (measurable_update y).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hp : |(∫ t, gx t ∂μ) - ∫ t, gy t ∂μ| ≤ (siteOscillation f j).toReal := by
    rw [← integral_sub (integrable_of_bounded hmx (fun t ↦ hB (Function.update x i t)))
      (integrable_of_bounded hmy (fun t ↦ hB (Function.update y i t)))]
    refine abs_integral_le_of_abs_le fun t ↦ abs_sub_le_siteOscillation hB fun k hk ↦ ?_
    by_cases hki : k = i
    · subst k
      simp
    · simp only [Function.update_of_ne hki, hxy k hk]
  have hq : |(∫ t, gy t ∂μ) - ∫ t, gy t ∂ν| ≤
      (siteOscillation f i).toReal * (tvSup μ ν).toReal :=
    abs_integral_sub_le_mul_tvSup hmy (fun t ↦ hB (Function.update y i t)) fun t u ↦
      abs_sub_le_siteOscillation hB fun k hk ↦ by simp only [Function.update_of_ne hk]
  have hC : tvSup μ ν ≤ dobrushinCoeff γ i j := by
    rw [dobrushinCoeff_def]
    exact le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
  rw [hx, hy]
  calc
    _ ≤ ENNReal.ofReal ((siteOscillation f j).toReal +
        (siteOscillation f i).toReal * (tvSup μ ν).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      exact (abs_sub_le _ (∫ t, gy t ∂μ) _).trans (add_le_add hp hq)
    _ ≤ _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (siteOscillation_le hB j)),
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (siteOscillation_le hB i)),
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top tvSup_le_one)]
      gcongr


/-- Summing an oscillation transfer over all sites controls its total by the corresponding row
sum of the influence matrix. -/
private lemma oscillation_step_tsum_le {S : Type*}
    (x y : S → ℝ≥0∞) (i : S) (C : S → ℝ≥0∞) (c : ℝ≥0∞)
    (hC : (∑' j, C j) ≤ c)
    (hstep : ∀ j, y j + (@ite ℝ≥0∞ (i = j) (Classical.propDecidable _) (x i) 0) ≤ x j + x i * C j) :
    (∑' j, y j) + x i ≤ (∑' j, x j) + x i * c := by
  classical
  calc
    _ = ∑' j, (y j + (if i = j then x i else 0)) := by
      rw [tsum_add, tsum_ite_eq']
    _ ≤ ∑' j, (x j + x i * C j) := tsum_le_tsum hstep
    _ = (∑' j, x j) + x i * (∑' j, C j) := by rw [tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

/-- The mass removed by successive oscillation transfers is summable. -/
private lemma tsum_removed_ne_top {c : ℝ≥0∞} (hc : c < 1) {s a : ℕ → ℝ≥0∞}
    (hs₀ : s 0 ≠ ⊤) (ha : ∀ n, a n ≤ s n)
    (hstep : ∀ n, s (n + 1) + a n ≤ s n + a n * c) :
    (∀ n, s n ≠ ⊤) ∧ (∑' n, a n) ≠ ⊤ := by
  have hct : c ≠ ⊤ := hc.ne_top
  have hsf (n : ℕ) : s n ≠ ⊤ := by
    induction n with
    | zero => exact hs₀
    | succ n ih =>
      have haf := ne_top_of_le_ne_top ih (ha n)
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ih, ENNReal.mul_ne_top haf hct⟩) ((le_self_add : s (n + 1) ≤ _).trans (hstep n))
  have haf (n : ℕ) : a n ≠ ⊤ := ne_top_of_le_ne_top (hsf n) (ha n)
  have hr (n : ℕ) : (s (n + 1)).toReal + (a n).toReal ≤ (s n).toReal + (a n).toReal * c.toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hsf n, ENNReal.mul_ne_top (haf n) hct⟩) (hstep n)
    simpa only [ENNReal.toReal_add (hsf (n + 1)) (haf n),
      ENNReal.toReal_add (hsf n) (ENNReal.mul_ne_top (haf n) hct), ENNReal.toReal_mul] using h
  have hpart (n : ℕ) :
      (1 - c.toReal) * (∑ k ∈ Finset.range n, (a k).toReal) + (s n).toReal ≤ (s 0).toReal := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith only [ih, hr n]
  have hc' : 0 < 1 - c.toReal := sub_pos.mpr
    (by simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hct ENNReal.one_ne_top).mpr hc)
  have hbound (n : ℕ) :
      (∑ k ∈ Finset.range n, a k) ≤ ENNReal.ofReal ((s 0).toReal / (1 - c.toReal)) := by
    have hn : (∑ k ∈ Finset.range n, a k) ≠ ⊤ :=
      (ENNReal.sum_lt_top.mpr (fun k _ ↦ (haf k).lt_top)).ne
    rw [← ENNReal.ofReal_toReal hn, ENNReal.toReal_sum (fun k _ ↦ haf k)]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hc').2
    linarith only [hpart n, ENNReal.toReal_nonneg (a := s n)]
  exact ⟨hsf, ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ENNReal.tsum_le_of_sum_range_le hbound)⟩

/-- After a site is updated its oscillation can grow only by the mass transferred by later
updates, and those transfers have a summable total. -/
private lemma tendsto_zero_of_resets {d a : ℕ → ℝ≥0∞} (ha : ∑' n, a n ≠ ⊤)
    (hstep : ∀ n, d (n + 1) ≤ d n + a n) (hvis : ∀ N, ∃ n ≥ N, d (n + 1) = 0) :
    Tendsto d atTop (𝓝 0) := by
  let T (n : ℕ) := ∑' k : ℕ, a (k + n)
  have hdecomp (n : ℕ) : T n = a n + T (n + 1) := by
    dsimp only [T]
    rw [tsum_eq_zero_add' CompleteLattice.summable, zero_add]
    exact congrArg (a n + ·) (tsum_congr fun k ↦ by
      congr 1
      omega)
  have hT : Tendsto T atTop (𝓝 0) := by
    have hrange : Tendsto (Finset.range : ℕ → Finset ℕ) atTop atTop := by
      refine tendsto_atTop.mpr fun F ↦ eventually_atTop.mpr ⟨F.sup id + 1, fun n hn j hj ↦ ?_⟩
      have hj' : j ≤ F.sup id := Finset.le_sup (f := id) hj
      exact Finset.mem_range.mpr (by omega)
    refine ((ENNReal.tendsto_tsum_compl_atTop_zero ha).comp hrange).congr' ?_
    exact Eventually.of_forall fun n ↦ by
      let e : ℕ ≃ {k : ℕ // k ∉ Finset.range n} :=
        { toFun := fun k ↦ ⟨k + n, by simp only [Finset.mem_range]; omega⟩
          invFun := fun k ↦ k.1 - n
          left_inv := fun k ↦ Nat.add_sub_cancel _ _
          right_inv := fun k ↦ Subtype.ext (by
            have hk := k.2
            simp only [Finset.mem_range] at hk
            change (k.1 - n) + n = k.1
            omega) }
      exact (e.tsum_eq (fun k ↦ a k.1)).symm
  let b (n : ℕ) := d n + T n
  have hb : Antitone b := antitone_nat_of_succ_le (fun n ↦ by
    dsimp only [b]
    calc
      _ ≤ (d n + a n) + T (n + 1) := add_le_add_left (hstep n) _
      _ = _ := by rw [hdecomp n, add_assoc])
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ENNReal.tendsto_nhds_zero.mp hT ε hε)
  obtain ⟨n, hn, hr⟩ := hvis N
  have hx : b (n + 1) ≤ ε := by dsimp only [b]; rw [hr, zero_add]; exact hN _ (by omega)
  exact eventually_atTop.mpr ⟨n + 1, fun m hm ↦
    (le_self_add : d m ≤ b m).trans ((hb hm).trans hx)⟩

/-- Oscillations of a bounded observable vanish under a recurrent schedule of single-site updates
whose influence matrix has all row sums strictly below one. -/
private lemma tendsto_tsum_oscillation_of_sweep {S : Type*} (C : S → S → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : c < 1) (hC : ∀ i, (∑' j, C i j) ≤ c) (i : ℕ → S)
    (hvis : ∀ j N, ∃ n ≥ N, i n = j) (d : ℕ → S → ℝ≥0∞)
    (hfin : (∑' j, d 0 j) ≠ ⊤)
    (hreset : ∀ n, d (n + 1) (i n) = 0)
    (hstep : ∀ n j, d (n + 1) j + (@ite ℝ≥0∞ (i n = j) (Classical.propDecidable _) (d n (i n)) 0) ≤
      d n j + d n (i n) * C (i n) j) :
    (∀ n, (∑' j, d n j) ≠ ⊤) ∧ Tendsto (fun n ↦ (∑' j, d n j).toReal) atTop (𝓝 0) := by
  classical
  let a (n : ℕ) := d n (i n)
  let s (n : ℕ) := ∑' j, d n j
  have htotal (n : ℕ) : s (n + 1) + a n ≤ s n + a n * c :=
    oscillation_step_tsum_le (d n) (d (n + 1)) (i n) (C (i n)) c (hC (i n)) (hstep n)
  obtain ⟨hsf, haf⟩ := tsum_removed_ne_top hc hfin (fun n ↦ le_tsum (d n) (i n)) htotal
  let M (j : S) := d 0 j + ∑' n, a n * C (i n) j
  have hM : (∑' j, M j) ≠ ⊤ := by
    have hle : (∑' j, M j) ≤ s 0 + c * ∑' n, a n := by
      change (∑' j, (d 0 j + ∑' n, a n * C (i n) j)) ≤ (∑' j, d 0 j) + c * ∑' n, a n
      rw [tsum_add, tsum_comm (f := fun j n ↦ a n * C (i n) j)]
      apply add_le_add_right
      calc
        _ = ∑' n, a n * (∑' j, C (i n) j) := by simp_rw [ENNReal.tsum_mul_left]
        _ ≤ ∑' n, c * a n := tsum_le_tsum fun n ↦ by
          rw [mul_comm c]
          gcongr
          exact hC (i n)
        _ = _ := by rw [ENNReal.tsum_mul_left]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨hfin, ENNReal.mul_ne_top hc.ne_top haf⟩) hle
  have hrec (n : ℕ) (j : S) : d (n + 1) j ≤ d n j + a n * C (i n) j :=
    le_self_add.trans (hstep n j)
  have hpart (n : ℕ) (j : S) : d n j ≤ d 0 j + ∑ k ∈ Finset.range n, a k * C (i k) j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      exact (hrec n j).trans (add_le_add_left ih _)
  have hdom (n : ℕ) (j : S) : d n j ≤ M j :=
    (hpart n j).trans (add_le_add_right (sum_le_tsum _) _)
  have hpt (j : S) : Tendsto (fun n ↦ (d n j).toReal) atTop (𝓝 0) := by
    have he (n : ℕ) : d (n + 1) j ≤ d n j + a n :=
      (hrec n j).trans (by
        have hj := (le_tsum (C (i n)) j |>.trans (hC (i n))).trans hc.le
        have hmul : a n * C (i n) j ≤ a n * 1 := by gcongr
        simpa only [mul_one] using add_le_add_right hmul (d n j))
    have h := tendsto_zero_of_resets (d := fun n ↦ d n j) (a := a) haf he (fun N ↦ by
      obtain ⟨n, hn, hi⟩ := hvis j N
      exact ⟨n, hn, hi ▸ hreset n⟩)
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have h := tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal hM)
    (f := fun n j ↦ (d n j).toReal) (g := fun _ ↦ (0 : ℝ)) hpt
    (Eventually.of_forall fun n j ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono (ne_top_of_tsum_ne_top hM j) (hdom n j))
  refine ⟨hsf, ?_⟩
  simpa only [tsum_zero, ENNReal.tsum_toReal_eq (fun j ↦ ne_top_of_tsum_ne_top (hsf _) j)] using h

omit [MeasurableSpace E] in
/-- A bounded local observable has a finite total site oscillation. -/
private lemma tsum_siteOscillation_ne_top_of_local {f : (S → E) → ℝ} (hf : IsLocalFunction f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) : (∑' j, siteOscillation f j) ≠ ⊤ := by
  classical
  obtain ⟨D, hD⟩ := isLocalFunction_def.mp hf
  have hzero (j : S) (hj : j ∉ D) : siteOscillation f j = 0 := by
    unfold siteOscillation
    refine le_antisymm ?_ (by positivity)
    refine iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun hxy ↦ ?_
    rw [hD x y (fun k hk ↦ hxy k (fun e ↦ hj (e ▸ hk))), sub_self, abs_zero, ENNReal.ofReal_zero]
  rw [tsum_eq_sum (s := D) hzero]
  exact (ENNReal.sum_lt_top.mpr (fun j _ ↦
    (siteOscillation_le hB j).trans_lt ENNReal.ofReal_lt_top)).ne

omit [MeasurableSpace E] in
/-- Changing finitely many coordinates costs at most the sum of their oscillations. -/
private lemma ofReal_abs_sub_le_sum_splice {f : (S → E) → ℝ} (x y : S → E) (D : Finset S) :
    letI := Classical.decEq S
    ENNReal.ofReal |f (splice D (D.restrict x) y) - f y| ≤ ∑ j ∈ D, siteOscillation f j := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    have h : splice ∅ ((∅ : Finset S).restrict x) y = y := by
      funext j
      simp only [splice_def, dite_eq_right (Finset.notMem_empty j)]
    simp only [h, sub_self, abs_zero, ENNReal.ofReal_zero, Finset.sum_empty, le_refl]
  | insert j D hj ih =>
    let z := splice D (D.restrict x) y
    let w := splice (insert j D) ((insert j D).restrict x) y
    have h : ∀ k, k ≠ j → w k = z k := by
      intro k hk
      simp only [w, z, splice_def, Finset.mem_insert, hk, false_or]
      by_cases hD : k ∈ D <;> simp only [hD, dite_true, dite_false, Finset.restrict_def]
    rw [Finset.sum_insert hj]
    calc
      ENNReal.ofReal |f w - f y| ≤ ENNReal.ofReal (|f w - f z| + |f z - f y|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
      _ = ENNReal.ofReal |f w - f z| + ENNReal.ofReal |f z - f y| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add (ofReal_abs_sub_le_siteOscillation h) ih

omit [MeasurableSpace E] in
/-- For uniformly local functions the total site oscillation bounds every change. -/
private lemma abs_sub_le_tsum_siteOscillation {f : (S → E) → ℝ} (hf : IsUniformlyLocal f)
    (htop : (∑' j, siteOscillation f j) ≠ ⊤) (x y : S → E) :
    |f x - f y| ≤ (∑' j, siteOscillation f j).toReal := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨D, hD⟩ := hf ε hε
  let z := splice D (D.restrict x) y
  have hx : |f x - f z| < ε := hD x z (fun j hj ↦ by
    simp only [z, splice_def, dite_eq_left hj, Finset.restrict_def])
  have hy : |f z - f y| ≤ (∑' j, siteOscillation f j).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).mp
      ((ofReal_abs_sub_le_sum_splice x y D).trans (sum_le_tsum D))
  linarith [abs_sub_le (f x) (f z) (f y)]

/-- The oscillation sweep gives equality of expectations of bounded local observables. -/
private lemma integral_eq_of_dobrushin [Countable S] [Nonempty S]
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (hq : IsQuasilocal γ)
    {c : ℝ≥0∞} (hc : c < 1) (hC : ∀ i, ∑' j, dobrushinCoeff γ i j ≤ c)
    {μ ν : Measure (S → E)} (hμ : IsGibbs γ μ) (hν : IsGibbs γ ν)
    {f : (S → E) → ℝ} (hl : IsLocalFunction f) (hm : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  classical
  let _ := (isGibbs_def.mp hμ).1
  let _ := (isGibbs_def.mp hν).1
  let a := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  obtain ⟨e, he⟩ := exists_surjective_nat S
  let i (n : ℕ) := e (Nat.unpair n).1
  have hvis (j : S) (N : ℕ) : ∃ n ≥ N, i n = j := by
    obtain ⟨m, hmj⟩ := he j
    exact ⟨Nat.pair m N, Nat.right_le_pair _ _, by simpa only [i, Nat.unpair_pair] using hmj⟩
  let F : ℕ → (S → E) → ℝ := Nat.rec f (fun n g ↦ siteMean γ (i n) g)
  have hF (n : ℕ) : Measurable (F n) ∧ (∀ x, |F n x| ≤ B) ∧ IsUniformlyLocal (F n) := by
    induction n with
    | zero => exact ⟨hm, hB, hl.isUniformlyLocal⟩
    | succ n ih =>
      exact ⟨measurable_siteMean hγ _ ih.1, abs_siteMean_le hγ _ ih.2.1,
        isUniformlyLocal_siteMean hγ hq _ a ih.1 ih.2.1 ih.2.2⟩
  let d (n : ℕ) := siteOscillation (F n)
  have hres (n : ℕ) : d (n + 1) (i n) = 0 := siteOscillation_siteMean_same hγ _ _
  have hstep (n : ℕ) (j : S) : d (n + 1) j + (if i n = j then d n (i n) else 0) ≤
      d n j + d n (i n) * dobrushinCoeff γ (i n) j := by
    by_cases hj : i n = j
    · subst j
      simp only [hres, ite_true, zero_add, le_self_add]
    · rw [ite_eq_right hj, add_zero]
      exact siteOscillation_siteMean_le hγ _ _ (hF n).1 (hF n).2.1
  obtain ⟨hfin, hlim⟩ := tendsto_tsum_oscillation_of_sweep (dobrushinCoeff γ) hc hC i hvis d
    (tsum_siteOscillation_ne_top_of_local hl hB) hres hstep
  have hinv (η : Measure (S → E)) (hη : IsGibbs γ η) (n : ℕ) :
      (∫ x, F n x ∂η) = ∫ x, f x ∂η := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let _ := (isGibbs_def.mp hη).1
      exact (integral_siteMean_of_consistent hγ η _ ((isGibbs_def.mp hη).2 _)
        (hF n).1 (hF n).2.1).trans ih
  have hbound (η : Measure (S → E)) [IsProbabilityMeasure η] (n : ℕ) :
      |(∫ x, F n x ∂η) - F n a| ≤ (∑' j, d n j).toReal := by
    have hconst : (∫ _ : S → E, F n a ∂η) = F n a := by simp
    rw [← hconst, ← integral_sub (integrable_of_bounded (hF n).1 (hF n).2.1) (integrable_const _)]
    exact abs_integral_le_of_abs_le
      (fun x ↦ abs_sub_le_tsum_siteOscillation (hF n).2.2 (hfin n) x a)
  have hle (n : ℕ) : |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 2 * (∑' j, d n j).toReal := by
    rw [← hinv μ hμ n, ← hinv ν hν n]
    have hx := hbound ν n
    rw [abs_sub_comm] at hx
    linarith [abs_sub_le (∫ x, F n x ∂μ) (F n a) (∫ x, F n x ∂ν), hbound μ n]
  have hzero : Tendsto (fun n ↦ 2 * (∑' j, d n j).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have h := le_of_tendsto_of_tendsto tendsto_const_nhds hzero (Eventually.of_forall hle)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- SYNOPSIS item 62, Dobrushin's uniqueness theorem: a quasilocal specification with
`sup_i ∑_j C_{ij} < 1` has at most one Gibbs measure. -/
theorem gibbsSet_subsingleton_of_dobrushin [Countable S]
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (hq : IsQuasilocal γ)
    (hD : ∃ c < 1, ∀ i, ∑' j, dobrushinCoeff γ i j ≤ c) : (gibbsSet γ).Subsingleton := by
  classical
  intro μ hμ ν hν
  have hgμ := mem_gibbsSet.mp hμ
  have hgν := mem_gibbsSet.mp hν
  let _ := (isGibbs_def.mp hgμ).1
  let _ := (isGibbs_def.mp hgν).1
  cases isEmpty_or_nonempty S with
  | inl hempty =>
    have _ : Subsingleton (S → E) := ⟨fun x y ↦ funext fun i ↦ isEmptyElim i⟩
    ext A hA
    rcases A.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · simp [h]
    have hu : A = univ := eq_univ_of_forall fun y ↦ (Subsingleton.elim x y) ▸ hx
    simp [hu]
  | inr hne =>
    obtain ⟨c, hc, hC⟩ := hD
    let π (D : Finset S) := μ.map (D.restrict (π := fun _ : S ↦ E))
    let _ (D : Finset S) : IsProbabilityMeasure (π D) :=
      (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
    have hproj : IsProjectiveLimit ν π := by
      intro D
      apply Measure.ext
      intro A hA
      let Q := (D.restrict (π := fun _ : S ↦ E)) ⁻¹' A
      have hQ : MeasurableSet Q := D.measurable_restrict hA
      let f : (S → E) → ℝ := Q.indicator 1
      have hloc : IsLocalFunction f := isLocalFunction_def.mpr ⟨D, fun x y hxy ↦ by
        have he : D.restrict (π := fun _ : S ↦ E) x = D.restrict y := funext fun j ↦ hxy j.1 j.2
        have hm : x ∈ Q ↔ y ∈ Q := by simp only [Q, mem_preimage, he]
        by_cases hx : x ∈ Q
        · simp only [f, indicator_of_mem hx, indicator_of_mem (hm.mp hx), Pi.one_apply]
        · simp only [f, indicator_of_notMem hx, indicator_of_notMem (fun hy ↦ hx (hm.mpr hy))]⟩
      have hf : Measurable f := measurable_const.indicator hQ
      have hbound (x : S → E) : |f x| ≤ 1 := by
        by_cases hx : x ∈ Q <;> simp [f, hx]
      have hi := integral_eq_of_dobrushin hγ hq hc hC hgμ hgν hloc hf hbound
      simp only [f, integral_indicator_one hQ, measureReal_def] at hi
      have hR : Measurable (D.restrict (π := fun _ : S ↦ E)) := D.measurable_restrict
      rw [Measure.map_apply hR hA]
      simp only [π, Measure.map_apply hR hA]
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hi |>.symm
    exact IsProjectiveLimit.unique (P := π) (fun _ ↦ rfl) hproj

/-- A uniform bound on signed event-mass differences bounds total variation. -/
private lemma tvSup_le_of_measureReal_sub_le {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C : ℝ}
    (h : ∀ A, MeasurableSet A → μ.real A - ν.real A ≤ C) : tvSup μ ν ≤ ENNReal.ofReal C := by
  have lift {α β : Measure X} [IsFiniteMeasure α] [IsFiniteMeasure β] (A : Set X)
      (hC : α.real A - β.real A ≤ C) : α A - β A ≤ ENNReal.ofReal C := by
    by_cases hab : β A ≤ α A
    · rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top (measure_ne_top α A) tsub_le_self),
        ENNReal.toReal_sub_of_le hab (measure_ne_top α A)]
      exact ENNReal.ofReal_le_ofReal hC
    · rw [tsub_eq_zero_of_le (le_of_not_ge hab)]
      exact zero_le
  rw [tvSup_def]
  refine iSup_le fun A ↦ iSup_le fun hA ↦ sup_le (lift A (h A hA)) (lift A ?_)
  have hc := h Aᶜ hA.compl
  rw [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hA] at hc
  linarith only [hc]

/-- The deterministic sweep gives a common oscillation bound for all observables
with a fixed finite support and bound. -/
private lemma exists_uniform_sweep_bound {γ : Finset S → (S → E) → Measure (S → E)}
    (hγ : IsSpecification γ) (hq : IsQuasilocal γ) (a : S → E)
    {c : ℝ≥0∞} (hc : c < 1) (hC : ∀ i, ∑' j, dobrushinCoeff γ i j ≤ c)
    (i : ℕ → S) (hvis : ∀ j N, ∃ n ≥ N, i n = j) (D : Finset S) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ {f : (S → E) → ℝ},
      (∀ x y, (∀ j ∈ D, x j = y j) → f x = f y) → Measurable f → (∀ x, |f x| ≤ 1) →
      ∀ n x y, |Nat.rec f (fun k g ↦ siteMean γ (i k) g) n x -
        Nat.rec f (fun k g ↦ siteMean γ (i k) g) n y| ≤ b n := by
  classical
  let d : ℕ → S → ℝ≥0∞ := Nat.rec (fun j ↦ if j ∈ D then 2 else 0)
    (fun n d j ↦ if i n = j then 0 else d j + d (i n) * dobrushinCoeff γ (i n) j)
  have hres (n : ℕ) : d (n + 1) (i n) = 0 := by simp [d]
  have hstep (n : ℕ) (j : S) : d (n + 1) j + (if i n = j then d n (i n) else 0) ≤
      d n j + d n (i n) * dobrushinCoeff γ (i n) j := by
    change (if i n = j then 0 else d n j + d n (i n) * dobrushinCoeff γ (i n) j) + _ ≤ _
    by_cases hj : i n = j
    · subst j
      simp only [ite_true, zero_add, le_self_add]
    · rw [ite_eq_right hj, ite_eq_right hj, add_zero]
  have hd₀ : (∑' j, d 0 j) ≠ ⊤ := by
    rw [tsum_eq_sum (s := D) (fun j hj ↦ by simp [d, hj])]
    exact (ENNReal.sum_lt_top.mpr fun j hj ↦ by simp [d, hj]).ne
  obtain ⟨hfin, hlim⟩ := tendsto_tsum_oscillation_of_sweep _ hc hC i hvis d hd₀ hres hstep
  refine ⟨fun n ↦ (∑' j, d n j).toReal, hlim, fun {f} hf hm hB ↦ ?_⟩
  let F : ℕ → (S → E) → ℝ := Nat.rec f (fun k g ↦ siteMean γ (i k) g)
  have hF (n : ℕ) : Measurable (F n) ∧ (∀ x, |F n x| ≤ 1) ∧ IsUniformlyLocal (F n) := by
    induction n with
    | zero => exact ⟨hm, hB, (isLocalFunction_def.mpr ⟨D, hf⟩).isUniformlyLocal⟩
    | succ n ih =>
      exact ⟨measurable_siteMean hγ _ ih.1, abs_siteMean_le hγ _ ih.2.1,
        isUniformlyLocal_siteMean hγ hq _ a ih.1 ih.2.1 ih.2.2⟩
  have hdom (n : ℕ) (j : S) : siteOscillation (F n) j ≤ d n j := by
    induction n generalizing j with
    | zero =>
      change siteOscillation f j ≤ (if j ∈ D then 2 else 0)
      by_cases hj : j ∈ D
      · simpa only [ite_eq_left hj, show (2 : ℝ) * 1 = 2 by norm_num,
          ENNReal.ofReal_ofNat] using siteOscillation_le hB j
      · rw [ite_eq_right hj]
        exact iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun hxy ↦ by
          rw [hf x y (fun k hk ↦ hxy k (fun he ↦ hj (he ▸ hk))),
            sub_self, abs_zero, ENNReal.ofReal_zero]
    | succ n ih =>
      change siteOscillation (siteMean γ (i n) (F n)) j ≤
        if i n = j then 0 else d n j + d n (i n) * dobrushinCoeff γ (i n) j
      by_cases hj : i n = j
      · subst j
        rw [ite_eq_left rfl, siteOscillation_siteMean_same hγ]
      · rw [ite_eq_right hj]
        exact (siteOscillation_siteMean_le hγ _ _ (hF n).1 (hF n).2.1).trans
          (by gcongr <;> exact ih _)
  intro n x y
  have hle : (∑' j, siteOscillation (F n) j) ≤ ∑' j, d n j :=
    tsum_le_tsum (hdom n)
  exact (abs_sub_le_tsum_siteOscillation (hF n).2.2 (ne_top_of_le_ne_top (hfin n) hle) x y).trans
    (ENNReal.toReal_mono (hfin n) hle)

/-- The marginal cylinder probabilities of finite-volume laws are uniformly Cauchy. -/
private lemma gibbs_marginal_cauchy_of_sweep [DecidableEq S]
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ)
    (hq : IsQuasilocal γ) {c : ℝ≥0∞} (hc : c < 1)
    (hC : ∀ i, ∑' j, dobrushinCoeff γ i j ≤ c) (a : S → E)
    (i : ℕ → S) (hvis : ∀ j N, ∃ n ≥ N, i n = j) (D : Finset S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N, ∀ A : Set (D → E), MeasurableSet A →
      |(γ ((Finset.range n).image i) a).real (D.restrict ⁻¹' A) -
        (γ ((Finset.range k).image i) a).real (D.restrict ⁻¹' A)| < ε := by
  obtain ⟨b, hb, hbF⟩ := exists_uniform_sweep_bound hγ hq a hc hC i hvis D
  obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.mp hb (ε / 2) (by positivity)).exists
  simp only [Real.dist_eq, sub_zero] at hN
  refine ⟨N, fun n hn k hk A hA ↦ ?_⟩
  let Q := D.restrict (π := fun _ : S ↦ E) ⁻¹' A
  let f := Q.indicator (1 : (S → E) → ℝ)
  have hQ : MeasurableSet Q := D.measurable_restrict hA
  have hloc (x y : S → E) (hxy : ∀ j ∈ D, x j = y j) : f x = f y := by
    have he : D.restrict (π := fun _ ↦ E) x = D.restrict y := funext fun j ↦ hxy j.1 j.2
    have hmem : x ∈ Q ↔ y ∈ Q := by simp only [Q, mem_preimage, he]
    by_cases hx : x ∈ Q
    · simp only [f, indicator_of_mem hx, indicator_of_mem (hmem.mp hx), Pi.one_apply]
    · simp only [f, indicator_of_notMem hx, indicator_of_notMem (hmem.not.mp hx)]
  have hf : Measurable f := measurable_const.indicator hQ
  have hB (x : S → E) : |f x| ≤ 1 := by by_cases hx : x ∈ Q <;> simp [f, hx]
  let F : ℕ → (S → E) → ℝ := Nat.rec f (fun m g ↦ siteMean γ (i m) g)
  have hF (m : ℕ) : Measurable (F m) ∧ ∀ x, |F m x| ≤ 1 := by
    induction m with
    | zero => exact ⟨hf, hB⟩
    | succ m ih => exact ⟨measurable_siteMean hγ _ ih.1, abs_siteMean_le hγ _ ih.2⟩
  let μ (m : ℕ) := γ ((Finset.range m).image i) a
  let _ (m : ℕ) : IsProbabilityMeasure (μ m) := hγ.isProbabilityMeasure _ _
  have hinv (m l : ℕ) (hl : l ≤ m) : (∫ x, F l x ∂μ m) = ∫ x, f x ∂μ m := by
    induction l with
    | zero => rfl
    | succ l ih =>
      have hi : ({i l} : Finset S) ⊆ (Finset.range m).image i :=
        Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr hl, rfl⟩)
      exact (integral_siteMean_of_consistent hγ (μ m) (i l)
        (fun B hB ↦ (hγ.consistent {i l} _ hi a B hB).symm) (hF l).1 (hF l).2).trans
        (ih (Nat.le_of_succ_le hl))
  have hbound (m : ℕ) (hm : N ≤ m) : |(μ m).real Q - F N a| ≤ b N := by
    rw [← integral_indicator_one hQ]
    change |(∫ x, f x ∂μ m) - F N a| ≤ _
    rw [← hinv m N hm, ← show (∫ _ : S → E, F N a ∂μ m) = F N a from by simp,
      ← integral_sub (integrable_of_bounded (hF N).1 (hF N).2) (integrable_const _)]
    exact abs_integral_le_of_abs_le fun x ↦ hbF hloc hf hB N x a
  have hk' := hbound k hk
  rw [abs_sub_comm] at hk'
  change |(μ n).real Q - (μ k).real Q| < ε
  linarith only [abs_sub_le ((μ n).real Q) (F N a) ((μ k).real Q), hbound n hn, hk',
    (le_abs_self (b N)).trans_lt hN]

/-- Probability marginals of finite-volume laws converge locally to a Gibbs law. -/
private lemma isGibbs_of_tendstoLocally [DecidableEq S]
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (hq : IsQuasilocal γ)
    {m : ℕ → Measure (S → E)} {μ : Measure (S → E)}
    [∀ n, IsProbabilityMeasure (m n)] [IsProbabilityMeasure μ]
    (hl : TendstoLocally atTop m μ)
    (hDLR : ∀ Λ : Finset S, ∀ᶠ n in atTop, ∀ A, MeasurableSet A →
      m n A = ∫⁻ ω, γ Λ ω A ∂m n) : IsGibbs γ μ := by
  refine isGibbs_def.mpr ⟨inferInstance, fun Λ A hA ↦ ?_⟩
  have hm := measurable_specification hγ Λ
  let π (D : Finset S) := μ.map (D.restrict (π := fun _ : S ↦ E))
  let _ (D : Finset S) : IsProbabilityMeasure (π D) :=
    (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
  have hproj : IsProjectiveLimit (μ.bind (γ Λ)) π := by
    intro D
    refine Measure.ext fun B hB ↦ ?_
    have hR : Measurable (D.restrict (π := fun _ : S ↦ E)) := D.measurable_restrict
    rw [Measure.map_apply hR hB, Measure.bind_apply (hR hB) hm.aemeasurable]
    simp only [π, Measure.map_apply hR hB]
    let Q := D.restrict (π := fun _ : S ↦ E) ⁻¹' B
    let f : (S → E) → ℝ := Q.indicator 1
    have hQ := hR hB
    have hloc : IsLocalFunction f := isLocalFunction_def.mpr ⟨D, fun x y hxy ↦ by
      have he : D.restrict (π := fun _ ↦ E) x = D.restrict y := funext fun j ↦ hxy j.1 j.2
      have hmem : x ∈ Q ↔ y ∈ Q := by simp only [Q, mem_preimage, he]
      by_cases hx : x ∈ Q
      · simp only [f, indicator_of_mem hx, indicator_of_mem (hmem.mp hx), Pi.one_apply]
      · simp only [f, indicator_of_notMem hx, indicator_of_notMem (hmem.not.mp hx)]⟩
    have hbound (x : S → E) : |f x| ≤ 1 := by
      by_cases hx : x ∈ Q <;> simp [f, hx]
    have hf : Measurable f := measurable_const.indicator hQ
    let g (ω : S → E) := (γ Λ ω).real Q
    have hg : Measurable g :=
      ((hγ.measurable Λ Q hQ).mono (outsideSigma_le _) le_rfl).ennreal_toReal
    have he (ω : S → E) : (∫ x, f x ∂γ Λ ω) = g ω := integral_indicator_one hQ
    have hgb (ω : S → E) : |g ω| ≤ 1 := by
      rw [← he ω]
      let _ := hγ.isProbabilityMeasure Λ ω
      exact abs_integral_le_of_abs_le hbound
    have hgl : Tendsto (fun n ↦ ∫ x, g x ∂m n) atTop (𝓝 (∫ x, g x ∂μ)) :=
      hl.tendsto_integral_of_oscillation (Eventually.of_forall fun _ ↦ inferInstance)
        hg 1 hgb (by simpa only [he] using hq Λ f hloc hf ⟨1, hbound⟩)
    have hge (η : Measure (S → E)) [IsProbabilityMeasure η] : ENNReal.ofReal (∫ x, g x ∂η) = ∫⁻ x, γ Λ x Q ∂η := by
      rw [ofReal_integral_eq_lintegral_ofReal (integrable_of_bounded hg hgb) (Eventually.of_forall fun _ ↦
        ENNReal.toReal_nonneg)]
      exact lintegral_congr fun ω ↦ by
        let _ := hγ.isProbabilityMeasure Λ ω
        exact ofReal_measureReal (measure_ne_top _ _)
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hgl
    rw [hge μ] at ht
    symm
    refine tendsto_nhds_unique (hl.tendsto_cylinder (Eventually.of_forall fun _ ↦ inferInstance) D hB)
      (ht.congr' ?_)
    filter_upwards [hDLR Λ] with n hn
    exact (hge (m n)).trans (hn Q hQ).symm
  have he : μ = μ.bind (γ Λ) := IsProjectiveLimit.unique (P := π) (fun _ ↦ rfl) hproj
  exact congrArg (fun ν : Measure (S → E) ↦ ν A) he |>.trans (Measure.bind_apply hA hm.aemeasurable)

/-- SYNOPSIS item 62: with a nonempty standard Borel state space, Dobrushin's condition gives
exactly one Gibbs measure. -/
theorem existsUnique_gibbs_of_dobrushin [Countable S] [Nonempty E] [StandardBorelSpace E]
    {γ : Finset S → (S → E) → Measure (S → E)} (hγ : IsSpecification γ) (hq : IsQuasilocal γ)
    (hD : ∃ c < 1, ∀ i, ∑' j, dobrushinCoeff γ i j ≤ c) : ∃! μ, IsGibbs γ μ := by
  classical
  obtain ⟨c, hc, hC⟩ := hD
  let a : S → E := fun _ ↦ Classical.choice inferInstance
  have hex : ∃ μ, IsGibbs γ μ := by
    cases isEmpty_or_nonempty S with
    | inl hS =>
      refine ⟨γ ∅ a, isGibbs_def.mpr ⟨hγ.isProbabilityMeasure _ _, fun Λ A hA ↦ ?_⟩⟩
      exact (hγ.consistent Λ ∅ (fun i _ ↦ isEmptyElim i) a A hA).symm
    | inr hS =>
      obtain ⟨e, he⟩ := exists_surjective_nat S
      let i (n : ℕ) := e (Nat.unpair n).1
      have hvis (j : S) (N : ℕ) : ∃ n ≥ N, i n = j := by
        obtain ⟨k, hk⟩ := he j
        exact ⟨Nat.pair k N, Nat.right_le_pair _ _, by simpa only [i, Nat.unpair_pair] using hk⟩
      let Δ (n : ℕ) := (Finset.range n).image i
      let m (n : ℕ) := γ (Δ n) a
      let _ (n : ℕ) : IsProbabilityMeasure (m n) := hγ.isProbabilityMeasure _ _
      have hDLR (Λ : Finset S) : ∀ᶠ n in atTop, ∀ A, MeasurableSet A →
          m n A = ∫⁻ ω, γ Λ ω A ∂m n := by
        choose k hk using fun j ↦ hvis j 0
        refine eventually_atTop.mpr ⟨Λ.sup k + 1, fun n hn A hA ↦ ?_⟩
        refine (hγ.consistent Λ (Δ n) (fun j hj ↦ ?_) a A hA).symm
        exact Finset.mem_image.mpr ⟨k j, Finset.mem_range.mpr (by
          have h := Finset.le_sup (f := k) hj
          omega), (hk j).2⟩
      have hex (D : Finset S) :
          ∃ ν : Measure (D → E), IsProbabilityMeasure ν ∧ ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
            ∀ A, MeasurableSet A → |((m n).map D.restrict).real A - ν.real A| ≤ ε := by
        let _ (n : ℕ) : IsProbabilityMeasure ((m n).map D.restrict) :=
          (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
        apply exists_prob_of_uniform_cauchy
        intro ε hε
        obtain ⟨N, hN⟩ := gibbs_marginal_cauchy_of_sweep hγ hq hc hC a i hvis D ε hε
        exact ⟨N, fun n hn k hk A hA ↦ by
          have hR : Measurable (D.restrict (π := fun _ : S ↦ E)) := D.measurable_restrict
          rw [map_measureReal_apply hR hA, map_measureReal_apply hR hA]
          exact hN n hn k hk A hA⟩
      choose family hprob ht using hex
      let _ := upgradeStandardBorel E
      let _ (D : Finset S) := hprob D
      have hlim (D : Finset S) (A : Set (D → E)) (hA : MeasurableSet A) :
          Tendsto (fun n ↦ (m n).map D.restrict A) atTop (𝓝 (family D A)) := by
        have hr : Tendsto (fun n ↦ ((m n).map D.restrict).real A) atTop
            (𝓝 ((family D).real A)) := by
          refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
          filter_upwards [ht D (ε / 2) (by positivity)] with n hn
          rw [Real.dist_eq]
          exact (hn A hA).trans_lt (half_lt_self hε)
        have hv := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
        rw [ofReal_measureReal (measure_ne_top (family D) A)] at hv
        exact hv.congr (fun n ↦ ofReal_measureReal (measure_ne_top _ _))
      have hP : IsProjectiveMeasureFamily (α := fun _ : S ↦ E) family := by
        intro J D hD
        refine Measure.ext fun A hA ↦ ?_
        have hR := Finset.measurable_restrict₂ (X := fun _ : S ↦ E) hD
        rw [Measure.map_apply hR hA]
        refine tendsto_nhds_unique (hlim D A hA) ((hlim J _ (hR hA)).congr ?_)
        intro n
        rw [← Measure.map_apply hR hA, Measure.map_map hR J.measurable_restrict,
          Finset.restrict₂_comp_restrict]
      let μ := projectiveLimit (α := fun _ : S ↦ E) family hP
      have hμ : IsProjectiveLimit μ family := isProjectiveLimit_projectiveLimit hP
      refine ⟨μ, isGibbs_of_tendstoLocally hγ hq (tendstoLocally_def.mpr ?_) hDLR⟩
      intro f hloc hf hb
      obtain ⟨D, hD⟩ := isLocalFunction_def.mp hloc
      obtain ⟨B, hB⟩ := hb
      let g (ζ : D → E) := f (splice D ζ a)
      have hg : Measurable g := hf.comp (measurable_splice D a)
      have hgf (ω : S → E) : g (D.restrict ω) = f ω :=
        hD _ _ fun j hj ↦ by simp only [splice_def, dite_eq_left hj, Finset.restrict_def]
      have hmap (ν : Measure (S → E)) :
          (∫ x, g x ∂ν.map D.restrict) = ∫ x, f x ∂ν := by
        rw [integral_map D.measurable_restrict.aemeasurable hg.aestronglyMeasurable]
        exact integral_congr_ae (ae_of_all _ hgf)
      refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
      let δ := ε / (2 * |B| + 1)
      have hδ : 0 < δ := div_pos hε (by positivity)
      filter_upwards [ht D δ hδ] with n hn
      let _ : IsProbabilityMeasure ((m n).map D.restrict) :=
        (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
      have hv := tvSup_le_of_measureReal_sub_le (μ := (m n).map D.restrict) (ν := family D)
        (fun A hA ↦ (le_abs_self _).trans (hn A hA))
      have hv' : (tvSup ((m n).map D.restrict) (family D)).toReal ≤ δ := by
        simpa only [ENNReal.toReal_ofReal hδ.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
      have hB' (z : D → E) : |g z| ≤ |B| := (hB _).trans (le_abs_self _)
      have hdiff (z w : D → E) : |g z - g w| ≤ 2 * |B| :=
        (abs_sub _ _).trans (by linarith only [hB' z, hB' w])
      rw [Real.dist_eq, ← hmap (m n), ← hmap μ, hμ D]
      refine ((abs_integral_sub_le_mul_tvSup hg hB' hdiff).trans
        (mul_le_mul_of_nonneg_left hv' (by positivity))).trans_lt ?_
      dsimp only [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith only [hε]
  obtain ⟨μ, hμ⟩ := hex
  exact ⟨μ, hμ, fun ν hν ↦
    gibbsSet_subsingleton_of_dobrushin hγ hq ⟨c, hc, hC⟩
      (mem_gibbsSet.mpr hν) (mem_gibbsSet.mpr hμ)⟩

/-- Cylinder probabilities controlled on the same finite set imply quasilocality of the
Gibbsian specification. -/
lemma isQuasilocal_gibbsKernel [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] : IsQuasilocal (gibbsKernel Φ ρ) := by
  intro Λ f hloc hf hb ε hε
  obtain ⟨D, hD⟩ := isLocalFunction_def.mp hloc
  obtain ⟨B, hB⟩ := hb
  let δ := ε / (2 * |B| + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨T, hT⟩ := gibbsKernel_real_cylinder_oscillation hΦ hsum ρ Λ D hδ
  refine ⟨T, fun x y hxy ↦ ?_⟩
  let g (ζ : D → E) := f (Function.updateFinset x D ζ)
  have hg : Measurable g := hf.comp measurable_updateFinset
  have hg_eq (z : S → E) : g (D.restrict z) = f z := by
    exact hD _ _ (fun i hi ↦ by
      simp only [Function.updateFinset_def, dite_eq_left hi, Finset.restrict_def])
  let μ := (gibbsKernel Φ ρ Λ x).map D.restrict
  let ν := (gibbsKernel Φ ρ Λ y).map D.restrict
  have hγ := isSpecification_gibbsKernel hΦ hsum ρ
  let _ := hγ.isProbabilityMeasure Λ x
  let _ := hγ.isProbabilityMeasure Λ y
  let _ : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
  let _ : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr inferInstance
  have htv : tvSup μ ν ≤ ENNReal.ofReal δ := tvSup_le_of_measureReal_sub_le fun A hA ↦ by
    dsimp only [μ, ν]
    rw [map_measureReal_apply D.measurable_restrict hA,
      map_measureReal_apply D.measurable_restrict hA]
    exact (le_abs_self _).trans (hT x y hxy A hA).le
  have htv' : (tvSup μ ν).toReal ≤ δ := by
    simpa only [ENNReal.toReal_ofReal hδ.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top htv
  have hgB (z : D → E) : |g z| ≤ |B| := (hB _).trans (le_abs_self _)
  have hgD (z z' : D → E) : |g z - g z'| ≤ 2 * |B| := by
    calc
      _ ≤ |g z| + |g z'| := abs_sub _ _
      _ ≤ _ := by linarith only [hgB z, hgB z']
  have hm (z : S → E) :
      ∫ w, g w ∂(gibbsKernel Φ ρ Λ z).map D.restrict = ∫ w, f w ∂gibbsKernel Φ ρ Λ z := by
    rw [integral_map D.measurable_restrict.aemeasurable hg.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ hg_eq)
  have hi := (abs_integral_sub_le_mul_tvSup hg hgB hgD).trans
    (mul_le_mul_of_nonneg_left htv' (by positivity))
  rw [hm x, hm y] at hi
  refine hi.trans_lt ?_
  dsimp only [δ]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith only [hε]

/-- The derivative of the log-odds function is at least four. -/
private lemma four_mul_sub_le_log_odds_sub {a b : ℝ} (ha : a ∈ Ioo 0 1)
    (hb : b ∈ Ioo 0 1) (hle : b ≤ a) :
    4 * (a - b) ≤ (Real.log a - Real.log (1 - a)) - (Real.log b - Real.log (1 - b)) := by
  let f (x : ℝ) := Real.log x - Real.log (1 - x)
  have hd (x : ℝ) (hx : x ∈ Ioo 0 1) :
      HasDerivAt f (x⁻¹ + (1 - x)⁻¹) x := by
    have h₁ := Real.hasDerivAt_log hx.1.ne'
    have hx' : 0 < 1 - x := sub_pos.mpr hx.2
    have h₂ := (Real.hasDerivAt_log hx'.ne').comp x ((hasDerivAt_id' x).const_sub (1 : ℝ))
    refine ((h₁.sub h₂).congr_deriv (by simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun z ↦ by simp only [f, Pi.sub_apply, Function.comp_apply]
  have hd' (x : ℝ) (hx : x ∈ Ioo 0 1) : 4 ≤ deriv f x := by
    rw [(hd x hx).deriv]
    have h₀ : 0 < x := hx.1
    have h₁ : 0 < 1 - x := sub_pos.mpr hx.2
    have hc : 4 * (x * (1 - x)) ≤ 1 := by nlinarith [sq_nonneg (2 * x - 1)]
    calc
      4 ≤ 1 / (x * (1 - x)) := (le_div_iff₀ (mul_pos h₀ h₁)).mpr hc
      _ = x⁻¹ + (1 - x)⁻¹ := by
        field_simp
        ring
  apply (convex_Ioo (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt) ?_ ?_ b hb a ha hle
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · exact fun x hx ↦ hd' x (interior_subset hx)

/-- A bound on the change of odds bounds the change in the probability. -/
private lemma sub_le_of_log_odds_le {a b M : ℝ} (ha : a ∈ Ioo 0 1)
    (hb : b ∈ Ioo 0 1) (hge : b ≤ a)
    (h : a * (1 - b) ≤ Real.exp M * (b * (1 - a))) : a - b ≤ M / 4 := by
  have ha' : 0 < 1 - a := sub_pos.mpr ha.2
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  have hc := (Real.log_le_log_iff (mul_pos ha.1 hb')
    (mul_pos (Real.exp_pos M) (mul_pos hb.1 ha'))).mpr h
  rw [Real.log_mul ha.1.ne' hb'.ne',
    Real.log_mul (Real.exp_pos M).ne' (mul_pos hb.1 ha').ne',
    Real.log_exp, Real.log_mul hb.1.ne' ha'.ne'] at hc
  linarith [four_mul_sub_le_log_odds_sub ha hb hge]

/-- A positive lower and finite upper bound for the likelihood ratio bound the change in
probability of an event by one quarter of the logarithmic range of the ratio. -/
lemma measureReal_sub_le_log_ratio {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hlo : ENNReal.ofReal l • ν ≤ μ)
    (hhi : μ ≤ ENNReal.ofReal u • ν) {A : Set E} (hA : MeasurableSet A) :
    μ.real A - ν.real A ≤ (Real.log u - Real.log l) / 4 := by
  let a := μ.real A
  let b := ν.real A
  let M := Real.log u - Real.log l
  have hu := hl.trans_le hlu
  have hM : 0 ≤ M := sub_nonneg.mpr (Real.log_le_log hl hlu)
  have hlo' (B : Set E) : l * ν.real B ≤ μ.real B := by
    have h := ENNReal.toReal_mono (measure_ne_top μ B) (hlo B)
    simpa only [smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hl.le, measureReal_def] using h
  have hhi' (B : Set E) : μ.real B ≤ u * ν.real B := by
    have ht : (ENNReal.ofReal u • ν) B ≠ ⊤ := by
      rw [smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν B)
    have h := ENNReal.toReal_mono ht (hhi B)
    simpa only [smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hu.le, measureReal_def] using h
  have hlow : l * (1 - b) ≤ 1 - a := by
    simpa only [probReal_compl_eq_one_sub hA, a, b] using hlo' Aᶜ
  have hhigh : a ≤ u * b := hhi' A
  by_cases hab : a ≤ b
  · exact (sub_nonpos.mpr hab).trans (by positivity)
  have hba : b < a := lt_of_not_ge hab
  have hb₀ : 0 ≤ b := measureReal_nonneg
  have ha₁ : a ≤ 1 := by
    simpa only [a, measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := A))
  have ha : a ∈ Ioo 0 1 := ⟨hb₀.trans_lt hba, lt_of_le_of_ne ha₁ fun he ↦ by
    rw [he, sub_self] at hlow
    exact (mul_pos hl (sub_pos.mpr (hba.trans_le ha₁))).not_ge hlow⟩
  have hb : b ∈ Ioo 0 1 := ⟨lt_of_le_of_ne hb₀ fun he ↦ by
    rw [← he, mul_zero] at hhigh
    exact ha.1.not_ge hhigh, hba.trans ha.2⟩
  have hOdds : a * (1 - b) ≤ Real.exp M * (b * (1 - a)) := by
    have h : l * (a * (1 - b)) ≤ u * (b * (1 - a)) := by
      calc
        _ = a * (l * (1 - b)) := by ring
        _ ≤ (u * b) * (1 - a) := mul_le_mul hhigh hlow (mul_nonneg hl.le (sub_nonneg.mpr hb.2.le)) (by positivity)
        _ = _ := by ring
    have he : Real.exp M = u / l := by
      simp only [M, Real.exp_sub, Real.exp_log hu, Real.exp_log hl]
    rw [he, div_mul_eq_mul_div, le_div_iff₀ hl]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  exact sub_le_of_log_odds_le ha hb hba.le hOdds

/-- The oscillation of a single interaction, expressed by the supremum of ordered
differences. -/
private def potentialOscillation (Φ : Finset S → (S → E) → ℝ) (A : Finset S) : ℝ≥0∞ :=
  ⨆ x, ⨆ y, ENNReal.ofReal (Φ A x - Φ A y)

/-- Potential terms contributing to the change at site `i` when site `j` is changed. -/
private def neighborOscillation [DecidableEq S] (Φ : Finset S → (S → E) → ℝ) (i j : S) :
    ℝ≥0∞ :=
  ∑' A : {A : Finset S // i ∈ A}, if j ∈ A.1.erase i then potentialOscillation Φ A else 0

omit [MeasurableSpace E] in
/-- Summing the interaction oscillations over neighbouring sites counts each interaction
once for every site it contains other than the updated site. -/
private lemma tsum_neighborOscillation [DecidableEq S] (Φ : Finset S → (S → E) → ℝ)
    (i : S) :
    ∑' j, neighborOscillation Φ i j =
      ∑' A : {A : Finset S // i ∈ A}, ((A.1.card : ℝ≥0∞) - 1) * potentialOscillation Φ A := by
  simp only [neighborOscillation]
  rw [tsum_comm]
  congr 1
  funext A
  have hc : ((A.1.erase i).card : ℝ≥0∞) + 1 = (A.1.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_erase_add_one A.2
  rw [tsum_eq_sum (s := A.1.erase i) (fun j hj ↦ ite_eq_right hj), ← hc,
    ENNReal.add_sub_cancel_right ENNReal.one_ne_top]
  calc
    _ = ∑ _j ∈ A.1.erase i, potentialOscillation Φ A := by
      exact Finset.sum_congr rfl fun j hj ↦ ite_eq_left hj
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Replacing the spin at the updated site makes its Hamiltonian sensitive only to
interactions which contain the changed exterior site. -/
private lemma abs_singleton_hamiltonian_sub_le [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (i j : S) (x y : S → E) (hxy : ∀ k, k ≠ j → x k = y k)
    (ζ : ({i} : Finset S) → E) (ht : neighborOscillation Φ i j ≠ ⊤) :
    |hamiltonian Φ {i} (Function.updateFinset y {i} ζ) -
      hamiltonian Φ {i} (Function.updateFinset x {i} ζ)| ≤
        (neighborOscillation Φ i j).toReal := by
  let J := {A : Finset S // i ∈ A}
  let g (A : J) := if j ∈ A.1.erase i then potentialOscillation Φ A else 0
  let u := Function.updateFinset y {i} ζ
  let v := Function.updateFinset x {i} ζ
  let e : {A : Finset S // ¬ Disjoint A {i}} ≃ J :=
    Equiv.subtypeEquivRight (fun A ↦ by rw [Finset.disjoint_singleton_right, not_not])
  have hs (w : S → E) : Summable fun A : J ↦ ‖Φ A.1 w‖ :=
    e.summable_iff.mp (summable_norm_potential_of_inter hsum {i} w)
  have hh (w : S → E) : hamiltonian Φ {i} w = ∑' A : J, Φ A.1 w :=
    (hamiltonian_def Φ {i} w).trans (e.tsum_eq (fun A ↦ Φ A.1 w))
  have hgt : (∑' A, g A) ≠ ⊤ := ht
  have hterm (A : J) := ne_top_of_tsum_ne_top hgt A
  have hle (A : J) : ‖Φ A.1 u - Φ A.1 v‖ ≤ (g A).toReal := by
    rw [Real.norm_eq_abs]
    by_cases hmem : j ∈ A.1.erase i
    · rw [← ENNReal.toReal_ofReal (abs_nonneg _)]
      apply ENNReal.toReal_mono (hterm A)
      dsimp only [g]
      rw [ite_eq_left hmem]
      by_cases hab : 0 ≤ Φ A.1 u - Φ A.1 v
      · rw [abs_of_nonneg hab]
        exact le_iSup₂_of_le u v le_rfl
      · rw [abs_of_neg (lt_of_not_ge hab), neg_sub]
        exact le_iSup₂_of_le v u le_rfl
    · have he := (isPotential_def.mp hΦ A.1).2 u v (fun k hk ↦ by
        by_cases hki : k ∈ ({i} : Finset S)
        · simp only [u, v, Function.updateFinset_def, dite_eq_left hki]
        · have hkj : k ≠ j := fun h ↦ hmem (h ▸ Finset.mem_erase.mpr
            ⟨fun hi ↦ hki (Finset.mem_singleton.mpr hi), hk⟩)
          simp only [u, v, Function.updateFinset_def, dite_eq_right hki, hxy k hkj])
      rw [he, sub_self, abs_zero]
      exact ENNReal.toReal_nonneg
  have hnorm : Summable fun A : J ↦ ‖Φ A.1 u - Φ A.1 v‖ :=
    (ENNReal.summable_toReal hgt).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [hh, hh, ← (hs u).of_norm.tsum_sub (hs v).of_norm, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' A : J, ‖Φ A.1 u - Φ A.1 v‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' A : J, (g A).toReal := hnorm.tsum_le_tsum hle (ENNReal.summable_toReal hgt)
    _ = _ := (ENNReal.tsum_toReal_eq hterm).symm

/-- Two exponentially comparable laws have total variation at most half the
Hamiltonian bound. -/
private lemma tvSup_le_of_exp_comparison {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hlo : ENNReal.ofReal (r * Real.exp (-δ)) • ν ≤ μ)
    (hhi : μ ≤ ENNReal.ofReal (r * Real.exp δ) • ν) :
    tvSup μ ν ≤ ENNReal.ofReal (δ / 2) := by
  have hl := mul_pos hr (Real.exp_pos (-δ))
  have hle : r * Real.exp (-δ) ≤ r * Real.exp δ :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hδ])) hr.le
  refine tvSup_le_of_measureReal_sub_le fun A hA ↦ ?_
  have h := measureReal_sub_le_log_ratio hl hle hlo hhi hA
  rw [Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_mul hr.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp] at h
  linarith only [h]

/-- The one-site influence of a Gibbs kernel is at most half the sum of
the oscillations of the interactions containing both sites. -/
private lemma dobrushinCoeff_gibbsKernel_le [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] (i j : S)
    (ht : neighborOscillation Φ i j ≠ ⊤) :
    dobrushinCoeff (gibbsKernel Φ ρ) i j ≤ neighborOscillation Φ i j / 2 := by
  rw [dobrushinCoeff_def]
  refine iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun hxy ↦ ?_
  obtain ⟨r, hr, hlo, hhi⟩ := exists_gibbsKernel_map_smul_bounds hΦ hsum ρ {i} x y
    (measurable_pi_apply i)
    (fun ζ ↦ by simp only [Function.updateFinset_def, Finset.mem_singleton_self, dite_true])
    (fun ζ ↦ abs_singleton_hamiltonian_sub_le hΦ hsum i j x y hxy ζ ht)
  have hγ := isSpecification_gibbsKernel hΦ hsum ρ
  let _ := singleSiteLaw_isProbability hγ i x
  let _ := singleSiteLaw_isProbability hγ i y
  have h := tvSup_le_of_exp_comparison hr (ENNReal.toReal_nonneg (a := neighborOscillation Φ i j))
    (μ := singleSiteLaw (gibbsKernel Φ ρ) i x) (ν := singleSiteLaw (gibbsKernel Φ ρ) i y) hlo hhi
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_toReal ht] at h
  simpa only [ENNReal.ofReal_ofNat] using h

/-- SYNOPSIS item 62 for Gibbsian specifications: Dobrushin's condition holds, and there is at
most one Gibbs measure, when `sup_i ∑_{A ∋ i} (|A| - 1)(sup Φ_A - inf Φ_A) < 2`. -/
theorem gibbsSet_subsingleton_of_oscillation [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ]
    (hosc : ∃ c < 2, ∀ i, ∑' A : {A : Finset S // i ∈ A},
      ((A.1.card : ℝ≥0∞) - 1) * ⨆ (ω : S → E) (ω' : S → E), ENNReal.ofReal (Φ A ω - Φ A ω') ≤
        c) :
    (∃ c < 1, ∀ i, ∑' j, dobrushinCoeff (gibbsKernel Φ ρ) i j ≤ c) ∧
      (gibbsSet (gibbsKernel Φ ρ)).Subsingleton := by
  obtain ⟨c, hc, hrow⟩ := hosc
  have hsmall : c / 2 < 1 := by
    exact (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mpr (by simpa only [one_mul] using hc)
  have hD : ∀ i, ∑' j, dobrushinCoeff (gibbsKernel Φ ρ) i j ≤ c / 2 := by
    intro i
    have hsum' : ∑' j, neighborOscillation Φ i j ≤ c := by
      rw [tsum_neighborOscillation]
      simpa only [potentialOscillation] using hrow i
    have ht (j : S) : neighborOscillation Φ i j ≠ ⊤ :=
      ne_top_of_tsum_ne_top (ne_top_of_le_ne_top (hc.trans_le le_top).ne hsum') j
    calc
      _ ≤ ∑' j, neighborOscillation Φ i j / 2 :=
        tsum_le_tsum fun j ↦ dobrushinCoeff_gibbsKernel_le hΦ hsum ρ i j (ht j)
      _ ≤ c / 2 := by
        simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
        exact mul_le_mul_of_nonneg_right hsum' bot_le
  exact ⟨⟨c / 2, hsmall, hD⟩, gibbsSet_subsingleton_of_dobrushin
    (isSpecification_gibbsKernel hΦ hsum ρ) (isQuasilocal_gibbsKernel hΦ hsum ρ) ⟨_, hsmall, hD⟩⟩

end MSSS
