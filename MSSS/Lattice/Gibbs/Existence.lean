module

public import MSSS.Lattice.Gibbs.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.KolmogorovExtension

/-!
# Local limits and existence of lattice Gibbs measures

An absolutely summable potential on a countable site set gives a specification with nonempty,
convex, and compact set of Gibbs measures for a finite nonzero reference measure on a standard
Borel state space. The specification's consistency uses Mathlib's marginalisation of a function
over a finite set of coordinates. Uniform domination of finite-dimensional laws gives countably
additive ultrafilter limits, and Mathlib's Kolmogorov extension supplies the limiting measure.
The finite-range approximations to the Hamiltonian let the DLR equations pass to this limit.

## Main results

* `MSSS.exists_measure_of_eventually_le`, setwise ultrafilter limits under finite domination.
* `MSSS.tendsto_integral_of_tendsto_measure_apply`, convergence of dominated integrals.
* `MSSS.gibbsSet_nonempty_convex_compact`, SYNOPSIS item 60.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Function

namespace MSSS

variable {S E : Type*} [MeasurableSpace E]

/-- The uniform extended nonnegative bound on a potential term. -/
private def potentialEnvelope (Φ : Finset S → (S → E) → ℝ) (A : Finset S) : ℝ≥0∞ :=
  ⨆ ω, ENNReal.ofReal |Φ A ω|

omit [MeasurableSpace E] in
/-- The total potential envelope over the interactions touching a finite region is finite. -/
private lemma tsum_potentialEnvelope_lt_top {Φ : Finset S → (S → E) → ℝ}
    (hsum : IsAbsolutelySummable Φ) (Λ : Finset S) :
    (∑' A : {A : Finset S // ¬ Disjoint A Λ}, potentialEnvelope Φ A) < ⊤ := by
  classical
  have hc : {A : Finset S | ¬ Disjoint A Λ} = ⋃ i ∈ Λ, {A : Finset S | i ∈ A} := by
    ext A
    simp only [mem_ofPred_eq, Finset.disjoint_left, not_forall, not_not, mem_iUnion,
      exists_prop]
    exact exists_congr fun i ↦ and_comm
  suffices hr : (∑' A : ↥{A : Finset S | ¬ Disjoint A Λ}, potentialEnvelope Φ A) < ⊤ from hr
  rw [hc]
  exact (tsum_biUnion_le (potentialEnvelope Φ) Λ (fun i ↦ {A : Finset S | i ∈ A})).trans_lt
    (ENNReal.sum_lt_top.mpr fun i _ ↦ (isAbsolutelySummable_def.mp hsum i))

omit [MeasurableSpace E] in
/-- The terms in the finite-region Hamiltonian are absolutely summable. -/
lemma summable_norm_potential_of_inter {Φ : Finset S → (S → E) → ℝ}
    (hsum : IsAbsolutelySummable Φ) (Λ : Finset S) (ω : S → E) :
    Summable fun A : {A : Finset S // ¬ Disjoint A Λ} ↦ ‖Φ A ω‖ := by
  have hfin := (tsum_potentialEnvelope_lt_top hsum Λ).ne
  apply (ENNReal.summable_toReal hfin).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro A
  rw [Real.norm_eq_abs, ← ENNReal.toReal_ofReal (abs_nonneg (Φ A ω))]
  exact ENNReal.toReal_mono (ne_top_of_tsum_ne_top hfin A)
    (le_iSup (fun ξ ↦ ENNReal.ofReal |Φ A ξ|) ω)

omit [MeasurableSpace E] in
/-- The finite-region Hamiltonian is bounded by the total potential envelope. -/
private lemma abs_hamiltonian_le {Φ : Finset S → (S → E) → ℝ}
    (hsum : IsAbsolutelySummable Φ) (Λ : Finset S) (ω : S → E) :
    |hamiltonian Φ Λ ω| ≤
      (∑' A : {A : Finset S // ¬ Disjoint A Λ}, potentialEnvelope Φ A).toReal := by
  have hfin := (tsum_potentialEnvelope_lt_top hsum Λ).ne
  rw [hamiltonian_def, ← Real.norm_eq_abs, ENNReal.tsum_toReal_eq
    (fun A ↦ ne_top_of_tsum_ne_top hfin A)]
  refine (norm_tsum_le_tsum_norm (summable_norm_potential_of_inter hsum Λ ω)).trans ?_
  refine (summable_norm_potential_of_inter hsum Λ ω).tsum_le_tsum (fun A ↦ ?_)
    (ENNReal.summable_toReal hfin)
  rw [Real.norm_eq_abs, ← ENNReal.toReal_ofReal (abs_nonneg (Φ A ω))]
  exact ENNReal.toReal_mono (ne_top_of_tsum_ne_top hfin A)
    (le_iSup (fun ξ ↦ ENNReal.ofReal |Φ A ξ|) ω)

/-- On a countable site set the finite-region Hamiltonian is measurable. -/
private lemma IsPotential.measurable_hamiltonian [Countable S] {Φ : Finset S → (S → E) → ℝ}
    (hΦ : IsPotential Φ) (Λ : Finset S) : Measurable (hamiltonian Φ Λ) := by
  let _ : Countable (Finset S) := @Finset.countable S inferInstance
  have he : hamiltonian Φ Λ = fun ω ↦ ∑' A : {A : Finset S // ¬ Disjoint A Λ}, Φ A ω :=
    funext (hamiltonian_def Φ Λ)
  rw [he]
  exact (StronglyMeasurable.tsum fun A : {A : Finset S // ¬ Disjoint A Λ} ↦
    (isPotential_def.mp hΦ A).1.stronglyMeasurable).measurable

/-- The positive measurable Boltzmann weight in a finite lattice region. -/
private def latticeGibbsWeight (Φ : Finset S → (S → E) → ℝ) (Λ : Finset S) (ω : S → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-hamiltonian Φ Λ ω))

/-- The finite-region Boltzmann weight is measurable. -/
private lemma IsPotential.measurable_latticeGibbsWeight [Countable S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (Λ : Finset S) :
    Measurable (latticeGibbsWeight Φ Λ) :=
  ((hΦ.measurable_hamiltonian Λ).neg.exp).ennreal_ofReal

omit [MeasurableSpace E] in
/-- Replacing the coordinates of a finite region has the standard product-update form. -/
private lemma splice_eq_updateFinset [DecidableEq S] (Λ : Finset S) (ζ : Λ → E) (ω : S → E) :
    splice Λ ζ ω = Function.updateFinset ω Λ ζ := by
  funext i
  rw [splice_def, Function.updateFinset_def]

/-- The finite-region map that replaces the interior of a configuration is measurable. -/
lemma measurable_splice [DecidableEq S] (Λ : Finset S) (ω : S → E) :
    Measurable (splice Λ · ω) := by
  simpa only [splice_eq_updateFinset] using
    (measurable_updateFinset (x := ω) (s := Λ))

/-- The Gibbs normalising factor is positive and finite for a finite nonzero reference measure. -/
private lemma lmarginal_latticeGibbsWeight_pos_lt_top [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] (Λ : Finset S) (ω : S → E) :
    let Z := lmarginal (fun _ ↦ ρ) Λ (latticeGibbsWeight Φ Λ) ω
    0 < Z ∧ Z < ⊤ := by
  intro Z
  let C := (∑' A : {A : Finset S // ¬ Disjoint A Λ}, potentialEnvelope Φ A).toReal
  let ν : Measure (Λ → E) := Measure.pi (fun _ ↦ ρ)
  have hν : ν univ ≠ 0 := by
    dsimp only [ν]
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦
      Measure.measure_univ_ne_zero.mpr (NeZero.ne ρ)
  have hl (ζ : Λ → E) :
      ENNReal.ofReal (Real.exp (-C)) ≤ latticeGibbsWeight Φ Λ (Function.updateFinset ω Λ ζ) := by
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (neg_le_neg (le_abs_self _ |>.trans (abs_hamiltonian_le hsum Λ _))))
  have hu (ζ : Λ → E) :
      latticeGibbsWeight Φ Λ (Function.updateFinset ω Λ ζ) ≤ ENNReal.ofReal (Real.exp C) := by
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (neg_le_abs _ |>.trans (abs_hamiltonian_le hsum Λ _)))
  have hlow : ENNReal.ofReal (Real.exp (-C)) * ν univ ≤ Z := by
    rw [← lintegral_const]
    exact lintegral_mono hl
  have hupp : Z ≤ ENNReal.ofReal (Real.exp C) * ν univ := by
    rw [← lintegral_const]
    exact lintegral_mono hu
  exact ⟨(ENNReal.mul_pos (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) hν).trans_le hlow,
    hupp.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))⟩

/-- Integration against a Gibbs kernel is the weighted finite-coordinate marginal divided
by the partition function. -/
private lemma lintegral_gibbsKernel [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (ρ : Measure E) [SigmaFinite ρ]
    (Λ : Finset S) (ω : S → E) {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ σ, f σ ∂gibbsKernel Φ ρ Λ ω) =
      (lmarginal (fun _ ↦ ρ) Λ (latticeGibbsWeight Φ Λ) ω)⁻¹ *
        lmarginal (fun _ ↦ ρ) Λ (fun σ ↦ latticeGibbsWeight Φ Λ σ * f σ) ω := by
  have hζ := measurable_splice Λ ω
  have hw : Measurable (fun q : Λ → E ↦ ENNReal.ofReal
      (Real.exp (-hamiltonian Φ Λ (splice Λ q ω)))) :=
    (hΦ.measurable_latticeGibbsWeight Λ).comp hζ
  have hg : Measurable (fun q : Λ → E ↦ f (splice Λ q ω)) := hf.comp hζ
  rw [gibbsKernel_def, lintegral_smul_measure, lintegral_map hf hζ,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_withDensity_eq_lintegral_mul _ hw hg]
  simp only [latticeGibbsWeight, lmarginal, splice_eq_updateFinset, Pi.mul_apply, smul_eq_mul]

/-- Gibbs kernels are probability measures when the reference measure is finite and nonzero. -/
private lemma isProbabilityMeasure_gibbsKernel [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] (Λ : Finset S) (ω : S → E) :
    IsProbabilityMeasure (gibbsKernel Φ ρ Λ ω) := by
  have hZ := lmarginal_latticeGibbsWeight_pos_lt_top hsum ρ Λ ω
  refine ⟨?_⟩
  have h := lintegral_gibbsKernel hΦ ρ Λ ω
    (f := fun _ ↦ (1 : ℝ≥0∞)) measurable_const
  rw [lintegral_const, one_mul] at h
  simpa only [h, mul_one] using ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne

/-- The Gibbs kernel of an event is expressed as a ratio of finite-coordinate marginals. -/
private lemma gibbsKernel_apply [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (ρ : Measure E) [SigmaFinite ρ]
    (Λ : Finset S) (ω : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    gibbsKernel Φ ρ Λ ω A =
      (lmarginal (fun _ ↦ ρ) Λ (latticeGibbsWeight Φ Λ) ω)⁻¹ *
        lmarginal (fun _ ↦ ρ) Λ (fun σ ↦ latticeGibbsWeight Φ Λ σ * A.indicator 1 σ) ω := by
  have h := lintegral_gibbsKernel hΦ ρ Λ ω
    (f := A.indicator (1 : (S → E) → ℝ≥0∞)) (measurable_const.indicator hA)
  rw [lintegral_indicator_one hA] at h
  exact h

/-- Gibbs kernels are exterior-measurable. -/
private lemma measurable_gibbsKernel_outside [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (ρ : Measure E) [SigmaFinite ρ]
    (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet A) :
    Measurable[outsideSigma (Λ : Set S)] (fun ω ↦ gibbsKernel Φ ρ Λ ω A) := by
  cases isEmpty_or_nonempty (S → E) with
  | inl h =>
    let _ : MeasurableSpace (S → E) := outsideSigma (E := E) (Λ : Set S)
    exact Subsingleton.measurable
  | inr h =>
    let a := Classical.choice h
    apply measurable_outsideSigma_of_eq a
    · simp_rw [gibbsKernel_apply hΦ ρ Λ _ hA]
      exact ((hΦ.measurable_latticeGibbsWeight Λ).lmarginal (fun _ ↦ ρ)).inv.mul
        (((hΦ.measurable_latticeGibbsWeight Λ).mul
          (measurable_const.indicator hA)).lmarginal (fun _ ↦ ρ))
    · intro x y hxy
      simp_rw [gibbsKernel_apply hΦ ρ Λ _ hA]
      rw [lmarginal_congr (fun _ ↦ ρ) _ hxy, lmarginal_congr (fun _ ↦ ρ) _ hxy]

/-- Gibbs kernels keep all exterior events fixed. -/
private lemma gibbsKernel_proper [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ]
    (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet[outsideSigma (Λ : Set S)] A)
    (ω : S → E) :
    gibbsKernel Φ ρ Λ ω A = A.indicator 1 ω := by
  have hAm := outsideSigma_le (E := E) (Λ : Set S) A hA
  have hfix (ζ : Λ → E) :
      Function.updateFinset ω Λ ζ ∈ A ↔ ω ∈ A := by
    rw [outsideSigma_def, MeasurableSpace.measurableSet_comap] at hA
    obtain ⟨B, -, rfl⟩ := hA
    have h : (fun j : ↥((Λ : Set S)ᶜ) ↦ Function.updateFinset ω Λ ζ j) =
        fun j : ↥((Λ : Set S)ᶜ) ↦ ω j := by
      funext j
      have hj : (j : S) ∉ Λ := j.2
      simp only [Function.updateFinset_def, dite_eq_right hj]
    simp only [mem_preimage, h]
  have hI (ζ : Λ → E) : A.indicator (1 : (S → E) → ℝ≥0∞) (Function.updateFinset ω Λ ζ) =
      A.indicator 1 ω := by
    by_cases h : ω ∈ A
    · simp only [indicator_of_mem ((hfix ζ).2 h), indicator_of_mem h, Pi.one_apply]
    · rw [indicator_of_notMem ((hfix ζ).not.mpr h), indicator_of_notMem h]
  have hZ := lmarginal_latticeGibbsWeight_pos_lt_top hsum ρ Λ ω
  rw [gibbsKernel_apply hΦ ρ Λ _ hAm]
  have hm : Measurable (fun ζ : Λ → E ↦
      latticeGibbsWeight Φ Λ (Function.updateFinset ω Λ ζ)) :=
    (hΦ.measurable_latticeGibbsWeight Λ).comp measurable_updateFinset
  have h :
      lmarginal (fun _ ↦ ρ) Λ (fun σ ↦ latticeGibbsWeight Φ Λ σ * A.indicator 1 σ) ω =
        lmarginal (fun _ ↦ ρ) Λ (latticeGibbsWeight Φ Λ) ω * A.indicator 1 ω := by
    simp only [lmarginal, hI]
    exact lintegral_mul_const _ hm
  rw [h, ← mul_assoc, ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne, one_mul]

/-- The interaction energy gained by enlarging the region depends only on coordinates outside
the original region. -/
private lemma hamiltonian_sub_of_eqOutside {Φ : Finset S → (S → E) → ℝ}
    (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ) {Λ Δ : Finset S}
    (hΛΔ : Λ ⊆ Δ) {ω ω' : S → E} (h : ∀ i ∉ Λ, ω i = ω' i) :
    hamiltonian Φ Δ ω - hamiltonian Φ Λ ω =
      hamiltonian Φ Δ ω' - hamiltonian Φ Λ ω' := by
  classical
  let T := {A : Finset S // ¬ Disjoint A Δ}
  let L : Set T := {A | ¬ Disjoint A.1 Λ}
  have hsubset {A : Finset S} (hA : ¬ Disjoint A Λ) : ¬ Disjoint A Δ :=
    fun hD ↦ hA (hD.mono_right hΛΔ)
  let e : ↥L ≃ {A : Finset S // ¬ Disjoint A Λ} :=
    Equiv.subtypeSubtypeEquivSubtype @hsubset
  let H (v : S → E) := ∑' A : ↥Lᶜ, Φ A.1.1 v
  have hh (v : S → E) : hamiltonian Φ Δ v = hamiltonian Φ Λ v + H v := by
    have hS : Summable (fun A : T ↦ Φ A.1 v) :=
      (summable_norm_potential_of_inter hsum Δ v).of_norm
    rw [hamiltonian_def Φ Δ v, ← hS.tsum_subtype_add_tsum_subtype_compl L, hamiltonian_def Φ Λ v]
    congr 1
    exact e.tsum_eq (fun A ↦ Φ A.1 v)
  have hH : H ω = H ω' := tsum_congr fun A ↦
    (isPotential_def.mp hΦ A.1.1).2 ω ω' fun i hi ↦ h i fun hi' ↦
      Finset.disjoint_left.mp (not_not.mp (show ¬ ¬ Disjoint A.1.1 Λ from A.2)) hi hi'
  rw [hh ω, hh ω', add_sub_cancel_left, add_sub_cancel_left, hH]

/-- Pulling a multiplier constant on exterior fibres out of a finite marginal. -/
private lemma lmarginal_mul_left_of_eqOutside [DecidableEq S] (ρ : Measure E) [SigmaFinite ρ]
    (Λ : Finset S) {f g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hf : ∀ x y : S → E, (∀ i ∉ Λ, x i = y i) → f x = f y) (ω : S → E) :
    lmarginal (fun _ ↦ ρ) Λ (fun x ↦ f x * g x) ω =
      f ω * lmarginal (fun _ ↦ ρ) Λ g ω := by
  have hm : Measurable (fun ζ : Λ → E ↦ g (Function.updateFinset ω Λ ζ)) :=
    hg.comp measurable_updateFinset
  rw [lmarginal, lmarginal, ← lintegral_const_mul _ hm]
  exact lintegral_congr fun ζ ↦ by
    rw [hf (Function.updateFinset ω Λ ζ) ω
      (fun i hi ↦ by simp only [Function.updateFinset_def, dite_eq_right hi])]

/-- Nested Gibbs kernels are consistent because the additional Boltzmann factor is constant
when integrating the inner region. -/
private lemma gibbsKernel_consistent [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ)
    (ω : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    (∫⁻ σ, gibbsKernel Φ ρ Λ σ A ∂gibbsKernel Φ ρ Δ ω) = gibbsKernel Φ ρ Δ ω A := by
  let R (B : Finset S) := lmarginal (fun _ ↦ ρ) B (X := fun _ ↦ E)
  let W := latticeGibbsWeight Φ
  let G (σ : S → E) := gibbsKernel Φ ρ Λ σ A
  let I : (S → E) → ℝ≥0∞ := A.indicator 1
  let C (σ : S → E) := ENNReal.ofReal (Real.exp (-(hamiltonian Φ Δ σ - hamiltonian Φ Λ σ)))
  have hw (B : Finset S) : Measurable (W B) := hΦ.measurable_latticeGibbsWeight B
  have hg : Measurable[outsideSigma (Λ : Set S)] G := measurable_gibbsKernel_outside hΦ ρ Λ hA
  have hg' : Measurable G := hg.mono (outsideSigma_le _) le_rfl
  have hi : Measurable I := measurable_const.indicator hA
  have hC (x y : S → E) (hxy : ∀ i ∉ Λ, x i = y i) : C x = C y := by
    simp only [C, hamiltonian_sub_of_eqOutside hΦ hsum hΛΔ hxy]
  have hW (x : S → E) : W Δ x = C x * W Λ x := by
    simp only [C, W, latticeGibbsWeight,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hgI (x : S → E) : G x = (R Λ (W Λ) x)⁻¹ * R Λ (fun y ↦ W Λ y * I y) x :=
    gibbsKernel_apply hΦ ρ Λ x hA
  have hmain : R Λ (fun x ↦ W Δ x * G x) = R Λ (fun x ↦ W Δ x * I x) := by
    funext x
    have hZ := lmarginal_latticeGibbsWeight_pos_lt_top hsum ρ Λ x
    calc
      _ = (C x * G x) * R Λ (W Λ) x := by
        have hf : (fun y ↦ W Δ y * G y) = fun y ↦ (C y * G y) * W Λ y := by
          funext y
          rw [hW]
          ac_rfl
        rw [hf]
        exact lmarginal_mul_left_of_eqOutside ρ Λ (hw Λ)
          (fun y z hyz ↦ congrArg₂ (· * ·) (hC y z hyz) (eq_of_measurable_outsideSigma hg hyz)) x
      _ = C x * R Λ (fun y ↦ W Λ y * I y) x := by
        rw [hgI x]
        calc
          _ = C x * R Λ (fun y ↦ W Λ y * I y) x * ((R Λ (W Λ) x)⁻¹ * R Λ (W Λ) x) := by ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne, mul_one]
      _ = _ := by
        simp only [hW, mul_assoc]
        exact (lmarginal_mul_left_of_eqOutside ρ Λ ((hw Λ).mul hi) hC x).symm
  have he := lmarginal_eq_of_subset (μ := fun _ ↦ ρ) hΛΔ
      ((hw Δ).mul hg') ((hw Δ).mul hi) hmain
  rw [lintegral_gibbsKernel hΦ ρ Δ ω hg', gibbsKernel_apply hΦ ρ Δ ω hA]
  exact congrArg (fun F : (S → E) → ℝ≥0∞ ↦ (R Δ (W Δ) ω)⁻¹ * F ω) he

/-- A bounded finite-region Hamiltonian from an absolutely summable potential defines a
specification. -/
lemma isSpecification_gibbsKernel [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] :
    IsSpecification (gibbsKernel Φ ρ) where
  isProbabilityMeasure := isProbabilityMeasure_gibbsKernel hΦ hsum ρ
  measurable Λ _ hA := measurable_gibbsKernel_outside hΦ ρ Λ hA
  proper Λ _ hB ω := gibbsKernel_proper hΦ hsum ρ Λ hB ω
  consistent _ _ hΛΔ ω _ hA := gibbsKernel_consistent hΦ hsum ρ hΛΔ ω hA

/-- An ultrafilter limit of measures eventually dominated by one finite measure exists setwise.
The domination controls the contribution of the tail of every disjoint sequence. -/
lemma exists_measure_of_eventually_le {X I : Type*} [MeasurableSpace X]
    (U : Ultrafilter I) (m : I → Measure X) (ρ : Measure X) [IsFiniteMeasure ρ]
    (hdom : ∀ᶠ i in (U : Filter I), m i ≤ ρ) :
    ∃ μ : Measure X, μ ≤ ρ ∧
      ∀ A, MeasurableSet A → Tendsto (fun i ↦ m i A) (U : Filter I) (𝓝 (μ A)) := by
  let q (A : Set X) := (U.map (fun i ↦ m i A)).lim
  have hq (A : Set X) : Tendsto (fun i ↦ m i A) (U : Filter I) (𝓝 (q A)) :=
    Ultrafilter.le_nhds_lim _
  have hle (A : Set X) : q A ≤ ρ A :=
    le_of_tendsto_of_tendsto (hq A) tendsto_const_nhds (hdom.mono fun i hi ↦ hi A)
  have h0 : q ∅ = 0 := tendsto_nhds_unique (hq ∅)
    (by simpa only [measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : I ↦ 0) (U : Filter I) (𝓝 (0 : ℝ≥0∞))))
  have hadd {A B : Set X} (ha : MeasurableSet A) (hb : MeasurableSet B) (hd : Disjoint A B) :
      q (A ∪ B) = q A + q B := by
    apply tendsto_nhds_unique (hq (A ∪ B))
    refine ((hq A).add (hq B)).congr' ?_
    exact Eventually.of_forall fun i ↦ (measure_union hd hb).symm
  have hsum {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n))
      (hd : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
      q (⋃ n, A n) = ∑' n, q (A n) := by
    let r (n : ℕ) := ⋃ k ∈ Finset.range n, A k
    let T := ⋃ n, A n
    let t (n : ℕ) := T \ r n
    have hr (n : ℕ) : MeasurableSet (r n) := MeasurableSet.biUnion
      (Finset.range n).countable_toSet fun k _ ↦ hA k
    have hT := MeasurableSet.iUnion hA
    have hrT (n : ℕ) : r n ⊆ T := iUnion₂_subset fun k _ ↦ subset_iUnion A k
    have hu (n : ℕ) : r n ∪ t n = T := by
      refine subset_antisymm (union_subset (hrT n) sdiff_subset) ?_
      intro x hx
      by_cases h : x ∈ r n
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    have hdt (n : ℕ) : Disjoint (r n) (t n) := disjoint_sdiff_right
    have htm (n : ℕ) : MeasurableSet (t n) := hT.diff (hr n)
    have hta : Antitone t := fun _ _ h ↦ sdiff_subset_sdiff_right
      (iUnion₂_mono' fun k hk ↦ ⟨k, Finset.range_subset_range.mpr h hk, Subset.rfl⟩)
    have ht0 : ⋂ n, t n = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
      obtain ⟨k, hk⟩ := mem_iUnion.mp (mem_iInter.mp hx 0).1
      exact (mem_iInter.mp hx (k + 1)).2
        (mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩)
    have htρ : Tendsto (fun n ↦ ρ (t n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ht0, measure_empty] using
        (tendsto_measure_iInter_atTop (fun n ↦ (htm n).nullMeasurableSet) hta
          ⟨0, measure_ne_top ρ (t 0)⟩)
    have htq : Tendsto (fun n ↦ q (t n)) atTop (𝓝 0) :=
      tendsto_const_nhds.squeeze htρ (fun _ ↦ zero_le) (fun n ↦ hle (t n))
    have hrq (n : ℕ) : q (r n) = ∑ k ∈ Finset.range n, q (A k) := by
      induction n with
      | zero => simp only [r, Finset.range_zero, Finset.notMem_empty, iUnion_of_empty,
          iUnion_empty, h0, Finset.sum_empty]
      | succ n ih =>
        have hrn : r (n + 1) = A n ∪ r n := by
          simp only [r, Finset.range_add_one, Finset.mem_insert, iUnion_iUnion_eq_or_left]
        have hdis : Disjoint (A n) (r n) := by
          dsimp only [r]
          rw [disjoint_iUnion_right]
          exact fun k ↦ disjoint_iUnion_right.mpr fun hk ↦ hd (by
            exact (Finset.mem_range.mp hk).ne')
        rw [hrn, hadd (hA n) (hr n) hdis, ih, Finset.sum_range_succ, add_comm]
    have ht := (ENNReal.tendsto_nat_tsum (fun n ↦ q (A n))).add htq
    simp only [add_zero] at ht
    have he (n : ℕ) : (∑ k ∈ Finset.range n, q (A k)) + q (t n) = q T := by
      rw [← hrq, ← hadd (hr n) (htm n) (hdt n), hu]
    exact tendsto_nhds_unique tendsto_const_nhds
      (ht.congr' (Eventually.of_forall he))
  let μ := Measure.ofMeasurable (fun A _ ↦ q A) h0 (fun {A} hA hd ↦ hsum (A := A) hA hd)
  refine ⟨μ, Measure.le_iff.mpr fun A hA ↦ ?_, fun A hA ↦ ?_⟩
  · rw [Measure.ofMeasurable_apply A hA]
    exact hle A
  · rw [Measure.ofMeasurable_apply A hA]
    exact hq A

/-- L¹ approximation in a dominating measure bounds the change of the integral under
every dominated measure. -/
lemma norm_integral_sub_le_of_measure_le {X : Type*} [MeasurableSpace X]
    {m ρ : Measure X} (hle : m ≤ ρ) {f g : X → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g ρ) :
    ‖(∫ x, f x ∂m) - ∫ x, g x ∂m‖ ≤ ∫ x, ‖f x - g x‖ ∂ρ := by
  rw [← integral_sub (hf.mono_measure hle) (hg.mono_measure hle)]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_measure hle (ae_of_all _ fun _ ↦ norm_nonneg _) (hf.sub hg).norm)

/-- Uniformly Cauchyprobabilities of measurable events converge uniformly to a probability
measure. -/
lemma exists_prob_of_uniform_cauchy {X : Type*} [MeasurableSpace X]
    (m : ℕ → Measure X) [∀ n, IsProbabilityMeasure (m n)]
    (hc : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N, ∀ A, MeasurableSet A →
      |(m n).real A - (m k).real A| < ε) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ A, MeasurableSet A → |(m n).real A - μ.real A| ≤ ε := by
  have hA (A : Set X) (hA : MeasurableSet A) :
      ∃ a : ℝ, Tendsto (fun n ↦ (m n).real A) atTop (𝓝 a) := by
    apply cauchySeq_tendsto_of_complete
    refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := hc ε hε
    exact ⟨N, fun n hn k hk ↦ by simpa only [Real.dist_eq] using hN n hn k hk A hA⟩
  choose a ha using hA
  have ha₀ (A : Set X) (hA : MeasurableSet A) : 0 ≤ a A hA :=
    ge_of_tendsto (ha A hA) (.of_forall fun _ ↦ measureReal_nonneg)
  have hunif (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ A, ∀ hA : MeasurableSet A,
      |(m n).real A - a A hA| ≤ ε := by
    obtain ⟨N, hN⟩ := hc ε hε
    refine eventually_atTop.mpr ⟨N, fun n hn A hAm ↦ ?_⟩
    apply le_of_tendsto ((tendsto_const_nhds.sub (ha A hAm)).abs)
    exact eventually_atTop.mpr ⟨N, fun k hk ↦ (hN n hn k hk A hAm).le⟩
  let b (A : Set X) (hA : MeasurableSet A) := ENNReal.ofReal (a A hA)
  have he (A : Set X) (hAm : MeasurableSet A) :
      Tendsto (fun n ↦ m n A) atTop (𝓝 (b A hAm)) := by
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ha A hAm)).congr
      (fun n ↦ ofReal_measureReal (measure_ne_top _ _))
  have h0 : b ∅ MeasurableSet.empty = 0 :=
    tendsto_nhds_unique (he _ _) (by simp)
  have h1 : b univ MeasurableSet.univ = 1 :=
    tendsto_nhds_unique (he _ _) (by simp)
  have hU ⦃f : ℕ → Set X⦄ (hf : ∀ j, MeasurableSet (f j))
      (hd : Pairwise (Disjoint on f)) :
      b (⋃ j, f j) (.iUnion hf) = ∑' j, b (f j) (hf j) := by
    let B (N : ℕ) := ⋃ j ∈ Finset.range N, f j
    have hB (N : ℕ) : MeasurableSet (B N) :=
      Finset.measurableSet_biUnion _ (fun j _ ↦ hf j)
    have hs (N : ℕ) : b (B N) (hB N) = ∑ j ∈ Finset.range N, b (f j) (hf j) := by
      apply tendsto_nhds_unique (he (B N) (hB N))
      refine (tendsto_finsetSum (Finset.range N) (fun j _ ↦ he _ (hf j))).congr fun n ↦ ?_
      have hdN : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint f := by
        intro i _ j _ hij
        exact hd hij
      exact (measure_biUnion_finset hdN (fun j _ ↦ hf j)).symm
    have hcont : Tendsto (fun N ↦ a (B N) (hB N)) atTop (𝓝 (a (⋃ j, f j) (.iUnion hf))) := by
      refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
      obtain ⟨n, hn⟩ := (hunif (ε / 3) (by positivity)).exists
      have hmono : Monotone B := fun i j hij ↦
        iUnion₂_mono' fun k hk ↦ ⟨k, (Finset.range_mono hij) hk, Subset.rfl⟩
      have hu : (⋃ N, B N) = ⋃ j, f j := by
        ext x
        simp only [B, mem_iUnion, Finset.mem_range]
        exact ⟨fun ⟨_, j, _, hj⟩ ↦ ⟨j, hj⟩, fun ⟨j, hj⟩ ↦ ⟨j + 1, j, Nat.lt_succ_self j, hj⟩⟩
      have ht := tendsto_measure_iUnion_atTop (μ := m n) hmono
      rw [hu] at ht
      have ht' : Tendsto (fun N ↦ (m n).real (B N)) atTop (𝓝 ((m n).real (⋃ j, f j))) :=
        (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
      filter_upwards [Metric.tendsto_nhds.mp ht' (ε / 3) (by positivity)] with N hN
      have hleft := hn (B N) (hB N)
      have hright := hn _ (.iUnion hf)
      rw [Real.dist_eq] at hN ⊢
      rw [abs_sub_comm] at hleft
      have htri₁ := abs_sub_le (a (B N) (hB N)) ((m n).real (B N))
        (a (⋃ j, f j) (.iUnion hf))
      have htri₂ := abs_sub_le ((m n).real (B N)) ((m n).real (⋃ j, f j))
        (a (⋃ j, f j) (.iUnion hf))
      linarith only [hleft, hright, hN, htri₁, htri₂]
    apply tendsto_nhds_unique (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcont)
    exact CompleteLattice.summable.hasSum.tendsto_sum_nat.congr (fun N ↦ (hs N).symm)
  let μ := Measure.ofMeasurable b h0 hU
  have hμ (A : Set X) (hAm : MeasurableSet A) : μ A = b A hAm :=
    Measure.ofMeasurable_apply A hAm
  refine ⟨μ, ⟨(hμ _ .univ).trans h1⟩, fun ε hε ↦ ?_⟩
  filter_upwards [hunif ε hε] with n hn A hAm
  rw [measureReal_def (μ := μ), hμ _ hAm, ENNReal.toReal_ofReal (ha₀ A hAm)]
  exact hn A hAm

/-- Under eventual domination, setwise convergence implies convergence of integrals of
functions integrable for the dominating measure. -/
lemma tendsto_integral_of_tendsto_measure_apply {X I : Type*} [MeasurableSpace X]
    {F : Filter I} {m : I → Measure X} {μ ρ : Measure X} [IsFiniteMeasure ρ]
    (hdom : ∀ᶠ i in F, m i ≤ ρ) (hle : μ ≤ ρ)
    (hm : ∀ A, MeasurableSet A → Tendsto (fun i ↦ m i A) F (𝓝 (μ A)))
    {f : X → ℝ} (hf : Measurable f) (hfi : Integrable f ρ) :
    Tendsto (fun i ↦ ∫ x, f x ∂m i) F (𝓝 (∫ x, f x ∂μ)) := by
  have ht (g : SimpleFunc X ℝ) (hg : Integrable g ρ) :
      Tendsto (fun i ↦ ∫ x, g x ∂m i) F (𝓝 (∫ x, g x ∂μ)) := by
    rw [SimpleFunc.integral_eq_sum g (hg.mono_measure hle)]
    refine (tendsto_finsetSum (f := fun r i ↦ (m i).real (g ⁻¹' {r}) • r)
      g.range fun r _ ↦ ?_).congr' ?_
    · have htop : μ (g ⁻¹' {r}) ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_ne_top ρ _) (hle _)
      exact ((ENNReal.tendsto_toReal htop).comp (hm _ (g.measurableSet_fiber r))).smul_const r
    · filter_upwards [hdom] with i hi using
        (SimpleFunc.integral_eq_sum g (hg.mono_measure hi)).symm
  let g := fun n ↦ SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n
  have hgi (n : ℕ) : Integrable (g n) ρ := SimpleFunc.integrable_approxOn_range hf hfi n
  have happ : Tendsto (fun n ↦ ∫ x, ‖g n x - f x‖ ∂ρ) atTop (𝓝 0) :=
    tendsto_integral_norm_approxOn_sub hf hfi
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp happ (ε / 3) (by positivity)).exists
  have hnon : 0 ≤ ∫ x, ‖g n x - f x‖ ∂ρ := integral_nonneg fun _ ↦ norm_nonneg _
  have hn' : (∫ x, ‖g n x - f x‖ ∂ρ) < ε / 3 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnon] using hn
  have he := Metric.tendsto_nhds.mp (ht (g n) (hgi n)) (ε / 3) (by positivity)
  filter_upwards [hdom, he] with i hi hfgn
  have h₁ := norm_integral_sub_le_of_measure_le hi (hgi n) hfi
  have h₂ := norm_integral_sub_le_of_measure_le hle (hgi n) hfi
  calc
    dist (∫ x, f x ∂m i) (∫ x, f x ∂μ) ≤
        dist (∫ x, f x ∂m i) (∫ x, g n x ∂m i) +
          dist (∫ x, g n x ∂m i) (∫ x, g n x ∂μ) +
          dist (∫ x, g n x ∂μ) (∫ x, f x ∂μ) := dist_triangle4 _ _ _ _
    _ < ε := by
      rw [dist_comm (∫ x, f x ∂m i)]
      simp only [dist_eq_norm] at hfgn ⊢
      linarith only [h₁, h₂, hfgn, hn']

/-- Uniform eventual domination on each finite block gives a locally convergent probability
measure along an ultrafilter. -/
lemma exists_tendstoLocally_of_eventually_domination [DecidableEq S] [StandardBorelSpace E]
    {I : Type*} (U : Ultrafilter I) (m : I → Measure (S → E))
    (hprob : ∀ᶠ i in (U : Filter I), IsProbabilityMeasure (m i))
    (hdom : ∀ Λ : Finset S, ∃ ρ : Measure (Λ → E), IsFiniteMeasure ρ ∧
      ∀ᶠ i in (U : Filter I), (m i).map Λ.restrict ≤ ρ) :
    ∃ μ : Measure (S → E), IsProbabilityMeasure μ ∧ TendstoLocally (U : Filter I) m μ := by
  classical
  choose ρ hρ hdom using hdom
  have hex (Λ : Finset S) : ∃ μ : Measure (Λ → E), μ ≤ ρ Λ ∧
      ∀ A, MeasurableSet A → Tendsto (fun i ↦ (m i).map Λ.restrict A)
        (U : Filter I) (𝓝 (μ A)) := by
    let _ := hρ Λ
    exact exists_measure_of_eventually_le U _ (ρ Λ) (hdom Λ)
  choose family hle hlim using hex
  have hp (Λ : Finset S) : IsProbabilityMeasure (family Λ) := by
    refine ⟨tendsto_nhds_unique (hlim Λ univ MeasurableSet.univ) ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hprob] with i hi
    let _ := hi
    rw [Measure.map_apply Λ.measurable_restrict MeasurableSet.univ, preimage_univ, measure_univ]
  let _ := upgradeStandardBorel E
  have hP : IsProjectiveMeasureFamily (α := fun _ : S ↦ E) family := by
    intro J Λ hΛ
    refine Measure.ext fun A hA ↦ ?_
    have hm : Measurable (Finset.restrict₂ (π := fun _ : S ↦ E) hΛ) :=
      Finset.measurable_restrict₂ hΛ
    rw [Measure.map_apply hm hA]
    refine tendsto_nhds_unique (hlim Λ A hA) ((hlim J _ (hm hA)).congr' ?_)
    refine Eventually.of_forall fun i ↦ ?_
    dsimp only
    rw [← Measure.map_apply hm hA, Measure.map_map hm J.measurable_restrict,
      Finset.restrict₂_comp_restrict]
  let μ := projectiveLimit (α := fun _ : S ↦ E) family hP
  have hμ : IsProjectiveLimit μ family := isProjectiveLimit_projectiveLimit hP
  refine ⟨μ, inferInstance, tendstoLocally_def.mpr fun f hloc hf hb ↦ ?_⟩
  obtain ⟨Λ, hΛ⟩ := isLocalFunction_def.mp hloc
  obtain ⟨C, hC⟩ := hb
  let a := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  let g (ζ : Λ → E) := f (splice Λ ζ a)
  have hg : Measurable g := hf.comp (measurable_splice Λ a)
  have hi : Integrable g (ρ Λ) := by
    let _ := hρ Λ
    exact (integrable_const C).mono' hg.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs, g] using hC (splice Λ x a))
  have hgf (ω : S → E) : g (Λ.restrict ω) = f ω := by
    apply hΛ
    intro j hj
    simp only [splice_def, dite_eq_left hj, Finset.restrict_def]
  have hmap (ν : Measure (S → E)) :
      (∫ x, g x ∂ν.map Λ.restrict) = ∫ x, f x ∂ν := by
    rw [integral_map Λ.measurable_restrict.aemeasurable hg.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ hgf)
  have ht : Tendsto (fun i ↦ ∫ ζ, g ζ ∂(m i).map Λ.restrict) (U : Filter I)
      (𝓝 (∫ ζ, g ζ ∂family Λ)) := by
    let _ := hρ Λ
    exact tendsto_integral_of_tendsto_measure_apply (hdom Λ) (hle Λ) (hlim Λ) hg hi
  rw [← hμ Λ, hmap μ] at ht
  simpa only [hmap] using ht

/-- Absolute summability makes the Hamiltonian uniformly insensitive to coordinates
outside a sufficiently large finite set. -/
private lemma abs_hamiltonian_sub_lt_of_eqOn [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (Λ : Finset S) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset S, ∀ ω ω' : S → E, (∀ i ∈ T, ω i = ω' i) →
      |hamiltonian Φ Λ ω - hamiltonian Φ Λ ω'| < ε := by
  classical
  let J := {A : Finset S // ¬ Disjoint A Λ}
  let G (A : J) := potentialEnvelope Φ A.1
  have htop : ∑' A : J, G A ≠ ⊤ := (tsum_potentialEnvelope_lt_top hsum Λ).ne
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (ENNReal.tendsto_tsum_compl_atTop_zero htop)
  obtain ⟨F, hF⟩ := (hlim.eventually_lt_const (by simpa only [ENNReal.toReal_zero] using
    (half_pos hε))).exists
  have hg (A : J) : G A ≠ ⊤ := ne_top_of_tsum_ne_top htop A
  have hbound (ω : S → E) (A : J) : ‖Φ A.1 ω‖ ≤ (G A).toReal := by
    rw [Real.norm_eq_abs, ← ENNReal.toReal_ofReal (abs_nonneg (Φ A.1 ω))]
    exact ENNReal.toReal_mono (hg A) (le_iSup (fun x ↦ ENNReal.ofReal |Φ A.1 x|) ω)
  refine ⟨F.biUnion Subtype.val, fun ω ω' h ↦ ?_⟩
  let d (A : J) := Φ A.1 ω - Φ A.1 ω'
  have hd (A : J) : ‖d A‖ ≤ 2 * (G A).toReal := by
    calc
      _ ≤ ‖Φ A.1 ω‖ + ‖Φ A.1 ω'‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hbound ω A, hbound ω' A]
  have hs := (ENNReal.summable_toReal htop).mul_left 2
  have hsn : Summable (fun A : J ↦ ‖d A‖) :=
    hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hd
  have hs₀ : ∑ A ∈ F, d A = 0 := by
    refine Finset.sum_eq_zero fun A hA ↦
      sub_eq_zero.mpr ((isPotential_def.mp hΦ A.1).2 ω ω' fun i hi ↦ ?_)
    exact h i (Finset.mem_biUnion.mpr ⟨A, hA, hi⟩)
  have ht : (∑' A : J, d A) = hamiltonian Φ Λ ω - hamiltonian Φ Λ ω' := by
    rw [hamiltonian_def, hamiltonian_def]
    exact (summable_norm_potential_of_inter hsum Λ ω).of_norm.tsum_sub
      (summable_norm_potential_of_inter hsum Λ ω').of_norm
  rw [← ht, ← hsn.of_norm.sum_add_tsum_compl (s := F), hs₀, zero_add, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' A : {A : J // A ∉ F}, ‖d A.1‖ :=
      norm_tsum_le_tsum_norm (hsn.subtype _)
    _ ≤ ∑' A : {A : J // A ∉ F}, 2 * (G A.1).toReal :=
      (hsn.subtype _).tsum_le_tsum (fun A ↦ hd A.1) (hs.subtype _)
    _ = 2 * (∑' A : {A : J // A ∉ F}, G A.1).toReal := by
      rw [tsum_mul_left]
      exact congrArg (2 * ·) (ENNReal.tsum_toReal_eq
        (f := fun A : {i : J // i ∉ F} ↦ G A.1) (fun A ↦ hg A.1)).symm
    _ < ε := by
      dsimp only [Function.comp_def] at hF
      linarith only [hF]

/-- A uniform upper bound for the ratio of weights gives the same bound for the
unnormalised marginals. -/
private lemma lmarginal_weight_le_mul [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ)
    (ρ : Measure E) [SigmaFinite ρ] (Λ : Finset S) (x y : S → E) (δ : ℝ)
    (h : ∀ ζ : Λ → E, hamiltonian Φ Λ (Function.updateFinset y Λ ζ) -
      hamiltonian Φ Λ (Function.updateFinset x Λ ζ) ≤ δ)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f)
    (he : ∀ ζ : Λ → E, f (Function.updateFinset x Λ ζ) = f (Function.updateFinset y Λ ζ)) :
    lmarginal (fun _ ↦ ρ) Λ (fun w ↦ latticeGibbsWeight Φ Λ w * f w) x ≤
      ENNReal.ofReal (Real.exp δ) *
        lmarginal (fun _ ↦ ρ) Λ (fun w ↦ latticeGibbsWeight Φ Λ w * f w) y := by
  have hm : Measurable (fun ζ : Λ → E ↦ latticeGibbsWeight Φ Λ
      (Function.updateFinset y Λ ζ) * f (Function.updateFinset y Λ ζ)) :=
    ((hΦ.measurable_latticeGibbsWeight Λ).mul hf).comp measurable_updateFinset
  rw [lmarginal, lmarginal, ← lintegral_const_mul _ hm]
  refine lintegral_mono fun ζ ↦ ?_
  have hw :
      latticeGibbsWeight Φ Λ (Function.updateFinset x Λ ζ) ≤
        ENNReal.ofReal (Real.exp δ) * latticeGibbsWeight Φ Λ (Function.updateFinset y Λ ζ) := by
    rw [latticeGibbsWeight, latticeGibbsWeight, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith only [h ζ]))
  rw [he ζ, ← mul_assoc]
  gcongr

/-- Measure weights integrated over the same projected event retain the exponential
bounds on their pointwise ratio. -/
private lemma gibbsKernel_map_numerator_comparison [Countable S] [DecidableEq S]
    {X : Type*} [MeasurableSpace X] {Φ : Finset S → (S → E) → ℝ}
    (hΦ : IsPotential Φ) (ρ : Measure E) [SigmaFinite ρ]
    (Λ : Finset S) (x y : S → E) {p : (S → E) → X} (hp : Measurable p)
    (he : ∀ ζ : Λ → E, p (Function.updateFinset x Λ ζ) = p (Function.updateFinset y Λ ζ))
    {δ : ℝ} (hH : ∀ ζ : Λ → E, |hamiltonian Φ Λ (Function.updateFinset y Λ ζ) -
      hamiltonian Φ Λ (Function.updateFinset x Λ ζ)| ≤ δ)
    {A : Set X} (hA : MeasurableSet A) :
    let N := lmarginal (fun _ ↦ ρ) Λ (fun w ↦
      latticeGibbsWeight Φ Λ w * (p ⁻¹' A).indicator 1 w)
    ENNReal.ofReal (Real.exp (-δ)) * N y ≤ N x ∧
      N x ≤ ENNReal.ofReal (Real.exp δ) * N y := by
  dsimp only
  let I : (S → E) → ℝ≥0∞ := (p ⁻¹' A).indicator 1
  have hI : Measurable I := measurable_const.indicator (hp hA)
  have hIeq (ζ : Λ → E) : I (Function.updateFinset x Λ ζ) = I (Function.updateFinset y Λ ζ) := by
    have hm : Function.updateFinset x Λ ζ ∈ p ⁻¹' A ↔
        Function.updateFinset y Λ ζ ∈ p ⁻¹' A := by simp only [Set.mem_preimage, he ζ]
    by_cases hx : Function.updateFinset x Λ ζ ∈ p ⁻¹' A
    · simp only [I, indicator_of_mem hx, indicator_of_mem (hm.mp hx), Pi.one_apply]
    · simp only [I, indicator_of_notMem hx, indicator_of_notMem (hm.not.mp hx)]
  have hu := lmarginal_weight_le_mul hΦ ρ Λ x y δ
    (fun ζ ↦ (le_abs_self _).trans (hH ζ)) hI hIeq
  have hl := lmarginal_weight_le_mul hΦ ρ Λ y x δ
    (fun ζ ↦ by simpa only [neg_sub] using (neg_le_abs _).trans (hH ζ)) hI
    (fun ζ ↦ (hIeq ζ).symm)
  refine ⟨?_, hu⟩
  let N := lmarginal (fun _ ↦ ρ) Λ (fun w ↦ latticeGibbsWeight Φ Λ w * I w)
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-δ)) * (ENNReal.ofReal (Real.exp δ) * N x) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- A uniform bound on the change of the Hamiltonian bounds the likelihood ratio of
projected Gibbs laws. Both bounds retain the same ratio of partition functions. -/
lemma exists_gibbsKernel_map_smul_bounds [Countable S] [DecidableEq S]
    {X : Type*} [MeasurableSpace X] {Φ : Finset S → (S → E) → ℝ}
    (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] (Λ : Finset S) (x y : S → E)
    {p : (S → E) → X} (hp : Measurable p)
    (he : ∀ ζ : Λ → E, p (Function.updateFinset x Λ ζ) = p (Function.updateFinset y Λ ζ))
    {δ : ℝ} (hH : ∀ ζ : Λ → E, |hamiltonian Φ Λ (Function.updateFinset y Λ ζ) -
      hamiltonian Φ Λ (Function.updateFinset x Λ ζ)| ≤ δ) :
    ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (r * Real.exp (-δ)) • (gibbsKernel Φ ρ Λ y).map p ≤
        (gibbsKernel Φ ρ Λ x).map p ∧
      (gibbsKernel Φ ρ Λ x).map p ≤
        ENNReal.ofReal (r * Real.exp δ) • (gibbsKernel Φ ρ Λ y).map p := by
  let W := latticeGibbsWeight Φ Λ
  let Z := lmarginal (fun _ ↦ ρ) Λ W
  let r := Z y * (Z x)⁻¹
  have hx := lmarginal_latticeGibbsWeight_pos_lt_top hsum ρ Λ x
  have hy := lmarginal_latticeGibbsWeight_pos_lt_top hsum ρ Λ y
  have hr₀ : 0 < r := ENNReal.mul_pos hy.1.ne' (ENNReal.inv_ne_zero.mpr hx.2.ne)
  have hrt : r ≠ ⊤ := ENNReal.mul_ne_top hy.2.ne (ENNReal.inv_ne_top.mpr hx.1.ne')
  have hr := ENNReal.toReal_pos hr₀.ne' hrt
  have hfactor (a : ℝ) (n : ℝ≥0∞) :
      ENNReal.ofReal (r.toReal * Real.exp a) * ((Z y)⁻¹ * n) =
        (Z x)⁻¹ * (ENNReal.ofReal (Real.exp a) * n) := by
    rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_toReal hrt]
    calc
      _ = (Z y * (Z y)⁻¹) * ((Z x)⁻¹ * (ENNReal.ofReal (Real.exp a) * n)) := by
        dsimp only [r]
        ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hy.1.ne' hy.2.ne, one_mul]
  refine ⟨r.toReal, hr, Measure.le_iff.mpr fun A hA ↦ ?_, Measure.le_iff.mpr fun A hA ↦ ?_⟩
  · have h := gibbsKernel_map_numerator_comparison hΦ ρ Λ x y hp he hH hA
    rw [smul_apply, smul_eq_mul, Measure.map_apply hp hA, Measure.map_apply hp hA,
      gibbsKernel_apply hΦ ρ Λ x (hp hA), gibbsKernel_apply hΦ ρ Λ y (hp hA), hfactor]
    exact mul_le_mul_of_nonneg_left h.1 bot_le
  · have h := gibbsKernel_map_numerator_comparison hΦ ρ Λ x y hp he hH hA
    rw [smul_apply, smul_eq_mul, Measure.map_apply hp hA, Measure.map_apply hp hA,
      gibbsKernel_apply hΦ ρ Λ x (hp hA), gibbsKernel_apply hΦ ρ Λ y (hp hA), hfactor]
    exact mul_le_mul_of_nonneg_left h.2 bot_le

/-- Normalising two weight bounds uses the upper bound from the first numerator and
the lower bound from the first denominator. -/
lemma inv_mul_le_sq_mul_inv_mul {n₁ n₂ z₁ z₂ a : ℝ≥0∞} (hn : n₁ ≤ a * n₂)
    (hz : z₂ ≤ a * z₁) (hz₁ : z₁ ≠ 0) (ht₁ : z₁ ≠ ⊤) (hz₂ : z₂ ≠ 0) (ht₂ : z₂ ≠ ⊤) :
    z₁⁻¹ * n₁ ≤ (a * a) * (z₂⁻¹ * n₂) := by
  have h₂ : n₂ = z₂ * (z₂⁻¹ * n₂) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hz₂ ht₂, one_mul]
  calc
    _ ≤ z₁⁻¹ * (a * n₂) := by gcongr
    _ = a * (z₁⁻¹ * (z₂ * (z₂⁻¹ * n₂))) := by nth_rw 1 [h₂]; ac_rfl
    _ ≤ a * (z₁⁻¹ * ((a * z₁) * (z₂⁻¹ * n₂))) := by gcongr
    _ = a * a * ((z₁⁻¹ * z₁) * (z₂⁻¹ * n₂)) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hz₁ ht₁, one_mul]

/-- One finite set controls the Gibbs probabilities of all events on a fixed cylinder. -/
lemma gibbsKernel_real_cylinder_oscillation [Countable S] [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ]
    (Λ D : Finset S) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset S, ∀ x y : S → E, (∀ i ∈ T, x i = y i) →
      ∀ A : Set (D → E), MeasurableSet A →
      |(gibbsKernel Φ ρ Λ x).real (D.restrict ⁻¹' A) -
        (gibbsKernel Φ ρ Λ y).real (D.restrict ⁻¹' A)| < ε := by
  let δ := Real.log (1 + ε) / 4
  have hlog := Real.log_pos (show 1 < 1 + ε by linarith)
  have hδ : 0 < δ := div_pos hlog (by norm_num)
  have hexp : Real.exp δ * Real.exp δ - 1 < ε := by
    rw [← Real.exp_add, sub_lt_iff_lt_add, add_comm ε 1, ← Real.exp_log (by linarith : 0 < 1 + ε)]
    exact Real.exp_lt_exp.mpr (by dsimp only [δ]; linarith only [hlog])
  obtain ⟨T, hT⟩ := abs_hamiltonian_sub_lt_of_eqOn hΦ hsum Λ hδ
  refine ⟨T ∪ D, fun x y hxy A hA ↦ ?_⟩
  let B : Set (S → E) := D.restrict ⁻¹' A
  have hB : MeasurableSet B := D.measurable_restrict hA
  let W := latticeGibbsWeight Φ Λ
  let I : (S → E) → ℝ≥0∞ := B.indicator 1
  let N (w : S → E) := lmarginal (fun _ ↦ ρ) Λ (fun u ↦ W u * I u) w
  let Z (w : S → E) := lmarginal (fun _ ↦ ρ) Λ W w
  let e := ENNReal.ofReal (Real.exp δ)
  let G (w : S → E) := gibbsKernel Φ ρ Λ w B
  have hG (w : S → E) : G w = (Z w)⁻¹ * N w := gibbsKernel_apply hΦ ρ Λ w hB
  have hd (u v : S → E) (h : ∀ i ∈ T ∪ D, u i = v i) (ζ : Λ → E) (i : S) (hi : i ∈ T ∪ D) :
      Function.updateFinset u Λ ζ i = Function.updateFinset v Λ ζ i := by
    by_cases hΛ : i ∈ Λ
    · simp only [Function.updateFinset_def, dite_eq_left hΛ]
    · simp only [Function.updateFinset_def, dite_eq_right hΛ, h i hi]
  have hZ (w : S → E) := lmarginal_latticeGibbsWeight_pos_lt_top hsum ρ Λ w
  have hle (u v : S → E) (h : ∀ i ∈ T ∪ D, u i = v i) : G u ≤ e * e * G v := by
    have hΔ (ζ : Λ → E) :
        |hamiltonian Φ Λ (Function.updateFinset v Λ ζ) -
          hamiltonian Φ Λ (Function.updateFinset u Λ ζ)| < δ :=
      hT _ _ (fun i hi ↦ (hd u v h ζ i (Finset.mem_union_left _ hi)).symm)
    have hN : N u ≤ e * N v := by
      apply lmarginal_weight_le_mul hΦ ρ Λ u v δ (fun ζ ↦ (le_abs_self _).trans (hΔ ζ).le)
        (f := I) (measurable_const.indicator hB)
      intro ζ
      have hR : D.restrict (Function.updateFinset u Λ ζ) =
          D.restrict (Function.updateFinset v Λ ζ) :=
        funext fun i ↦ hd u v h ζ i (Finset.mem_union_right _ i.2)
      have hm : Function.updateFinset u Λ ζ ∈ B ↔ Function.updateFinset v Λ ζ ∈ B := by
        simp only [B, mem_preimage, hR]
      by_cases hu : Function.updateFinset u Λ ζ ∈ B
      · simp only [I, indicator_of_mem hu, indicator_of_mem (hm.mp hu), Pi.one_apply]
      · simp only [I, indicator_of_notMem hu, indicator_of_notMem (hm.not.mp hu)]
    have heZ : Z v ≤ e * Z u := by
      simpa only [Z, mul_one] using lmarginal_weight_le_mul hΦ ρ Λ v u δ
        (fun ζ ↦ by linarith [(neg_le_abs _).trans (hΔ ζ).le])
        (f := fun _ ↦ (1 : ℝ≥0∞)) measurable_const (fun _ ↦ rfl)
    rw [hG, hG]
    exact inv_mul_le_sq_mul_inv_mul hN heZ
      (hZ u).1.ne' (hZ u).2.ne (hZ v).1.ne' (hZ v).2.ne
  have hr (u v : S → E) (h : ∀ i ∈ T ∪ D, u i = v i) :
      (G u).toReal - (G v).toReal ≤ Real.exp δ * Real.exp δ - 1 := by
    let _ := isProbabilityMeasure_gibbsKernel hΦ hsum ρ Λ u
    let _ := isProbabilityMeasure_gibbsKernel hΦ hsum ρ Λ v
    have hv : G v ≤ 1 := prob_le_one
    have htop : e * e * G v ≠ ⊤ := ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
    have hu := ENNReal.toReal_mono htop (hle u v h)
    have hv' := ENNReal.toReal_mono ENNReal.one_ne_top hv
    simp only [ENNReal.toReal_mul, e, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hu
    simp only [ENNReal.toReal_one] at hv'
    have hp : 1 ≤ Real.exp δ * Real.exp δ := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    nlinarith only [hu, hv', mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hv')]
  rw [measureReal_def, measureReal_def, abs_sub_lt_iff]
  exact ⟨(hr x y hxy).trans_lt hexp, (hr y x (fun i hi ↦ (hxy i hi).symm)).trans_lt hexp⟩

/-- Uniformly local approximation preserves convergence of integrals along locally
convergent probability measures. -/
lemma TendstoLocally.tendsto_integral_of_oscillation [DecidableEq S] {I : Type*}
    {F : Filter I} {m : I → Measure (S → E)} {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hl : TendstoLocally F m μ) (hprob : ∀ᶠ i in F, IsProbabilityMeasure (m i))
    {f : (S → E) → ℝ} (hm : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C)
    (ho : ∀ ε > 0, ∃ T : Finset S, ∀ x y : S → E, (∀ i ∈ T, x i = y i) →
      |f x - f y| < ε) :
    Tendsto (fun i ↦ ∫ x, f x ∂m i) F (𝓝 (∫ x, f x ∂μ)) := by
  let a := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨T, hT⟩ := ho (ε / 4) (by positivity)
  let g (x : S → E) := f (splice T (T.restrict x) a)
  have hg : Measurable g := hm.comp ((measurable_splice T a).comp T.measurable_restrict)
  have hloc : IsLocalFunction g := isLocalFunction_def.mpr ⟨T, fun x y heq ↦ by
    have h : T.restrict x = T.restrict y := funext fun i ↦ heq i i.2
    simp only [g, h]⟩
  have hfg (x : S → E) : ‖f x - g x‖ ≤ ε / 4 := by
    rw [Real.norm_eq_abs]
    exact (hT x _ (by
      intro j hj
      simp only [splice_def, dite_eq_left hj, Finset.restrict_def])).le
  have hdist (ν : Measure (S → E)) [IsProbabilityMeasure ν] :
      dist (∫ x, f x ∂ν) (∫ x, g x ∂ν) ≤ ε / 4 := by
    have hfi : Integrable f ν := (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
    have hgi : Integrable g ν := (integrable_const C).mono' hg.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs, g] using hb (splice T (T.restrict x) a))
    rw [dist_eq_norm]
    calc
      _ ≤ ∫ x, ‖f x - g x‖ ∂ν := norm_integral_sub_le_of_measure_le le_rfl hfi hgi
      _ ≤ ∫ _, ε / 4 ∂ν :=
        integral_mono (hfi.sub hgi).norm (integrable_const _) hfg
      _ = _ := by simp [integral_const]
  have hconv := tendstoLocally_def.mp hl g hloc hg ⟨C, fun _ ↦ hb _⟩
  filter_upwards [hprob, Metric.tendsto_nhds.mp hconv (ε / 4) (by positivity)] with i hi hgi
  let _ := hi
  calc
    _ ≤ dist (∫ x, f x ∂m i) (∫ x, g x ∂m i) +
        dist (∫ x, g x ∂m i) (∫ x, g x ∂μ) +
        dist (∫ x, g x ∂μ) (∫ x, f x ∂μ) := dist_triangle4 _ _ _ _
    _ < ε := by
      rw [dist_comm (∫ x, g x ∂μ) (∫ x, f x ∂μ)]
      linarith only [hdist (m i), hdist μ, hgi, hε]

/-- The expectations of a kernel's cylinder probabilities converge at any local limit of
probability measures. -/
private lemma tendsto_lintegral_gibbsKernel_cylinder [Countable S] [DecidableEq S] {I : Type*}
    {F : Filter I} {m : I → Measure (S → E)} {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hl : TendstoLocally F m μ) (hprob : ∀ᶠ i in F, IsProbabilityMeasure (m i))
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ]
    (Λ D : Finset S) {A : Set (D → E)} (hA : MeasurableSet A) :
    Tendsto (fun i ↦ ∫⁻ x, gibbsKernel Φ ρ Λ x (D.restrict ⁻¹' A) ∂m i) F
      (𝓝 (∫⁻ x, gibbsKernel Φ ρ Λ x (D.restrict ⁻¹' A) ∂μ)) := by
  let B : Set (S → E) := D.restrict ⁻¹' A
  let f (x : S → E) := gibbsKernel Φ ρ Λ x B
  have hm : Measurable f := (measurable_gibbsKernel_outside hΦ ρ Λ
    (D.measurable_restrict hA)).mono (outsideSigma_le _) le_rfl
  have hle (x : S → E) : f x ≤ 1 := by
    let _ := isProbabilityMeasure_gibbsKernel hΦ hsum ρ Λ x
    exact prob_le_one
  have gbound (x : S → E) : |(f x).toReal| ≤ 1 := by
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (hle x)
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ T : Finset S, ∀ x y : S → E,
      (∀ i ∈ T, x i = y i) → |(f x).toReal - (f y).toReal| < ε := by
    obtain ⟨T, hT⟩ := gibbsKernel_real_cylinder_oscillation hΦ hsum ρ Λ D hε
    exact ⟨T, fun x y hxy ↦ hT x y hxy A hA⟩
  have hconv := hl.tendsto_integral_of_oscillation hprob hm.ennreal_toReal 1 gbound happ
  have he (ν : Measure (S → E)) [IsProbabilityMeasure ν] :
      ENNReal.ofReal (∫ x, (f x).toReal ∂ν) = ∫⁻ x, f x ∂ν := by
    have hfi : Integrable (fun x ↦ (f x).toReal) ν :=
      (integrable_const (1 : ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
        (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using gbound x)
    rw [ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
    exact lintegral_congr fun x ↦ ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hle x))
  have hf := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv
  rw [he μ] at hf
  refine hf.congr' ?_
  filter_upwards [hprob] with i hi
  let _ := hi
  exact he (m i)

/-- The probabilities of all cylinder events converge along locally converging
probability measures. -/
lemma TendstoLocally.tendsto_cylinder [DecidableEq S] {I : Type*} {F : Filter I}
    {m : I → Measure (S → E)} {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hl : TendstoLocally F m μ) (hprob : ∀ᶠ i in F, IsProbabilityMeasure (m i))
    (D : Finset S) {A : Set (D → E)} (hA : MeasurableSet A) :
    Tendsto (fun i ↦ m i (D.restrict ⁻¹' A)) F (𝓝 (μ (D.restrict ⁻¹' A))) := by
  let B : Set (S → E) := D.restrict ⁻¹' A
  let f := B.indicator (1 : (S → E) → ℝ)
  have hm : MeasurableSet B := D.measurable_restrict hA
  have hloc : IsLocalFunction f := isLocalFunction_def.mpr ⟨D, fun x y heq ↦ by
    have h : D.restrict x = D.restrict y := funext fun i ↦ heq i i.2
    have hxy : x ∈ B ↔ y ∈ B := by simp only [B, mem_preimage, h]
    by_cases hx : x ∈ B
    · simp only [f, indicator_of_mem hx, indicator_of_mem (hxy.mp hx), Pi.one_apply]
    · simp only [f, indicator_of_notMem hx, indicator_of_notMem (hxy.not.mp hx)]⟩
  have hb (x : S → E) : |f x| ≤ 1 := by
    by_cases hx : x ∈ B
    · simp only [f, indicator_of_mem hx, Pi.one_apply, abs_one, le_refl]
    · simp only [f, indicator_of_notMem hx, abs_zero, zero_le_one]
  have hconv := tendstoLocally_def.mp hl f hloc (measurable_const.indicator hm) ⟨1, hb⟩
  simp only [f, integral_indicator_one hm] at hconv
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv
  rw [ofReal_measureReal (measure_ne_top μ B)] at he
  refine he.congr' ?_
  filter_upwards [hprob] with i hi
  let _ := hi
  exact ofReal_measureReal (measure_ne_top (m i) B)

/-- The finite-volume Gibbs law's marginal is dominated by a fixed finite multiple
of the product reference measure, uniformly in its exterior configuration. -/
private lemma exists_domination_gibbsKernel [DecidableEq S]
    {Φ : Finset S → (S → E) → ℝ} (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] (Λ : Finset S) :
    ∃ ν : Measure (Λ → E), IsFiniteMeasure ν ∧
      ∀ ω, (gibbsKernel Φ ρ Λ ω).map Λ.restrict ≤ ν := by
  let P : Measure (Λ → E) := Measure.pi (fun _ ↦ ρ)
  let C := (∑' A : {A : Finset S // ¬ Disjoint A Λ}, potentialEnvelope Φ A).toReal
  let a := ENNReal.ofReal (Real.exp C)
  let b := ENNReal.ofReal (Real.exp (-C)) * P univ
  have hP : P univ ≠ 0 := by
    dsimp only [P]
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ Measure.measure_univ_ne_zero.mpr (NeZero.ne ρ)
  have hb : b ≠ 0 := mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) hP
  have hfin : IsFiniteMeasure ((b⁻¹ * a) • P) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hb) ENNReal.ofReal_ne_top).lt_top
      (measure_lt_top _ _)
  refine ⟨(b⁻¹ * a) • P, hfin, fun ω ↦ ?_⟩
  let w (ζ : Λ → E) := latticeGibbsWeight Φ Λ (splice Λ ζ ω)
  have hl (ζ : Λ → E) : ENNReal.ofReal (Real.exp (-C)) ≤ w ζ :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (neg_le_neg ((le_abs_self _).trans (abs_hamiltonian_le hsum Λ _))))
  have hu (ζ : Λ → E) : w ζ ≤ a :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      ((neg_le_abs _).trans (abs_hamiltonian_le hsum Λ _)))
  have hz : b ≤ (P.withDensity w) univ := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact (lintegral_const _).symm.le.trans (lintegral_mono hl)
  have hr : Λ.restrict ∘ (splice Λ · ω) = id := by
    funext ζ j
    simp only [Function.comp_apply, Finset.restrict_def, splice_def, dite_eq_left j.2, id_eq]
  have hk : Measurable (splice Λ · ω) := measurable_splice Λ ω
  rw [gibbsKernel_def, Measure.map_smul _ Λ.measurable_restrict.aemeasurable,
    Measure.map_map Λ.measurable_restrict hk, hr, Measure.map_id]
  have hd : P.withDensity w ≤ a • P := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ hu)
  refine Measure.le_iff.mpr fun A _ ↦ ?_
  simp only [smul_apply, smul_eq_mul]
  have ha : (P.withDensity w) A ≤ a * P A := by
    simpa only [smul_apply, smul_eq_mul] using hd A
  calc
    _ ≤ b⁻¹ * (a * P A) := by
      exact mul_le_mul' (ENNReal.inv_le_inv.mpr hz) ha
    _ = _ := (mul_assoc _ _ _).symm

/-- Probability measures satisfying each finite-region DLR equation eventually along an
ultrafilter have a Gibbs local limit. -/
private lemma exists_gibbs_tendstoLocally_of_eventually_dlr
    [Countable S] [DecidableEq S] [StandardBorelSpace E]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] {I : Type*} (U : Ultrafilter I)
    (m : I → Measure (S → E))
    (hp : ∀ᶠ i in (U : Filter I), IsProbabilityMeasure (m i))
    (hDLR : ∀ Λ : Finset S, ∀ᶠ i in (U : Filter I), ∀ A, MeasurableSet A →
      m i A = ∫⁻ ω, gibbsKernel Φ ρ Λ ω A ∂m i) :
    ∃ μ, IsGibbs (gibbsKernel Φ ρ) μ ∧ TendstoLocally (U : Filter I) m μ := by
  have hdom (Λ : Finset S) : ∃ ν : Measure (Λ → E), IsFiniteMeasure ν ∧
      ∀ᶠ i in (U : Filter I), (m i).map Λ.restrict ≤ ν := by
    obtain ⟨ν, hν, hle⟩ := exists_domination_gibbsKernel hsum ρ Λ
    refine ⟨ν, hν, ?_⟩
    filter_upwards [hp, hDLR Λ] with i hi hreg
    let _ := hi
    refine Measure.le_iff.mpr fun A hA ↦ ?_
    have hR : Measurable (Λ.restrict (π := fun _ : S ↦ E)) := Λ.measurable_restrict
    rw [Measure.map_apply hR hA, hreg _ (hR hA)]
    calc
      _ ≤ ∫⁻ _, ν A ∂m i := lintegral_mono fun ω ↦ by
        have hv := hle ω A
        rwa [Measure.map_apply hR hA] at hv
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  obtain ⟨μ, hμ, hl⟩ := exists_tendstoLocally_of_eventually_domination U m hp hdom
  let _ := hμ
  refine ⟨μ, isGibbs_def.mpr ⟨hμ, fun Λ A hA ↦ ?_⟩, hl⟩
  let γ := gibbsKernel Φ ρ
  have hγ : Measurable (γ Λ) := Measure.measurable_measure.mpr fun B hB ↦
    (measurable_gibbsKernel_outside hΦ ρ Λ hB).mono (outsideSigma_le _) le_rfl
  let π (D : Finset S) := μ.map (D.restrict (π := fun _ : S ↦ E))
  let _ (D : Finset S) : IsProbabilityMeasure (π D) :=
    (Measure.isProbabilityMeasure_map_iff D.measurable_restrict.aemeasurable).mpr hμ
  have hproj : IsProjectiveLimit (μ.bind (γ Λ)) π := by
    intro D
    refine Measure.ext fun B hB ↦ ?_
    have hR : Measurable (D.restrict (π := fun _ : S ↦ E)) := D.measurable_restrict
    rw [Measure.map_apply hR hB, Measure.bind_apply (hR hB) hγ.aemeasurable]
    simp only [π, Measure.map_apply hR hB]
    symm
    refine tendsto_nhds_unique (hl.tendsto_cylinder hp D hB)
      ((tendsto_lintegral_gibbsKernel_cylinder hl hp hΦ hsum ρ Λ D hB).congr' ?_)
    filter_upwards [hDLR Λ] with i hi
    exact (hi _ (D.measurable_restrict hB)).symm
  have he : μ = μ.bind (γ Λ) :=
    IsProjectiveLimit.unique (P := π) (fun _ ↦ rfl) hproj
  exact congrArg (fun ν : Measure (S → E) ↦ ν A) he |>.trans
    (Measure.bind_apply hA hγ.aemeasurable)

/-! ### Existence (SYNOPSIS item 60) -/

/-- SYNOPSIS item 60: for a standard Borel state space, a finite nonzero a priori measure, and an
absolutely summable potential on a countable site set, the Gibbsian specification is a
specification and its set of Gibbs measures is nonempty, convex, and compact in the topology of
local convergence. -/
theorem gibbsSet_nonempty_convex_compact [Countable S] [DecidableEq S] [StandardBorelSpace E]
    {Φ : Finset S → (S → E) → ℝ} (hΦ : IsPotential Φ) (hsum : IsAbsolutelySummable Φ)
    (ρ : Measure E) [IsFiniteMeasure ρ] [NeZero ρ] :
    IsSpecification (gibbsKernel Φ ρ) ∧ (gibbsSet (gibbsKernel Φ ρ)).Nonempty ∧
      (∀ μ ∈ gibbsSet (gibbsKernel Φ ρ), ∀ ν ∈ gibbsSet (gibbsKernel Φ ρ), ∀ t : ℝ,
        0 ≤ t → t ≤ 1 →
          ENNReal.ofReal t • μ + ENNReal.ofReal (1 - t) • ν ∈ gibbsSet (gibbsKernel Φ ρ)) ∧
      ∀ U : Ultrafilter (Measure (S → E)), gibbsSet (gibbsKernel Φ ρ) ∈ U →
        ∃ μ ∈ gibbsSet (gibbsKernel Φ ρ), TendstoLocally (U : Filter (Measure (S → E))) id μ := by
  classical
  let γ := gibbsKernel Φ ρ
  have hγ : IsSpecification γ := isSpecification_gibbsKernel hΦ hsum ρ
  refine ⟨hγ, ?_, ?_, ?_⟩
  · have hρ : ρ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne ρ)
    obtain ⟨a, _⟩ := nonempty_of_measure_ne_zero hρ
    let ω : S → E := fun _ ↦ a
    let U := Ultrafilter.of (atTop : Filter (Finset S))
    let m (Λ : Finset S) := γ Λ ω
    have hp : ∀ᶠ Λ in (U : Filter (Finset S)), IsProbabilityMeasure (m Λ) :=
      Eventually.of_forall fun Λ ↦ hγ.isProbabilityMeasure Λ ω
    have hDLR (Λ : Finset S) : ∀ᶠ Δ in (U : Filter (Finset S)), ∀ A, MeasurableSet A →
        m Δ A = ∫⁻ σ, γ Λ σ A ∂m Δ := by
      filter_upwards [(eventually_ge_atTop Λ).filter_mono (Ultrafilter.of_le _)] with Δ hΔ
      exact fun A hA ↦ (hγ.consistent Λ Δ hΔ ω A hA).symm
    obtain ⟨μ, hμ, _⟩ :=
      exists_gibbs_tendstoLocally_of_eventually_dlr hΦ hsum ρ U m hp hDLR
    exact ⟨μ, mem_gibbsSet.mpr hμ⟩
  · intro μ hμ ν hν t ht₀ ht₁
    exact mem_gibbsSet.mpr ((mem_gibbsSet.mp hμ).convex_combination (mem_gibbsSet.mp hν) ht₀ ht₁)
  · intro U hU
    have he : ∀ᶠ μ in (U : Filter (Measure (S → E))), IsGibbs γ μ :=
      (show ∀ᶠ μ in (U : Filter (Measure (S → E))), μ ∈ gibbsSet γ from hU).mono
        (fun _ h ↦ mem_gibbsSet.mp h)
    obtain ⟨μ, hμ, hl⟩ := exists_gibbs_tendstoLocally_of_eventually_dlr hΦ hsum ρ U id
      (he.mono fun _ hμ ↦ (isGibbs_def.mp hμ).1)
      (fun Λ ↦ he.mono fun _ hμ A hA ↦ (isGibbs_def.mp hμ).2 Λ A hA)
    exact ⟨μ, mem_gibbsSet.mpr hμ, hl⟩

end MSSS
