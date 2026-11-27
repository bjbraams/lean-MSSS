module

public import MSSS.PointProcesses.Palm
public import MSSS.RandomFields.Basic
public import TauCeti.Analysis.SpecialFunctions.Exp.Negative

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Fin.Tuple.Basic
import TauCeti.Probability.Distributions.Poisson.Measurability
import TauCeti.Probability.Distributions.Poisson.FactorialMoments
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.MeasureTheory.Measure.Mixture.Basic

/-!
# Cox processes

SYNOPSIS items 85 and 86: moments and characterisations of Cox processes, and log-Gaussian Cox
processes. A point process `η` is a Cox process directed by the random measure `ξ` when,
conditionally on `ξ`, it is a Poisson process with intensity `ξ`; this is stated through the
joint law of `ξ` and the counts of `η` on finitely many disjoint sets (`MSSS.IsCoxProcess`).
For the intensity and second product densities we use TauCeti’s Poisson factorial moments,
product densities, and integration of mixtures. The void probability uses TauCeti’s exponential
of a negative extended nonnegative mass.

## Main definitions

* `MSSS.IsCoxProcess P η ξ`: `η` is a Cox process directed by `ξ`.

## Main results

* `MSSS.factorialMoment_cox`, `MSSS.variance_cox`, `MSSS.map_eq_iff_cox`,
  `MSSS.isCoxProcess_iff_mecke`, `MSSS.simple_iff_diffuse_cox`, `MSSS.moments_cox_density`:
  SYNOPSIS item 85.
* `MSSS.factorialMoment_logGaussianCox`, `MSSS.isStationary_logGaussianCox_iff`,
  `MSSS.logGaussianCox_parameters_injective`: SYNOPSIS item 86.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Function TauCeti.Probability
open scoped ENNReal NNReal

namespace MSSS

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- `η` is a **Cox process directed by** `ξ`: for disjoint measurable `A_1, …, A_n`, counts
`k_i`, and a measurable set `C` of measures,
`P(ξ ∈ C, η(A_i) = k_i ∀ i) = E[𝟙_C(ξ) ∏_i Po(ξ(A_i))({k_i})]`, with `Po(∞)({k}) = 0`. -/
def IsCoxProcess (P : Measure Ω) (η ξ : Ω → Measure X) : Prop :=
  Measurable η ∧ Measurable ξ ∧ ∀ (n : ℕ) (A : Fin n → Set X) (k : Fin n → ℕ)
    (C : Set (Measure X)), (∀ i, MeasurableSet (A i)) → Pairwise (Function.onFun Disjoint A) →
    MeasurableSet C →
    P {ω | ξ ω ∈ C ∧ ∀ i, η ω (A i) = k i} =
      ∫⁻ ω in ξ ⁻¹' C, ∏ i, (if ξ ω (A i) = ∞ then 0
        else poissonMeasure (ξ ω (A i)).toNNReal {k i}) ∂P

lemma isCoxProcess_def {P : Measure Ω} {η ξ : Ω → Measure X} : IsCoxProcess P η ξ ↔
    Measurable η ∧ Measurable ξ ∧ ∀ (n : ℕ) (A : Fin n → Set X) (k : Fin n → ℕ)
      (C : Set (Measure X)), (∀ i, MeasurableSet (A i)) → Pairwise (Function.onFun Disjoint A) →
      MeasurableSet C →
      P {ω | ξ ω ∈ C ∧ ∀ i, η ω (A i) = k i} =
        ∫⁻ ω in ξ ⁻¹' C, ∏ i, (if ξ ω (A i) = ∞ then 0
          else poissonMeasure (ξ ω (A i)).toNNReal {k i}) ∂P := Iff.rfl

/-! ### Moments of Cox processes (SYNOPSIS item 85) -/

/-- SYNOPSIS item 85 (a): the factorial moment measures of a Cox process are the moment measures
of the directing measure, `E η^{(m)} = E ξ^m`; for `m = 1`, `η` and `ξ` have the same intensity
measure. -/
theorem factorialMoment_cox {P : Measure Ω} [IsProbabilityMeasure P] (I : Ω → ℕ → Bool)
    (x : Ω → ℕ → X) {ξ : Ω → Measure X} [∀ ω, SigmaFinite (ξ ω)]
    (hcox : IsCoxProcess P (fun ω ↦ pointSum (I ω) (x ω)) ξ) (m : ℕ) :
    P.bind (fun ω ↦ factorialPointSum m (I ω) (x ω)) =
      P.bind (fun ω ↦ Measure.pi fun _ : Fin m ↦ ξ ω) := by
  sorry

/-- SYNOPSIS item 85 (b): with `ν` the common intensity measure and `u ∈ L¹(ν)`,
`E η(u)² < ∞` if and only if `E ξ(u)² < ∞` and `u ∈ L²(ν)`, and then
`Var η(u) = ν(u²) + Var ξ(u)`. -/
theorem variance_cox {P : Measure Ω} [IsProbabilityMeasure P] {η ξ : Ω → Measure X}
    (hcox : IsCoxProcess P η ξ) {u : X → ℝ} (hu : Integrable u (P.bind ξ)) :
    (MemLp (fun ω ↦ ∫ y, u y ∂η ω) 2 P ↔
        MemLp (fun ω ↦ ∫ y, u y ∂ξ ω) 2 P ∧ MemLp u 2 (P.bind ξ)) ∧
      (MemLp (fun ω ↦ ∫ y, u y ∂η ω) 2 P →
        Var[fun ω ↦ ∫ y, u y ∂η ω; P] =
          ∫ y, u y ^ 2 ∂P.bind ξ + Var[fun ω ↦ ∫ y, u y ∂ξ ω; P]) := by
  sorry

/-- SYNOPSIS item 85 (c): two Cox point processes have the same law if and only if their directing
measures do. The count formulation of `IsCoxProcess` tests only natural-valued counts, so
integer-valued configurations are required almost surely in both laws. -/
theorem map_eq_iff_cox {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {η ξ : Ω → Measure X}
    {η' ξ' : Ω' → Measure X} (hcox : IsCoxProcess P η ξ) (hcox' : IsCoxProcess P' η' ξ')
    (hint : ∀ᵐ ω ∂P, (η ω).IsIntegerValued) (hint' : ∀ᵐ ω ∂P', (η' ω).IsIntegerValued) :
    P.map η = P'.map η' ↔ P.map ξ = P'.map ξ' := by
  sorry

/-- SYNOPSIS item 85 (d): `η` is a Cox process directed by `ξ` if and only if
`E ∫ f(x, η, ξ) η(dx) = E ∫ f(x, η + δ_x, ξ) ξ(dx)` for all measurable `f ≥ 0`. -/
theorem isCoxProcess_iff_mecke {P : Measure Ω} [IsProbabilityMeasure P] {η ξ : Ω → Measure X}
    (hηm : Measurable η) (hξm : Measurable ξ) (hint : ∀ ω, (η ω).IsIntegerValued)
    (hsf : ∀ ω, SFinite (η ω)) (hξsf : ∀ ω, SFinite (ξ ω)) :
    IsCoxProcess P η ξ ↔ ∀ f : X → Measure X → Measure X → ℝ≥0∞,
      Measurable (fun z : X × Measure X × Measure X ↦ f z.1 z.2.1 z.2.2) →
        ∫⁻ ω, ∫⁻ y, f y (η ω) (ξ ω) ∂(η ω) ∂P =
          ∫⁻ ω, ∫⁻ y, f y (η ω + Measure.dirac y) (ξ ω) ∂(ξ ω) ∂P := by
  sorry

/-- SYNOPSIS item 85 (e): on a standard Borel space, a Cox process directed by an almost surely
σ-finite `ξ` is almost surely simple if and only if `ξ` is almost surely diffuse. -/
theorem simple_iff_diffuse_cox [StandardBorelSpace X] {P : Measure Ω} [IsProbabilityMeasure P]
    {η ξ : Ω → Measure X} (hcox : IsCoxProcess P η ξ) (hσ : ∀ᵐ ω ∂P, SigmaFinite (ξ ω)) :
    (∀ᵐ ω ∂P, ∀ y, η ω {y} ≤ 1) ↔ ∀ᵐ ω ∂P, ∀ y, ξ ω {y} = 0 := by
  sorry

section CountMoments

variable {P : Measure Ω} {η ξ : Ω → Measure X}

/-- A Cox count is zero with probability the mean of the exponential of minus the directing
mass, with zero contribution from infinite directing masses. -/
theorem IsCoxProcess.measure_eq_zero_apply (h : IsCoxProcess P η ξ)
    {B : Set X} (hB : MeasurableSet B) :
    P {ω | η ω B = 0} = ∫⁻ ω, (ENNReal.expNeg (ξ ω B) : ℝ≥0∞) ∂P := by
  have h₀ := h.2.2 1 (fun _ ↦ B) (fun _ ↦ 0) univ (fun _ ↦ hB)
    (fun i j hne ↦ False.elim (hne (Subsingleton.elim i j))) MeasurableSet.univ
  simp only [Set.mem_univ, true_and, Set.preimage_univ, Measure.restrict_univ,
    Fin.prod_univ_one, Nat.cast_zero] at h₀
  have hL : {ω | ∀ i : Fin 1, η ω B = (0 : ℝ≥0∞)} = {ω | η ω B = 0} := by
    ext ω
    exact ⟨fun hω ↦ hω 0, fun hω _ ↦ hω⟩
  rw [← hL, h₀]
  refine lintegral_congr fun ω ↦ ?_
  by_cases htop : ξ ω B = ⊤
  · simp only [htop, ite_eq_left, ENNReal.expNeg_top, ENNReal.coe_zero]
  · simp only [ite_eq_right htop, poissonMeasure_singleton, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, div_one]
    nth_rw 2 [← ENNReal.coe_toNNReal htop]
    rw [ENNReal.expNeg_coe]
    rfl

private lemma poissonCountTuple_apply_singleton {n : ℕ} (r : Fin n → ℝ≥0) (k : Fin n → ℕ) :
    (Measure.pi fun i ↦ poissonMeasure (r i)) {k} = ∏ i, poissonMeasure (r i) {k i} := by
  have he : ({k} : Set (Fin n → ℕ)) = Set.univ.pi (fun i ↦ {k i}) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun e ↦ congrFun e, funext⟩
  rw [he, Measure.pi_pi]

private lemma measurable_poissonCountTuple_apply_singleton {n : ℕ} {r : Ω → Fin n → ℝ≥0}
    (hr : ∀ i, Measurable (fun ω ↦ r ω i)) (k : Fin n → ℕ) :
    Measurable (fun ω ↦ (Measure.pi fun i ↦ poissonMeasure (r ω i)) {k}) := by
  simp only [poissonCountTuple_apply_singleton]
  exact Finset.measurable_prod _ fun i _ ↦ (Measure.measurable_coe (measurableSet_singleton _)).comp
    (measurable_poissonMeasure.comp (hr i))

/-- The count-tuple integrals of a Cox process on disjoint sets of almost surely finite
directing mass are mixtures of the corresponding independent Poisson count integrals. -/
private theorem IsCoxProcess.ae_natCast_eval_pi_and_lintegral [IsProbabilityMeasure P]
    (h : IsCoxProcess P η ξ) {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfin : ∀ᵐ ω ∂P, ∀ i, ξ ω (A i) < ⊤) :
    (∀ᵐ ω ∂P, ∃ k : Fin n → ℕ, ∀ i, η ω (A i) = k i) ∧
    ∀ G : (Fin n → ℝ≥0∞) → ℝ≥0∞,
      ∫⁻ ω, G (fun i ↦ η ω (A i)) ∂P =
        ∫⁻ ω, ∫⁻ k : Fin n → ℕ, G (fun i ↦ k i)
          ∂Measure.pi (fun i ↦ poissonMeasure (ξ ω (A i)).toNNReal) ∂P := by
  let L (ω : Ω) := Measure.pi (fun i ↦ poissonMeasure (ξ ω (A i)).toNNReal)
  let S (k : Fin n → ℕ) := {ω | ∀ i, η ω (A i) = k i}
  have hSm (k : Fin n → ℕ) : MeasurableSet (S k) := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ ((Measure.measurable_coe (hA i)).comp h.1)
      (measurableSet_singleton _)
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    intro k l hkl
    refine Set.disjoint_left.mpr fun ω hk hl ↦ hkl ?_
    exact funext fun i ↦ by exact_mod_cast (hk i).symm.trans (hl i)
  have hLm (k : Fin n → ℕ) : Measurable (fun ω ↦ L ω {k}) :=
    measurable_poissonCountTuple_apply_singleton (fun i ↦
      ((Measure.measurable_coe (hA i)).comp h.2.1).ennreal_toNNReal) k
  have hS (k : Fin n → ℕ) : P (S k) = ∫⁻ ω, L ω {k} ∂P := by
    have he := h.2.2 n A k univ hA hdisj MeasurableSet.univ
    simp only [Set.mem_univ, true_and, Set.preimage_univ, Measure.restrict_univ] at he
    rw [show P (S k) = _ from he]
    refine lintegral_congr_ae (hfin.mono fun ω hω ↦ ?_)
    dsimp only
    rw [show L ω {k} = _ from poissonCountTuple_apply_singleton _ _]
    exact Finset.prod_congr rfl fun i _ ↦ ite_eq_right (hω i).ne
  have honce : P (⋃ k, S k) = 1 := by
    rw [measure_iUnion hSd hSm]
    simp_rw [hS]
    rw [← lintegral_tsum (fun k ↦ (hLm k).aemeasurable)]
    have hsum (ω : Ω) : ∑' k : Fin n → ℕ, L ω {k} = 1 := by
      simpa only [lintegral_const, measure_univ, one_mul] using
        (lintegral_countable' (μ := L ω) (fun _ ↦ (1 : ℝ≥0∞))).symm
    simp only [hsum, lintegral_const, measure_univ, mul_one]
  have haeUnion : ∀ᵐ ω ∂P, ω ∈ ⋃ k, S k :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hSm)).mpr honce
  have hAE : ∀ᵐ ω ∂P, ∃ k : Fin n → ℕ, ∀ i, η ω (A i) = k i :=
    haeUnion.mono fun ω hω ↦ Set.mem_iUnion.mp hω
  refine ⟨hAE, fun G ↦ ?_⟩
  have hrepr : (fun ω ↦ G (fun i ↦ η ω (A i))) =ᵐ[P]
      fun ω ↦ ∑' k : Fin n → ℕ, (S k).indicator (fun _ ↦ G (fun i ↦ k i)) ω := by
    filter_upwards [hAE] with ω hω
    obtain ⟨k, hk⟩ := hω
    rw [tsum_eq_single k, Set.indicator_of_mem (show ω ∈ S k from hk), funext hk]
    intro j hj
    rw [Set.indicator_of_notMem (fun hjω ↦ hj (funext fun i ↦
      by exact_mod_cast (hjω i).symm.trans (hk i)))]
  rw [lintegral_congr_ae hrepr, lintegral_tsum (fun k ↦
    (measurable_const.indicator (hSm k)).aemeasurable)]
  simp_rw [lintegral_indicator (hSm _), lintegral_const, Measure.restrict_apply_univ, hS,
    ← lintegral_const_mul _ (hLm _)]
  rw [← lintegral_tsum (fun k ↦ ((hLm k).const_mul _).aemeasurable)]
  exact lintegral_congr fun ω ↦ (lintegral_countable' (μ := L ω) _).symm

/-- A product of Poisson counts has mixed factorial moments given by its rate powers. -/
private lemma lintegral_prod_descFactorial_pi_eq {n : ℕ} {v : Fin n → ℝ≥0∞}
    (hω : ∀ i, v i < ⊤) (r : Fin n → ℕ) :
    (∫⁻ k : Fin n → ℕ, ∏ i, ((k i).descFactorial (r i) : ℝ≥0∞)
      ∂Measure.pi (fun i ↦ poissonMeasure (v i).toNNReal)) =
      ∏ i, (v i) ^ r i := by
  let lam : Fin n → ℝ≥0 := fun i ↦ (v i).toNNReal
  have he (k : Fin n → ℕ) :
      (∏ i, ((k i).descFactorial (r i) : ℝ≥0∞)) =
        ENNReal.ofReal (∏ i, ((k i).descFactorial (r i) : ℝ)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_prod_descFactorial_pi_poissonMeasure lam r)
    (ae_of_all _ (fun k ↦ Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)),
    integral_prod_descFactorial_pi_poissonMeasure,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ pow_nonneg (NNReal.coe_nonneg _) _)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_toNNReal (hω i).ne]

/-- A mixed factorial moment of Cox counts equals the same mixed power moment of the directing
masses, for disjoint sets with almost surely finite directing masses. -/
theorem IsCoxProcess.lintegral_eval_pi_eq_of_descFactorial [IsProbabilityMeasure P]
    (h : IsCoxProcess P η ξ) {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hfin : ∀ᵐ ω ∂P, ∀ i, ξ ω (A i) < ⊤)
    (r : Fin n → ℕ) (G : (Fin n → ℝ≥0∞) → ℝ≥0∞)
    (hG : ∀ k : Fin n → ℕ, G (fun i ↦ k i) = ∏ i, ((k i).descFactorial (r i) : ℝ≥0∞)) :
    ∫⁻ ω, G (fun i ↦ η ω (A i)) ∂P = ∫⁻ ω, ∏ i, (ξ ω (A i)) ^ r i ∂P := by
  rw [(h.ae_natCast_eval_pi_and_lintegral hA hdisj hfin).2 G]
  refine lintegral_congr_ae (hfin.mono fun ω hω ↦ ?_)
  simp_rw [hG]
  exact lintegral_prod_descFactorial_pi_eq hω r

/-- On a set of almost surely finite directing mass a Cox count has that mass as its
conditional mean, and therefore the same unconditional mean. -/
theorem IsCoxProcess.lintegral_eval_eq [IsProbabilityMeasure P] (h : IsCoxProcess P η ξ)
    {A : Set X} (hA : MeasurableSet A) (hfin : ∀ᵐ ω ∂P, ξ ω A < ⊤) :
    ∫⁻ ω, η ω A ∂P = ∫⁻ ω, ξ ω A ∂P := by
  simpa only [Fin.prod_univ_one, pow_one] using h.lintegral_eval_pi_eq_of_descFactorial
    (n := 1) (A := fun _ ↦ A) (fun _ ↦ hA)
    (fun _ _ hij ↦ (hij (Subsingleton.elim _ _)).elim) (hfin.mono fun _ hω _ ↦ hω)
    (fun _ ↦ 1) (fun l ↦ l 0) (fun k ↦ by rw [Fin.prod_univ_one, Nat.descFactorial_one])

/-- The second falling factorial plus the count itself is the square of the count. -/
private lemma natCast_mul_sub_one_add_self (n : ℕ) :
    (n : ℝ≥0∞) * ((n : ℝ≥0∞) - 1) + n = (n : ℝ≥0∞) * n := by
  rw [← Nat.cast_one, ← ENNReal.natCast_sub, ← Nat.cast_mul, ← Nat.cast_add,
    ← Nat.cast_mul]
  exact_mod_cast (show n * (n - 1) + n = n * n from by
    cases n with
    | zero => rfl
    | succ n => rw [Nat.succ_sub_one, Nat.mul_succ])

private lemma lintegral_poissonCountTuple_distinctPairs {v : Fin 3 → ℝ≥0∞}
    (hω : ∀ i, v i < ⊤) :
    ∫⁻ k : Fin 3 → ℕ, (k 0 : ℝ≥0∞) * k 1 + (k 0 : ℝ≥0∞) * k 2 + (k 2 : ℝ≥0∞) * k 1 +
      (k 2 : ℝ≥0∞) * ((k 2 : ℝ≥0∞) - 1)
      ∂Measure.pi (fun i ↦ poissonMeasure (v i).toNNReal) = (v 0 + v 2) * (v 1 + v 2) := by
  let lam : Fin 3 → ℝ≥0 := fun i ↦ (v i).toNNReal
  let Q : Measure (Fin 3 → ℕ) := Measure.pi (fun i ↦ poissonMeasure (lam i))
  have hμ (r : Fin 3 → ℕ) :
      ∫⁻ k : Fin 3 → ℕ, ∏ i, ((k i).descFactorial (r i) : ℝ≥0∞) ∂Q =
        ∏ i, (v i) ^ r i :=
    lintegral_prod_descFactorial_pi_eq hω r
  have h11 :
      ∫⁻ k : Fin 3 → ℕ, (k 0 : ℝ≥0∞) * k 1 ∂Q = v 0 * v 1 := by
    simpa [Fin.prod_univ_three] using hμ ![1, 1, 0]
  have h12 :
      ∫⁻ k : Fin 3 → ℕ, (k 0 : ℝ≥0∞) * k 2 ∂Q = v 0 * v 2 := by
    simpa [Fin.prod_univ_three] using hμ ![1, 0, 1]
  have h21 :
      ∫⁻ k : Fin 3 → ℕ, (k 2 : ℝ≥0∞) * k 1 ∂Q = v 2 * v 1 := by
    simpa [Fin.prod_univ_three, mul_comm] using hμ ![0, 1, 1]
  have h22 :
      ∫⁻ k : Fin 3 → ℕ, (k 2 : ℝ≥0∞) * ((k 2 : ℝ≥0∞) - 1) ∂Q = (v 2) ^ 2 := by
    simpa [Fin.prod_univ_three, Nat.descFactorial_succ, ENNReal.natCast_sub,
      mul_comm] using hμ ![0, 0, 2]
  change (∫⁻ k : Fin 3 → ℕ, (k 0 : ℝ≥0∞) * k 1 + (k 0 : ℝ≥0∞) * k 2 +
    (k 2 : ℝ≥0∞) * k 1 + (k 2 : ℝ≥0∞) * ((k 2 : ℝ≥0∞) - 1) ∂Q) = _
  simp only [lintegral_add_left Measurable.of_discrete, h11, h12, h21, h22]
  rw [pow_two]
  ring

/-- The covariance contribution of overlap disappears when counting ordered pairs of
distinct occurrences of a Cox process. -/
theorem lintegral_factorialPointSum_two_apply_prod_cox [IsProbabilityMeasure P]
    (I : Ω → ℕ → Bool) (x : Ω → ℕ → X)
    (hcox : IsCoxProcess P (fun ω ↦ pointSum (I ω) (x ω)) ξ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, ξ ω (A ∪ B) < ⊤) :
    ∫⁻ ω, ((factorialPointSum 2 (I ω) (x ω)).map MeasurableEquiv.finTwoArrow) (A ×ˢ B) ∂P =
      ∫⁻ ω, ξ ω A * ξ ω B ∂P := by
  let D : Fin 3 → Set X := ![A \ B, B \ A, A ∩ B]
  have hDm : ∀ i, MeasurableSet (D i) := by
    intro i
    fin_cases i
    · exact hA.diff hB
    · exact hB.diff hA
    · exact hA.inter hB
  have hDd : Pairwise (Function.onFun Disjoint D) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp [Function.onFun, D, Set.disjoint_left] at hij ⊢
    all_goals aesop
  have hDf : ∀ᵐ ω ∂P, ∀ i, ξ ω (D i) < ⊤ := hfin.mono fun ω hw i ↦ by
    refine lt_of_le_of_lt (measure_mono ?_) hw
    fin_cases i
    · exact Set.sdiff_subset.trans Set.subset_union_left
    · exact Set.sdiff_subset.trans Set.subset_union_right
    · exact Set.inter_subset_left.trans Set.subset_union_left
  let F (k : Fin 3 → ℝ≥0∞) :=
    k 0 * k 1 + k 0 * k 2 + k 2 * k 1 + k 2 * (k 2 - 1)
  let η (ω : Ω) := pointSum (I ω) (x ω)
  have hshift (ν : Measure X) :
      ν A = ν (D 0) + ν (D 2) ∧ ν B = ν (D 1) + ν (D 2) :=
    ⟨(measure_sdiff_add_inter A hB).symm,
      by simpa [D, Set.inter_comm B A] using (measure_sdiff_add_inter B hA).symm⟩
  obtain ⟨hηfin, hEval⟩ := hcox.ae_natCast_eval_pi_and_lintegral hDm hDd hDf
  calc
    _ = ∫⁻ ω, F (fun i ↦ η ω (D i)) ∂P := by
      refine lintegral_congr_ae (hηfin.mono fun ω ⟨k, hk⟩ ↦ ?_)
      dsimp only
      have hd : η ω (A ∩ B) = (k 2 : ℝ≥0∞) := hk 2
      apply (ENNReal.add_left_inj (a := η ω (A ∩ B))
        (by rw [hd]; exact ENNReal.natCast_ne_top _)).mp
      rw [factorialPointSum_two_apply_prod_add _ _ hA hB]
      have hh (i : Fin 3) : η ω (D i) = k i := hk i
      dsimp only [F]
      rw [hshift (η ω) |>.1, hshift (η ω) |>.2, hd, hh 0, hh 1, hh 2]
      rw [add_assoc, natCast_mul_sub_one_add_self, add_mul, mul_add, mul_add]
      ac_rfl
    _ = ∫⁻ ω, ∫⁻ k : Fin 3 → ℕ, F (fun i ↦ k i)
          ∂Measure.pi (fun i ↦ poissonMeasure (ξ ω (D i)).toNNReal) ∂P := hEval F
    _ = _ := by
      refine lintegral_congr_ae (hDf.mono fun ω hω ↦ ?_)
      dsimp only
      rw [hshift (ξ ω) |>.1, hshift (ξ ω) |>.2]
      exact lintegral_poissonCountTuple_distinctPairs hω

/-- The mean measure of a Cox process equals the mean directing measure if almost surely the
directing measure is finite on each set of a deterministic measurable cover. -/
theorem IsCoxProcess.bind_eq_of_cover [IsProbabilityMeasure P]
    (h : IsCoxProcess P η ξ) {C : ℕ → Set X} (hC : ∀ n, MeasurableSet (C n))
    (hcover : ⋃ n, C n = univ) (hfin : ∀ n, ∀ᵐ ω ∂P, ξ ω (C n) < ⊤) :
    P.bind η = P.bind ξ := by
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro n
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
    Measure.bind_apply (hA.inter (hC n)) h.1.aemeasurable,
    Measure.bind_apply (hA.inter (hC n)) h.2.1.aemeasurable]
  exact h.lintegral_eval_eq (hA.inter (hC n))
    ((hfin n).mono fun ω hw ↦ (measure_mono Set.inter_subset_right).trans_lt hw)

/-- A mixture of two-coordinate product measures evaluated on a rectangle is the expected
product of the masses of the two factors of the rectangle. -/
theorem bind_pi_two_map_apply_prod [∀ ω, SigmaFinite (ξ ω)]
    (hm : Measurable (fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)))
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((P.bind fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)).map
      MeasurableEquiv.finTwoArrow) (A ×ˢ B) = ∫⁻ ω, ξ ω A * ξ ω B ∂P := by
  let e : (Fin 2 → X) ≃ᵐ X × X := MeasurableEquiv.finTwoArrow
  rw [Measure.map_apply e.measurable (hA.prod hB),
    Measure.bind_apply (e.measurable (hA.prod hB)) hm.aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  rw [← Measure.map_apply e.measurable (hA.prod hB), (measurePreserving_finTwoArrow (ξ ω)).map_eq,
    Measure.prod_prod]

/-- Under a deterministic cover with finite directing second moments, the second factorial
moment measure of a Cox process is the mixture of the two-fold directing product measures. -/
theorem bind_factorialPointSum_two_cox_of_cover [IsProbabilityMeasure P]
    (I : Ω → ℕ → Bool) (x : Ω → ℕ → X) [∀ ω, SigmaFinite (ξ ω)]
    (hcox : IsCoxProcess P (fun ω ↦ pointSum (I ω) (x ω)) ξ)
    (hm : Measurable (fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)))
    {C : ℕ → Set X} (hC : ∀ n, MeasurableSet (C n)) (hmono : Monotone C)
    (hcover : ⋃ n, C n = univ) (hfin : ∀ n, ∀ᵐ ω ∂P, ξ ω (C n) < ⊤)
    (h₂ : ∀ n, ∫⁻ ω, ξ ω (C n) * ξ ω (C n) ∂P < ⊤) :
    P.bind (fun ω ↦ factorialPointSum 2 (I ω) (x ω)) =
      P.bind (fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)) := by
  let η (ω : Ω) := pointSum (I ω) (x ω)
  have hηfin : ∀ᵐ ω ∂P, ∀ n, η ω (C n) < ⊤ := ae_all_iff.2 fun n ↦ by
    have hN := (hcox.ae_natCast_eval_pi_and_lintegral (n := 1) (A := fun _ ↦ C n)
      (fun _ ↦ hC n) (fun i j hne ↦ (hne (Subsingleton.elim i j)).elim)
      ((hfin n).mono fun _ hw _ ↦ hw)).1
    exact hN.mono fun ω ⟨k, hk⟩ ↦ by
      dsimp only [η]
      rw [hk 0]
      exact ENNReal.natCast_lt_top _
  have hα := aemeasurable_factorialPointSum_two_of_cover I x hcox.1 hC hmono hcover hηfin
  let e : (Fin 2 → X) ≃ᵐ X × X := MeasurableEquiv.finTwoArrow
  apply e.map_measurableEquiv_injective
  symm
  have hcp : (⋃ n, C n ×ˢ C n) = univ := by
    simpa only [univ_inter, univ_prod_univ] using iUnion_prod_inter_eq_prod hmono hcover univ univ
  apply Measure.ext_of_iUnion_eq_univ hcp
  intro n
  have : IsFiniteMeasure (((P.bind fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)).map e).restrict
      (C n ×ˢ C n)) := ⟨by
        rw [Measure.restrict_apply_univ, bind_pi_two_map_apply_prod hm (hC n) (hC n)]
        exact h₂ n⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.restrict_apply (hA.prod hB), Measure.restrict_apply (hA.prod hB), Set.prod_inter_prod,
    bind_pi_two_map_apply_prod hm (hA.inter (hC n)) (hB.inter (hC n)),
    Measure.map_apply e.measurable ((hA.inter (hC n)).prod (hB.inter (hC n))),
    Measure.bind_apply (e.measurable ((hA.inter (hC n)).prod (hB.inter (hC n)))) hα]
  have hfinAB : ∀ᵐ ω ∂P, ξ ω ((A ∩ C n) ∪ (B ∩ C n)) < ⊤ :=
    (hfin n).mono fun ω hw ↦ (measure_mono
      (Set.union_subset Set.inter_subset_right Set.inter_subset_right)).trans_lt hw
  symm
  simpa only [← Measure.map_apply e.measurable ((hA.inter (hC n)).prod (hB.inter (hC n)))] using
    lintegral_factorialPointSum_two_apply_prod_cox I x hcox
      (hA.inter (hC n)) (hB.inter (hC n)) hfinAB

/-- A jointly measurable density with finite second moment at each location supplies a fixed
measurable cover on which the directing masses have a finite first and second moment. -/
private lemma exists_cox_moment_cover [IsProbabilityMeasure P]
    {Q : Measure X} [SigmaFinite Q] {Z : X → Ω → ℝ}
    (hZm : Measurable (Function.uncurry Z)) (hZ0 : ∀ y ω, 0 ≤ Z y ω)
    (hZ2 : ∀ y, MemLp (Z y) 2 P)
    [∀ ω, SigmaFinite (ξ ω)] (hξm : Measurable ξ)
    (hPim : Measurable (fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)))
    (hρ : P.bind ξ = Q.withDensity (fun y ↦ ∫⁻ ω, ENNReal.ofReal (Z y ω) ∂P))
    (hρ₂ : (P.bind fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)) =
      (Measure.pi fun _ : Fin 2 ↦ Q).withDensity (fun z ↦
        ∫⁻ ω, ENNReal.ofReal (Z (z 0) ω) * ENNReal.ofReal (Z (z 1) ω) ∂P)) :
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧ Monotone C ∧ (⋃ n, C n) = univ ∧
      ∀ n, (∫⁻ ω, ξ ω (C n) ∂P < ⊤) ∧ (∫⁻ ω, ξ ω (C n) * ξ ω (C n) ∂P < ⊤) := by
  let U (y : X) := ∫⁻ ω, ENNReal.ofReal (Z y ω ^ 2) ∂P
  have hU : Measurable U :=
    (Measurable.ennreal_ofReal (hZm.pow_const 2)).lintegral_prod_right
  have hUf (y : X) : U y < ⊤ := by
    dsimp only [U]
    rw [← ofReal_integral_eq_lintegral_ofReal (hZ2 y).integrable_sq
      (ae_of_all _ (fun _ ↦ sq_nonneg _))]
    exact ENNReal.ofReal_lt_top
  let C (n : ℕ) := spanningSets Q n ∩ {y | U y ≤ (n : ℝ≥0∞)}
  have hCm (n : ℕ) : MeasurableSet (C n) :=
    (measurableSet_spanningSets Q n).inter (hU measurableSet_Iic)
  have hmono : Monotone C := fun i j hij ↦ by
    have hij' : (i : ℝ≥0∞) ≤ (j : ℝ≥0∞) := by exact_mod_cast hij
    exact Set.inter_subset_inter (spanningSets_mono hij) (fun _ hy ↦ hy.trans hij')
  have hcover : ⋃ n, C n = univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (iUnion_spanningSets Q ▸ Set.mem_univ y)
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (hUf y).ne
    exact Set.mem_iUnion.mpr ⟨max n m, spanningSets_mono (le_max_left _ _) hn,
      hm.le.trans ((by exact_mod_cast (le_max_right n m)))⟩
  have hvol (n : ℕ) : Q (C n) < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top Q n)
  have hmZ (y : X) : Measurable (Z y) := hZm.comp measurable_prodMk_left
  have hU1 (y : X) :
      (∫⁻ ω, ENNReal.ofReal (Z y ω) ∂P) ≤ 1 + U y := by
    calc
      _ ≤ ∫⁻ ω, 1 + ENNReal.ofReal (Z y ω ^ 2) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith only [sq_nonneg (Z y ω - 1)])
      _ = _ := by
        rw [lintegral_add_left measurable_const]
        simp only [lintegral_const, measure_univ, mul_one, U]
  have hU2 (y z : X) :
      (∫⁻ ω, ENNReal.ofReal (Z y ω) * ENNReal.ofReal (Z z ω) ∂P) ≤ U y + U z := by
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Z y ω ^ 2) + ENNReal.ofReal (Z z ω ^ 2) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_mul (hZ0 y ω), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by
          nlinarith only [sq_nonneg (Z y ω - Z z ω), sq_nonneg (Z y ω), sq_nonneg (Z z ω)])
      _ = _ := lintegral_add_left ((hmZ y).pow_const 2).ennreal_ofReal _
  refine ⟨C, hCm, hmono, hcover, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [← Measure.bind_apply (hCm n) hξm.aemeasurable, hρ, withDensity_apply _ (hCm n)]
    refine lt_of_le_of_lt (b := ∫⁻ _ in C n, (1 : ℝ≥0∞) + n ∂Q)
      (lintegral_mono_ae ((ae_restrict_mem (hCm n)).mono fun y hy ↦
        (hU1 y).trans (add_le_add le_rfl (show U y ≤ (n : ℝ≥0∞) from hy.2)))) ?_
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.natCast_lt_top _⟩)
      (hvol n)
  · let e : (Fin 2 → X) ≃ᵐ X × X := MeasurableEquiv.finTwoArrow
    let A := e ⁻¹' (C n ×ˢ C n)
    have hAm : MeasurableSet A := e.measurable ((hCm n).prod (hCm n))
    rw [← bind_pi_two_map_apply_prod hPim (hCm n) (hCm n), hρ₂,
      Measure.map_apply e.measurable ((hCm n).prod (hCm n)), withDensity_apply _ hAm]
    have hfin : Measure.pi (fun _ : Fin 2 ↦ Q) A < ⊤ := by
      rw [← Measure.map_apply e.measurable ((hCm n).prod (hCm n)),
        (measurePreserving_finTwoArrow Q).map_eq, Measure.prod_prod]
      exact ENNReal.mul_lt_top (hvol n) (hvol n)
    refine lt_of_le_of_lt (b := ∫⁻ _ in A, (n : ℝ≥0∞) + n ∂Measure.pi (fun _ ↦ Q))
      (lintegral_mono_ae ((ae_restrict_mem hAm).mono fun z hz ↦
        (hU2 (z 0) (z 1)).trans (add_le_add hz.1.2 hz.2.2))) ?_
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top _,
      ENNReal.natCast_lt_top _⟩) hfin

end CountMoments

/-- SYNOPSIS item 85 (f): a Cox process with a jointly measurable nonnegative
square-integrable directing density
has intensity and second product densities given by the first and second moments of that
density. Its void probabilities use the extended nonnegative integral. -/
theorem moments_cox_density {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Ω → ℕ → Bool) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    {Z : EuclideanSpace ℝ (Fin d) → Ω → ℝ} (hZm : Measurable (Function.uncurry Z))
    (hZ0 : ∀ y ω, 0 ≤ Z y ω) (hZ2 : ∀ y, MemLp (Z y) 2 P)
    (hcox : IsCoxProcess P (fun ω ↦ pointSum (I ω) (x ω))
      fun ω ↦ volume.withDensity fun y ↦ ENNReal.ofReal (Z y ω)) :
    P.bind (fun ω ↦ pointSum (I ω) (x ω)) =
        volume.withDensity (fun y ↦ ENNReal.ofReal (∫ ω, Z y ω ∂P)) ∧
      P.bind (fun ω ↦ factorialPointSum 2 (I ω) (x ω)) =
        volume.withDensity (fun z ↦ ENNReal.ofReal (∫ ω, Z (z 0) ω * Z (z 1) ω ∂P)) ∧
      ∀ B, MeasurableSet B → P {ω | pointSum (I ω) (x ω) B = 0} =
        ∫⁻ ω, (ENNReal.expNeg (∫⁻ y in B, ENNReal.ofReal (Z y ω)) : ℝ≥0∞) ∂P := by
  let Y := EuclideanSpace ℝ (Fin d)
  let μ : Measure Y := volume
  let ξ (ω : Ω) := μ.withDensity (fun y ↦ ENNReal.ofReal (Z y ω))
  let Q₂ : Measure (Fin 2 → Y) := Measure.pi (fun _ ↦ μ)
  let H₂ (ω : Ω) (z : Fin 2 → Y) :=
    ENNReal.ofReal (Z (z 0) ω) * ENNReal.ofReal (Z (z 1) ω)
  have hZm₁ : Measurable (Function.uncurry (fun ω y ↦ ENNReal.ofReal (Z y ω))) :=
    hZm.ennreal_ofReal.comp measurable_swap
  have hpair (i : Fin 2) : Measurable (fun p : Ω × (Fin 2 → Y) ↦ (p.2 i, p.1)) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst
  have hZm₂ : Measurable (Function.uncurry H₂) :=
    (hZm.ennreal_ofReal.comp (hpair 0)).mul (hZm.ennreal_ofReal.comp (hpair 1))
  have hPi (ω : Ω) : Measure.pi (fun _ : Fin 2 ↦ ξ ω) = Q₂.withDensity (H₂ ω) := by
    have hZω : Measurable (fun y : Y ↦ ENNReal.ofReal (Z y ω)) :=
      (hZm.comp measurable_prodMk_right).ennreal_ofReal
    simpa only [ξ, Q₂, H₂, Fin.prod_univ_two] using
      TauCeti.pi_withDensity (fun _ : Fin 2 ↦ μ) (fun _ ↦ hZω)
  have hPim : Measurable (fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)) := by
    simp_rw [hPi]
    exact measurable_withDensity hZm₂
  have hρ : P.bind ξ = μ.withDensity (fun y ↦ ∫⁻ ω, ENNReal.ofReal (Z y ω) ∂P) :=
    Measure.bind_withDensity P μ hZm₁
  have hρ₂ : (P.bind fun ω ↦ Measure.pi (fun _ : Fin 2 ↦ ξ ω)) =
      Q₂.withDensity (fun z ↦ ∫⁻ ω, H₂ ω z ∂P) := by
    simp_rw [hPi]
    exact Measure.bind_withDensity P Q₂ hZm₂
  obtain ⟨C, hC, hmono, hcover, hfinite⟩ :=
    exists_cox_moment_cover hZm hZ0 hZ2 hcox.2.1 hPim hρ hρ₂
  have hfin (n : ℕ) : ∀ᵐ ω ∂P, ξ ω (C n) < ⊤ :=
    ae_lt_top ((Measure.measurable_coe (hC n)).comp hcox.2.1) (hfinite n).1.ne
  refine ⟨?_, ?_, fun B hB ↦ ?_⟩
  · rw [hcox.bind_eq_of_cover hC hcover hfin, hρ]
    congr 1
    ext y
    rw [ofReal_integral_eq_lintegral_ofReal ((hZ2 y).integrable (by norm_num))
      (ae_of_all _ (hZ0 y))]
  · rw [bind_factorialPointSum_two_cox_of_cover I x hcox hPim hC hmono hcover hfin
      (fun n ↦ (hfinite n).2), hρ₂]
    congr 1
    ext z
    have hprod : Integrable (fun ω ↦ Z (z 0) ω * Z (z 1) ω) P :=
      (hZ2 (z 0)).integrable_mul (hZ2 (z 1))
    rw [ofReal_integral_eq_lintegral_ofReal hprod
      (ae_of_all _ fun ω ↦ mul_nonneg (hZ0 _ _) (hZ0 _ _))]
    exact lintegral_congr fun ω ↦ (ENNReal.ofReal_mul (hZ0 _ ω)).symm
  · rw [hcox.measure_eq_zero_apply hB]
    exact lintegral_congr fun ω ↦ by rw [withDensity_apply _ hB]


/-! ### Log-Gaussian Cox processes (SYNOPSIS item 86) -/

/-- SYNOPSIS item 86: for a Gaussian field `Y` on `ℝ^d` with mean `m` and covariance `c` and
`e^Y` almost surely locally integrable, the Cox process directed by `e^{Y(x)} dx` has product
densities `ρ^{(n)}(x_1, …, x_n) = exp(∑_i m(x_i) + ½ ∑_{i,j} c(x_i, x_j))`; in particular
`ρ(x) = exp(m(x) + c(x, x)/2)` and `g(x, y) = exp(c(x, y))`. -/
theorem factorialMoment_logGaussianCox {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Ω → ℕ → Bool) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    {Y : EuclideanSpace ℝ (Fin d) → Ω → ℝ} (hYm : Measurable (Function.uncurry Y))
    (hY : IsGaussianProcess Y P) {m : EuclideanSpace ℝ (Fin d) → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ} (hm : ∀ y, P[Y y] = m y)
    (hc : ∀ y z, cov[Y y, Y z; P] = c y z)
    (hloc : ∀ᵐ ω ∂P, LocallyIntegrable (fun y ↦ Real.exp (Y y ω)))
    (hcox : IsCoxProcess P (fun ω ↦ pointSum (I ω) (x ω))
      fun ω ↦ volume.withDensity fun y ↦ ENNReal.ofReal (Real.exp (Y y ω))) (n : ℕ) :
    P.bind (fun ω ↦ factorialPointSum n (I ω) (x ω)) =
      volume.withDensity fun z ↦ ENNReal.ofReal
        (Real.exp (∑ i, m (z i) + (1 / 2) * ∑ i, ∑ j, c (z i) (z j))) := by
  sorry

/-- SYNOPSIS item 86: when `Y` has almost surely continuous sample paths, the log-Gaussian Cox
process is stationary if and only if `Y` is, that is, its mean is constant and its covariance is
translation invariant. Without continuity the forward implication fails: changing `Y` at one
point leaves the directing measure, hence the law of `η`, unchanged. -/
theorem isStationary_logGaussianCox_iff {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} {Y : EuclideanSpace ℝ (Fin d) → Ω → ℝ}
    (hYm : Measurable (Function.uncurry Y)) (hY : IsGaussianProcess Y P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun y ↦ Y y ω)
    (hloc : ∀ᵐ ω ∂P, LocallyIntegrable (fun y ↦ Real.exp (Y y ω)))
    (hcox : IsCoxProcess P η fun ω ↦ volume.withDensity fun y ↦ ENNReal.ofReal (Real.exp (Y y ω))) :
    IsStationary P η ↔ (∀ y z, P[Y y] = P[Y z]) ∧ ∀ y z h, cov[Y (y + h), Y (z + h); P] =
      cov[Y y, Y z; P] := by
  sorry

/-- SYNOPSIS item 86: in the stationary case the map from the mean `μ`, variance `σ² > 0`, and
correlation `r` (with `r(0) = 1`) of `Y` to `ρ = e^{μ + σ²/2}` and `g(h) = e^{σ² r(h)}` is
injective. -/
theorem logGaussianCox_parameters_injective {d : ℕ} {μ μ' σsq σsq' : ℝ}
    {r r' : EuclideanSpace ℝ (Fin d) → ℝ} (hσ : 0 < σsq) (_hσ' : 0 < σsq') (hr : r 0 = 1)
    (hr' : r' 0 = 1) (hρ : Real.exp (μ + σsq / 2) = Real.exp (μ' + σsq' / 2))
    (hg : ∀ h, Real.exp (σsq * r h) = Real.exp (σsq' * r' h)) :
    μ = μ' ∧ σsq = σsq' ∧ r = r' := by
  have hvar : σsq = σsq' := by
    simpa only [hr, hr', mul_one] using Real.exp_injective (hg 0)
  refine ⟨?_, hvar, ?_⟩
  · exact add_right_cancel (hvar ▸ Real.exp_injective hρ)
  · funext h
    have hh := Real.exp_injective (hg h)
    rw [← hvar] at hh
    exact mul_left_cancel₀ hσ.ne' hh

end MSSS
