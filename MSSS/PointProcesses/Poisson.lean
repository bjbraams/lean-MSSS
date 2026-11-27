module

public import MSSS.PointProcesses.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

import TauCeti.Probability.PointProcess.Marking.Optional
import TauCeti.Probability.PointProcess.Poisson.Laplace
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization

/-!
# The Poisson process

SYNOPSIS items 75 and 78–81: the marking theorem, Rényi's theorem, the Mecke equation and its
multivariate form, and the Poincaré inequality. A Poisson process with intensity measure `Λ` is
`TauCeti.Probability.IsPoissonRandomMeasure P η Λ`: independent Poisson counts on disjoint sets,
with `Po(∞)` the point mass at `∞`.

## Main results

* `MSSS.isPoissonRandomMeasure_marking_of_map_eq_compProd`,
  `MSSS.isPoissonRandomMeasure_marking`: SYNOPSIS item 75.
* `MSSS.isPoissonRandomMeasure_of_void`, `MSSS.isPoissonRandomMeasure_iff_poisson_counts`:
  SYNOPSIS item 78.
* `MSSS.isPoissonRandomMeasure_iff_mecke`: SYNOPSIS item 79.
* `MSSS.mecke_multivariate`, `MSSS.factorialMoment_poisson`: SYNOPSIS item 80.
* `MSSS.poincare_poisson`, `MSSS.variance_count_poisson`: SYNOPSIS item 81.

The marking proof uses TauCeti’s optional tuple marking and Poisson Laplace characterization.
For the count variance we use the Poisson count law and its second moment from TauCeti.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability
open scoped ENNReal NNReal

namespace MSSS

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The conditional distribution of the masked marked configuration is given by independent
optional tuple marking. -/
private lemma map_masked_marks_eq_optionalTupleMarking {Y : Type*} [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (I : ℕ → Bool) (x : ℕ → X) :
    (Measure.infinitePi fun n ↦ K (x n)).map
      (fun ys ↦ pointSum I (fun n ↦ (x n, ys n))) =
      K.optionalTupleMarking ℕ (fun n ↦ if I n then some (x n) else none) := by
  classical
  let g (n : ℕ) (y : Y) : Measure (X × Y) := if I n then Measure.dirac (x n, y) else 0
  have hg (n : ℕ) : Measurable (g n) := by
    by_cases hn : I n
    · simpa only [g, ite_eq_left hn, Function.comp_def] using
        (Measure.measurable_dirac.comp (measurable_prodMk_left (x := x n)))
    · simpa only [g, ite_eq_right hn] using (measurable_const : Measurable (fun _ : Y ↦
        (0 : Measure (X × Y))))
  have hmap (n : ℕ) :
      (K (x n)).map (g n) = K.optionalMark (if I n then some (x n) else none) := by
    by_cases hn : I n
    · simp only [g, ite_eq_left hn, Kernel.optionalMark_some, Kernel.prod_apply, Kernel.id_apply,
        Measure.dirac_prod, Measure.map_map Measure.measurable_dirac measurable_prodMk_left,
        Function.comp_def]
    · simp only [g, ite_eq_right hn, Kernel.optionalMark_none, Measure.map_const, measure_univ,
        one_smul]
  simp_rw [Kernel.optionalTupleMarking_apply, ← hmap]
  have hgPi : Measurable (fun y : ℕ → Y ↦ fun n ↦ g n (y n)) :=
    Measurable.of_eval fun n ↦ (hg n).comp (measurable_pi_apply n)
  rw [← Measure.infinitePi_map_pi _ hg,
    Measure.map_map TauCeti.MeasureTheory.measurable_measure_sum hgPi]
  simp only [pointSum_def, Function.comp_def, g]

/-- Conditional integration of the marked Laplace test over the given ground enumeration. -/
private lemma lintegral_marked_laplace {Y : Type*} [MeasurableSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] (κ : Ω → ℕ∞) (Xs : Ω → ℕ → X) (Ys : Ω → ℕ → Y)
    (hm : Measurable fun ω ↦ (κ ω, Xs ω)) (hYm : Measurable Ys)
    (Lk : Kernel (ℕ∞ × (ℕ → X)) (ℕ → Y)) [IsSFiniteKernel Lk]
    (hjoint : P.map (fun ω ↦ ((κ ω, Xs ω), Ys ω)) =
      (P.map fun ω ↦ (κ ω, Xs ω)) ⊗ₘ Lk)
    (hmark : ∀ᵐ ω ∂P, Lk (κ ω, Xs ω) = Measure.infinitePi fun n ↦ K (Xs ω n))
    {f : X × Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, (ENNReal.expNeg
      (∫⁻ z, f z ∂pointSum (finiteMask (κ ω)) (fun n ↦ (Xs ω n, Ys ω n))) : ℝ≥0∞) ∂P) =
      ∫⁻ ω, ∏' n, if finiteMask (κ ω) n
        then ∫⁻ y, (ENNReal.expNeg (f (Xs ω n, y)) : ℝ≥0∞) ∂K (Xs ω n)
        else 1 ∂P := by
  let E := ℕ∞ × (ℕ → X)
  let G : Ω → E := fun ω ↦ (κ ω, Xs ω)
  let m : E × (ℕ → Y) → Measure (X × Y) :=
    fun a ↦ pointSum (finiteMask a.1.1) (fun n ↦ (a.1.2 n, a.2 n))
  have hm' : Measurable m :=
    measurable_pointSum (measurable_finiteMask.comp (measurable_fst.comp measurable_fst))
      (Measurable.of_eval fun n ↦
        (((measurable_pi_apply n).comp measurable_snd).comp measurable_fst).prodMk
          ((measurable_pi_apply n).comp measurable_snd))
  let L : Measure (X × Y) → ℝ≥0∞ := fun μ ↦
    (ENNReal.expNeg (∫⁻ z, f z ∂μ) : ℝ≥0∞)
  have hL : Measurable L := measurable_coe_nnreal_ennreal.comp
    (ENNReal.measurable_expNeg.comp (Measure.measurable_lintegral hf))
  have hLm : Measurable (L ∘ m) := hL.comp hm'
  have hG : Measurable G := hm
  calc
    _ = ∫⁻ a, (L ∘ m) a ∂(P.map fun ω ↦ (G ω, Ys ω)) :=
      (lintegral_map hLm (hG.prodMk hYm)).symm
    _ = ∫⁻ a, ∫⁻ y, (L ∘ m) (a, y) ∂Lk a ∂P.map G := by
      rw [hjoint, Measure.lintegral_compProd hLm]
    _ = ∫⁻ ω, ∫⁻ y, (L ∘ m) (G ω, y) ∂Lk (G ω) ∂P :=
      lintegral_map (hLm.lintegral_kernel_prod_right' (κ := Lk)) hG
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hmark] with ω hω
      have hmark' : Lk (G ω) = Measure.infinitePi (fun n ↦ K (Xs ω n)) := hω
      rw [hmark']
      have hpts : Measurable (fun y : ℕ → Y ↦
          pointSum (finiteMask (κ ω)) (fun n ↦ (Xs ω n, y n))) :=
        measurable_pointSum measurable_const (Measurable.of_eval fun n ↦
          measurable_const.prodMk (measurable_pi_apply n))
      dsimp only [Function.comp_apply, m, G]
      rw [← lintegral_map hL hpts,
        map_masked_marks_eq_optionalTupleMarking,
        Kernel.lintegral_expNeg_optionalTupleMarking _ _ hf]
      apply tprod_congr
      intro n
      by_cases hn : finiteMask (κ ω) n
      · simp only [ite_eq_left hn, Option.elim_some]
      · simp only [ite_eq_right hn, Option.elim_none]

/-- A measurable test on the marked space gives a ground-space Laplace test by averaging its
exponential under the mark kernel. -/
private lemma exists_expNeg_eq_markTransform {Y : Type*} [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] {f : X × Y → ℝ≥0∞} (hf : Measurable f) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧ ∀ x,
      (ENNReal.expNeg (g x) : ℝ≥0∞) = ∫⁻ y, (ENNReal.expNeg (f (x, y)) : ℝ≥0∞) ∂K x := by
  let T : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, (ENNReal.expNeg (f (x, y)) : ℝ≥0∞) ∂K x
  have hTm : Measurable T := (measurable_coe_nnreal_ennreal.comp
    (ENNReal.measurable_expNeg.comp hf)).lintegral_kernel_prod_right' (κ := K)
  have hT (x : X) : T x ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ : Y, (1 : ℝ≥0∞) ∂K x :=
        lintegral_mono fun _ ↦ ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
      _ = _ := by simp
  refine ⟨fun x ↦ (-ENNReal.log (T x)).toENNReal,
    EReal.continuous_toENNReal.measurable.comp hTm.ennreal_log.neg, fun x ↦ ?_⟩
  rw [ENNReal.coe_expNeg,
    EReal.coe_toENNReal (EReal.neg_nonneg.mpr (ENNReal.log_le_zero_iff.mpr (hT x))),
    neg_neg, ENNReal.exp_log]

/-- Independent kernel marking from the joint law of the enumeration and the marks. -/
theorem isPoissonRandomMeasure_marking_of_map_eq_compProd {Y : Type*} [MeasurableSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Measure X} [SFinite Λ]
    (K : ProbabilityTheory.Kernel X Y) [IsMarkovKernel K] (κ : Ω → ℕ∞) (Xs : Ω → ℕ → X)
    (Ys : Ω → ℕ → Y) (hm : Measurable fun ω ↦ (κ ω, Xs ω)) (hYm : Measurable Ys)
    (hη : IsPoissonRandomMeasure P (fun ω ↦ pointSum (finiteMask (κ ω)) (Xs ω)) Λ)
    (Lk : Kernel (ℕ∞ × (ℕ → X)) (ℕ → Y)) [IsSFiniteKernel Lk]
    (hjoint : P.map (fun ω ↦ ((κ ω, Xs ω), Ys ω)) =
      (P.map fun ω ↦ (κ ω, Xs ω)) ⊗ₘ Lk)
    (hmark : ∀ᵐ ω ∂P, Lk (κ ω, Xs ω) = Measure.infinitePi fun n ↦ K (Xs ω n)) :
    IsPoissonRandomMeasure P
      (fun ω ↦ pointSum (finiteMask (κ ω)) fun n ↦ (Xs ω n, Ys ω n)) (Λ ⊗ₘ K) := by
  have hI : Measurable (fun ω ↦ finiteMask (κ ω)) :=
    measurable_finiteMask.comp (measurable_fst.comp hm)
  have hN : Measurable (fun ω ↦ pointSum (finiteMask (κ ω))
      (fun n ↦ (Xs ω n, Ys ω n))) :=
    measurable_pointSum hI (Measurable.of_eval fun n ↦
      ((measurable_pi_apply n).comp (measurable_snd.comp hm)).prodMk
        ((measurable_pi_apply n).comp hYm))
  refine isPoissonRandomMeasure_of_laplaceFunctional hN (fun f hf ↦ ?_)
  obtain ⟨g, hgm, hg⟩ := exists_expNeg_eq_markTransform K hf
  rw [Measure.laplaceFunctional_def]
  calc
    _ = ∫⁻ ω, ∏' n, if finiteMask (κ ω) n then
          ∫⁻ y, (ENNReal.expNeg (f (Xs ω n, y)) : ℝ≥0∞) ∂K (Xs ω n) else 1 ∂P :=
      lintegral_marked_laplace K κ Xs Ys hm hYm Lk hjoint hmark hf
    _ = P.laplaceFunctional (fun ω ↦ pointSum (finiteMask (κ ω)) (Xs ω)) g := by
      rw [Measure.laplaceFunctional_def]
      apply lintegral_congr
      intro ω
      rw [pointSum_def, lintegral_sum_measure, ENNReal.coe_expNeg_tsum]
      apply tprod_congr
      intro n
      by_cases hn : finiteMask (κ ω) n
      · rw [ite_eq_left hn, ite_eq_left hn, lintegral_dirac' _ hgm, hg]
      · simp only [ite_eq_right hn, lintegral_zero_measure, ENNReal.expNeg_zero, ENNReal.coe_one]
    _ = (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (g x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) :=
      hη.laplaceFunctional_eq_expNeg hgm
    _ = _ := by
      let F : X × Y → ℝ≥0∞ := fun z ↦ (ENNReal.expNeg (f z) : ℝ≥0∞)
      have hF : Measurable F := measurable_coe_nnreal_ennreal.comp
        (ENNReal.measurable_expNeg.comp hf)
      have hF1 (z : X × Y) : F z ≤ 1 :=
        ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
      -- Use the named mark transform to state the inner integral.
      change _ = (ENNReal.expNeg (∫⁻ z, 1 - F z ∂Λ ⊗ₘ K) : ℝ≥0∞)
      have hFsub : Measurable (fun z ↦ (1 : ℝ≥0∞) - F z) := measurable_const.sub hF
      rw [Measure.lintegral_compProd hFsub]
      congr 2
      apply lintegral_congr
      intro x
      have hle : (fun y ↦ F (x, y)) ≤ᵐ[K x] fun _ ↦ 1 :=
        ae_of_all _ fun y ↦ hF1 (x, y)
      have hfin : (∫⁻ y, F (x, y) ∂K x) ≠ ∞ :=
        (calc
          _ ≤ ∫⁻ _ : Y, (1 : ℝ≥0∞) ∂K x := lintegral_mono fun y ↦ hF1 (x, y)
          _ = 1 := by simp).trans_lt ENNReal.one_lt_top |>.ne
      have hxmeas : Measurable (fun y ↦ F (x, y)) := hF.comp measurable_prodMk_left
      rw [lintegral_sub hxmeas hfin hle, hg]
      simp only [lintegral_const, measure_univ, mul_one, F]

/-- SYNOPSIS item 75, marking theorem: let `η = ∑_{n < κ} δ_{X_n}` be a Poisson process with
s-finite intensity `Λ` and let the marks `Y_n` be, given `(κ, X)`, independent with laws
`K(X_n, ·)`. Then `∑_{n < κ} δ_{(X_n, Y_n)}` is a Poisson process on `𝕏 × 𝕐` with intensity
`Λ ⊗ K`. -/
theorem isPoissonRandomMeasure_marking {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y]
    [Nonempty Y] {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Measure X} [SFinite Λ]
    (K : ProbabilityTheory.Kernel X Y) [IsMarkovKernel K] (κ : Ω → ℕ∞) (Xs : Ω → ℕ → X)
    (Ys : Ω → ℕ → Y) (hm : Measurable fun ω ↦ (κ ω, Xs ω)) (hYm : Measurable Ys)
    (hη : IsPoissonRandomMeasure P (fun ω ↦ pointSum (finiteMask (κ ω)) (Xs ω)) Λ)
    (hmark : ∀ᵐ ω ∂P, condDistrib Ys (fun ω ↦ (κ ω, Xs ω)) P (κ ω, Xs ω) =
      Measure.infinitePi fun n ↦ K (Xs ω n)) :
    IsPoissonRandomMeasure P
      (fun ω ↦ pointSum (finiteMask (κ ω)) fun n ↦ (Xs ω n, Ys ω n)) (Λ ⊗ₘ K) := by
  exact isPoissonRandomMeasure_marking_of_map_eq_compProd K κ Xs Ys hm hYm hη
    (condDistrib Ys (fun ω ↦ (κ ω, Xs ω)) P)
    (compProd_map_condDistrib hm.aemeasurable hYm.aemeasurable).symm hmark

/-- The zero-count probability of a Poisson variable embedded in the extended nonnegative reals. -/
lemma measureReal_count_eq_zero_of_hasLaw_poisson {P : Measure Ω} {N : Ω → ℝ≥0∞}
    {rate : ℝ≥0} (h : HasLaw N ((poissonMeasure rate).map (Nat.cast : ℕ → ℝ≥0∞)) P) :
    P.real {ω | N ω = 0} = Real.exp (-(rate : ℝ)) := by
  have hpre : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' {0} = ({0} : Set ℕ) := by
    ext i
    simp
  have hN : {ω | N ω = 0} = N ⁻¹' {0} := rfl
  rw [hN, measureReal_def, ← Measure.map_apply_of_aemeasurable h.aemeasurable
    (measurableSet_singleton 0), h.map_eq, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton 0), hpre, ← measureReal_def, poissonMeasure_real_singleton]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]

/-- SYNOPSIS item 78, Rényi's theorem: on a Borel space, a simple point process with void
probabilities `P(η(B) = 0) = e^{-Λ(B)}` for a diffuse s-finite `Λ` (with `e^{-∞} = 0`) is a
Poisson process with intensity `Λ`. -/
theorem isPoissonRandomMeasure_of_void [StandardBorelSpace X] {P : Measure Ω}
    [IsProbabilityMeasure P] {Λ : Measure X} [SFinite Λ] [NoAtoms Λ] {η : Ω → Measure X}
    (hηm : Measurable η) (hint : ∀ ω, (η ω).IsIntegerValued) (hsf : ∀ ω, SFinite (η ω))
    (hsimple : ∀ᵐ ω ∂P, ∀ x, η ω {x} ≤ 1)
    (hvoid : ∀ B, MeasurableSet B →
      P {ω | η ω B = 0} = if Λ B = ∞ then 0 else ENNReal.ofReal (Real.exp (-(Λ B).toReal))) :
    IsPoissonRandomMeasure P η Λ := by
  sorry

/-- SYNOPSIS item 78 on a localized Borel space: a random measure on a proper metric space, almost
surely locally finite and without fixed atoms, is a Poisson process (with its intensity measure)
if and only if `ξ(U)` is Poisson distributed for every `U` in a ring of bounded Borel sets that
generates the Borel σ-algebra. -/
theorem isPoissonRandomMeasure_iff_poisson_counts [MetricSpace X] [ProperSpace X] [BorelSpace X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure X} (hξm : Measurable ξ)
    (hlf : ∀ ω, IsLocallyFiniteMeasure (ξ ω)) (hatoms : ∀ x, P {ω | 0 < ξ ω {x}} = 0)
    {R : Set (Set X)} (hR : IsSetRing R) (hRb : ∀ U ∈ R, Bornology.IsBounded U ∧ MeasurableSet U)
    (hgen : MeasurableSpace.generateFrom R = ‹MeasurableSpace X›) :
    IsPoissonRandomMeasure P ξ (P.bind ξ) ↔ ∀ U ∈ R, ∃ c : ℝ≥0,
      HasLaw (fun ω ↦ ξ ω U) ((poissonMeasure c).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  sorry

/-- SYNOPSIS item 79, Mecke equation: a point process `η` is a Poisson process with s-finite
intensity `Λ` if and only if `E ∫ f(x, η) η(dx) = ∫ E f(x, η + δ_x) Λ(dx)` for every measurable
`f ≥ 0`. -/
theorem isPoissonRandomMeasure_iff_mecke {P : Measure Ω} [IsProbabilityMeasure P]
    {Λ : Measure X} [SFinite Λ] {η : Ω → Measure X} (hηm : Measurable η)
    (hint : ∀ ω, (η ω).IsIntegerValued) (hsf : ∀ ω, SFinite (η ω)) :
    IsPoissonRandomMeasure P η Λ ↔ ∀ f : X → Measure X → ℝ≥0∞, Measurable (Function.uncurry f) →
      ∫⁻ ω, ∫⁻ x, f x (η ω) ∂(η ω) ∂P = ∫⁻ x, ∫⁻ ω, f x (η ω + Measure.dirac x) ∂P ∂Λ := by
  sorry

/-- SYNOPSIS item 80, multivariate Mecke equation: for a Poisson process
`η = ∑_{n : I n} δ_{x_n}` with σ-finite intensity `Λ` and `m ≥ 1`,
`E ∫ f(x, η) η^{(m)}(dx) = ∫ E f(x, η + δ_{x_1} + ⋯ + δ_{x_m}) Λ^m(dx)`. -/
theorem mecke_multivariate {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Measure X}
    [SigmaFinite Λ] (I : Ω → ℕ → Bool) (x : Ω → ℕ → X)
    (hη : IsPoissonRandomMeasure P (fun ω ↦ pointSum (I ω) (x ω)) Λ) {m : ℕ} (hm : 1 ≤ m)
    (f : (Fin m → X) → Measure X → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ ω, ∫⁻ y, f y (pointSum (I ω) (x ω)) ∂(factorialPointSum m (I ω) (x ω)) ∂P =
      ∫⁻ y, ∫⁻ ω, f y (pointSum (I ω) (x ω) + ∑ i, Measure.dirac (y i)) ∂P
        ∂(Measure.pi fun _ ↦ Λ) := by
  sorry

/-- SYNOPSIS item 80: the factorial moment measures of a Poisson process are `α_m = Λ^m`. -/
theorem factorialMoment_poisson {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Measure X}
    [SigmaFinite Λ] (I : Ω → ℕ → Bool) (x : Ω → ℕ → X)
    (hη : IsPoissonRandomMeasure P (fun ω ↦ pointSum (I ω) (x ω)) Λ) (m : ℕ) :
    P.bind (fun ω ↦ factorialPointSum m (I ω) (x ω)) = Measure.pi fun _ ↦ Λ := by
  sorry

/-- SYNOPSIS item 81, Poincaré inequality: for a Poisson process with σ-finite intensity and
`E f(η)² < ∞`, `Var f(η) ≤ ∫ E (D_x f(η))² Λ(dx)` with `D_x f(μ) = f(μ + δ_x) - f(μ)`. -/
theorem poincare_poisson {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Measure X}
    [SigmaFinite Λ] {η : Ω → Measure X} (hη : IsPoissonRandomMeasure P η Λ)
    {f : Measure X → ℝ} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (η ω)) 2 P) :
    ENNReal.ofReal Var[fun ω ↦ f (η ω); P] ≤
      ∫⁻ x, ∫⁻ ω, ENNReal.ofReal ((f (η ω + Measure.dirac x) - f (η ω)) ^ 2) ∂P ∂Λ := by
  sorry

/-- SYNOPSIS item 81: equality holds for `f(μ) = μ(B)` with `Λ(B) < ∞`, where
`Var η(B) = Λ(B)`. -/
theorem variance_count_poisson {P : Measure Ω} [IsProbabilityMeasure P] {Λ : Measure X}
    [SigmaFinite Λ] {η : Ω → Measure X} (hη : IsPoissonRandomMeasure P η Λ) {B : Set X}
    (hB : MeasurableSet B) (hΛB : Λ B < ∞) :
    Var[fun ω ↦ (η ω B).toReal; P] = (Λ B).toReal ∧
      ENNReal.ofReal Var[fun ω ↦ (η ω B).toReal; P] =
        ∫⁻ x, ∫⁻ ω, ENNReal.ofReal ((((η ω + Measure.dirac x) B).toReal - (η ω B).toReal) ^ 2)
          ∂P ∂Λ := by
  have hcount := hη.hasLaw hB hΛB
  have hlaw : HasLaw (fun ω ↦ (η ω B).toReal)
      ((poissonMeasure (Λ B).toNNReal).map (Nat.cast : ℕ → ℝ)) P := by
    refine ⟨ENNReal.measurable_toReal.comp_aemeasurable hcount.aemeasurable, ?_⟩
    calc
      _ = ((P.map (fun ω ↦ η ω B)).map ENNReal.toReal) :=
        (Measure.map_map ENNReal.measurable_toReal ((Measure.measurable_coe hB).comp
          hη.measurable)).symm
      _ = _ := by
        rw [hcount.map_eq, Measure.map_map ENNReal.measurable_toReal (by fun_prop)]
        simp only [Function.comp_def, ENNReal.toReal_natCast]
  have hv : Var[fun ω ↦ (η ω B).toReal; P] = (Λ B).toReal :=
    variance_of_hasLaw_map_cast_poissonMeasure hlaw
  refine ⟨hv, ?_⟩
  rw [hv, ENNReal.ofReal_toReal hΛB.ne]
  have hinner (x : X) :
      (∫⁻ ω, ENNReal.ofReal ((((η ω + Measure.dirac x) B).toReal -
        (η ω B).toReal) ^ 2) ∂P) = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    calc
      _ = ∫⁻ _ : Ω, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hη.ae_lt_top hB hΛB] with ω hω
        by_cases hx : x ∈ B
        · simp [Measure.dirac_apply' _ hB, hx,
            ENNReal.toReal_add hω.ne ENNReal.one_ne_top]
        · simp [Measure.dirac_apply' _ hB, hx]
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  simp only [hinner, lintegral_indicator_const hB, one_mul]

end MSSS
