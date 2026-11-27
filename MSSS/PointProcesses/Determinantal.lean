module

public import MSSS.PointProcesses.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Determinantal point processes

SYNOPSIS items 88–90. On a locally compact Polish space `Λ` with a σ-finite Radon measure `μ`, a
simple point process `∑_{n : I n} δ_{x_n}` is determinantal with kernel `K` when its factorial
moment measures have densities `det(K(x_i, x_j))_{i,j ≤ k}` with respect to `μ^k`.

The integral operator of `K` is described through quadratic forms on bounded measurable
functions `f` with compact support: it is Hermitian when `K(y, x) = conj K(x, y)`, nonnegative when
`∫∫ conj f(x) K(x, y) f(y) ≥ 0`, contractive when that form is at most `∫ |f|²`, and locally of
trace class when `∫_D K(x, x) dμ < ∞` for compact `D`. In item 89 the condition that `K` agrees on
the diagonal with the version given by the spectral expansion is replaced by continuity of `K`,
which implies it.

## Main definitions

* `MSSS.IsDeterminantal P I x K μ`, `MSSS.determinantalLaw K μ`.
* `MSSS.IsAdmissibleKernel K μ`: local square integrability, Hermitian symmetry, nonnegativity,
  and local trace class.
* `MSSS.kernelForm K μ f`: the quadratic form `∫∫ conj f(x) K(x, y) f(y) μ(dx) μ(dy)`.

## Main results

* `MSSS.map_eq_determinantalLaw`, `MSSS.exponential_tail_determinantal`,
  `MSSS.intensity_determinantal`, `MSSS.pairCorrelation_determinantal`,
  `MSSS.isDeterminantal_thinning`: SYNOPSIS item 88.
* `MSSS.exists_determinantal_iff`: SYNOPSIS item 89.
* `MSSS.determinantal_mixture`, `MSSS.count_determinantal`: SYNOPSIS item 90.

The first factorial moment uses Mathlib's measure-preserving equivalence for products over a
singleton index type. The thinning formula uses Mathlib's projection law for independent
products, measurable minorants representing density measures, and multiplicativity of the
determinant.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set ComplexConjugate
open scoped ENNReal

namespace MSSS

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The point process `∑_{n : I n} δ_{x_n}` is **determinantal** with kernel `K` with respect to
`μ`: it is almost surely simple and `α_k = det(K(x_i, x_j)) μ^k` for every `k ≥ 1`. -/
def IsDeterminantal (P : Measure Ω) (I : Ω → ℕ → Bool) (x : Ω → ℕ → X) (K : X → X → ℂ)
    (μ : Measure X) [SigmaFinite μ] : Prop :=
  (∀ᵐ ω ∂P, ∀ n m, I ω n → I ω m → x ω n = x ω m → n = m) ∧
    ∀ k, 1 ≤ k → P.bind (fun ω ↦ factorialPointSum k (I ω) (x ω)) =
      (Measure.pi fun _ : Fin k ↦ μ).withDensity fun z ↦
        ENNReal.ofReal (Matrix.det (Matrix.of fun i j ↦ K (z i) (z j))).re

lemma isDeterminantal_def {P : Measure Ω} {I : Ω → ℕ → Bool} {x : Ω → ℕ → X} {K : X → X → ℂ}
    {μ : Measure X} [SigmaFinite μ] : IsDeterminantal P I x K μ ↔
      (∀ᵐ ω ∂P, ∀ n m, I ω n → I ω m → x ω n = x ω m → n = m) ∧
      ∀ k, 1 ≤ k → P.bind (fun ω ↦ factorialPointSum k (I ω) (x ω)) =
        (Measure.pi fun _ : Fin k ↦ μ).withDensity fun z ↦
          ENNReal.ofReal (Matrix.det (Matrix.of fun i j ↦ K (z i) (z j))).re := Iff.rfl

open Classical in
/-- The law of the determinantal point process with kernel `K`, if one exists (it is then
unique, `MSSS.map_eq_determinantalLaw`); otherwise `0`. -/
def determinantalLaw (K : X → X → ℂ) (μ : Measure X) [SigmaFinite μ] : Measure (Measure X) :=
  if h : ∃ Q : Measure ((ℕ → Bool) × (ℕ → X)), IsProbabilityMeasure Q ∧
      IsDeterminantal Q Prod.fst Prod.snd K μ then
    (Classical.choose h).map fun z ↦ pointSum z.1 z.2
  else 0

/-- The quadratic form `∫∫ conj f(x) K(x, y) f(y) μ(dx) μ(dy)` of the integral operator. -/
def kernelForm (K : X → X → ℂ) (μ : Measure X) (f : X → ℂ) : ℂ :=
  ∫ y, ∫ z, conj (f y) * K y z * f z ∂μ ∂μ

/-- `K` is an **admissible kernel**: locally square integrable, Hermitian, nonnegative, and
locally of trace class. -/
def IsAdmissibleKernel [TopologicalSpace X] (K : X → X → ℂ) (μ : Measure X) : Prop :=
  (∀ D : Set X, IsCompact D → ∫⁻ z in D ×ˢ D, ‖K z.1 z.2‖ₑ ^ 2 ∂μ.prod μ < ∞) ∧
    (∀ y z, K z y = conj (K y z)) ∧
    (∀ f : X → ℂ, Measurable f → (∃ C, ∀ y, ‖f y‖ ≤ C) → HasCompactSupport f →
      0 ≤ (kernelForm K μ f).re) ∧
    ∀ D : Set X, IsCompact D → ∫⁻ y in D, ‖K y y‖ₑ ∂μ < ∞

lemma kernelForm_def (K : X → X → ℂ) (μ : Measure X) (f : X → ℂ) :
    kernelForm K μ f = ∫ y, ∫ z, conj (f y) * K y z * f z ∂μ ∂μ := by
  rw [kernelForm]

lemma isAdmissibleKernel_def [TopologicalSpace X] {K : X → X → ℂ} {μ : Measure X} :
    IsAdmissibleKernel K μ ↔
      (∀ D : Set X, IsCompact D → ∫⁻ z in D ×ˢ D, ‖K z.1 z.2‖ₑ ^ 2 ∂μ.prod μ < ∞) ∧
      (∀ y z, K z y = conj (K y z)) ∧
      (∀ f : X → ℂ, Measurable f → (∃ C, ∀ y, ‖f y‖ ≤ C) → HasCompactSupport f →
        0 ≤ (kernelForm K μ f).re) ∧
      ∀ D : Set X, IsCompact D → ∫⁻ y in D, ‖K y y‖ₑ ∂μ < ∞ := Iff.rfl

/-! ### Basic properties (SYNOPSIS item 88) -/

/-- Evaluation at the sole coordinate sends the first factorial counting measure to the
ordinary counting measure. -/
theorem map_eval_factorialPointSum_one (I : ℕ → Bool) (x : ℕ → X) :
    (factorialPointSum 1 I x).map (fun z ↦ z 0) = pointSum I x := by
  let e : {n : Fin 1 → ℕ // Function.Injective n} ≃ ℕ :=
    { toFun := fun n ↦ n.1 0
      invFun := fun k ↦ ⟨fun _ ↦ k, fun _ _ _ ↦ Subsingleton.elim _ _⟩
      left_inv := fun n ↦ Subtype.ext (funext fun i ↦ congrArg n.1 (Subsingleton.elim 0 i))
      right_inv := fun _ ↦ rfl }
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply 0) hs, factorialPointSum_def, pointSum_def,
    Measure.sum_apply _ ((measurable_pi_apply 0) hs), Measure.sum_apply _ hs, ← e.tsum_eq]
  apply tsum_congr
  intro n
  have hmask : (∀ i, I (n.1 i)) ↔ I (e n) :=
    ⟨fun h ↦ h 0, fun h i ↦ (congrArg n.1 (Subsingleton.elim 0 i)) ▸ h⟩
  rw [if_congr hmask rfl rfl]
  split_ifs
  · rw [Measure.dirac_apply' _ ((measurable_pi_apply 0) hs), Measure.dirac_apply' _ hs]
    rfl
  · rfl

variable [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X]

/-- SYNOPSIS item 88: for an admissible kernel there is at most one determinantal point process:
every one has the law `MSSS.determinantalLaw K μ`. -/
theorem map_eq_determinantalLaw {P : Measure Ω} [IsProbabilityMeasure P] {I : Ω → ℕ → Bool}
    {x : Ω → ℕ → X} {K : X → X → ℂ} {μ : Measure X} [SigmaFinite μ] [IsLocallyFiniteMeasure μ]
    (hK : IsAdmissibleKernel K μ) (hm : Measurable fun ω ↦ (I ω, x ω))
    (h : IsDeterminantal P I x K μ) :
    P.map (fun ω ↦ pointSum (I ω) (x ω)) = determinantalLaw K μ := by
  sorry

/-- SYNOPSIS item 88: the counts of a determinantal process on compact sets have exponential
tails. -/
theorem exponential_tail_determinantal {P : Measure Ω} [IsProbabilityMeasure P]
    {I : Ω → ℕ → Bool} {x : Ω → ℕ → X} {K : X → X → ℂ} {μ : Measure X} [SigmaFinite μ]
    [IsLocallyFiniteMeasure μ] (hK : IsAdmissibleKernel K μ) (h : IsDeterminantal P I x K μ)
    {D : Set X} (hD : IsCompact D) :
    ∃ c > 0, ∫⁻ ω, ENNReal.ofReal (Real.exp (c * (pointSum (I ω) (x ω) D).toReal)) ∂P < ∞ ∧
      ∀ᵐ ω ∂P, pointSum (I ω) (x ω) D < ∞ := by
  sorry

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
/-- SYNOPSIS item 88: the intensity of a determinantal process with an a.e. measurable first
factorial counting measure has density `Re K(x, x)`, truncated at zero. -/
theorem intensity_determinantal {P : Measure Ω} [IsProbabilityMeasure P] {I : Ω → ℕ → Bool}
    {x : Ω → ℕ → X} {K : X → X → ℂ} {μ : Measure X} [SigmaFinite μ]
    (h : IsDeterminantal P I x K μ)
    (hm : AEMeasurable (fun ω ↦ factorialPointSum 1 (I ω) (x ω)) P) :
    P.bind (fun ω ↦ pointSum (I ω) (x ω)) = μ.withDensity fun y ↦ ENNReal.ofReal (K y y).re := by
  let e := MeasurableEquiv.funUnique (Fin 1) X
  have hpoint (ω : Ω) : (factorialPointSum 1 (I ω) (x ω)).map e = pointSum (I ω) (x ω) :=
    map_eval_factorialPointSum_one (I ω) (x ω)
  have hmap := Measure.map_bind (g := e) hm e.measurable.aemeasurable
  have hfirst := (isDeterminantal_def.mp h).2 1 le_rfl
  simp only [Matrix.det_fin_one, Matrix.of_apply] at hfirst
  have heval (z : Fin 1 → X) : e z = z 0 := rfl
  simp only [hpoint, hfirst] at hmap
  refine hmap.symm.trans ?_
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  have he : MeasurePreserving e (Measure.pi fun _ : Fin 1 ↦ μ) μ :=
    measurePreserving_funUnique μ (Fin 1)
  simpa only [heval] using he.setLIntegral_comp_preimage_emb
    e.measurableEmbedding (fun y ↦ ENNReal.ofReal (K y y).re) s

omit [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X]
    [BorelSpace X] in
/-- SYNOPSIS item 88: for a Hermitian kernel, where `K(x, x) K(y, y) > 0` the pair correlation
`ρ^{(2)}(x, y) / (ρ(x) ρ(y))` is `1 - |K(x, y)|² / (K(x, x) K(y, y)) ≤ 1`. -/
theorem pairCorrelation_determinantal {K : X → X → ℂ} (hK : ∀ y z, K z y = conj (K y z))
    {y z : X} (hpos : 0 < (K y y).re * (K z z).re) :
    (Matrix.det (Matrix.of fun i j : Fin 2 ↦ K (![y, z] i) (![y, z] j))).re /
        ((K y y).re * (K z z).re) = 1 - ‖K y z‖ ^ 2 / ((K y y).re * (K z z).re) ∧
      1 - ‖K y z‖ ^ 2 / ((K y y).re * (K z z).re) ≤ 1 := by
  have hdiag (a : X) : (K a a).im = 0 := by
    have heq := congrArg Complex.im (hK a a)
    rw [Complex.conj_im] at heq
    linarith
  have hdet :
      (Matrix.det (Matrix.of fun i j : Fin 2 ↦ K (![y, z] i) (![y, z] j))).re =
        (K y y).re * (K z z).re - ‖K y z‖ ^ 2 := by
    calc
      _ = (K y y * K z z - K y z * K z y).re := by simp [Matrix.det_fin_two]
      _ = _ := by
        rw [hK y z, Complex.mul_conj', ← Complex.ofReal_pow, Complex.sub_re,
          Complex.ofReal_re, Complex.mul_re, hdiag, zero_mul, sub_zero]
  constructor
  · rw [hdet, sub_div, div_self hpos.ne']
  · exact sub_le_self _ (div_nonneg (sq_nonneg _) hpos.le)

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
private lemma volume_uniform_tuple_lt {k : ℕ} {n : Fin k → ℕ} (hn : Function.Injective n)
    (t : Fin k → unitInterval) :
    (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))
      {u | ∀ i, u (n i) < t i} = ∏ i, ENNReal.ofReal (t i : ℝ) := by
  let proj : (ℕ → unitInterval) → Fin k → unitInterval := fun u i ↦ u (n i)
  have hm : Measurable proj := Measurable.of_eval fun _ ↦ measurable_pi_apply _
  have hMp : (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval)).map proj =
      Measure.pi fun _ : Fin k ↦ (volume : Measure unitInterval) := by
    simpa only [Measure.infinitePi_eq_pi, proj, Function.comp_apply] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ ↦ (volume : Measure unitInterval)) hn)
  let S := Set.pi univ fun i ↦ Iio (t i)
  have hS : MeasurableSet S := MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Iio
  have heq : proj ⁻¹' S = {u | ∀ i, u (n i) < t i} := by ext u; simp [S, proj]
  rw [← heq, ← Measure.map_apply hm hS, hMp, Measure.pi_pi]
  simp only [unitInterval.volume_Iio]

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
private lemma lintegral_factorialPointSum {k : ℕ} {a : ℕ → Bool} {y : ℕ → X}
    {f : (Fin k → X) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂factorialPointSum k a y =
      ∑' n : {n : Fin k → ℕ // Function.Injective n},
        if ∀ i, a (n.1 i) then f (fun i ↦ y (n.1 i)) else 0 := by
  rw [factorialPointSum_def, lintegral_sum_measure]
  apply tsum_congr
  intro n
  split_ifs <;> simp [lintegral_dirac' _ hf]

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
private lemma thinning_tuple_lintegral {k : ℕ} {n : Fin k → ℕ} (hn : Function.Injective n)
    {p : X → ℝ} (hp : Measurable p) (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {I : Ω → ℕ → Bool} {x : Ω → ℕ → X}
    {U : Ω → ℕ → unitInterval} (hUm : Measurable U)
    (hU : P.map U = Measure.infinitePi fun _ ↦ volume)
    (hind : IndepFun (fun ω ↦ (I ω, x ω)) U P) (hm : Measurable fun ω ↦ (I ω, x ω))
    {f : (Fin k → X) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, (if ∀ i, I ω (n i) && decide ((U ω (n i) : ℝ) < p (x ω (n i))) then
        f (fun i ↦ x ω (n i)) else 0) ∂P =
      ∫⁻ ω, (if ∀ i, I ω (n i) then
        f (fun i ↦ x ω (n i)) * ∏ i, ENNReal.ofReal (p (x ω (n i))) else 0) ∂P := by
  classical
  let g (a : (ℕ → Bool) × (ℕ → X)) : ℝ≥0∞ :=
    if ∀ i, a.1 (n i) then f (fun i ↦ a.2 (n i)) else 0
  let w (a : (ℕ → Bool) × (ℕ → X)) : ℝ≥0∞ := ∏ i, ENNReal.ofReal (p (a.2 (n i)))
  let A : Set (((ℕ → Bool) × (ℕ → X)) × (ℕ → unitInterval)) :=
    {v | ∀ i, (v.2 (n i) : ℝ) < p (v.1.2 (n i))}
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i ↦ measurableSet_lt ?_ ?_
    · fun_prop
    · exact hp.comp ((measurable_pi_apply (n i)).comp
        (measurable_snd.comp measurable_fst))
  have hg : Measurable g := by
    refine Measurable.ite ?_ (hf.comp (Measurable.of_eval fun i ↦
      (measurable_pi_apply (n i)).comp measurable_snd)) measurable_const
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i ↦ ?_
    exact measurableSet_eq_fun
      ((measurable_pi_apply (n i)).comp measurable_fst) measurable_const
  have hw : Measurable w := Finset.measurable_prod _ fun i _ ↦
    (hp.comp ((measurable_pi_apply (n i)).comp measurable_snd)).ennreal_ofReal
  let G (v : ((ℕ → Bool) × (ℕ → X)) × (ℕ → unitInterval)) :=
    A.indicator (fun v ↦ g v.1) v
  have hG : Measurable G := (hg.comp measurable_fst).indicator hA
  have hprod := hind.map_prod_eq_prod_map_map hm.aemeasurable hUm.aemeasurable
  calc
    _ = ∫⁻ ω, G ((I ω, x ω), U ω) ∂P := by
      apply lintegral_congr
      intro ω
      by_cases hi : ∀ i, I ω (n i) <;> by_cases hu : ∀ i, (U ω (n i) : ℝ) < p (x ω (n i)) <;>
        simp [G, A, g, hi, hu, Bool.and_eq_true, forall_and]
    _ = ∫⁻ a, ∫⁻ u, G (a, u) ∂(Measure.infinitePi fun _ : ℕ ↦ volume) ∂
        P.map (fun ω ↦ (I ω, x ω)) := by
      rw [← lintegral_map hG (hm.prodMk hUm), hprod, hU, lintegral_prod _ hG.aemeasurable]
    _ = ∫⁻ a, g a * w a ∂P.map (fun ω ↦ (I ω, x ω)) := by
      apply lintegral_congr
      intro a
      let t (i : Fin k) : unitInterval := ⟨p (a.2 (n i)), hp0 _, hp1 _⟩
      let S : Set (ℕ → unitInterval) := {u | ∀ i, u (n i) < t i}
      have hS : MeasurableSet S := by
        dsimp only [S]
        rw [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i ↦
          measurableSet_lt (measurable_pi_apply (n i)) measurable_const
      have hGS (u : ℕ → unitInterval) : G (a, u) = S.indicator (fun _ ↦ g a) u := rfl
      simp only [hGS, lintegral_indicator hS, lintegral_const, Measure.restrict_apply_univ,
        volume_uniform_tuple_lt hn, S, w, t]
    _ = _ := by
      rw [lintegral_map (hg.fun_mul hw) hm]
      exact lintegral_congr fun ω ↦ by by_cases hi : ∀ i, I ω (n i) <;> simp [g, w, hi]

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
private lemma measurable_thinning_mask {I : Ω → ℕ → Bool} {x : Ω → ℕ → X} {p : X → ℝ}
    {U : Ω → ℕ → unitInterval} (hp : Measurable p) (hUm : Measurable U)
    (hI : Measurable I) (hx : Measurable x) :
    Measurable (fun ω n ↦ I ω n && decide ((U ω n : ℝ) < p (x ω n))) := by
  classical
  apply Measurable.of_eval
  intro n
  let S : Set Ω := {ω | (U ω n : ℝ) < p (x ω n)}
  have hS : MeasurableSet S :=
    measurableSet_lt (by fun_prop) (hp.comp ((measurable_pi_apply n).comp hx))
  have hd : Measurable (fun ω ↦ decide ((U ω n : ℝ) < p (x ω n))) := by
    have h : Measurable (fun ω ↦ if ω ∈ S then true else false) :=
      Measurable.ite hS measurable_const measurable_const
    convert h using 1
    funext ω
    by_cases hω : (U ω n : ℝ) < p (x ω n) <;> simp [S, hω]
  exact (Measurable.of_discrete (f := fun a : Bool × Bool ↦ a.1 && a.2)).comp
    (((measurable_pi_apply n).comp hI).prodMk hd)

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
private lemma thinning_factorialPointSum {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {I : Ω → ℕ → Bool} {x : Ω → ℕ → X} {p : X → ℝ}
    (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∀ y, p y ≤ 1)
    {U : Ω → ℕ → unitInterval} (hUm : Measurable U)
    (hU : P.map U = Measure.infinitePi fun _ ↦ volume)
    (hind : IndepFun (fun ω ↦ (I ω, x ω)) U P) (hm : Measurable fun ω ↦ (I ω, x ω)) :
    P.bind (fun ω ↦ factorialPointSum k
      (fun n ↦ I ω n && decide ((U ω n : ℝ) < p (x ω n))) (x ω)) =
    (P.bind fun ω ↦ factorialPointSum k (I ω) (x ω)).withDensity
      (fun z ↦ ∏ i, ENNReal.ofReal (p (z i))) := by
  classical
  let J (ω : Ω) (n : ℕ) := I ω n && decide ((U ω n : ℝ) < p (x ω n))
  have hI : Measurable I := hm.fst
  have hx : Measurable x := hm.snd
  have hJ : Measurable J := measurable_thinning_mask hp hUm hI hx
  have hterm {a : Ω → ℕ → Bool} {f : (Fin k → X) → ℝ≥0∞}
      (ha : Measurable a) (hf : Measurable f)
      (n : {n : Fin k → ℕ // Function.Injective n}) :
      AEMeasurable (fun ω ↦ if ∀ i, a ω (n.1 i) then f (fun i ↦ x ω (n.1 i)) else 0) P := by
    apply Measurable.aemeasurable
    refine Measurable.ite ?_ (hf.comp (Measurable.of_eval fun i ↦
      (measurable_pi_apply (n.1 i)).comp hx)) measurable_const
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_eq_fun
      ((measurable_pi_apply (n.1 i)).comp ha) measurable_const
  let w (z : Fin k → X) := ∏ i, ENNReal.ofReal (p (z i))
  have hw : Measurable w := Finset.measurable_prod _ fun i _ ↦
    (hp.comp (measurable_pi_apply i)).ennreal_ofReal
  ext S hS
  let F : (Fin k → X) → ℝ≥0∞ := S.indicator 1
  have hF : Measurable F := (measurable_const (a := (1 : ℝ≥0∞))).indicator hS
  -- Name both tests explicitly for the two applications of the bind integral formula.
  change P.bind (fun ω ↦ factorialPointSum k (J ω) (x ω)) S =
    ((P.bind fun ω ↦ factorialPointSum k (I ω) (x ω)).withDensity w) S
  rw [withDensity_apply _ hS, ← lintegral_indicator hS, ← lintegral_indicator_one hS]
  rw [Measure.lintegral_bind (m := P) (measurable_factorialPointSum k hJ hx).aemeasurable
      hF.aemeasurable,
    Measure.lintegral_bind (m := P) (measurable_factorialPointSum k hI hx).aemeasurable
      (hw.indicator hS).aemeasurable]
  simp only [lintegral_factorialPointSum hF, lintegral_factorialPointSum (hw.indicator hS)]
  rw [lintegral_tsum (hterm hJ hF), lintegral_tsum (hterm hI (hw.indicator hS))]
  apply tsum_congr
  intro n
  rw [thinning_tuple_lintegral n.2 hp hp0 hp1 hUm hU hind hm hF]
  apply lintegral_congr
  intro ω
  by_cases hi : ∀ i, I ω (n.1 i) <;> by_cases hs : (fun i ↦ x ω (n.1 i)) ∈ S <;>
    simp [hi, hs, w, F, Set.indicator]

omit [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X]
    [BorelSpace X] in
private lemma det_thinning_weight {k : ℕ} {p : X → ℝ} (hp0 : ∀ y, 0 ≤ p y)
    (K : X → X → ℂ) (z : Fin k → X) :
    ENNReal.ofReal (Matrix.det (Matrix.of fun i j ↦
      (Real.sqrt (p (z i)) : ℂ) * K (z i) (z j) * Real.sqrt (p (z j)))).re =
      ENNReal.ofReal (Matrix.det (Matrix.of fun i j ↦ K (z i) (z j))).re *
        ∏ i, ENNReal.ofReal (p (z i)) := by
  let v (i : Fin k) := (Real.sqrt (p (z i)) : ℂ)
  let A : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i j ↦ K (z i) (z j)
  have hmat : (Matrix.of fun i j ↦ v i * K (z i) (z j) * v j) =
      Matrix.diagonal v * A * Matrix.diagonal v := by
    ext i j
    simp [A, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change ENNReal.ofReal (Matrix.det (Matrix.of fun i j ↦ v i * K (z i) (z j) * v j)).re = _
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_right_comm,
    ← Finset.prod_mul_distrib]
  have hv (i : Fin k) : v i * v i = (p (z i) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (hp0 _)]
  simp only [hv, ← Complex.ofReal_prod, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦ hp0 _), ENNReal.ofReal_prod_of_nonneg,
    mul_comm]
  exact fun i _ ↦ hp0 _

private lemma withDensity_mul_measurable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [SFinite μ] (f : Y → ℝ≥0∞) {w : Y → ℝ≥0∞} (hw : Measurable w)
    (hfin : ∀ y, w y < ∞) :
    (μ.withDensity f).withDensity w = μ.withDensity (f * w) := by
  -- Use one minorant that represents the density for both base measures.
  obtain ⟨f₁, hf₁, hle₁, heq₁⟩ := exists_measurable_le_withDensity_eq μ f
  obtain ⟨f₂, hf₂, hle₂, heq₂⟩ := exists_measurable_le_withDensity_eq (μ.withDensity w) f
  let g := fun y ↦ max (f₁ y) (f₂ y)
  have hg : Measurable g := hf₁.max hf₂
  have hle : g ≤ f := fun y ↦ max_le (hle₁ y) (hle₂ y)
  have h₁ : μ.withDensity f = μ.withDensity g := by
    refine le_antisymm ?_ (withDensity_mono (Filter.Eventually.of_forall hle))
    rw [← heq₁]
    exact withDensity_mono (Filter.Eventually.of_forall fun y ↦ le_max_left _ _)
  have h₂ : (μ.withDensity w).withDensity f = (μ.withDensity w).withDensity g := by
    refine le_antisymm ?_ (withDensity_mono (Filter.Eventually.of_forall hle))
    rw [← heq₂]
    exact withDensity_mono (Filter.Eventually.of_forall fun y ↦ le_max_right _ _)
  ext s hs
  rw [h₁, ← withDensity_mul μ hg hw, mul_comm g w, withDensity_mul μ hw hg, ← h₂,
    withDensity_apply _ hs, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
      μ hw f hs (Filter.Eventually.of_forall hfin), mul_comm, withDensity_apply _ hs]

omit [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X] [BorelSpace X] in
/-- SYNOPSIS item 88: independent `p`-thinning (retaining `x_n` when `U_n < p(x_n)` for i.i.d.
uniform `U_n` independent of the process) of a determinantal process with kernel `K` gives the
determinantal process with kernel `√p(x) K(x, y) √p(y)`. -/
theorem isDeterminantal_thinning {P : Measure Ω} [IsProbabilityMeasure P] {I : Ω → ℕ → Bool}
    {x : Ω → ℕ → X} {K : X → X → ℂ} {μ : Measure X} [SigmaFinite μ]
    (h : IsDeterminantal P I x K μ) {p : X → ℝ} (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (U : Ω → ℕ → unitInterval) (hUm : Measurable U)
    (hU : P.map U = Measure.infinitePi fun _ ↦ volume)
    (hind : IndepFun (fun ω ↦ (I ω, x ω)) U P) (hm : Measurable fun ω ↦ (I ω, x ω)) :
    IsDeterminantal P (fun ω n ↦ I ω n && decide ((U ω n : ℝ) < p (x ω n))) x
      (fun y z ↦ (Real.sqrt (p y) : ℂ) * K y z * Real.sqrt (p z)) μ := by
  rcases isDeterminantal_def.mp h with ⟨hs, hα⟩
  apply isDeterminantal_def.mpr
  refine ⟨?_, fun k hk ↦ ?_⟩
  · filter_upwards [hs] with ω hω
    intro n m hn hm hEq
    simp only [Bool.and_eq_true] at hn hm
    exact hω n m hn.1 hm.1 hEq
  rw [thinning_factorialPointSum hp hp0 hp1 hUm hU hind hm, hα k hk]
  let w (z : Fin k → X) := ∏ i, ENNReal.ofReal (p (z i))
  have hw : Measurable w := Finset.measurable_prod _ fun i _ ↦
    (hp.comp (measurable_pi_apply i)).ennreal_ofReal
  -- The definition allows a determinant density without a measurability hypothesis.
  rw [withDensity_mul_measurable _ _ hw fun z ↦ ENNReal.prod_lt_top fun _ _ ↦
    ENNReal.ofReal_lt_top]
  congr 1
  funext z
  exact (det_thinning_weight hp0 K z).symm

/-! ### The Macchi–Soshnikov theorem (SYNOPSIS item 89) -/

/-- SYNOPSIS item 89, Macchi–Soshnikov theorem: for a continuous Hermitian kernel whose integral
operator is locally of trace class, a determinantal point process with kernel `K` exists if and
only if the spectrum of the operator lies in `[0, 1]`, that is,
`0 ≤ ⟨f, K f⟩ ≤ ‖f‖²` for bounded measurable compactly supported `f`. -/
theorem exists_determinantal_iff {K : X → X → ℂ} (hKc : Continuous (Function.uncurry K))
    (hK : ∀ y z, K z y = conj (K y z)) {μ : Measure X} [SigmaFinite μ]
    [IsLocallyFiniteMeasure μ] (htr : ∀ D : Set X, IsCompact D → ∫⁻ y in D, ‖K y y‖ₑ ∂μ < ∞) :
    (∃ Q : Measure ((ℕ → Bool) × (ℕ → X)), IsProbabilityMeasure Q ∧
        IsDeterminantal Q Prod.fst Prod.snd K μ) ↔
      ∀ f : X → ℂ, Measurable f → (∃ C, ∀ y, ‖f y‖ ≤ C) → HasCompactSupport f →
        0 ≤ (kernelForm K μ f).re ∧ (kernelForm K μ f).re ≤ ∫ y, ‖f y‖ ^ 2 ∂μ := by
  sorry

/-! ### Number of points (SYNOPSIS item 90) -/

/-- SYNOPSIS item 90: for a trace-class kernel `K(x, y) = ∑_k λ_k φ_k(x) conj φ_k(y)` with
orthonormal `φ_k` and `λ_k ∈ [0, 1]`, the determinantal law is the mixture over independent
`I_k ∼ Bernoulli(λ_k)` (realised as `I_k = 𝟙{U_k < λ_k}` for i.i.d. uniform `U_k`) of the
determinantal projection laws with kernels `∑_k I_k φ_k(x) conj φ_k(y)`. -/
theorem determinantal_mixture {μ : Measure X} [SigmaFinite μ] [IsLocallyFiniteMeasure μ]
    {φ : ℕ → X → ℂ} (hφ : ∀ k, MemLp (φ k) 2 μ)
    (hon : ∀ k l, ∫ y, conj (φ k y) * φ l y ∂μ = if k = l then 1 else 0) {ls : ℕ → ℝ}
    (hl0 : ∀ k, 0 ≤ ls k) (hl1 : ∀ k, ls k ≤ 1) (hsum : Summable ls) :
    determinantalLaw (fun y z ↦ ∑' k, (ls k : ℂ) * φ k y * conj (φ k z)) μ =
      (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval)).bind fun u ↦
        determinantalLaw (fun y z ↦ ∑' k,
          (if (u k : ℝ) < ls k then (1 : ℂ) else 0) * φ k y * conj (φ k z)) μ := by
  sorry

/-- SYNOPSIS item 90: in the setting of `MSSS.determinantal_mixture`, the total number of points
has the law of `∑_k I_k`, with mean `∑ λ_k`, variance `∑ λ_k (1 - λ_k)`, and void probability
`∏ (1 - λ_k)`. -/
theorem count_determinantal {P : Measure Ω} [IsProbabilityMeasure P] {I : Ω → ℕ → Bool}
    {x : Ω → ℕ → X} {μ : Measure X} [SigmaFinite μ] [IsLocallyFiniteMeasure μ]
    {φ : ℕ → X → ℂ} (hφ : ∀ k, MemLp (φ k) 2 μ)
    (hon : ∀ k l, ∫ y, conj (φ k y) * φ l y ∂μ = if k = l then 1 else 0) {ls : ℕ → ℝ}
    (hl0 : ∀ k, 0 ≤ ls k) (hl1 : ∀ k, ls k ≤ 1) (hsum : Summable ls)
    (h : IsDeterminantal P I x (fun y z ↦ ∑' k, (ls k : ℂ) * φ k y * conj (φ k z)) μ) :
    P.map (fun ω ↦ pointSum (I ω) (x ω) univ) =
        (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval)).map
          (fun u ↦ ∑' k, if (u k : ℝ) < ls k then (1 : ℝ≥0∞) else 0) ∧
      ∫ ω, (pointSum (I ω) (x ω) univ).toReal ∂P = ∑' k, ls k ∧
      Var[fun ω ↦ (pointSum (I ω) (x ω) univ).toReal; P] = ∑' k, ls k * (1 - ls k) ∧
      P {ω | pointSum (I ω) (x ω) univ = 0} = ENNReal.ofReal (∏' k, (1 - ls k)) := by
  sorry

end MSSS
