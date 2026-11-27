module

public import MSSS.GibbsPointProcesses.Finite
public import MSSS.PointProcesses.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Order.Filter.AtTopBot.Basic
public import TauCeti.Probability.PointProcess.Poisson.Basic

/-!
# Infinite-volume Gibbs point processes

SYNOPSIS items 100, 101, and 108. A configuration in `ℝ^d` is a measure `x`; it is **simple and
locally finite** when its restriction to each bounded measurable set is the counting measure of
finitely many points (`MSSS.IsSimpleConfig`). For an energy `H` on finite configurations of
finite range `R`, the local energy of `ξ` in an infinite configuration `x` is that of `ξ` in the
points of `x` within distance `R` of `ξ` (`MSSS.infLocalEnergy`).

A probability measure `P` on configurations is an **infinite-volume Gibbs measure**
(`MSSS.IsInfiniteGibbs`) when it is stationary, concentrated on simple locally finite
configurations, and satisfies the DLR equations for every bounded `Δ` with `|Δ| > 0`: given the
configuration outside `Δ`, the points in `Δ` have density proportional to
`z^{n(y)} e^{-β (H(y ∪ c) - H(c))}` with respect to `Π_Δ`, where `c` is the configuration in the
`R`-neighbourhood of `Δ` outside `Δ`.

Not stated: the tightness of the stationarised finite-volume Gibbs measures and the
identification of their accumulation points (item 100); only the existence statement is given.

## Main definitions

* `MSSS.atomsIn x B`, `MSSS.configMeasure y`, `MSSS.IsSimpleConfig x`.
* `MSSS.localEnergy H ξ x`, `MSSS.boltzmann β e`, `MSSS.IsFiniteRange H R`,
  `MSSS.IsTranslationInvariant H`, `MSSS.infLocalEnergy H R ξ x`.
* `MSSS.dlrWeight`, `MSSS.IsInfiniteGibbs P z β R H`.
* `MSSS.Percolates x`, `MSSS.criticalIntensity d`, `MSSS.widomRowlinsonEnergy R`.
* `MSSS.cube n`, `MSSS.takacsFiksel z β R H Λ f x`.

## Main results

All admitted.

* `MSSS.exists_isInfiniteGibbs`, `MSSS.isInfiniteGibbs_iff_gnz`: SYNOPSIS item 100.
* `MSSS.criticalIntensity_pos`, `MSSS.criticalIntensity_lt_top`, `MSSS.isInfiniteGibbs_unique`,
  `MSSS.widomRowlinson_phase_transition`: SYNOPSIS item 101.
* `MSSS.integral_takacsFiksel`, `MSSS.takacsFiksel_consistent`,
  `MSSS.pseudolikelihood_consistent`: SYNOPSIS item 108.
-/

public section

noncomputable section

open MeasureTheory Set Filter Metric TauCeti.Probability
open scoped ENNReal Topology

namespace MSSS

variable {d : ℕ}

/-! ### Configurations and local energies -/

open Classical in
/-- The finite set of atoms of `x` in `B`, or `∅` if there are infinitely many. -/
def atomsIn (x : Measure (EuclideanSpace ℝ (Fin d))) (B : Set (EuclideanSpace ℝ (Fin d))) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  if h : {y ∈ B | x {y} ≠ 0}.Finite then h.toFinset else ∅

/-- The counting measure `∑_{ξ ∈ y} δ_ξ` of a finite configuration. -/
def configMeasure (y : Finset (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ ξ ∈ y, Measure.dirac ξ

/-- `x` is a **simple locally finite configuration**: on every bounded measurable `B` it is the
counting measure of its finitely many atoms in `B`. -/
def IsSimpleConfig (x : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ B, MeasurableSet B → Bornology.IsBounded B → x.restrict B = configMeasure (atomsIn x B)

open Classical in
lemma atomsIn_def (x : Measure (EuclideanSpace ℝ (Fin d))) (B : Set (EuclideanSpace ℝ (Fin d))) :
    atomsIn x B = if h : {y ∈ B | x {y} ≠ 0}.Finite then h.toFinset else ∅ := by
  rw [atomsIn]

lemma configMeasure_def (y : Finset (EuclideanSpace ℝ (Fin d))) :
    configMeasure y = ∑ ξ ∈ y, Measure.dirac ξ := by
  rw [configMeasure]

lemma isSimpleConfig_def {x : Measure (EuclideanSpace ℝ (Fin d))} : IsSimpleConfig x ↔
    ∀ B, MeasurableSet B → Bornology.IsBounded B → x.restrict B = configMeasure (atomsIn x B) :=
  Iff.rfl

section Energy

variable {E : Type*} [DecidableEq E]

/-- The **local energy** `h(ξ, x) = H(x ∪ {ξ}) - H(x)`, with `(+∞) - (+∞) = 0` and `0` whenever
`H(x) = +∞`. -/
def localEnergy (H : Finset E → WithTop ℝ) (ξ : E) (x : Finset E) : WithTop ℝ :=
  if H x = ⊤ then 0 else if h : H (insert ξ x) = ⊤ then ⊤ else
    (((H (insert ξ x)).untop h - (H x).untopD 0 : ℝ) : WithTop ℝ)

/-- The Boltzmann factor `e^{-β e}`. For `e = +∞` it is `0` when `β ≠ 0` and `1` when `β = 0`
(the convention `e^{-0·∞} = 1`). -/
def boltzmann (β : ℝ) (e : WithTop ℝ) : ℝ :=
  if h : e = ⊤ then (if β = 0 then 1 else 0) else Real.exp (-β * e.untop h)

lemma localEnergy_def (H : Finset E → WithTop ℝ) (ξ : E) (x : Finset E) :
    localEnergy H ξ x = if H x = ⊤ then 0 else if h : H (insert ξ x) = ⊤ then ⊤ else
      (((H (insert ξ x)).untop h - (H x).untopD 0 : ℝ) : WithTop ℝ) := by
  rw [localEnergy]

omit [DecidableEq E] in
lemma boltzmann_def (β : ℝ) (e : WithTop ℝ) :
    boltzmann β e =
      if h : e = ⊤ then (if β = 0 then 1 else 0) else Real.exp (-β * e.untop h) := by
  rw [boltzmann]

end Energy

/-- `H` has **finite range** `R`: the local energy of `ξ` depends only on the points within
distance `R` of `ξ`. -/
def IsFiniteRange (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ) (R : ℝ) : Prop :=
  ∀ x ξ, ξ ∉ x → localEnergy H ξ x = localEnergy H ξ (x.filter fun η ↦ dist ξ η ≤ R)

/-- `H` is **translation invariant**. -/
def IsTranslationInvariant (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ) : Prop :=
  ∀ x v, H (x.image (· + v)) = H x

/-- The local energy `h(ξ, x)` of `ξ` in a configuration `x`, computed from the points of `x`
within distance `R` of `ξ`. -/
def infLocalEnergy (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ) (R : ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) (x : Measure (EuclideanSpace ℝ (Fin d))) : WithTop ℝ :=
  localEnergy H ξ (atomsIn x (closedBall ξ R))

/-- The unnormalised DLR weight `z^{n(y)} e^{-β (H(y ∪ c) - H(c))}` of a configuration `y` in `Δ`,
with `c` the points of `x` in the `R`-neighbourhood of `Δ` outside `Δ`. -/
def dlrWeight (z β R : ℝ) (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ)
    (Δ : Set (EuclideanSpace ℝ (Fin d))) (y : Finset (EuclideanSpace ℝ (Fin d)))
    (x : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  z ^ y.card * gibbsWeight β H (y ∪ atomsIn x (cthickening R Δ \ Δ)) /
    gibbsWeight β H (atomsIn x (cthickening R Δ \ Δ))

/-- `P` is an **infinite-volume Gibbs measure** for `(z, β, H)` with interaction range `R`. -/
def IsInfiniteGibbs (P : Measure (Measure (EuclideanSpace ℝ (Fin d)))) (z β R : ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ) : Prop :=
  IsProbabilityMeasure P ∧ IsStationary P id ∧ (∀ᵐ x ∂P, IsSimpleConfig x) ∧
    ∀ Δ, MeasurableSet Δ → Bornology.IsBounded Δ → 0 < volume Δ →
      ∀ f : Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞, Measurable f →
        ∫⁻ x, f x ∂P = ∫⁻ x,
          poissonIntegral Δ (fun y ↦ f (configMeasure y + x.restrict Δᶜ) *
              ENNReal.ofReal (dlrWeight z β R H Δ y x)) /
            poissonIntegral Δ (fun y ↦ ENNReal.ofReal (dlrWeight z β R H Δ y x)) ∂P

lemma isFiniteRange_def {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ} :
    IsFiniteRange H R ↔
      ∀ x ξ, ξ ∉ x → localEnergy H ξ x = localEnergy H ξ (x.filter fun η ↦ dist ξ η ≤ R) :=
  Iff.rfl

lemma isTranslationInvariant_def {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} :
    IsTranslationInvariant H ↔ ∀ x v, H (x.image (· + v)) = H x := Iff.rfl

lemma infLocalEnergy_def (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ) (R : ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) (x : Measure (EuclideanSpace ℝ (Fin d))) :
    infLocalEnergy H R ξ x = localEnergy H ξ (atomsIn x (closedBall ξ R)) := by
  rw [infLocalEnergy]

lemma dlrWeight_def (z β R : ℝ) (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ)
    (Δ : Set (EuclideanSpace ℝ (Fin d))) (y : Finset (EuclideanSpace ℝ (Fin d)))
    (x : Measure (EuclideanSpace ℝ (Fin d))) : dlrWeight z β R H Δ y x =
      z ^ y.card * gibbsWeight β H (y ∪ atomsIn x (cthickening R Δ \ Δ)) /
        gibbsWeight β H (atomsIn x (cthickening R Δ \ Δ)) := by
  rw [dlrWeight]

lemma isInfiniteGibbs_def {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))} {z β R : ℝ}
    {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} : IsInfiniteGibbs P z β R H ↔
      IsProbabilityMeasure P ∧ IsStationary P id ∧ (∀ᵐ x ∂P, IsSimpleConfig x) ∧
      ∀ Δ, MeasurableSet Δ → Bornology.IsBounded Δ → 0 < volume Δ →
        ∀ f : Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂P = ∫⁻ x,
            poissonIntegral Δ (fun y ↦ f (configMeasure y + x.restrict Δᶜ) *
                ENNReal.ofReal (dlrWeight z β R H Δ y x)) /
              poissonIntegral Δ (fun y ↦ ENNReal.ofReal (dlrWeight z β R H Δ y x)) ∂P :=
  Iff.rfl

/-! ### Existence and the GNZ characterisation (SYNOPSIS item 100) -/

/-- SYNOPSIS item 100: for a non-degenerate, hereditary, stable, translation-invariant energy of
finite range `R`, an infinite-volume Gibbs measure exists for all `z > 0` and `β ≥ 0`. -/
theorem exists_isInfiniteGibbs {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) :
    ∃ P : Measure (Measure (EuclideanSpace ℝ (Fin d))), IsInfiniteGibbs P z β R H := by
  sorry

/-- SYNOPSIS item 100: a stationary probability measure on simple locally finite configurations
is an infinite-volume Gibbs measure if and only if
`∫ ∑_{ξ ∈ x} f(ξ, x ∖ {ξ}) P(dx) = z ∫∫ f(ξ, x) e^{-β h(ξ, x)} dξ P(dx)` for measurable
`f ≥ 0`. -/
theorem isInfiniteGibbs_iff_gnz {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))}
    [IsProbabilityMeasure P] (hstat : IsStationary P id) (hsimple : ∀ᵐ x ∂P, IsSimpleConfig x) :
    IsInfiniteGibbs P z β R H ↔
      ∀ f : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞,
        Measurable (Function.uncurry f) →
        ∫⁻ x, ∫⁻ ξ, f ξ (x - Measure.dirac ξ) ∂x ∂P =
          ENNReal.ofReal z *
            ∫⁻ x, ∫⁻ ξ, f ξ x * ENNReal.ofReal (boltzmann β (infLocalEnergy H R ξ x))
              ∂volume ∂P := by
  sorry

/-! ### Uniqueness and phase transition (SYNOPSIS item 101) -/

/-- A configuration **percolates** in the Boolean model with balls of radius `1/2`: it has an
infinite self-avoiding chain of atoms with consecutive distances at most `1`. -/
def Percolates (x : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ s : ℕ → EuclideanSpace ℝ (Fin d), Function.Injective s ∧ (∀ n, x {s n} ≠ 0) ∧
    ∀ n, dist (s n) (s (n + 1)) ≤ 1

/-- The percolation threshold `z_d` of the Poisson Boolean model with balls of radius `1/2`: the
infimum of the intensities at which the Poisson process percolates with positive probability. -/
def criticalIntensity (d : ℕ) : ℝ≥0∞ :=
  sInf {z : ℝ≥0∞ | ∃ P : Measure (Measure (EuclideanSpace ℝ (Fin d))),
    IsPoissonRandomMeasure P id (z • volume) ∧ 0 < P {x | Percolates x}}

/-- The **Widom–Rowlinson** energy `H(x) = |⋃_{ξ ∈ x} B(ξ, R)|`. -/
def widomRowlinsonEnergy (R : ℝ) (x : Finset (EuclideanSpace ℝ (Fin d))) : WithTop ℝ :=
  ((volume (⋃ ξ ∈ x, closedBall ξ R)).toReal : WithTop ℝ)

lemma percolates_def {x : Measure (EuclideanSpace ℝ (Fin d))} : Percolates x ↔
    ∃ s : ℕ → EuclideanSpace ℝ (Fin d), Function.Injective s ∧ (∀ n, x {s n} ≠ 0) ∧
      ∀ n, dist (s n) (s (n + 1)) ≤ 1 := Iff.rfl

lemma criticalIntensity_def (d : ℕ) : criticalIntensity d =
    sInf {z : ℝ≥0∞ | ∃ P : Measure (Measure (EuclideanSpace ℝ (Fin d))),
      IsPoissonRandomMeasure P id (z • volume) ∧ 0 < P {x | Percolates x}} := by
  rw [criticalIntensity]

lemma widomRowlinsonEnergy_def (R : ℝ) (x : Finset (EuclideanSpace ℝ (Fin d))) :
    widomRowlinsonEnergy R x = ((volume (⋃ ξ ∈ x, closedBall ξ R)).toReal : WithTop ℝ) := by
  rw [widomRowlinsonEnergy]

/-- SYNOPSIS item 101: `z_d > 0` for `d ≥ 1`. -/
theorem criticalIntensity_pos (hd : 1 ≤ d) : 0 < criticalIntensity d := by
  sorry

/-- SYNOPSIS item 101: `z_d < ∞` for `d ≥ 2`. -/
theorem criticalIntensity_lt_top (hd : 2 ≤ d) : criticalIntensity d < ∞ := by
  sorry

/-- SYNOPSIS item 101: for an energy of finite range `R` with local energy bounded below by `C`,
the infinite-volume Gibbs measure is unique when `z < z_d e^{C β} / R^d`. -/
theorem isInfiniteGibbs_unique {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R C : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    (hC : ∀ x ξ, ξ ∉ x → (C : WithTop ℝ) ≤ localEnergy H ξ x) {z β : ℝ} (hz : 0 < z)
    (hβ : 0 ≤ β)
    (hsmall : ENNReal.ofReal z < criticalIntensity d * ENNReal.ofReal (Real.exp (C * β) / R ^ d))
    {P P' : Measure (Measure (EuclideanSpace ℝ (Fin d)))} (hP : IsInfiniteGibbs P z β R H)
    (hP' : IsInfiniteGibbs P' z β R H) : P = P' := by
  sorry

/-- SYNOPSIS item 101: for the Widom–Rowlinson energy (of range `2R`) and `d ≥ 2`, there are at
least two infinite-volume Gibbs measures when `z = β` is large enough. -/
theorem widomRowlinson_phase_transition (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) :
    ∃ z₀ : ℝ, ∀ z ≥ z₀, ∃ P P' : Measure (Measure (EuclideanSpace ℝ (Fin d))),
      IsInfiniteGibbs P z z (2 * R) (widomRowlinsonEnergy R) ∧
        IsInfiniteGibbs P' z z (2 * R) (widomRowlinsonEnergy R) ∧ P ≠ P' := by
  sorry

/-! ### Takacs–Fiksel estimation (SYNOPSIS item 108) -/

/-- The cube `[-n, n]^d`. -/
def cube (d : ℕ) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, WithLp.ofLp x i ∈ Icc (-(n : ℝ)) n}

/-- The **Takacs–Fiksel** contrast
`C_Λ(f, x) = ∑_{ξ ∈ x ∩ Λ} f(ξ, x ∖ {ξ}) - z ∫_Λ e^{-β h(ξ, x)} f(ξ, x) dξ`. -/
def takacsFiksel (z β R : ℝ) (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ)
    (Λ : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ)
    (x : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∫ ξ in Λ, f ξ (x - Measure.dirac ξ) ∂x -
    z * ∫ ξ in Λ, boltzmann β (infLocalEnergy H R ξ x) * f ξ x

lemma cube_def (d : ℕ) (n : ℕ) :
    cube d n = {x : EuclideanSpace ℝ (Fin d) | ∀ i, WithLp.ofLp x i ∈ Icc (-(n : ℝ)) n} := by
  rw [cube]

lemma takacsFiksel_def (z β R : ℝ) (H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ)
    (Λ : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ)
    (x : Measure (EuclideanSpace ℝ (Fin d))) : takacsFiksel z β R H Λ f x =
      ∫ ξ in Λ, f ξ (x - Measure.dirac ξ) ∂x -
        z * ∫ ξ in Λ, boltzmann β (infLocalEnergy H R ξ x) * f ξ x := by
  rw [takacsFiksel]

/-- SYNOPSIS item 108: by the GNZ equation of item 100, the Takacs–Fiksel contrast has mean zero
at the true parameters, for bounded `Λ` and integrable test functions. -/
theorem integral_takacsFiksel {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {z β : ℝ} (hz : 0 < z) (hβ : 0 ≤ β) {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))}
    (hP : IsInfiniteGibbs P z β R H) {Λ : Set (EuclideanSpace ℝ (Fin d))}
    (hΛ : Bornology.IsBounded Λ) (hΛm : MeasurableSet Λ)
    {f : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfi : ∫⁻ x, ∫⁻ ξ in Λ, ‖f ξ x‖ₑ *
      ENNReal.ofReal (boltzmann β (infLocalEnergy H R ξ x)) ∂volume ∂P < ∞) :
    ∫ x, takacsFiksel z β R H Λ f x ∂P = 0 := by
  sorry

/-- SYNOPSIS item 108: for a stationary finite-range infinite-volume Gibbs measure with
parameters `θ* = (z*, β*)` in a bounded set `D ⊆ (0, ∞) × [0, ∞)`, under the integrability
condition `E[|f_k(0, Γ)| (1 + |h(0, Γ)|) sup_D e^{-β h(0, Γ)}] < ∞` and identifiability, every
minimiser over `D` of `∑_k C_{[-n,n]^d}(f_k, Γ)²` converges almost surely to `θ*`. -/
theorem takacsFiksel_consistent {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {D : Set (ℝ × ℝ)} (hD : Bornology.IsBounded D) (hDsub : D ⊆ Ioi 0 ×ˢ Ici 0) {θs : ℝ × ℝ}
    (hθs : θs ∈ D) {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))}
    (hP : IsInfiniteGibbs P θs.1 θs.2 R H) {K : ℕ}
    (f : Fin K → EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf : ∀ k, Measurable (Function.uncurry (f k)))
    (hint : ∀ k, ∫⁻ x, ‖f k 0 x‖ₑ * (1 + ‖(infLocalEnergy H R 0 x).untopD 0‖ₑ) *
      ⨆ θ ∈ D, ENNReal.ofReal (boltzmann θ.2 (infLocalEnergy H R 0 x)) ∂P < ∞)
    (hident : ∀ θ ∈ D, ∑ k, (∫ x, f k 0 x * (θ.1 * boltzmann θ.2 (infLocalEnergy H R 0 x) -
      θs.1 * boltzmann θs.2 (infLocalEnergy H R 0 x)) ∂P) ^ 2 = 0 → θ = θs)
    (θhat : ℕ → Measure (EuclideanSpace ℝ (Fin d)) → ℝ × ℝ)
    (hmin : ∀ n x, θhat n x ∈ D ∧ ∀ θ ∈ D,
      ∑ k, takacsFiksel (θhat n x).1 (θhat n x).2 R H (cube d n) (f k) x ^ 2 ≤
        ∑ k, takacsFiksel θ.1 θ.2 R H (cube d n) (f k) x ^ 2) :
    ∀ᵐ x ∂P, Tendsto (fun n ↦ θhat n x) atTop (𝓝 θs) := by
  sorry

/-- SYNOPSIS item 108: the maximum pseudolikelihood estimator, the Takacs–Fiksel estimator with
`f_1 = 1` and `f_2 = h`, is strongly consistent when
`E[(1 + h(0, Γ)²) sup_D e^{-β h(0, Γ)}] < ∞` and `P(h(0, Γ) = h(0, ∅)) < 1`. -/
theorem pseudolikelihood_consistent {H : Finset (EuclideanSpace ℝ (Fin d)) → WithTop ℝ} {R : ℝ}
    (hR : 0 < R) (hnd : IsNonDegenerate H) (hher : IsHereditaryEnergy H) (hst : IsStableEnergy H)
    (hHm : IsEnergyMeasurable H) (hti : IsTranslationInvariant H) (hfr : IsFiniteRange H R)
    {D : Set (ℝ × ℝ)} (hD : Bornology.IsBounded D) (hDsub : D ⊆ Ioi 0 ×ˢ Ici 0) {θs : ℝ × ℝ}
    (hθs : θs ∈ D) {P : Measure (Measure (EuclideanSpace ℝ (Fin d)))}
    (hP : IsInfiniteGibbs P θs.1 θs.2 R H)
    (hint : ∫⁻ x, (1 + ‖(infLocalEnergy H R 0 x).untopD 0‖ₑ ^ 2) *
      ⨆ θ ∈ D, ENNReal.ofReal (boltzmann θ.2 (infLocalEnergy H R 0 x)) ∂P < ∞)
    (hnondeg : P {x | infLocalEnergy H R 0 x = localEnergy H 0 ∅} < 1)
    (θhat : ℕ → Measure (EuclideanSpace ℝ (Fin d)) → ℝ × ℝ)
    (hmin : ∀ n x, θhat n x ∈ D ∧ ∀ θ ∈ D,
      ∑ k : Fin 2, takacsFiksel (θhat n x).1 (θhat n x).2 R H (cube d n)
          (![fun _ _ ↦ 1, fun ξ y ↦ (infLocalEnergy H R ξ y).untopD 0] k) x ^ 2 ≤
        ∑ k : Fin 2, takacsFiksel θ.1 θ.2 R H (cube d n)
          (![fun _ _ ↦ 1, fun ξ y ↦ (infLocalEnergy H R ξ y).untopD 0] k) x ^ 2) :
    ∀ᵐ x ∂P, Tendsto (fun n ↦ θhat n x) atTop (𝓝 θs) := by
  sorry

end MSSS
