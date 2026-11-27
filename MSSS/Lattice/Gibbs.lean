module

public import MSSS.Lattice.Gibbs.Dobrushin
public import MSSS.Lattice.Gibbs.Existence

/-!
# Gibbs measures on infinite lattices

The basic theory of specifications and extreme Gibbs measures is developed in
`MSSS.Lattice.Gibbs.Basic`. Existence and local compactness for absolutely summable potentials
are proved in `MSSS.Lattice.Gibbs.Existence`. The Dobrushin uniqueness proof is in
`MSSS.Lattice.Gibbs.Dobrushin`. This module also treats the one-dimensional Markov description
and the two-dimensional Ising transition.

## Main definitions

* `MSSS.singleSiteLaw`, `MSSS.tvSup`, `MSSS.dobrushinCoeff`, and `MSSS.IsQuasilocal`.
* `MSSS.IsMarkovChainLaw`, the law of a stationary Markov chain on `ℤ`.
* `MSSS.isingPotential`, the nearest-neighbour Ising potential on `ℤ²`.

## Main results

* `MSSS.gibbsSet_subsingleton_of_dobrushin`, `MSSS.existsUnique_gibbs_of_dobrushin`,
  `MSSS.gibbsSet_subsingleton_of_oscillation` (SYNOPSIS item 62).
* `MSSS.existsUnique_gibbs_markovSpecification`, `MSSS.markovSpecification_of_transition`,
  `MSSS.transition_injective` (SYNOPSIS item 63).
* `MSSS.ising_phaseTransition` and `MSSS.ising_critical` (SYNOPSIS item 64).
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MSSS

variable {S E : Type*} [MeasurableSpace E]

/-! ### One dimension (SYNOPSIS item 63) -/

section OneDimension

variable [Fintype E] [MeasurableSingletonClass E]

/-- `μ` is the law of the stationary Markov chain on `ℤ` with transition matrix `P`: for some
stationary distribution `ν`, cylinder probabilities are `ν(x_0) ∏ P(x_t, x_{t+1})`. -/
def IsMarkovChainLaw (P : E → E → ℝ) (μ : Measure (ℤ → E)) : Prop :=
  ∃ ν : E → ℝ, (∑ x, ν x = 1) ∧ (∀ y, ∑ x, ν x * P x y = ν y) ∧
    ∀ (k : ℤ) (n : ℕ) (x : Fin (n + 1) → E), μ {ω | ∀ t : Fin (n + 1), ω (k + t) = x t} =
      ENNReal.ofReal (ν (x 0) * ∏ t : Fin n, P (x t.castSucc) (x t.succ))

omit [Fintype E] [MeasurableSingletonClass E] in
lemma isMarkovChainLaw_def [Fintype E] {P : E → E → ℝ} {μ : Measure (ℤ → E)} :
    IsMarkovChainLaw P μ ↔ ∃ ν : E → ℝ, (∑ x, ν x = 1) ∧ (∀ y, ∑ x, ν x * P x y = ν y) ∧
      ∀ (k : ℤ) (n : ℕ) (x : Fin (n + 1) → E), μ {ω | ∀ t : Fin (n + 1), ω (k + t) = x t} =
        ENNReal.ofReal (ν (x 0) * ∏ t : Fin n, P (x t.castSucc) (x t.succ)) := Iff.rfl

/-- SYNOPSIS item 63: a positive homogeneous Markov specification on `ℤ` with nonempty states,
`γ_{{i}}(σ_i = y ∣ ω) = g(ω_{i-1}, y, ω_{i+1})` with `g > 0`, has exactly one Gibbs measure.
It is the stationary Markov chain with transition matrix `P(x, y) = Q(x, y) r(y) / (q r(x))`,
where `Q(x, y) = g(a, x, y) / g(a, a, y)` for a fixed `a`, `q` is the Perron eigenvalue of `Q`,
and `r` is a positive right eigenvector. -/
theorem existsUnique_gibbs_markovSpecification [Nonempty E]
    {γ : Finset ℤ → (ℤ → E) → Measure (ℤ → E)}
    (hγ : IsSpecification γ) (g : E → E → E → ℝ) (hg : ∀ x y z, 0 < g x y z)
    (hγg : ∀ i ω y, γ {i} ω {σ | σ i = y} = ENNReal.ofReal (g (ω (i - 1)) y (ω (i + 1)))) :
    (∃! μ, IsGibbs γ μ) ∧ ∀ μ, IsGibbs γ μ → ∀ (a : E) (q : ℝ) (r : E → ℝ), 0 < q →
      (∀ x, 0 < r x) → (∀ x, ∑ y, g a x y / g a a y * r y = q * r x) →
      IsMarkovChainLaw (fun x y ↦ g a x y / g a a y * r y / (q * r x)) μ := by
  sorry

/-- SYNOPSIS item 63: every transition matrix `P` with positive entries arises: the stationary
chain of `P` is the Gibbs measure of a positive homogeneous Markov specification, with
`g(x, y, z) = P(x, y) P(y, z) / ∑_w P(x, w) P(w, z)`. -/
theorem markovSpecification_of_transition {P : E → E → ℝ} (hP : ∀ x y, 0 < P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) :
    ∃ γ : Finset ℤ → (ℤ → E) → Measure (ℤ → E), IsSpecification γ ∧
      (∀ i ω y, γ {i} ω {σ | σ i = y} = ENNReal.ofReal (P (ω (i - 1)) y * P y (ω (i + 1)) /
        ∑ w, P (ω (i - 1)) w * P w (ω (i + 1)))) ∧
      ∀ μ, IsGibbs γ μ → IsMarkovChainLaw P μ := by
  sorry

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Equal conditional bridge probabilities imply a ratio independent of the middle state. -/
private lemma transition_bridge_ratio {P P' : E → E → ℝ}
    (hP : ∀ x y, 0 < P x y) (hP' : ∀ x y, 0 < P' x y) (x y z : E)
    (h : P x y * P y z / ∑ w, P x w * P w z = P' x y * P' y z / ∑ w, P' x w * P' w z) :
    (P' x y / P x y) * (P' y z / P y z) = (∑ w, P' x w * P' w z) / ∑ w, P x w * P w z := by
  have hs : 0 < ∑ w, P x w * P w z :=
    Finset.sum_pos (fun w _ ↦ mul_pos (hP x w) (hP w z)) ⟨y, Finset.mem_univ y⟩
  have hs' : 0 < ∑ w, P' x w * P' w z :=
    Finset.sum_pos (fun w _ ↦ mul_pos (hP' x w) (hP' w z)) ⟨y, Finset.mem_univ y⟩
  rw [div_mul_div_comm]
  exact (div_eq_div_iff (mul_pos (hP x y) (hP y z)).ne' hs.ne').2
    (((div_eq_div_iff hs.ne' hs'.ne').1 h).symm.trans (mul_comm _ _))

-- Keep the measurable state-space instances in the stated theorem.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 63: the transition matrix is determined by the specification:
`P ↦ (x, y, z) ↦ P(x, y) P(y, z) / ∑_w P(x, w) P(w, z)` is injective on positive stochastic
matrices. -/
theorem transition_injective {P P' : E → E → ℝ} (hP : ∀ x y, 0 < P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) (hP' : ∀ x y, 0 < P' x y) (hP'1 : ∀ x, ∑ y, P' x y = 1)
    (h : ∀ x y z, P x y * P y z / ∑ w, P x w * P w z = P' x y * P' y z / ∑ w, P' x w * P' w z) :
    P = P' := by
  classical
  funext a b
  let R (x y : E) := P' x y / P x y
  let r (x : E) := R a x
  let q := R a a
  have hr (x : E) : 0 < r x := div_pos (hP' a x) (hP a x)
  have hweight (x y : E) : P' x y * r x = q * (P x y * r y) := by
    have heq := (transition_bridge_ratio hP hP' a x y (h a x y)).trans
      (transition_bridge_ratio hP hP' a a y (h a a y)).symm
    calc
      P' x y * r x = P x y * (R a x * R x y) := by
        rw [mul_left_comm (P x y), mul_comm (P' x y)]
        exact congrArg (r x * ·) (mul_div_cancel₀ _ (hP x y).ne').symm
      _ = P x y * (q * r y) := congrArg (P x y * ·) heq
      _ = q * (P x y * r y) := mul_left_comm _ _ _
  have hrow (x : E) : q * ∑ y, P x y * r y = r x := by
    simp only [Finset.mul_sum, ← hweight, ← Finset.sum_mul, hP'1, one_mul]
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ r ⟨a, Finset.mem_univ a⟩
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ r ⟨a, Finset.mem_univ a⟩
  have hupper (x : E) : (∑ y, P x y * r y) ≤ r imax := by
    rw [← one_mul (r imax), ← hP1 x, Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (hmax y hy) (hP x y).le
  have hlower (x : E) : r imin ≤ ∑ y, P x y * r y := by
    rw [← one_mul (r imin), ← hP1 x, Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (hmin y hy) (hP x y).le
  have hq : q = 1 := by
    apply le_antisymm
    · have heq := mul_le_mul_of_nonneg_left (hlower imin) (hr a).le
      rw [hrow] at heq
      exact le_of_mul_le_mul_right (by simpa only [one_mul] using heq) (hr imin)
    · have heq := mul_le_mul_of_nonneg_left (hupper imax) (hr a).le
      rw [hrow] at heq
      exact le_of_mul_le_mul_right (by simpa only [one_mul] using heq) (hr imax)
  have hsum : (∑ y, P imax y * (r imax - r y)) = 0 := by
    have hmean := hrow imax
    simp only [hq, one_mul] at hmean
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul _ _ (r imax), hP1, one_mul,
      hmean, sub_self]
  have hconst (y : E) : r y = r imax := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj ↦
      mul_nonneg (hP imax j).le (sub_nonneg.mpr (hmax j hj)))).1 hsum y (Finset.mem_univ y)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hP imax y).ne')).symm
  apply mul_right_cancel₀ (hr a).ne'
  simpa only [hconst b, hconst a, hq, one_mul] using (hweight a b).symm

end OneDimension

/-! ### The two-dimensional Ising model (SYNOPSIS item 64) -/

/-- The spin `±1` of a state `b : Bool`, `spin b = 1 - 2 b`: `spin true = -1` and
`spin false = 1`, so the all-plus configuration is the constant `false`. -/
def spin (b : Bool) : ℝ := if b then -1 else 1

/-- The nearest-neighbour **Ising potential** on `ℤ²`: `Φ_{{i,j}} = -σ_i σ_j` for nearest
neighbours `i, j`, and `Φ_A = 0` otherwise. -/
def isingPotential (A : Finset (ℤ × ℤ)) (ω : ℤ × ℤ → Bool) : ℝ :=
  if A.card = 2 ∧ ∀ i ∈ A, ∀ j ∈ A, i ≠ j → |i.1 - j.1| + |i.2 - j.2| = 1 then
    -∏ i ∈ A, spin (ω i)
  else 0

lemma spin_def (b : Bool) : spin b = if b then -1 else 1 := by
  rw [spin]

lemma isingPotential_def (A : Finset (ℤ × ℤ)) (ω : ℤ × ℤ → Bool) : isingPotential A ω =
    if A.card = 2 ∧ ∀ i ∈ A, ∀ j ∈ A, i ≠ j → |i.1 - j.1| + |i.2 - j.2| = 1 then
      -∏ i ∈ A, spin (ω i)
    else 0 := by
  rw [isingPotential]

/-- SYNOPSIS item 64, phase transition of the two-dimensional Ising model: for all sufficiently
large `β` there are shift-invariant Gibbs measures `μ₊^β` and `μ₋^β` for `βΦ`, each the
spin-flip image of the other, with `μ₋^β(σ_0) < 0 < μ₊^β(σ_0)`, and `μ₊^β` converges locally to
the point mass on the all-plus configuration (the constant `false`) as `β → ∞`. -/
theorem ising_phaseTransition :
    ∃ (β₀ : ℝ) (μp μm : ℝ → Measure (ℤ × ℤ → Bool)), ∀ β > β₀,
      let G := gibbsSet (gibbsKernel (fun A ω ↦ β * isingPotential A ω) Measure.count)
      μp β ∈ G ∧ μm β ∈ G ∧
        (∀ v : ℤ × ℤ, (μp β).map (fun ω i ↦ ω (i + v)) = μp β) ∧
        (∀ v : ℤ × ℤ, (μm β).map (fun ω i ↦ ω (i + v)) = μm β) ∧
        μm β = (μp β).map (fun ω i ↦ !ω i) ∧
        ∫ ω, spin (ω 0) ∂μm β < 0 ∧ 0 < ∫ ω, spin (ω 0) ∂μp β ∧
        ∀ Λ : Finset (ℤ × ℤ),
          Tendsto (fun β ↦ μp β {ω | ∀ i ∈ Λ, ω i = false}) atTop (𝓝 1) := by
  sorry

/-- SYNOPSIS item 64: with `β_c = ½ log(1 + √2)`, the Ising model on `ℤ²` has a unique Gibbs
measure for `β < β_c` and a phase transition for `β > β_c`. -/
theorem ising_critical (β : ℝ) (hβ : 0 ≤ β) :
    let G := gibbsSet (gibbsKernel (fun A ω ↦ β * isingPotential A ω) Measure.count)
    (β < (1 / 2) * Real.log (1 + Real.sqrt 2) → G.Subsingleton) ∧
      ((1 / 2) * Real.log (1 + Real.sqrt 2) < β → ¬ G.Subsingleton) := by
  sorry

end MSSS
