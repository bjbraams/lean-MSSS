module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.LinearCombination

/-!
# Positive definite functions on spheres

SYNOPSIS item 18, Schoenberg's theorem on spheres. The sphere `S^d` is the unit sphere of
`ℝ^{d+1}` with geodesic distance `θ(x, y) = arccos⟨x, y⟩ ∈ [0, π]`.

The Gegenbauer polynomials `C_n^λ` are defined by the three-term recurrence
`(n + 2) C_{n+2}^λ = 2(n + 1 + λ) X C_{n+1}^λ - (n + 2λ) C_n^λ`, `C_0^λ = 1`, `C_1^λ = 2λX`. The
normalised polynomials `C_n^λ(x) / C_n^λ(1)` are taken to be the Chebyshev polynomials `T_n` at
`λ = 0`, so that the normalised `C_n^0(cos θ)` is `cos nθ` as in the synopsis. For `d = 2`
(`λ = 1/2`) they are the Legendre polynomials. We use Mathlib's Chebyshev cosine identity and
its shifted Legendre polynomials. Their coefficient formula yields the three-term recurrence
needed to compare the two bases.
For the closure properties we use Mathlib's Schur product theorem and closedness of the
positive semidefinite cone in the entrywise topology.

## Main definitions

* `MSSS.gegenbauer a n`: the Gegenbauer polynomial `C_n^a`.
* `MSSS.normalizedGegenbauer a n x`: `C_n^a(x) / C_n^a(1)`, and `T_n(x)` for `a = 0`.
* `MSSS.sphereClass d`, `MSSS.strictSphereClass d`: the classes `Ψ_d` and `Ψ_d^+`.
* `MSSS.sphereClassInf`, `MSSS.strictSphereClassInf`: `Ψ_∞` and `Ψ_∞^+`.

## Main results

* `MSSS.normalizedGegenbauer_zero_cos`, `MSSS.normalizedGegenbauer_half_eq_shiftedLegendre`:
  the circle and two-dimensional sphere bases in item 18 (a).
* `MSSS.mem_sphereClass_iff`, `MSSS.eq_of_hasSum_normalizedGegenbauer`,
  `MSSS.mem_sphereClassInf_iff`, `MSSS.mem_strictSphereClass_iff`,
  `MSSS.mem_strictSphereClassInf_iff`, `MSSS.convex_sphereClass`, `MSSS.mul_mem_sphereClass`,
  `MSSS.mem_sphereClass_of_tendsto`, `MSSS.convex_sphereClassInf`,
  `MSSS.mul_mem_sphereClassInf`, `MSSS.mem_sphereClassInf_of_tendsto`: SYNOPSIS item 18.
-/

public section

noncomputable section

open Polynomial Filter Topology Set Metric
open scoped RealInnerProductSpace

namespace MSSS

/-- The Gegenbauer polynomial `C_n^a`, by the three-term recurrence. -/
def gegenbauer (a : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (2 * a) * X
  | n + 2 => C (1 / ((n : ℝ) + 2)) *
      (C (2 * ((n : ℝ) + 1 + a)) * X * gegenbauer a (n + 1) - C ((n : ℝ) + 2 * a) * gegenbauer a n)

@[simp] lemma gegenbauer_zero (a : ℝ) : gegenbauer a 0 = 1 := by rw [gegenbauer]

@[simp] lemma gegenbauer_one (a : ℝ) : gegenbauer a 1 = C (2 * a) * X := by rw [gegenbauer]

lemma gegenbauer_add_two (a : ℝ) (n : ℕ) : gegenbauer a (n + 2) = C (1 / ((n : ℝ) + 2)) *
    (C (2 * ((n : ℝ) + 1 + a)) * X * gegenbauer a (n + 1) - C ((n : ℝ) + 2 * a) * gegenbauer a n) :=
  by rw [gegenbauer]

/-- The normalised Gegenbauer function `C_n^a(x) / C_n^a(1)`, taken to be the Chebyshev
polynomial `T_n(x)` when `a = 0`. -/
def normalizedGegenbauer (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if a = 0 then (Chebyshev.T ℝ n).eval x else (gegenbauer a n).eval x / (gegenbauer a n).eval 1

lemma normalizedGegenbauer_def (a : ℝ) (n : ℕ) (x : ℝ) : normalizedGegenbauer a n x =
    if a = 0 then (Chebyshev.T ℝ n).eval x
    else (gegenbauer a n).eval x / (gegenbauer a n).eval 1 := by
  rw [normalizedGegenbauer]

/-- SYNOPSIS item 18 (a): the basis for the circle is the cosine basis. -/
lemma normalizedGegenbauer_zero_cos (n : ℕ) (θ : ℝ) :
    normalizedGegenbauer 0 n (Real.cos θ) = Real.cos ((n : ℝ) * θ) := by
  rw [normalizedGegenbauer_def, ite_eq_left rfl]
  exact_mod_cast Chebyshev.T_real_cos θ (n : ℤ)

/-- Unsigned coefficient of the shifted Legendre polynomial in the monomial basis. -/
private def legendreCoeff (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((n + k).choose k : ℝ)

/-- The constant coefficient of every shifted Legendre polynomial is one. -/
private lemma legendreCoeff_zero (n : ℕ) : legendreCoeff n 0 = 1 := by
  simp [legendreCoeff]

/-- Raise the degree while keeping the coefficient index fixed. -/
private lemma legendreCoeff_step (n k : ℕ) :
    ((n : ℝ) + k + 1) * legendreCoeff n k =
      ((n : ℝ) + 1 - k) * legendreCoeff (n + 1) k := by
  by_cases hk : k ≤ n + 1
  · have h₀ := Nat.choose_mul_succ_eq n k
    have h₁ := Nat.choose_mul_succ_eq (n + k) k
    have hs : n + k + 1 - k = n + 1 := by omega
    have hsum : n + k + 1 = n + 1 + k := add_right_comm n k 1
    rw [hs, hsum] at h₁
    have h₀' : (n.choose k : ℝ) * ((n : ℝ) + 1) =
        ((n + 1).choose k : ℝ) * ((n : ℝ) + 1 - k) := by
      exact_mod_cast h₀
    have h₁' : ((n + k).choose k : ℝ) * ((n : ℝ) + k + 1) =
        ((n + 1 + k).choose k : ℝ) * ((n : ℝ) + 1) := by
      rw [add_right_comm]
      exact_mod_cast h₁
    unfold legendreCoeff
    calc
      _ = (n.choose k : ℝ) * (((n + k).choose k : ℝ) * ((n : ℝ) + k + 1)) := by ring
      _ = ((n + 1 + k).choose k : ℝ) * ((n.choose k : ℝ) * ((n : ℝ) + 1)) := by
        rw [h₁']; ring
      _ = _ := by rw [h₀']; ring
  · rw [legendreCoeff, legendreCoeff, Nat.choose_eq_zero_of_lt (by omega : n < k),
      Nat.choose_eq_zero_of_lt (by omega : n + 1 < k)]
    simp

/-- Raise both the degree and the coefficient index. -/
private lemma legendreCoeff_step_both (n k : ℕ) :
    ((n : ℝ) + k + 1) * ((n : ℝ) + k + 2) * legendreCoeff n k =
      ((k : ℝ) + 1) ^ 2 * legendreCoeff (n + 1) (k + 1) := by
  have a : ((n : ℝ) + 1) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  have b : ((n : ℝ) + k + 1) * ((n + k).choose k : ℝ) =
      ((n + 1 + k).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    rw [add_right_comm n 1 k]
    exact_mod_cast Nat.add_one_mul_choose_eq (n + k) k
  have c : ((n + 1 + k).choose (k + 1) : ℝ) * ((n : ℝ) + k + 2) =
      ((n + 1 + (k + 1)).choose (k + 1) : ℝ) * ((n : ℝ) + 1) := by
    have hchoose := Nat.choose_mul_succ_eq (n + 1 + k) (k + 1)
    have hsub : n + 1 + k + 1 - (k + 1) = n + 1 := by omega
    rw [hsub, add_assoc (n + 1) k 1] at hchoose
    have h := congrArg (fun r : ℕ ↦ (r : ℝ)) hchoose
    push_cast at h
    linear_combination h
  unfold legendreCoeff
  calc
    _ = ((n : ℝ) + k + 2) * (n.choose k : ℝ) *
        (((n : ℝ) + k + 1) * ((n + k).choose k : ℝ)) := by ring
    _ = (((n + 1 + k).choose (k + 1) : ℝ) * ((n : ℝ) + k + 2)) *
        (n.choose k : ℝ) * ((k : ℝ) + 1) := by rw [b]; ring
    _ = ((n + 1 + (k + 1)).choose (k + 1) : ℝ) *
        (((n : ℝ) + 1) * (n.choose k : ℝ)) * ((k : ℝ) + 1) := by rw [c]; ring
    _ = _ := by rw [a]; ring

/-- The three-term Legendre recurrence at the positive coefficient indices. -/
private lemma legendreCoeff_rec (n k : ℕ) :
    ((n : ℝ) + 2) * legendreCoeff (n + 2) (k + 1) =
      (2 * n + 3) * legendreCoeff (n + 1) (k + 1) +
      2 * (2 * n + 3) * legendreCoeff (n + 1) k -
      ((n : ℝ) + 1) * legendreCoeff n (k + 1) := by
  have hn := legendreCoeff_step n (k + 1)
  have hn' := legendreCoeff_step (n + 1) (k + 1)
  have hk := legendreCoeff_step_both (n + 1) k
  push_cast at hn hn' hk
  let N : ℝ := (n : ℝ) + 2
  let K : ℝ := (k : ℝ) + 1
  have h₁ : 0 < N + K := by dsimp [N, K]; positivity
  have h₂ : 0 < N + K - 1 := by
    dsimp [N, K]
    linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k]
  apply mul_left_cancel₀ (mul_pos h₁ h₂).ne'
  dsimp only [N, K]
  linear_combination
    (((n : ℝ) + 1) * ((n : ℝ) + 2 + ((k : ℝ) + 1))) * hn +
    (- (2 * (n : ℝ) + 3) * ((n : ℝ) + 2 + ((k : ℝ) + 1) - 1) +
      ((n : ℝ) + 1) * ((n : ℝ) + 2 - ((k : ℝ) + 1) - 1)) * hn' -
    2 * (2 * (n : ℝ) + 3) * hk

/-- Mathlib’s shifted Legendre polynomial over the reals. -/
private def shiftedLegendreReal (n : ℕ) : ℝ[X] :=
  (shiftedLegendre n).map (Int.castRingHom ℝ)

/-- The monomial coefficient of the real shifted Legendre polynomial. -/
private lemma coeff_shiftedLegendreReal (n k : ℕ) :
    (shiftedLegendreReal n).coeff k = (-1 : ℝ) ^ k * legendreCoeff n k := by
  rw [shiftedLegendreReal, coeff_map, coeff_shiftedLegendre]
  conv_lhs => rw [Nat.choose_symm_add]
  simp only [Int.coe_castRingHom]
  push_cast
  unfold legendreCoeff
  ring

/-- The three-term recurrence with the shifted argument `1 - 2X`. -/
private lemma shiftedLegendreReal_recurrence (n : ℕ) :
    C ((n : ℝ) + 2) * shiftedLegendreReal (n + 2) =
      C (2 * (n : ℝ) + 3) * (1 - C 2 * X) * shiftedLegendreReal (n + 1) -
        C ((n : ℝ) + 1) * shiftedLegendreReal n := by
  ext k
  simp only [mul_assoc, sub_mul, one_mul, coeff_sub, coeff_C_mul]
  cases k with
  | zero => simp [coeff_shiftedLegendreReal, legendreCoeff_zero]; ring
  | succ k =>
    simp only [coeff_X_mul, coeff_shiftedLegendreReal, pow_succ]
    have h := legendreCoeff_rec n k
    linear_combination -((-1 : ℝ) ^ k) * h

/-- The shifted Legendre polynomial is normalised at zero. -/
private lemma eval_shiftedLegendreReal_at_zero (n : ℕ) : (shiftedLegendreReal n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_shiftedLegendreReal, legendreCoeff_zero, pow_zero, one_mul]

/-- The shifted Legendre polynomial of degree zero. -/
private lemma shiftedLegendreReal_zero : shiftedLegendreReal 0 = 1 := by
  simp [shiftedLegendreReal, shiftedLegendre]

/-- The shifted Legendre polynomial of degree one. -/
private lemma shiftedLegendreReal_one : shiftedLegendreReal 1 = 1 - C 2 * X := by
  simp [shiftedLegendreReal, shiftedLegendre, Finset.sum_range_succ, C_ofNat]
  ring

/-- The Gegenbauer and shifted Legendre polynomials follow the same recurrence
with the shifted argument. -/
private lemma eval_gegenbauer_half_eq (n : ℕ) (x : ℝ) :
    (gegenbauer (1 / 2) n).eval x = (shiftedLegendreReal n).eval ((1 - x) / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [shiftedLegendreReal_zero]
  | one =>
    rw [gegenbauer_one, shiftedLegendreReal_one]
    simp only [eval_mul, eval_C, eval_sub, eval_one, eval_X]
    ring
  | more n ih₀ ih₁ =>
    rw [gegenbauer_add_two]
    simp only [eval_mul, eval_sub, eval_C, eval_X, ih₀, ih₁]
    have h := congrArg (fun p : ℝ[X] ↦ p.eval ((1 - x) / 2)) (shiftedLegendreReal_recurrence n)
    simp only [eval_mul, eval_sub, eval_C, eval_one, eval_X] at h
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hn]
    linear_combination -h

/-- SYNOPSIS item 18 (a): the basis on the two-dimensional sphere consists of Legendre
polynomials. Mathlib's shifted Legendre polynomial is evaluated at `(1 - x) / 2`. -/
theorem normalizedGegenbauer_half_eq_shiftedLegendre (n : ℕ) (x : ℝ) :
    normalizedGegenbauer (1 / 2) n x =
      ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).eval ((1 - x) / 2) := by
  rw [normalizedGegenbauer_def, ite_eq_right (by norm_num), eval_gegenbauer_half_eq,
    eval_gegenbauer_half_eq, sub_self, zero_div, eval_shiftedLegendreReal_at_zero, div_one,
    shiftedLegendreReal]

/-- The kernel `(x, y) ↦ ψ(arccos⟨x, y⟩)` on the unit sphere `S^d ⊂ ℝ^{d+1}`. -/
def sphereKernel (d : ℕ) (ψ : ℝ → ℝ) :
    Matrix (sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ℝ :=
  Matrix.of fun x y ↦ ψ (Real.arccos ⟪(x : EuclideanSpace ℝ (Fin (d + 1))), y⟫)

lemma sphereKernel_apply (d : ℕ) (ψ : ℝ → ℝ) (x y : sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) :
    sphereKernel d ψ x y = ψ (Real.arccos ⟪(x : EuclideanSpace ℝ (Fin (d + 1))), y⟫) := by
  rw [sphereKernel, Matrix.of_apply]

/-- The class `Ψ_d` of continuous `ψ : [0, π] → ℝ` with `ψ 0 = 1` such that `ψ(θ(x, y))` is
positive definite on `S^d`. -/
def sphereClass (d : ℕ) : Set (ℝ → ℝ) :=
  {ψ | ContinuousOn ψ (Icc 0 Real.pi) ∧ ψ 0 = 1 ∧ (sphereKernel d ψ).PosSemidef}

/-- The class `Ψ_d^+` of members of `Ψ_d` that are strictly positive definite on `S^d`. -/
def strictSphereClass (d : ℕ) : Set (ℝ → ℝ) :=
  {ψ | ContinuousOn ψ (Icc 0 Real.pi) ∧ ψ 0 = 1 ∧ (sphereKernel d ψ).PosDef}

/-- The class `Ψ_∞ = ⋂_{d ≥ 1} Ψ_d`. -/
def sphereClassInf : Set (ℝ → ℝ) := ⋂ d : ℕ, sphereClass (d + 1)

/-- The class `Ψ_∞^+ = ⋂_{d ≥ 1} Ψ_d^+`. -/
def strictSphereClassInf : Set (ℝ → ℝ) := ⋂ d : ℕ, strictSphereClass (d + 1)

lemma mem_sphereClass {d : ℕ} {ψ : ℝ → ℝ} : ψ ∈ sphereClass d ↔
    ContinuousOn ψ (Icc 0 Real.pi) ∧ ψ 0 = 1 ∧ (sphereKernel d ψ).PosSemidef := by
  rw [sphereClass, mem_ofPred_eq]

lemma mem_strictSphereClass {d : ℕ} {ψ : ℝ → ℝ} : ψ ∈ strictSphereClass d ↔
    ContinuousOn ψ (Icc 0 Real.pi) ∧ ψ 0 = 1 ∧ (sphereKernel d ψ).PosDef := by
  rw [strictSphereClass, mem_ofPred_eq]

lemma mem_sphereClassInf {ψ : ℝ → ℝ} : ψ ∈ sphereClassInf ↔ ∀ d : ℕ, ψ ∈ sphereClass (d + 1) := by
  rw [sphereClassInf, mem_iInter]

lemma mem_strictSphereClassInf {ψ : ℝ → ℝ} :
    ψ ∈ strictSphereClassInf ↔ ∀ d : ℕ, ψ ∈ strictSphereClass (d + 1) := by
  rw [strictSphereClassInf, mem_iInter]

/-- SYNOPSIS item 18 (a): for `d ≥ 1`, `ψ ∈ Ψ_d` if and only if
`ψ(θ) = ∑ b_{n,d} C_n^{(d-1)/2}(cos θ) / C_n^{(d-1)/2}(1)` on `[0, π]` with `b_{n,d} ≥ 0` and
`∑ b_{n,d} = 1`. For `d = 1` this is the cosine series `∑ b_{n,1} cos nθ`. -/
theorem mem_sphereClass_iff {d : ℕ} (hd : 1 ≤ d) {ψ : ℝ → ℝ} :
    ψ ∈ sphereClass d ↔ ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ HasSum b 1 ∧
      ∀ θ ∈ Icc 0 Real.pi,
        HasSum (fun n ↦ b n * normalizedGegenbauer (((d : ℝ) - 1) / 2) n (Real.cos θ)) (ψ θ) := by
  sorry

/-- SYNOPSIS item 18 (a), uniqueness of the Schoenberg coefficients `b_{n,d}`. -/
theorem eq_of_hasSum_normalizedGegenbauer {d : ℕ} (hd : 1 ≤ d) {ψ : ℝ → ℝ} {b b' : ℕ → ℝ}
    (hb : ∀ θ ∈ Icc 0 Real.pi,
      HasSum (fun n ↦ b n * normalizedGegenbauer (((d : ℝ) - 1) / 2) n (Real.cos θ)) (ψ θ))
    (hb' : ∀ θ ∈ Icc 0 Real.pi,
      HasSum (fun n ↦ b' n * normalizedGegenbauer (((d : ℝ) - 1) / 2) n (Real.cos θ)) (ψ θ))
    (hs : Summable fun n ↦ |b n|) (hs' : Summable fun n ↦ |b' n|) : b = b' := by
  sorry

/-- SYNOPSIS item 18 (b): `ψ ∈ Ψ_∞` if and only if `ψ(θ) = ∑ b_n (cos θ)^n` on `[0, π]` with
`b_n ≥ 0` and `∑ b_n = 1`. -/
theorem mem_sphereClassInf_iff {ψ : ℝ → ℝ} :
    ψ ∈ sphereClassInf ↔ ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ HasSum b 1 ∧
      ∀ θ ∈ Icc 0 Real.pi, HasSum (fun n ↦ b n * Real.cos θ ^ n) (ψ θ) := by
  sorry

/-- SYNOPSIS item 18 (c): for `d ≥ 2` and `ψ ∈ Ψ_d` with Schoenberg coefficients `b_{n,d}`,
`ψ ∈ Ψ_d^+` if and only if `b_{n,d} > 0` for infinitely many even and infinitely many odd `n`. -/
theorem mem_strictSphereClass_iff {d : ℕ} (hd : 2 ≤ d) {ψ : ℝ → ℝ} (hψ : ψ ∈ sphereClass d)
    {b : ℕ → ℝ} (hb₀ : ∀ n, 0 ≤ b n) (hb₁ : HasSum b 1)
    (hb : ∀ θ ∈ Icc 0 Real.pi,
      HasSum (fun n ↦ b n * normalizedGegenbauer (((d : ℝ) - 1) / 2) n (Real.cos θ)) (ψ θ)) :
    ψ ∈ strictSphereClass d ↔
      {n | Even n ∧ 0 < b n}.Infinite ∧ {n | Odd n ∧ 0 < b n}.Infinite := by
  sorry

/-- SYNOPSIS item 18 (c), for `Ψ_∞^+`: `ψ ∈ Ψ_∞` with coefficients `b_n` belongs to `Ψ_∞^+` if
and only if `b_n > 0` for infinitely many even and infinitely many odd `n`. -/
theorem mem_strictSphereClassInf_iff {ψ : ℝ → ℝ} {b : ℕ → ℝ} (hb₀ : ∀ n, 0 ≤ b n)
    (hb₁ : HasSum b 1) (hb : ∀ θ ∈ Icc 0 Real.pi, HasSum (fun n ↦ b n * Real.cos θ ^ n) (ψ θ)) :
    ψ ∈ strictSphereClassInf ↔
      {n | Even n ∧ 0 < b n}.Infinite ∧ {n | Odd n ∧ 0 < b n}.Infinite := by
  sorry

/-- SYNOPSIS item 18 (d): `Ψ_d` is convex. -/
theorem convex_sphereClass (d : ℕ) : Convex ℝ (sphereClass d) := by
  intro ψ hψ φ hφ a b ha hb hab
  obtain ⟨hψc, hψ₀, hψp⟩ := mem_sphereClass.mp hψ
  obtain ⟨hφc, hφ₀, hφp⟩ := mem_sphereClass.mp hφ
  refine mem_sphereClass.mpr ⟨(hψc.const_smul a).add (hφc.const_smul b), ?_, ?_⟩
  · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hψ₀, hφ₀, mul_one] using hab
  · convert (hψp.smul ha).add (hφp.smul hb) using 1
    ext x y
    simp only [sphereKernel_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
      Pi.smul_apply]

/-- SYNOPSIS item 18 (d): `Ψ_d` is closed under products. -/
theorem mul_mem_sphereClass {d : ℕ} {ψ₁ ψ₂ : ℝ → ℝ} (h₁ : ψ₁ ∈ sphereClass d)
    (h₂ : ψ₂ ∈ sphereClass d) : ψ₁ * ψ₂ ∈ sphereClass d := by
  obtain ⟨hc₁, h₀₁, hp₁⟩ := mem_sphereClass.mp h₁
  obtain ⟨hc₂, h₀₂, hp₂⟩ := mem_sphereClass.mp h₂
  refine mem_sphereClass.mpr ⟨hc₁.mul hc₂, ?_, ?_⟩
  · simp only [Pi.mul_apply, h₀₁, h₀₂, mul_one]
  · convert hp₁.hadamard hp₂ using 1
    ext x y
    simp only [sphereKernel_apply, Matrix.hadamard_apply, Pi.mul_apply]

/-- SYNOPSIS item 18 (d): `Ψ_d` is closed under pointwise limits with continuous limit. -/
theorem mem_sphereClass_of_tendsto {d : ℕ} {ψ : ℕ → ℝ → ℝ} {ψ₀ : ℝ → ℝ}
    (hψ : ∀ k, ψ k ∈ sphereClass d)
    (hlim : ∀ θ ∈ Icc 0 Real.pi, Tendsto (fun k ↦ ψ k θ) atTop (𝓝 (ψ₀ θ)))
    (hc : ContinuousOn ψ₀ (Icc 0 Real.pi)) : ψ₀ ∈ sphereClass d := by
  have hspec k := mem_sphereClass.mp (hψ k)
  refine mem_sphereClass.mpr ⟨hc, ?_, ?_⟩
  · apply tendsto_nhds_unique (hlim 0 ⟨le_rfl, Real.pi_nonneg⟩)
    simpa only [funext (fun k ↦ (hspec k).2.1)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  · have hK : Tendsto (fun k ↦ sphereKernel d (ψ k)) atTop (𝓝 (sphereKernel d ψ₀)) := by
      refine tendsto_pi_nhds.mpr fun x ↦ tendsto_pi_nhds.mpr fun y ↦ ?_
      simpa only [sphereKernel_apply] using hlim _ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    exact isClosed_setOfPred_posSemidef.mem_of_tendsto hK
      (Eventually.of_forall fun k ↦ (hspec k).2.2)

/-- SYNOPSIS item 18 (d): `Ψ_∞` is convex. -/
theorem convex_sphereClassInf : Convex ℝ sphereClassInf := by
  rw [sphereClassInf]
  exact convex_iInter fun d ↦ convex_sphereClass (d + 1)

/-- SYNOPSIS item 18 (d): `Ψ_∞` is closed under products. -/
theorem mul_mem_sphereClassInf {ψ₁ ψ₂ : ℝ → ℝ} (h₁ : ψ₁ ∈ sphereClassInf)
    (h₂ : ψ₂ ∈ sphereClassInf) : ψ₁ * ψ₂ ∈ sphereClassInf := by
  exact mem_sphereClassInf.mpr fun d ↦
    mul_mem_sphereClass (mem_sphereClassInf.mp h₁ d) (mem_sphereClassInf.mp h₂ d)

/-- SYNOPSIS item 18 (d): `Ψ_∞` is closed under pointwise limits with continuous limit. -/
theorem mem_sphereClassInf_of_tendsto {ψ : ℕ → ℝ → ℝ} {ψ₀ : ℝ → ℝ}
    (hψ : ∀ k, ψ k ∈ sphereClassInf)
    (hlim : ∀ θ ∈ Icc 0 Real.pi, Tendsto (fun k ↦ ψ k θ) atTop (𝓝 (ψ₀ θ)))
    (hc : ContinuousOn ψ₀ (Icc 0 Real.pi)) : ψ₀ ∈ sphereClassInf := by
  exact mem_sphereClassInf.mpr fun d ↦
    mem_sphereClass_of_tendsto (fun k ↦ mem_sphereClassInf.mp (hψ k) d) hlim hc

end MSSS
