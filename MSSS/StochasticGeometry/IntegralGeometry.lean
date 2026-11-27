module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Integral geometry of convex bodies

SYNOPSIS items 114–117: the Steiner formula and intrinsic volumes, Hadwiger's characterisation
theorem, the Crofton formula, and the principal kinematic formula.

Convex bodies are compact convex subsets of `ℝ^d`; functionals are defined on all sets and
hypotheses refer to compact convex sets. The intrinsic volumes `V_j(K)` are defined from the
Steiner polynomial: `MSSS.steinerPolynomial K` interpolates `ε ↦ V_d(K + ε B^d)` at
`ε = 0, 1, …, d`, and `V_j(K)` is its coefficient of `ε^{d-j}` divided by `κ_{d-j}`; for
`j > d`, `V_j = 0`. The Steiner formula (item 114) says that this polynomial gives
`V_d(K + ε B^d)` for every `ε ≥ 0`.

Rotations are orthogonal matrices, and the rotation-invariant probability on them is any
probability measure invariant under left multiplication (`MSSS.IsRotationInvariant`). The affine
`k`-flats are `ϑ(L_0 + y)` with `L_0` the span of the first `k` coordinate vectors, `ϑ` a
rotation, and `y` in the span of the remaining coordinate vectors; the motion-invariant measure
`μ_k` integrates over `ϑ` under the rotation-invariant probability and over `y` under Lebesgue
measure.

The surface-area identity of item 114 is stated for convex bodies with nonempty interior, where
the surface area is the `(d - 1)`-dimensional Hausdorff measure of the boundary.

## Main definitions

* `MSSS.unitBallVolume j`: `κ_j`; `MSSS.kinematicConst r s`: `c^r_s = r! κ_r / (s! κ_s)`.
* `MSSS.steinerPolynomial K`, `MSSS.intrinsicVolume j K`.
* `MSSS.supportFunction K u`, `MSSS.meanWidth K`.
* `MSSS.IsConvexValuation ψ`, `MSSS.IsHausdorffContinuous ψ`, `MSSS.IsMotionInvariant ψ`.
* `MSSS.rotate g`, `MSSS.IsRotationInvariant ν`, `MSSS.standardFlat k y`, `MSSS.flat k g y`.

## Main results

The volume proofs use Mathlib's Lagrange interpolation and ball-volume formulas, and
TauCeti's volume of a nonempty zero-dimensional set and volume preservation under affine
isometries. Continuity uses Mathlib's separation theorem and the nullity of convex frontiers.

* `MSSS.steiner_formula`, `MSSS.intrinsicVolume_top`, `MSSS.surfaceArea_eq`,
  `MSSS.intrinsicVolume_one_eq_meanWidth`, `MSSS.intrinsicVolume_zero`,
  `MSSS.intrinsicVolume_linearIsometry`, `MSSS.intrinsicVolume_ball`,
  `MSSS.isConvexValuation_intrinsicVolume`, `MSSS.isHausdorffContinuous_intrinsicVolume`,
  `MSSS.isMotionInvariant_intrinsicVolume`, `MSSS.intrinsicVolume_smul`: SYNOPSIS item 114.
* `MSSS.hadwiger`, `MSSS.hadwiger_monotone`: SYNOPSIS item 115.
* `MSSS.crofton`: SYNOPSIS item 116.
* `MSSS.principal_kinematic`, `MSSS.kinematic_valuation`: SYNOPSIS item 117.
-/

public section

noncomputable section

open MeasureTheory Set Metric Polynomial
open scoped Pointwise

namespace MSSS

/-- The volume `κ_j` of the unit ball of `ℝ^j`. -/
def unitBallVolume (j : ℕ) : ℝ :=
  (volume (closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)).toReal

/-- The constant `c^r_s = r! κ_r / (s! κ_s)`. -/
def kinematicConst (r s : ℕ) : ℝ :=
  r.factorial * unitBallVolume r / (s.factorial * unitBallVolume s)

lemma unitBallVolume_def (j : ℕ) :
    unitBallVolume j = (volume (closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)).toReal := by
  rw [unitBallVolume]

lemma kinematicConst_def (r s : ℕ) :
    kinematicConst r s = r.factorial * unitBallVolume r / (s.factorial * unitBallVolume s) := by
  rw [kinematicConst]

variable {d : ℕ}

/-! ### Intrinsic volumes (SYNOPSIS item 114) -/

/-- The polynomial of degree at most `d` that interpolates `ε ↦ V_d(K + ε B^d)` at
`ε = 0, 1, …, d`. -/
def steinerPolynomial (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ[X] :=
  Lagrange.interpolate (Finset.range (d + 1)) (fun i : ℕ ↦ (i : ℝ))
    (fun i ↦ (volume (K + closedBall (0 : EuclideanSpace ℝ (Fin d)) i)).toReal)

/-- The **intrinsic volume** `V_j(K)`: the coefficient of `ε^{d-j}` in the Steiner polynomial
divided by `κ_{d-j}`, and `0` for `j > d`. -/
def intrinsicVolume (j : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  if j ≤ d then (steinerPolynomial K).coeff (d - j) / unitBallVolume (d - j) else 0

/-- The support function `h_K(u) = sup_{x ∈ K} ⟨x, u⟩`. -/
def supportFunction (K : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun x ↦ inner ℝ x u) '' K)

/-- The **mean width** `w(K) = σ(S^{d-1})⁻¹ ∫_{S^{d-1}} (h_K(u) + h_K(-u)) σ(du)`. -/
def meanWidth (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (volume.toSphere (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))).toReal⁻¹ *
    ∫ u, (supportFunction K u.1 + supportFunction K (-u.1)) ∂volume.toSphere

lemma steinerPolynomial_def (K : Set (EuclideanSpace ℝ (Fin d))) :
    steinerPolynomial K = Lagrange.interpolate (Finset.range (d + 1)) (fun i : ℕ ↦ (i : ℝ))
      (fun i ↦ (volume (K + closedBall (0 : EuclideanSpace ℝ (Fin d)) i)).toReal) := by
  rw [steinerPolynomial]

lemma intrinsicVolume_def (j : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) : intrinsicVolume j K =
    if j ≤ d then (steinerPolynomial K).coeff (d - j) / unitBallVolume (d - j) else 0 := by
  rw [intrinsicVolume]

lemma supportFunction_def (K : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d)) :
    supportFunction K u = sSup ((fun x ↦ inner ℝ x u) '' K) := by
  rw [supportFunction]

lemma meanWidth_def (K : Set (EuclideanSpace ℝ (Fin d))) : meanWidth K =
    (volume.toSphere (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))).toReal⁻¹ *
      ∫ u, (supportFunction K u.1 + supportFunction K (-u.1)) ∂volume.toSphere := by
  rw [meanWidth]

/-- SYNOPSIS item 114, Steiner formula: for a convex body `K` and `ε ≥ 0`,
`V_d(K + ε B^d) = ∑_{j=0}^d ε^{d-j} κ_{d-j} V_j(K)`. -/
theorem steiner_formula {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hKc : Convex ℝ K) {ε : ℝ} (hε : 0 ≤ ε) :
    (volume (K + closedBall (0 : EuclideanSpace ℝ (Fin d)) ε)).toReal =
      ∑ j ∈ Finset.range (d + 1), ε ^ (d - j) * unitBallVolume (d - j) * intrinsicVolume j K := by
  sorry

-- Keep the convex-body hypotheses of the existing interface.
set_option linter.unusedVariables false in
/-- SYNOPSIS item 114: `V_d` is the volume. -/
theorem intrinsicVolume_top {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hKc : Convex ℝ K) : intrinsicVolume d K = (volume K).toReal := by
  have hunit : unitBallVolume 0 = 1 := by
    rw [unitBallVolume_def,
      TauCeti.volume_eq_one_of_subsingleton ⟨0, mem_closedBall_self zero_le_one⟩,
      ENNReal.toReal_one]
  rw [intrinsicVolume_def, ite_eq_left le_rfl, Nat.sub_self, hunit, div_one,
    coeff_zero_eq_eval_zero, steinerPolynomial_def]
  have hinj : Set.InjOn (fun i : ℕ ↦ (i : ℝ)) (Finset.range (d + 1)) := Nat.cast_injective.injOn
  simpa using Lagrange.eval_interpolate_at_node
    (fun i : ℕ ↦ (volume (K + closedBall (0 : EuclideanSpace ℝ (Fin d)) i)).toReal)
    hinj (i := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ d))

/-- SYNOPSIS item 114: for a convex body with nonempty interior, `2 V_{d-1}(K)` is the surface
area, the `(d - 1)`-dimensional Euclidean-normalised Hausdorff measure `μHE[d - 1]` (equal to
Lebesgue measure on `(d - 1)`-dimensional affine subspaces) of the boundary. -/
theorem surfaceArea_eq (hd : 1 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKi : (interior K).Nonempty) :
    2 * intrinsicVolume (d - 1) K =
      (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1) (frontier K)).toReal := by
  sorry

/-- SYNOPSIS item 114: `V_1(K) = d κ_d / (2 κ_{d-1}) w(K)` is a multiple of the mean width. -/
theorem intrinsicVolume_one_eq_meanWidth (hd : 1 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKn : K.Nonempty) :
    intrinsicVolume 1 K = d * unitBallVolume d / (2 * unitBallVolume (d - 1)) * meanWidth K := by
  sorry

/-- SYNOPSIS item 114: `V_0` is the Euler characteristic, equal to `1` on nonempty convex
bodies. -/
theorem intrinsicVolume_zero {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKn : K.Nonempty) : intrinsicVolume 0 K = 1 := by
  sorry

/-- SYNOPSIS item 114: `V_j` does not depend on the dimension of the ambient space: it is
unchanged under a linear isometric embedding `ℝ^d → ℝ^n`. -/
theorem intrinsicVolume_linearIsometry {n : ℕ}
    (e : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKc : Convex ℝ K) (j : ℕ) :
    intrinsicVolume j (e '' K) = intrinsicVolume j K := by
  sorry

/-- SYNOPSIS item 114: `V_j(B^d) = (d choose j) κ_d / κ_{d-j}` for `j ≤ d`. -/
theorem intrinsicVolume_ball {j : ℕ} (hj : j ≤ d) :
    intrinsicVolume j (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) =
      d.choose j * unitBallVolume d / unitBallVolume (d - j) := by
  let B := closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  let p : ℝ[X] := C (unitBallVolume d) * (X + 1) ^ d
  have hinj : Set.InjOn (fun i : ℕ ↦ (i : ℝ)) (Finset.range (d + 1)) := Nat.cast_injective.injOn
  have hnat : p.natDegree ≤ d := by
    refine (natDegree_C_mul_le _ _).trans ?_
    simpa only [C_1] using (natDegree_pow_X_add_C (R := ℝ) d 1).le
  have hp : p.degree < (Finset.range (d + 1)).card := by
    rw [Finset.card_range]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hnat))
  have hpB : p = steinerPolynomial B := by
    rw [steinerPolynomial_def]
    refine Lagrange.eq_interpolate_of_eval_eq _ hinj hp fun i _ ↦ ?_
    have hball : B + closedBall (0 : EuclideanSpace ℝ (Fin d)) (i : ℝ) =
        closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 + i) := by
      simpa only [B, zero_add] using
        (closedBall_add_closedBall zero_le_one (Nat.cast_nonneg i)
          (0 : EuclideanSpace ℝ (Fin d)) 0)
    rw [hball, ← measureReal_def, Measure.addHaar_real_closedBall' volume 0 (by positivity)]
    simp only [p, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one,
      finrank_euclideanSpace_fin, unitBallVolume_def, measureReal_def]
    rw [add_comm (i : ℝ), mul_comm]
  rw [intrinsicVolume_def, ite_eq_left hj, ← hpB]
  simp only [p, coeff_C_mul, coeff_X_add_one_pow, Nat.choose_symm hj]
  rw [mul_comm]

/-! ### Valuations (SYNOPSIS items 114, 115) -/

/-- `ψ` is **additive** on convex bodies: `ψ(K ∪ M) + ψ(K ∩ M) = ψ(K) + ψ(M)` whenever `K`, `M`,
and `K ∪ M` are convex bodies. -/
def IsConvexValuation (ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ) : Prop :=
  ∀ K M, IsCompact K → Convex ℝ K → IsCompact M → Convex ℝ M → Convex ℝ (K ∪ M) →
    ψ (K ∪ M) + ψ (K ∩ M) = ψ K + ψ M

/-- `ψ` is **continuous in the Hausdorff metric** on nonempty convex bodies. -/
def IsHausdorffContinuous (ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ) : Prop :=
  ∀ K, IsCompact K → Convex ℝ K → K.Nonempty → ∀ ε > 0, ∃ δ > 0, ∀ M, IsCompact M →
    Convex ℝ M → M.Nonempty → hausdorffDist K M < δ → |ψ M - ψ K| < ε

/-- `ψ` is **invariant under rigid motions**. -/
def IsMotionInvariant (ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) K, ψ (f '' K) = ψ K

lemma isConvexValuation_def {ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ} : IsConvexValuation ψ ↔
    ∀ K M, IsCompact K → Convex ℝ K → IsCompact M → Convex ℝ M → Convex ℝ (K ∪ M) →
      ψ (K ∪ M) + ψ (K ∩ M) = ψ K + ψ M := Iff.rfl

lemma isHausdorffContinuous_def {ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ} :
    IsHausdorffContinuous ψ ↔ ∀ K, IsCompact K → Convex ℝ K → K.Nonempty → ∀ ε > 0,
      ∃ δ > 0, ∀ M, IsCompact M → Convex ℝ M → M.Nonempty → hausdorffDist K M < δ →
        |ψ M - ψ K| < ε := Iff.rfl

lemma isMotionInvariant_def {ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ} : IsMotionInvariant ψ ↔
    ∀ (f : EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)) K, ψ (f '' K) = ψ K :=
  Iff.rfl

/-- Outer parallel sets preserve intersections of two closed sets with convex union. -/
private lemma add_closedBall_inter_of_convex_union {K M : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsClosed K) (hM : IsClosed M) (hKM : Convex ℝ (K ∪ M)) (r : ℝ) :
    (K ∩ M) + closedBall 0 r = (K + closedBall 0 r) ∩ (M + closedBall 0 r) := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, ⟨hxK, hxM⟩, b, hb, rfl⟩
    exact ⟨⟨x, hxK, b, hb, rfl⟩, ⟨x, hxM, b, hb, rfl⟩⟩
  · rintro z ⟨⟨x, hx, b, hb, hbx⟩, ⟨y, hy, c, hc, hcy⟩⟩
    have hbx' : x ∈ closedBall z r := by
      rw [← hbx, Metric.mem_closedBall, dist_comm, dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hb
    have hcy' : y ∈ closedBall z r := by
      rw [← hcy, Metric.mem_closedBall, dist_comm, dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hc
    have hconv : Convex ℝ (closedBall z r ∩ (K ∪ M)) :=
      (convex_closedBall _ _).inter hKM
    obtain ⟨w, hw, hwKM⟩ := isPreconnected_closed_iff.mp hconv.isPreconnected K M hK hM
      inter_subset_right ⟨x, ⟨hbx', Or.inl hx⟩, hx⟩ ⟨y, ⟨hcy', Or.inr hy⟩, hy⟩
    refine ⟨w, hwKM, z - w, ?_, add_sub_cancel w z⟩
    rw [mem_closedBall_zero_iff, ← dist_eq_norm, dist_comm]
    exact hw.1

/-- SYNOPSIS item 114: each `V_j` is additive. -/
theorem isConvexValuation_intrinsicVolume (j : ℕ) :
    IsConvexValuation (intrinsicVolume (d := d) j) := by
  intro K M hK _ hM _ hKM
  have hpol : steinerPolynomial (K ∪ M) + steinerPolynomial (K ∩ M) =
      steinerPolynomial K + steinerPolynomial M := by
    simp only [steinerPolynomial_def, ← map_add]
    congr 1
    funext i
    simp only [Pi.add_apply, union_add,
      add_closedBall_inter_of_convex_union hK.isClosed hM.isClosed hKM]
    have hKb := hK.add (isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := (i : ℝ)))
    have hMb := hM.add (isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := (i : ℝ)))
    exact measureReal_union_add_inter (μ := volume) hMb.measurableSet
      hKb.measure_ne_top hMb.measure_ne_top
  by_cases hj : j ≤ d
  · simp only [intrinsicVolume_def, ite_eq_left hj, ← add_div, ← coeff_add, hpol]
  · simp only [intrinsicVolume_def, ite_eq_right hj, add_zero]

section HausdorffContinuity

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An interior point remains in every convex body that is sufficiently close in the
Hausdorff metric. -/
lemma eventually_mem_convexBody_of_mem_interior {K : ConvexBody E} {x : E}
    (hx : x ∈ interior (K : Set E)) : ∀ᶠ L in 𝓝 K, x ∈ L := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hn : ∀ᶠ L in 𝓝 K, L ∈ ball K (ε / 2) := Metric.ball_mem_nhds _ (half_pos hε)
  filter_upwards [hn] with L hL
  by_contra hn
  obtain ⟨f, c, hLsep, hsep⟩ := geometric_hahn_banach_closed_point L.convex L.isClosed hn
  let v := (InnerProductSpace.toDual ℝ E).symm f
  have hf (y : E) : inner ℝ v y = f y := InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro hv₀
    obtain ⟨z, hz⟩ := L.nonempty
    have h₁ := hf z
    have h₂ := hf x
    simp only [hv₀, inner_zero_left] at h₁ h₂
    linarith only [hLsep z hz, hsep, h₁, h₂]
  let a := ε / 2 / ‖v‖
  let z := x + a • v
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ha : 0 < a := div_pos (half_pos hε) hvpos
  have haz : a * ‖v‖ = ε / 2 := div_mul_cancel₀ _ hvpos.ne'
  have hz : z ∈ K := interior_subset (hball (by
    dsimp only [z]
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, haz]
    linarith only [hε]))
  have hdist : hausdorffDist (K : Set E) L < ε / 2 := by
    simpa only [ConvexBody.hausdorffDist_coe, Metric.mem_ball, dist_comm L K] using hL
  obtain ⟨y, hy, hzy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hz hdist
    ConvexBody.hausdorffEDist_ne_top
  have hin : inner ℝ v (z - y) = f x - f y + (ε / 2) * ‖v‖ := by
    dsimp only [z]
    rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      pow_two, ← mul_assoc a, haz, hf, hf]
    ring
  have habs : inner ℝ v (z - y) ≤ ‖v‖ * dist z y := by
    rw [dist_eq_norm]
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v (z - y))
  have hsmall := mul_lt_mul_of_pos_left hzy hvpos
  rw [hin] at habs
  linarith only [hLsep y hy, hsep, habs, hsmall]

omit [FiniteDimensional ℝ E] in
/-- A point outside a convex body remains outside sufficiently close bodies. -/
lemma eventually_notMem_convexBody_of_notMem {K : ConvexBody E} {x : E} (hx : x ∉ K) :
    ∀ᶠ L in 𝓝 K, x ∉ L := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp K.isClosed.isOpen_compl x hx
  have hn : ∀ᶠ L in 𝓝 K, L ∈ ball K ε := Metric.ball_mem_nhds K hε
  filter_upwards [hn] with L hL
  intro hxL
  have hdist : hausdorffDist (L : Set E) K < ε := hL
  obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hxL hdist
    ConvexBody.hausdorffEDist_ne_top
  exact (hball (by rwa [Metric.mem_ball, dist_comm])) hy

variable [MeasurableSpace E] [BorelSpace E]

/-- Lebesgue volume of a convex body is continuous in the Hausdorff metric. -/
lemma continuous_volume_real_convexBody :
    Continuous (fun K : ConvexBody E ↦ volume.real (K : Set E)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro K
  let s : Set E := (K : Set E) + closedBall 0 1
  let F (L : ConvexBody E) : E → ℝ := (L : Set E).indicator 1
  have hreal (L : ConvexBody E) : (∫ x, F L x) = volume.real (L : Set E) :=
    integral_indicator_one L.isClosed.measurableSet
  have hS : IsCompact s := K.isCompact.add (isCompact_closedBall 0 1)
  have hD : Integrable (s.indicator (1 : E → ℝ)) := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact integrableOn_const hS.measure_ne_top
  have hB : ∀ᶠ L in 𝓝 K, ∀ᵐ x ∂volume, ‖F L x‖ ≤ s.indicator 1 x := by
    have hn : ∀ᶠ L in 𝓝 K, L ∈ ball K 1 := Metric.ball_mem_nhds K zero_lt_one
    filter_upwards [hn] with L hL
    refine ae_of_all _ fun x ↦ ?_
    have hdist : hausdorffDist (L : Set E) K < 1 := hL
    by_cases hx : x ∈ L
    · obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx hdist
        ConvexBody.hausdorffEDist_ne_top
      have hxs : x ∈ s := ⟨y, hy, x - y, mem_closedBall_zero_iff.mpr
        (by rw [← dist_eq_norm]; exact hxy.le), add_sub_cancel _ _⟩
      simp only [F, Set.indicator_of_mem hx, Set.indicator_of_mem hxs, Pi.one_apply, norm_one]
      exact le_rfl
    · dsimp only [F]
      rw [Set.indicator_of_notMem hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun L ↦ F L x) (𝓝 K) (𝓝 (F K x)) := by
    have hb : ∀ᵐ x ∂volume, x ∉ frontier (K : Set E) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using K.convex.addHaar_frontier volume
    filter_upwards [hb] with x hx
    apply tendsto_const_nhds.congr'
    by_cases hKx : x ∈ K
    · filter_upwards [eventually_mem_convexBody_of_mem_interior
        ((mem_interior_iff_notMem_frontier hKx).2 hx)] with L hLx
      simp only [F, Set.indicator_of_mem hKx, Set.indicator_of_mem hLx]
    · filter_upwards [eventually_notMem_convexBody_of_notMem hKx] with L hLx
      simp only [F, Set.indicator_of_notMem hKx, Set.indicator_of_notMem hLx]
  have hm (L : ConvexBody E) : AEStronglyMeasurable (F L) volume :=
    (measurable_const.indicator L.isClosed.measurableSet).aestronglyMeasurable
  simpa only [ContinuousAt, hreal] using
    tendsto_integral_filter_of_dominated_convergence (μ := volume) (F := F) (f := F K)
      (s.indicator 1) (Eventually.of_forall hm) hB hD hlim

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Taking the Minkowski sum with a fixed convex body is nonexpansive. -/
lemma lipschitzWith_add_right_convexBody (B : ConvexBody E) :
    LipschitzWith 1 (fun L : ConvexBody E ↦ L + B) := by
  refine LipschitzWith.of_dist_le_mul fun K L ↦ ?_
  simp only [NNReal.coe_one, one_mul, ← ConvexBody.hausdorffDist_coe, ConvexBody.coe_add]
  refine le_of_forall_gt fun r hr ↦ ?_
  let r' := (hausdorffDist (K : Set E) L + r) / 2
  have hnear : hausdorffDist (K : Set E) L < r' := by dsimp only [r']; linarith only [hr]
  have hr' : r' < r := by dsimp only [r']; linarith only [hr]
  apply lt_of_le_of_lt _ hr'
  have hr₀ := (dist_nonneg (x := K) (y := L)).trans hnear.le
  refine Metric.hausdorffDist_le_of_mem_dist (s := (K : Set E) + (B : Set E))
    (t := (L : Set E) + (B : Set E)) hr₀ ?_ ?_
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨z, hz, hdis⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx hnear
      ConvexBody.hausdorffEDist_ne_top
    refine ⟨z + y, ⟨z, hz, y, hy, rfl⟩, ?_⟩
    simpa only [dist_add_right] using hdis.le
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨z, hz, hdis⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hx hnear
      ConvexBody.hausdorffEDist_ne_top
    refine ⟨z + y, ⟨z, hz, y, hy, rfl⟩, ?_⟩
    simpa only [dist_add_right, dist_comm] using hdis.le

end HausdorffContinuity

/-- SYNOPSIS item 114: each `V_j` is continuous in the Hausdorff metric. -/
theorem isHausdorffContinuous_intrinsicVolume (j : ℕ) :
    IsHausdorffContinuous (intrinsicVolume (d := d) j) := by
  have hvol (i : ℕ) : Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin d)) ↦
      (volume ((K : Set (EuclideanSpace ℝ (Fin d))) + closedBall 0 (i : ℝ))).toReal) := by
    let B : ConvexBody (EuclideanSpace ℝ (Fin d)) :=
      ⟨closedBall 0 (i : ℝ), convex_closedBall _ _, isCompact_closedBall _ _,
        ⟨0, mem_closedBall_self (Nat.cast_nonneg i)⟩⟩
    exact continuous_volume_real_convexBody.comp (lipschitzWith_add_right_convexBody B).continuous
  have hcont : Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin d)) ↦
      intrinsicVolume j (K : Set (EuclideanSpace ℝ (Fin d)))) := by
    by_cases hj : j ≤ d
    · simp only [intrinsicVolume_def, ite_eq_left hj, steinerPolynomial_def,
        Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul]
      exact (continuous_finsetSum _ fun i _ ↦ (hvol i).mul continuous_const).div_const _
    · simp only [intrinsicVolume_def, ite_eq_right hj]
      exact continuous_const
  intro K hKc hKx hKn ε hε
  let K' : ConvexBody (EuclideanSpace ℝ (Fin d)) := ⟨K, hKx, hKc, hKn⟩
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
  refine ⟨δ, hδ, fun M hMc hMx hMn hDM ↦ ?_⟩
  let M' : ConvexBody (EuclideanSpace ℝ (Fin d)) := ⟨M, hMx, hMc, hMn⟩
  have hDM' : hausdorffDist (K' : Set (EuclideanSpace ℝ (Fin d))) M' < δ := hDM
  rw [ConvexBody.hausdorffDist_coe, dist_comm] at hDM'
  have hK' : (K' : Set (EuclideanSpace ℝ (Fin d))) = K := rfl
  have hM' : (M' : Set (EuclideanSpace ℝ (Fin d))) = M := rfl
  simpa only [Real.dist_eq, hK', hM'] using hclose hDM'

/-- SYNOPSIS item 114: each `V_j` is invariant under rigid motions. -/
theorem isMotionInvariant_intrinsicVolume (j : ℕ) :
    IsMotionInvariant (intrinsicVolume (d := d) j) := by
  intro f K
  have hoffset (r : ℝ) : f '' (K + closedBall 0 r) = f '' K + closedBall 0 r := by
    have hadd (k b : EuclideanSpace ℝ (Fin d)) : f (k + b) = f k + f.linearIsometryEquiv b := by
      simpa only [vadd_eq_add, add_comm] using f.map_vadd k b
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, b, hb, rfl⟩, rfl⟩
      refine ⟨f k, ⟨k, hk, rfl⟩, f.linearIsometryEquiv b, ?_, (hadd k b).symm⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hb
    · rintro ⟨_, ⟨k, hk, rfl⟩, b, hb, rfl⟩
      refine ⟨k + f.linearIsometryEquiv.symm b, ⟨k, hk, _, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hb
      · rw [hadd, LinearIsometryEquiv.apply_symm_apply]
  have hvol (r : ℝ) : volume (f '' K + closedBall 0 r) = volume (K + closedBall 0 r) := by
    -- TauCeti's affine extension of volume preservation applies to arbitrary sets.
    have hm (s : Set (EuclideanSpace ℝ (Fin d))) :
        (volume.map f) s = volume (f ⁻¹' s) :=
      f.toHomeomorph.measurableEmbedding.map_apply volume s
    rw [← hoffset]
    calc
      volume (f '' (K + closedBall 0 r)) = (volume.map f) (f '' (K + closedBall 0 r)) := by
        rw [f.measurePreserving.map_eq]
      _ = volume (K + closedBall 0 r) := by rw [hm, Set.preimage_image_eq _ f.injective]
  have hp : steinerPolynomial (f '' K) = steinerPolynomial K := by
    rw [steinerPolynomial_def, steinerPolynomial_def]
    exact congrArg _ (funext fun i ↦ congrArg ENNReal.toReal (hvol i))
  simp only [intrinsicVolume_def, hp]

/-- SYNOPSIS item 114: `V_j` is homogeneous of degree `j`. -/
theorem intrinsicVolume_smul {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hKc : Convex ℝ K) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    intrinsicVolume j (t • K) = t ^ j * intrinsicVolume j K := by
  sorry

/-- SYNOPSIS item 115, Hadwiger's characterisation theorem: an additive, motion-invariant,
Hausdorff-continuous `ψ` is a linear combination `∑_{i=0}^d c_i V_i` on nonempty convex
bodies. -/
theorem hadwiger {ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ} (hval : IsConvexValuation ψ)
    (hmot : IsMotionInvariant ψ) (hcont : IsHausdorffContinuous ψ) :
    ∃ c : ℕ → ℝ, ∀ K, IsCompact K → Convex ℝ K → K.Nonempty →
      ψ K = ∑ i ∈ Finset.range (d + 1), c i * intrinsicVolume i K := by
  sorry

/-- SYNOPSIS item 115: an additive, motion-invariant `ψ` that is monotone on convex bodies is a
linear combination `∑_{i=0}^d c_i V_i` with `c_i ≥ 0` on nonempty convex bodies. -/
theorem hadwiger_monotone {ψ : Set (EuclideanSpace ℝ (Fin d)) → ℝ} (hval : IsConvexValuation ψ)
    (hmot : IsMotionInvariant ψ)
    (hmono : ∀ K M, IsCompact K → Convex ℝ K → IsCompact M → Convex ℝ M → K ⊆ M → ψ K ≤ ψ M) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ K, IsCompact K → Convex ℝ K → K.Nonempty →
      ψ K = ∑ i ∈ Finset.range (d + 1), c i * intrinsicVolume i K := by
  sorry

/-! ### Flats and the Crofton and kinematic formulas (SYNOPSIS items 116, 117) -/

/-- The action `x ↦ ϑ x` of an orthogonal matrix on `ℝ^d`. -/
def rotate (g : Matrix.orthogonalGroup (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((g : Matrix (Fin d) (Fin d) ℝ).mulVec (WithLp.ofLp x))

/-- `ν` is the **rotation-invariant probability**: a probability measure on the orthogonal
group invariant under left multiplication. -/
def IsRotationInvariant (ν : Measure (Matrix.orthogonalGroup (Fin d) ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ g, ν.map (g * ·) = ν

/-- The affine `k`-flat `L_0 + y` through the point with coordinates `y_i` for `i ≥ k`, with
`L_0` the span of the first `k` coordinate vectors. -/
def standardFlat (k : ℕ) (y : {i : Fin d // k ≤ i.val} → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, WithLp.ofLp x i.1 = y i}

/-- The affine `k`-flat `ϑ(L_0 + y)`. -/
def flat (k : ℕ) (g : Matrix.orthogonalGroup (Fin d) ℝ) (y : {i : Fin d // k ≤ i.val} → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  rotate g '' standardFlat k y

lemma rotate_def (g : Matrix.orthogonalGroup (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    rotate g x = WithLp.toLp 2 ((g : Matrix (Fin d) (Fin d) ℝ).mulVec (WithLp.ofLp x)) := by
  rw [rotate]

lemma isRotationInvariant_def {ν : Measure (Matrix.orthogonalGroup (Fin d) ℝ)} :
    IsRotationInvariant ν ↔ IsProbabilityMeasure ν ∧ ∀ g, ν.map (g * ·) = ν := Iff.rfl

lemma standardFlat_def (k : ℕ) (y : {i : Fin d // k ≤ i.val} → ℝ) :
    standardFlat k y = {x : EuclideanSpace ℝ (Fin d) | ∀ i, WithLp.ofLp x i.1 = y i} := by
  rw [standardFlat]

lemma flat_def (k : ℕ) (g : Matrix.orthogonalGroup (Fin d) ℝ) (y : {i : Fin d // k ≤ i.val} → ℝ) :
    flat k g y = rotate g '' standardFlat k y := by
  rw [flat]

/-- SYNOPSIS item 116, Crofton formula: for a convex body `K`, `1 ≤ k ≤ d - 1`, and `j ≤ k`,
`∫_{A(d,k)} V_j(K ∩ F) μ_k(dF) = c^{k, d-k+j}_{j, d} V_{d-k+j}(K)`. -/
theorem crofton {ν : Measure (Matrix.orthogonalGroup (Fin d) ℝ)} (hν : IsRotationInvariant ν)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKc : Convex ℝ K) {k j : ℕ}
    (hk1 : 1 ≤ k) (hkd : k + 1 ≤ d) (hj : j ≤ k) :
    ∫ g, ∫ y, intrinsicVolume j (K ∩ flat k g y) ∂volume ∂ν =
      kinematicConst k j * kinematicConst (d - k + j) d * intrinsicVolume (d - k + j) K := by
  sorry

/-- SYNOPSIS item 117, principal kinematic formula: for convex bodies `K`, `M` and `j ≤ d`,
`∫_{G_d} V_j(K ∩ gM) μ(dg) = ∑_{k=j}^d c^{k, d-k+j}_{j, d} V_k(K) V_{d-k+j}(M)`, with `μ` the
product of the rotation-invariant probability and Lebesgue measure on translations. -/
theorem principal_kinematic {ν : Measure (Matrix.orthogonalGroup (Fin d) ℝ)}
    (hν : IsRotationInvariant ν) {K M : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hM : IsCompact M) (hMc : Convex ℝ M) {j : ℕ} (hj : j ≤ d) :
    ∫ g, ∫ t, intrinsicVolume j (K ∩ ((· + t) '' (rotate g '' M))) ∂volume ∂ν =
      ∑ k ∈ Finset.Icc j d, kinematicConst k j * kinematicConst (d - k + j) d *
        intrinsicVolume k K * intrinsicVolume (d - k + j) M := by
  sorry

/-- SYNOPSIS item 117: for an additive Hausdorff-continuous `φ` with `φ(∅) = 0`,
`∫_{G_d} φ(K ∩ gM) μ(dg) = ∑_{k=0}^d φ_{d-k}(K) V_k(M)` with
`φ_{d-k}(K) = ∫_{A(d,k)} φ(K ∩ F) μ_k(dF)`. -/
theorem kinematic_valuation {ν : Measure (Matrix.orthogonalGroup (Fin d) ℝ)}
    (hν : IsRotationInvariant ν) {φ : Set (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hval : IsConvexValuation φ) (hcont : IsHausdorffContinuous φ) (hφ0 : φ ∅ = 0)
    {K M : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hM : IsCompact M) (hMc : Convex ℝ M) :
    ∫ g, ∫ t, φ (K ∩ ((· + t) '' (rotate g '' M))) ∂volume ∂ν =
      ∑ k ∈ Finset.range (d + 1),
        (∫ g, ∫ y, φ (K ∩ flat k g y) ∂volume ∂ν) * intrinsicVolume k M := by
  sorry

end MSSS
