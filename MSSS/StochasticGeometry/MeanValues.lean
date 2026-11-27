module

public import MSSS.StochasticGeometry.IntegralGeometry
public import MSSS.StochasticGeometry.RandomClosedSets
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card

/-!
# Mean values for Boolean models and tessellations

SYNOPSIS items 119, 121, and 122: Miles' formulas for Boolean models, and mean values for
Poisson line, Poisson hyperplane, and Poisson–Voronoi tessellations.

For a Boolean model with convex grains, `V_j(Ξ ∩ B)` is computed by inclusion–exclusion over
the finitely many grains hitting `B` (`MSSS.booleanIntrinsicVolume`). A grain law is isotropic
when its capacity functional is rotation invariant (`MSSS.IsIsotropicGrainLaw`), which by the
Choquet–Matheron theorem means that the law is rotation invariant.

The `k`-faces of a hyperplane arrangement `A` are the connected components of
`⋂ J ∖ ⋃ (A ∖ J)` over sets `J ⊆ A` of `d - k` hyperplanes; the `k`-faces of the Voronoi
tessellation of a point set `N` are the connected components of the set of points with exactly
`d - k + 1` nearest points of `N`. Intensities are limits of mean numbers of faces hitting
`B(0, r)` divided by `|B(0, r)|`, and mean values for the typical face are limits of ratios of
mean sums over the faces hitting `B(0, r)` to mean numbers of such faces. Lengths and perimeters
are one-dimensional Hausdorff measures.

The statement that every vertex of a Poisson line tessellation has degree `4` is expressed as:
almost surely no point lies on three lines. That every vertex of a planar Poisson–Voronoi
tessellation lies on three cells is expressed as: almost surely no point has four nearest
nuclei.

## Main definitions

* `MSSS.unionIntrinsicVolume`, `MSSS.hitIndices`, `MSSS.booleanIntrinsicVolume`,
  `MSSS.grainMeanIntrinsicVolume`, `MSSS.IsIsotropicGrainLaw`.
* `MSSS.hyperplane u t`, `MSSS.arrangementFaces A k`, `MSSS.voronoiNearest N x`,
  `MSSS.voronoiFaces N k`.
* `MSSS.hitCount`, `MSSS.hitSum`, `MSSS.HasFaceIntensity`, `MSSS.HasTypicalMean`.
* `MSSS.lineArrangement η ω`, `MSSS.hyperplaneArrangement η ω`, `MSSS.zonoidSupport Θ u`,
  `MSSS.associatedZonoid Θ`, `MSSS.nuclei η ω`.

## Main results

All admitted.

* `MSSS.miles_densities`, `MSSS.miles_plane`, `MSSS.miles_space`: SYNOPSIS item 119.
* `MSSS.poissonLine_simple`, `MSSS.poissonLine_intensities`, `MSSS.poissonLine_typical`,
  `MSSS.poissonHyperplane_faceIntensity`: SYNOPSIS item 121.
* `MSSS.poissonVoronoi_cells`, `MSSS.poissonVoronoi_plane`, `MSSS.poissonVoronoi_space`:
  SYNOPSIS item 122.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric TopologicalSpace TauCeti.Probability
open scoped ENNReal Topology Pointwise

namespace MSSS

attribute [local instance] fellSigma

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-! ### Miles' formulas (SYNOPSIS item 119) -/

/-- The intrinsic volume of a union `⋃_{i ∈ S} G_i` of convex bodies by inclusion–exclusion:
`∑_{∅ ≠ I ⊆ S} (-1)^{|I|+1} V_j(⋂_{i ∈ I} G_i)`. -/
def unionIntrinsicVolume (j : ℕ) (S : Finset ℕ) (G : ℕ → Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∑ I ∈ S.powerset.filter (·.Nonempty), (-1) ^ (I.card + 1) * intrinsicVolume j (⋂ i ∈ I, G i)

open Classical in
/-- The indices `n < κ` of the grains `x_n + Ξ_n` that hit `B`, if finitely many; otherwise
`∅`. -/
def hitIndices (κ : Ω → ℕ∞) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin d))) (ω : Ω) (B : Set (EuclideanSpace ℝ (Fin d))) :
    Finset ℕ :=
  if h : {n : ℕ | (n : ℕ∞) < κ ω ∧
      ((· + x ω n) '' (G ω n : Set (EuclideanSpace ℝ (Fin d))) ∩ B).Nonempty}.Finite then
    h.toFinset else ∅

/-- The intrinsic volume `V_j(Ξ ∩ B)` of the Boolean model restricted to `B`. -/
def booleanIntrinsicVolume (j : ℕ) (κ : Ω → ℕ∞) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin d))) (ω : Ω) (B : Set (EuclideanSpace ℝ (Fin d))) :
    ℝ :=
  unionIntrinsicVolume j (hitIndices κ x G ω B)
    fun n ↦ (· + x ω n) '' (G ω n : Set (EuclideanSpace ℝ (Fin d))) ∩ B

/-- The mean intrinsic volume `E V_j(Ξ_0)` of a grain. -/
def grainMeanIntrinsicVolume (j : ℕ) (Q : Measure (Closeds (EuclideanSpace ℝ (Fin d)))) : ℝ :=
  ∫ F, intrinsicVolume j (F : Set (EuclideanSpace ℝ (Fin d))) ∂Q

/-- The grain law `Q` is **isotropic**: its capacity functional is rotation invariant. -/
def IsIsotropicGrainLaw (Q : Measure (Closeds (EuclideanSpace ℝ (Fin d)))) : Prop :=
  ∀ (g : Matrix.orthogonalGroup (Fin d) ℝ) (C : Set (EuclideanSpace ℝ (Fin d))), IsCompact C →
    Q {F | ((F : Set (EuclideanSpace ℝ (Fin d))) ∩ C).Nonempty} =
      Q {F | ((F : Set (EuclideanSpace ℝ (Fin d))) ∩ rotate g '' C).Nonempty}

lemma unionIntrinsicVolume_def (j : ℕ) (S : Finset ℕ) (G : ℕ → Set (EuclideanSpace ℝ (Fin d))) :
    unionIntrinsicVolume j S G = ∑ I ∈ S.powerset.filter (·.Nonempty),
      (-1) ^ (I.card + 1) * intrinsicVolume j (⋂ i ∈ I, G i) := by
  rw [unionIntrinsicVolume]

open Classical in
omit [MeasurableSpace Ω] in
lemma hitIndices_def (κ : Ω → ℕ∞) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin d))) (ω : Ω) (B : Set (EuclideanSpace ℝ (Fin d))) :
    hitIndices κ x G ω B = if h : {n : ℕ | (n : ℕ∞) < κ ω ∧
      ((· + x ω n) '' (G ω n : Set (EuclideanSpace ℝ (Fin d))) ∩ B).Nonempty}.Finite then
        h.toFinset else ∅ := by
  rw [hitIndices]

omit [MeasurableSpace Ω] in
lemma booleanIntrinsicVolume_def (j : ℕ) (κ : Ω → ℕ∞) (x : Ω → ℕ → EuclideanSpace ℝ (Fin d))
    (G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin d))) (ω : Ω) (B : Set (EuclideanSpace ℝ (Fin d))) :
    booleanIntrinsicVolume j κ x G ω B = unionIntrinsicVolume j (hitIndices κ x G ω B)
      fun n ↦ (· + x ω n) '' (G ω n : Set (EuclideanSpace ℝ (Fin d))) ∩ B := by
  rw [booleanIntrinsicVolume]

lemma grainMeanIntrinsicVolume_def (j : ℕ) (Q : Measure (Closeds (EuclideanSpace ℝ (Fin d)))) :
    grainMeanIntrinsicVolume j Q = ∫ F, intrinsicVolume j (F : Set (EuclideanSpace ℝ (Fin d))) ∂Q :=
  by rw [grainMeanIntrinsicVolume]

lemma isIsotropicGrainLaw_def {Q : Measure (Closeds (EuclideanSpace ℝ (Fin d)))} :
    IsIsotropicGrainLaw Q ↔ ∀ (g : Matrix.orthogonalGroup (Fin d) ℝ)
      (C : Set (EuclideanSpace ℝ (Fin d))), IsCompact C →
      Q {F | ((F : Set (EuclideanSpace ℝ (Fin d))) ∩ C).Nonempty} =
        Q {F | ((F : Set (EuclideanSpace ℝ (Fin d))) ∩ rotate g '' C).Nonempty} := Iff.rfl

/-- SYNOPSIS item 119: for a stationary Boolean model with nonempty convex grains and a convex
body `W` with `V_d(W) > 0`, the densities `V̄_j(Ξ) = lim_{r → ∞} E V_j(Ξ ∩ rW) / V_d(rW)` exist,
and with `V̄_j(X) = λ E V_j(Ξ_0)`, `V̄_d(Ξ) = 1 - e^{-V̄_d(X)}` and
`V̄_{d-1}(Ξ) = e^{-V̄_d(X)} V̄_{d-1}(X)`. -/
theorem miles_densities {P : Measure Ω} {κ : Ω → ℕ∞} {x : Ω → ℕ → EuclideanSpace ℝ (Fin d)}
    {G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin d))} {lam : ℝ}
    {Q : Measure (Closeds (EuclideanSpace ℝ (Fin d)))} (hB : IsBooleanModel P κ x G lam Q)
    (hconv : ∀ᵐ (F : Closeds (EuclideanSpace ℝ (Fin d))) ∂Q,
      Convex ℝ (F : Set (EuclideanSpace ℝ (Fin d))) ∧
      (F : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    {W : Set (EuclideanSpace ℝ (Fin d))} (hW : IsCompact W) (hWc : Convex ℝ W)
    (hW0 : 0 < volume W) (hd : 1 ≤ d) :
    ∃ Vbar : ℕ → ℝ, (∀ j, Tendsto (fun r : ℝ ↦ (∫ ω, booleanIntrinsicVolume j κ x G ω (r • W) ∂P) /
        (volume (r • W)).toReal) atTop (𝓝 (Vbar j))) ∧
      Vbar d = 1 - Real.exp (-(lam * grainMeanIntrinsicVolume d Q)) ∧
      Vbar (d - 1) = Real.exp (-(lam * grainMeanIntrinsicVolume d Q)) *
        (lam * grainMeanIntrinsicVolume (d - 1) Q) := by
  sorry

/-- SYNOPSIS item 119, Miles' formulas in the plane: for isotropic convex grains with mean area
`E A = E V_2(Ξ_0)` and mean perimeter `E L = 2 E V_1(Ξ_0)`, the area fraction, perimeter
density, and Euler characteristic density are `A_A = 1 - e^{-λ E A}`,
`L_A = λ e^{-λ E A} E L`, and `χ_A = e^{-λ E A} (λ - λ² (E L)² / (4π))`. -/
theorem miles_plane {P : Measure Ω} {κ : Ω → ℕ∞} {x : Ω → ℕ → EuclideanSpace ℝ (Fin 2)}
    {G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin 2))} {lam : ℝ}
    {Q : Measure (Closeds (EuclideanSpace ℝ (Fin 2)))} (hB : IsBooleanModel P κ x G lam Q)
    (hconv : ∀ᵐ (F : Closeds (EuclideanSpace ℝ (Fin 2))) ∂Q,
      Convex ℝ (F : Set (EuclideanSpace ℝ (Fin 2))) ∧
      (F : Set (EuclideanSpace ℝ (Fin 2))).Nonempty)
    (hiso : IsIsotropicGrainLaw Q) {W : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsCompact W)
    (hWc : Convex ℝ W) (hW0 : 0 < volume W) :
    let EA := grainMeanIntrinsicVolume 2 Q
    let EL := 2 * grainMeanIntrinsicVolume 1 Q
    let dens : ℕ → ℝ → ℝ := fun j r ↦
      (∫ ω, booleanIntrinsicVolume j κ x G ω (r • W) ∂P) / (volume (r • W)).toReal
    Tendsto (dens 2) atTop (𝓝 (1 - Real.exp (-(lam * EA)))) ∧
      Tendsto (fun r ↦ 2 * dens 1 r) atTop (𝓝 (lam * Real.exp (-(lam * EA)) * EL)) ∧
      Tendsto (dens 0) atTop
        (𝓝 (Real.exp (-(lam * EA)) * (lam - lam ^ 2 * EL ^ 2 / (4 * Real.pi)))) := by
  sorry

/-- SYNOPSIS item 119, Miles' formulas in space: for isotropic convex grains, with volume
`V = V_3`, surface area `S = 2 V_2`, integral of mean curvature `M = π V_1`, Euler
characteristic `χ = V_0`, and grain densities `V̄ = λ E V`, `S̄ = λ E S`, `M̄ = λ E M`,
`χ̄ = λ E χ`: `V_V = 1 - e^{-V̄}`, `S_V = e^{-V̄} S̄`, `M_V = e^{-V̄} (M̄ - π² S̄² / 32)`, and
`χ_V = e^{-V̄} (χ̄ - M̄ S̄ / (4π) + π S̄³ / 384)`. -/
theorem miles_space {P : Measure Ω} {κ : Ω → ℕ∞} {x : Ω → ℕ → EuclideanSpace ℝ (Fin 3)}
    {G : Ω → ℕ → Closeds (EuclideanSpace ℝ (Fin 3))} {lam : ℝ}
    {Q : Measure (Closeds (EuclideanSpace ℝ (Fin 3)))} (hB : IsBooleanModel P κ x G lam Q)
    (hconv : ∀ᵐ (F : Closeds (EuclideanSpace ℝ (Fin 3))) ∂Q,
      Convex ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) ∧
      (F : Set (EuclideanSpace ℝ (Fin 3))).Nonempty)
    (hiso : IsIsotropicGrainLaw Q) {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsCompact W)
    (hWc : Convex ℝ W) (hW0 : 0 < volume W) :
    let Vb := lam * grainMeanIntrinsicVolume 3 Q
    let Sb := lam * (2 * grainMeanIntrinsicVolume 2 Q)
    let Mb := lam * (Real.pi * grainMeanIntrinsicVolume 1 Q)
    let χb := lam * grainMeanIntrinsicVolume 0 Q
    let dens : ℕ → ℝ → ℝ := fun j r ↦
      (∫ ω, booleanIntrinsicVolume j κ x G ω (r • W) ∂P) / (volume (r • W)).toReal
    Tendsto (dens 3) atTop (𝓝 (1 - Real.exp (-Vb))) ∧
      Tendsto (fun r ↦ 2 * dens 2 r) atTop (𝓝 (Real.exp (-Vb) * Sb)) ∧
      Tendsto (fun r ↦ Real.pi * dens 1 r) atTop
        (𝓝 (Real.exp (-Vb) * (Mb - Real.pi ^ 2 / 32 * Sb ^ 2))) ∧
      Tendsto (dens 0) atTop (𝓝 (Real.exp (-Vb) *
        (χb - Mb * Sb / (4 * Real.pi) + Real.pi * Sb ^ 3 / 384))) := by
  sorry

/-! ### Tessellations -/

/-- The hyperplane `{x : ⟨x, u⟩ = t}`. -/
def hyperplane (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | inner ℝ x u = t}

/-- The `k`-faces of a hyperplane arrangement `A`: the connected components of
`⋂ J ∖ ⋃ (A ∖ J)` for sets `J ⊆ A` of `d - k` hyperplanes. -/
def arrangementFaces (A : Set (Set (EuclideanSpace ℝ (Fin d)))) (k : ℕ) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {F | ∃ J : Finset (Set (EuclideanSpace ℝ (Fin d))), (J : Set (Set _)) ⊆ A ∧ J.card + k = d ∧
    ∃ z ∈ ⋂₀ (J : Set (Set _)) \ ⋃₀ (A \ J),
      F = connectedComponentIn (⋂₀ (J : Set (Set _)) \ ⋃₀ (A \ J)) z}

/-- The points of `N` nearest to `x`. -/
def voronoiNearest (N : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {y ∈ N | ∀ y' ∈ N, dist x y ≤ dist x y'}

/-- The `k`-faces of the Voronoi tessellation of `N`: the connected components of the set of
points with exactly `d - k + 1` nearest points of `N`. -/
def voronoiFaces (N : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {F | ∃ z, (voronoiNearest N z).encard = (d - k + 1 : ℕ) ∧
    F = connectedComponentIn {x | (voronoiNearest N x).encard = (d - k + 1 : ℕ)} z}

/-- The number of members of `S` that hit `B`. -/
def hitCount (S : Set (Set (EuclideanSpace ℝ (Fin d)))) (B : Set (EuclideanSpace ℝ (Fin d))) :
    ℝ≥0∞ :=
  ({F ∈ S | (F ∩ B).Nonempty}.encard : ℝ≥0∞)

/-- The sum of `f` over the members of `S` that hit `B`. -/
def hitSum (S : Set (Set (EuclideanSpace ℝ (Fin d)))) (B : Set (EuclideanSpace ℝ (Fin d)))
    (f : Set (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' F : {F ∈ S | (F ∩ B).Nonempty}, f F

/-- The random family of faces `S` has **intensity** `γ`: the mean number of faces hitting
`B(0, r)` divided by `|B(0, r)|` tends to `γ`. -/
def HasFaceIntensity (P : Measure Ω) (S : Ω → Set (Set (EuclideanSpace ℝ (Fin d)))) (γ : ℝ) :
    Prop :=
  Tendsto (fun r : ℝ ↦ (∫⁻ ω, hitCount (S ω) (closedBall 0 r) ∂P).toReal /
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)).toReal) atTop (𝓝 γ)

/-- The **typical face** of `S` has mean value `m` of `f` (which may depend on the whole
configuration): the ratio of the mean sum of `f`
over the faces hitting `B(0, r)` to the mean number of such faces tends to `m`. -/
def HasTypicalMean (P : Measure Ω) (S : Ω → Set (Set (EuclideanSpace ℝ (Fin d))))
    (f : Ω → Set (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞) (m : ℝ) : Prop :=
  Tendsto (fun r : ℝ ↦ (∫⁻ ω, hitSum (S ω) (closedBall 0 r) (f ω) ∂P).toReal /
    (∫⁻ ω, hitCount (S ω) (closedBall 0 r) ∂P).toReal) atTop (𝓝 m)

lemma hyperplane_def (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    hyperplane u t = {x | inner ℝ x u = t} := by
  rw [hyperplane]

lemma arrangementFaces_def (A : Set (Set (EuclideanSpace ℝ (Fin d)))) (k : ℕ) :
    arrangementFaces A k = {F | ∃ J : Finset (Set (EuclideanSpace ℝ (Fin d))),
      (J : Set (Set _)) ⊆ A ∧ J.card + k = d ∧ ∃ z ∈ ⋂₀ (J : Set (Set _)) \ ⋃₀ (A \ J),
        F = connectedComponentIn (⋂₀ (J : Set (Set _)) \ ⋃₀ (A \ J)) z} := by
  rw [arrangementFaces]

lemma voronoiNearest_def (N : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    voronoiNearest N x = {y ∈ N | ∀ y' ∈ N, dist x y ≤ dist x y'} := by
  rw [voronoiNearest]

lemma voronoiFaces_def (N : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    voronoiFaces N k = {F | ∃ z, (voronoiNearest N z).encard = (d - k + 1 : ℕ) ∧
      F = connectedComponentIn {x | (voronoiNearest N x).encard = (d - k + 1 : ℕ)} z} := by
  rw [voronoiFaces]

lemma hitCount_def (S : Set (Set (EuclideanSpace ℝ (Fin d)))) (B : Set (EuclideanSpace ℝ (Fin d))) :
    hitCount S B = ({F ∈ S | (F ∩ B).Nonempty}.encard : ℝ≥0∞) := by
  rw [hitCount]

lemma hitSum_def (S : Set (Set (EuclideanSpace ℝ (Fin d)))) (B : Set (EuclideanSpace ℝ (Fin d)))
    (f : Set (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞) :
    hitSum S B f = ∑' F : {F ∈ S | (F ∩ B).Nonempty}, f F := by
  rw [hitSum]

lemma hasFaceIntensity_def {P : Measure Ω} {S : Ω → Set (Set (EuclideanSpace ℝ (Fin d)))}
    {γ : ℝ} : HasFaceIntensity P S γ ↔
      Tendsto (fun r : ℝ ↦ (∫⁻ ω, hitCount (S ω) (closedBall 0 r) ∂P).toReal /
        (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r)).toReal) atTop (𝓝 γ) := Iff.rfl

lemma hasTypicalMean_def {P : Measure Ω} {S : Ω → Set (Set (EuclideanSpace ℝ (Fin d)))}
    {f : Ω → Set (EuclideanSpace ℝ (Fin d)) → ℝ≥0∞} {m : ℝ} : HasTypicalMean P S f m ↔
      Tendsto (fun r : ℝ ↦ (∫⁻ ω, hitSum (S ω) (closedBall 0 r) (f ω) ∂P).toReal /
        (∫⁻ ω, hitCount (S ω) (closedBall 0 r) ∂P).toReal) atTop (𝓝 m) := Iff.rfl

/-! ### Poisson line and hyperplane tessellations (SYNOPSIS item 121) -/

/-- The lines `{x : x_1 cos θ + x_2 sin θ = p}` for the atoms `(p, θ)` of `η ω`. -/
def lineArrangement (η : Ω → Measure (ℝ × ℝ)) (ω : Ω) : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  (fun z : ℝ × ℝ ↦ hyperplane (WithLp.toLp 2 ![Real.cos z.2, Real.sin z.2]) z.1) ''
    {z | η ω {z} ≠ 0}

/-- The hyperplanes `{x : ⟨x, u⟩ = t}` for the atoms `(u, t)` of `η ω`. -/
def hyperplaneArrangement (η : Ω → Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (ω : Ω) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  (fun z ↦ hyperplane z.1 z.2) '' {z | η ω {z} ≠ 0}

/-- The support function `h(Π, u) = ½ Θ({(v, t) : H(v, t) meets [0, u]})` of the associated
zonoid: half the mean number of hyperplanes hitting the segment `[0, u]`. -/
def zonoidSupport (Θ : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (u : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  (Θ {z | ∃ s ∈ Icc (0 : ℝ) 1, s * inner ℝ u z.1 = z.2}).toReal / 2

/-- The **associated zonoid** `Π = {x : ⟨x, u⟩ ≤ h(Π, u) for all u}`. -/
def associatedZonoid (Θ : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ u, inner ℝ x u ≤ zonoidSupport Θ u}

omit [MeasurableSpace Ω] in
lemma lineArrangement_def (η : Ω → Measure (ℝ × ℝ)) (ω : Ω) : lineArrangement η ω =
    (fun z : ℝ × ℝ ↦ hyperplane (WithLp.toLp 2 ![Real.cos z.2, Real.sin z.2]) z.1) ''
      {z | η ω {z} ≠ 0} := by
  rw [lineArrangement]

omit [MeasurableSpace Ω] in
lemma hyperplaneArrangement_def (η : Ω → Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (ω : Ω) :
    hyperplaneArrangement η ω = (fun z ↦ hyperplane z.1 z.2) '' {z | η ω {z} ≠ 0} := by
  rw [hyperplaneArrangement]

lemma zonoidSupport_def (Θ : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    (u : EuclideanSpace ℝ (Fin d)) :
    zonoidSupport Θ u = (Θ {z | ∃ s ∈ Icc (0 : ℝ) 1, s * inner ℝ u z.1 = z.2}).toReal / 2 := by
  rw [zonoidSupport]

lemma associatedZonoid_def (Θ : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    associatedZonoid Θ = {x | ∀ u, inner ℝ x u ≤ zonoidSupport Θ u} := by
  rw [associatedZonoid]

/-- SYNOPSIS item 121: for the motion-invariant Poisson line process with `ϱ > 0` lines hitting a
unit segment on average (intensity `ϱ/2` in the parameters `(p, θ) ∈ ℝ × [0, π)`), almost surely
no point lies on three lines, so that every vertex has degree `4`. -/
theorem poissonLine_simple {P : Measure Ω} [IsProbabilityMeasure P] {η : Ω → Measure (ℝ × ℝ)}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hη : IsPoissonRandomMeasure P η
      (ENNReal.ofReal (ρ / 2) • volume.restrict (univ ×ˢ Ico 0 Real.pi))) :
    ∀ᵐ ω ∂P, ∀ v : EuclideanSpace ℝ (Fin 2), {L ∈ lineArrangement η ω | v ∈ L}.encard ≤ 2 := by
  sorry

/-- SYNOPSIS item 121: the intensities of vertices, edges, and cells of the Poisson line
tessellation are `π ϱ² / 4`, `π ϱ² / 2`, and `π ϱ² / 4`. -/
theorem poissonLine_intensities {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (ℝ × ℝ)} {ρ : ℝ} (hρ : 0 < ρ)
    (hη : IsPoissonRandomMeasure P η
      (ENNReal.ofReal (ρ / 2) • volume.restrict (univ ×ˢ Ico 0 Real.pi))) :
    HasFaceIntensity P (fun ω ↦ arrangementFaces (lineArrangement η ω) 0) (Real.pi * ρ ^ 2 / 4) ∧
      HasFaceIntensity P (fun ω ↦ arrangementFaces (lineArrangement η ω) 1)
        (Real.pi * ρ ^ 2 / 2) ∧
      HasFaceIntensity P (fun ω ↦ arrangementFaces (lineArrangement η ω) 2)
        (Real.pi * ρ ^ 2 / 4) := by
  sorry

/-- SYNOPSIS item 121: the mean edge length is `1/ϱ`, and the typical cell has mean area
`4 / (π ϱ²)`, mean perimeter `4/ϱ`, mean number of vertices `4`, and mean squared area
`8 / ϱ⁴`. -/
theorem poissonLine_typical {P : Measure Ω} [IsProbabilityMeasure P] {η : Ω → Measure (ℝ × ℝ)}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hη : IsPoissonRandomMeasure P η
      (ENNReal.ofReal (ρ / 2) • volume.restrict (univ ×ˢ Ico 0 Real.pi))) :
    HasTypicalMean P (fun ω ↦ arrangementFaces (lineArrangement η ω) 1)
        (fun _ F ↦ Measure.hausdorffMeasure 1 F) (1 / ρ) ∧
      HasTypicalMean P (fun ω ↦ arrangementFaces (lineArrangement η ω) 2) (fun _ F ↦ volume F)
        (4 / (Real.pi * ρ ^ 2)) ∧
      HasTypicalMean P (fun ω ↦ arrangementFaces (lineArrangement η ω) 2)
        (fun _ F ↦ Measure.hausdorffMeasure 1 (frontier F)) (4 / ρ) ∧
      HasTypicalMean P (fun ω ↦ arrangementFaces (lineArrangement η ω) 2)
        (fun ω F ↦ ({v | {v} ∈ arrangementFaces (lineArrangement η ω) 0 ∧
          v ∈ closure F}.encard : ℝ≥0∞)) 4 ∧
      HasTypicalMean P (fun ω ↦ arrangementFaces (lineArrangement η ω) 2)
        (fun _ F ↦ volume F ^ 2) (8 / ρ ^ 4) := by
  sorry

/-- SYNOPSIS item 121: for a stationary Poisson hyperplane process with intensity measure `Θ` on
the parameters `(u, t)`, `‖u‖ = 1`, whose directions are not concentrated on a great subsphere,
the intensity of `k`-faces of the tessellation is `(d choose k) V_d(Π)`, `Π` the associated
zonoid. -/
theorem poissonHyperplane_faceIntensity {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    {Θ : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} (hη : IsPoissonRandomMeasure P η Θ)
    (hunit : ∀ᵐ z ∂Θ, ‖z.1‖ = 1)
    (hstat : ∀ y, Θ.map (fun z ↦ (z.1, z.2 + inner ℝ y z.1)) = Θ)
    (hfin : ∀ r : ℝ, Θ {z | |z.2| ≤ r} < ∞)
    (hnd : ∀ w : EuclideanSpace ℝ (Fin d), w ≠ 0 → 0 < Θ {z | inner ℝ z.1 w ≠ 0})
    (hpos : 0 < Θ univ) {k : ℕ} (hk : k ≤ d) :
    HasFaceIntensity P (fun ω ↦ arrangementFaces (hyperplaneArrangement η ω) k)
      (d.choose k * (volume (associatedZonoid Θ)).toReal) := by
  sorry

/-! ### Poisson–Voronoi tessellations (SYNOPSIS item 122) -/

/-- The atoms of `η ω`. -/
def nuclei (η : Ω → Measure (EuclideanSpace ℝ (Fin d))) (ω : Ω) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | η ω {y} ≠ 0}

omit [MeasurableSpace Ω] in
lemma nuclei_def (η : Ω → Measure (EuclideanSpace ℝ (Fin d))) (ω : Ω) :
    nuclei η ω = {y | η ω {y} ≠ 0} := by
  rw [nuclei]

/-- SYNOPSIS item 122: for the Voronoi tessellation of a stationary Poisson process of intensity
`γ > 0` in `ℝ^d`, the cell intensity is `γ` and the typical cell has mean volume `1/γ`. -/
theorem poissonVoronoi_cells (hd : 1 ≤ d) {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} {γ : ℝ} (hγ : 0 < γ)
    (hη : IsPoissonRandomMeasure P η (ENNReal.ofReal γ • volume)) :
    HasFaceIntensity P (fun ω ↦ voronoiFaces (nuclei η ω) d) γ ∧
      HasTypicalMean P (fun ω ↦ voronoiFaces (nuclei η ω) d) (fun _ F ↦ volume F)
        (1 / γ) := by
  sorry

/-- SYNOPSIS item 122, the plane: almost surely no point has four nearest nuclei, so every
vertex lies on three cells; the vertex and edge intensities are `2γ` and `3γ`; the typical cell
has on average `6` vertices and mean perimeter `4/√γ`; the mean edge length is `2/(3√γ)`; and
the edge length per unit area is `2√γ`. -/
theorem poissonVoronoi_plane {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin 2))} {γ : ℝ} (hγ : 0 < γ)
    (hη : IsPoissonRandomMeasure P η (ENNReal.ofReal γ • volume)) :
    (∀ᵐ ω ∂P, ∀ x, (voronoiNearest (nuclei η ω) x).encard ≤ 3) ∧
      HasFaceIntensity P (fun ω ↦ voronoiFaces (nuclei η ω) 0) (2 * γ) ∧
      HasFaceIntensity P (fun ω ↦ voronoiFaces (nuclei η ω) 1) (3 * γ) ∧
      HasTypicalMean P (fun ω ↦ voronoiFaces (nuclei η ω) 2)
        (fun ω F ↦ ({v | {v} ∈ voronoiFaces (nuclei η ω) 0 ∧ v ∈ closure F}.encard : ℝ≥0∞)) 6 ∧
      HasTypicalMean P (fun ω ↦ voronoiFaces (nuclei η ω) 2)
        (fun _ F ↦ Measure.hausdorffMeasure 1 (frontier F)) (4 / Real.sqrt γ) ∧
      HasTypicalMean P (fun ω ↦ voronoiFaces (nuclei η ω) 1)
        (fun _ F ↦ Measure.hausdorffMeasure 1 F) (2 / (3 * Real.sqrt γ)) ∧
      Tendsto (fun r : ℝ ↦ (∫⁻ ω, Measure.hausdorffMeasure 1
          (⋃₀ voronoiFaces (nuclei η ω) 1 ∩ closedBall 0 r) ∂P).toReal /
        (volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) r)).toReal)
        atTop (𝓝 (2 * Real.sqrt γ)) := by
  sorry

/-- SYNOPSIS item 122, space: the vertex, edge, and face intensities of the Poisson–Voronoi
tessellation in `ℝ³` are `24π²/35 γ`, `48π²/35 γ`, and `(24π²/35 + 1) γ`. -/
theorem poissonVoronoi_space {P : Measure Ω} [IsProbabilityMeasure P]
    {η : Ω → Measure (EuclideanSpace ℝ (Fin 3))} {γ : ℝ} (hγ : 0 < γ)
    (hη : IsPoissonRandomMeasure P η (ENNReal.ofReal γ • volume)) :
    HasFaceIntensity P (fun ω ↦ voronoiFaces (nuclei η ω) 0) (24 * Real.pi ^ 2 / 35 * γ) ∧
      HasFaceIntensity P (fun ω ↦ voronoiFaces (nuclei η ω) 1) (48 * Real.pi ^ 2 / 35 * γ) ∧
      HasFaceIntensity P (fun ω ↦ voronoiFaces (nuclei η ω) 2)
        ((24 * Real.pi ^ 2 / 35 + 1) * γ) := by
  sorry

end MSSS
