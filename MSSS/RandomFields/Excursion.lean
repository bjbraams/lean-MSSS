module

public import MSSS.RandomFields.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType

/-!
# Level crossings and excursion sets of Gaussian processes

SYNOPSIS items 22 and 23: level crossings of Gaussian processes, the first Kac–Rice formula,
and the expected Euler characteristic of excursions on intervals and cubes.
The cube formula uses TauCeti's Euler characteristic for spaces of finite CW type.

## Main definitions

* `MSSS.upcrossings g u T`: the upcrossings of the level `u` by `g` in `[0, T]`.
* `MSSS.excursionComponents g u L`: the connected components of `{t ∈ [0, L] : g t ≥ u}`.

## Main results

All admitted.

* `MSSS.rice_formula`: SYNOPSIS item 22 (the stationary one-dimensional formula).
* `MSSS.lintegral_encard_levelSet`: SYNOPSIS item 22 in joint-density form.
* `MSSS.integral_eulerChar_excursion_cube`: SYNOPSIS item 23 on cubes.
* `MSSS.lintegral_encard_excursionComponents`: SYNOPSIS item 23 for `N = 1`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MSSS

/-- The **upcrossings** of the level `u` by `g` in `[0, T]`: points `t` with `g t = u` such that
`g < u` just before `t` and `g > u` just after `t`. -/
def upcrossings (g : ℝ → ℝ) (u T : ℝ) : Set ℝ :=
  {t ∈ Icc 0 T | g t = u ∧ ∃ ε > 0, (∀ s ∈ Ioo (t - ε) t, g s < u) ∧ ∀ s ∈ Ioo t (t + ε), u < g s}

/-- The connected components of the excursion set `{t ∈ [0, L] : g t ≥ u}`; their number is the
Euler characteristic of the excursion set. -/
def excursionComponents (g : ℝ → ℝ) (u L : ℝ) : Set (Set ℝ) :=
  {c | ∃ t ∈ {t ∈ Icc 0 L | u ≤ g t}, c = connectedComponentIn {t ∈ Icc 0 L | u ≤ g t} t}

lemma upcrossings_def (g : ℝ → ℝ) (u T : ℝ) : upcrossings g u T =
    {t ∈ Icc 0 T | g t = u ∧ ∃ ε > 0, (∀ s ∈ Ioo (t - ε) t, g s < u) ∧
      ∀ s ∈ Ioo t (t + ε), u < g s} := by
  rw [upcrossings]

lemma excursionComponents_def (g : ℝ → ℝ) (u L : ℝ) : excursionComponents g u L =
    {c | ∃ t ∈ {t ∈ Icc 0 L | u ≤ g t}, c = connectedComponentIn {t ∈ Icc 0 L | u ≤ g t} t} := by
  rw [excursionComponents]

/-- SYNOPSIS item 22, Rice's formula: for a centred stationary Gaussian process on `ℝ` with unit
variance, continuously differentiable sample paths, and second spectral moment
`λ₂ = Var f'(0)`, the expected number of upcrossings of `u` in `[0, T]` is
`T λ₂^{1/2} e^{-u²/2} / (2π)`. -/
theorem rice_formula {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℝ → Ω → ℝ} (hf : IsGaussianProcess f P) (hstat : IsSecondOrderStationary f P)
    (hc : ∀ t, P[f t] = 0) (hvar : Var[f 0; P] = 1) (hC1 : ∀ ω, ContDiff ℝ 1 fun t ↦ f t ω)
    (u : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (upcrossings (fun t ↦ f t ω) u T).encard ∂P =
      ENNReal.ofReal (T * Real.sqrt (Var[fun ω ↦ deriv (fun t ↦ f t ω) 0; P]) /
        (2 * Real.pi) * Real.exp (-u ^ 2 / 2)) := by
  sorry

/-- SYNOPSIS item 22, the first Kac–Rice formula in joint-density form.
The target level avoids boundary and critical values almost surely. The counts at nearby
levels have an integrable majorant, and the integrated determinant-weighted density is
continuous at the target. See Adler and Taylor (2007), §11.2, p. 267, and §11.4, p. 283. -/
theorem lintegral_encard_levelSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → Ω → EuclideanSpace ℝ (Fin n)}
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsCompact T) (u : EuclideanSpace ℝ (Fin n))
    (hC1 : ∀ᵐ ω ∂P, ContDiff ℝ 1 (fun t ↦ f t ω))
    (hreg : ∀ᵐ ω ∂P, ∀ t ∈ T, f t ω = u →
      t ∈ interior T ∧ LinearMap.det (fderiv ℝ (fun s ↦ f s ω) t).toLinearMap ≠ 0)
    (hcount : Measurable fun q : EuclideanSpace ℝ (Fin n) × Ω ↦
      {t ∈ T | f t q.2 = q.1}.encard)
    (p : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × (Fin n → Fin n → ℝ) → ℝ≥0∞)
    (hp : Measurable (Function.uncurry p))
    (hlaw : ∀ t ∈ T, HasLaw (fun ω ↦ (f t ω,
      fun i j ↦ LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ (fun s ↦ f s ω) t).toLinearMap
          i j))
      ((volume.prod volume).withDensity (p t)) P)
    (hdom : ∃ (δ : ℝ) (M : Ω → ℝ≥0∞), 0 < δ ∧ Measurable M ∧
      (∫⁻ ω, M ω ∂P) < ⊤ ∧
      ∀ᵐ ω ∂P, ∀ v ∈ Metric.ball u δ, ({t ∈ T | f t ω = v}.encard : ℝ≥0∞) ≤ M ω)
    (hcont : ContinuousAt (fun v ↦
      ∫⁻ t in T, ∫⁻ A, ENNReal.ofReal |(Matrix.of A).det| * p t (v, A) ∂volume ∂volume) u) :
    ∫⁻ ω, ({t ∈ T | f t ω = u}.encard : ℝ≥0∞) ∂P =
      ∫⁻ t in T, ∫⁻ A, ENNReal.ofReal |(Matrix.of A).det| * p t (u, A) ∂volume ∂volume := by
  sorry

/-- SYNOPSIS item 23 for `N = 1`: for a centred stationary Gaussian process on `ℝ` with variance
`σ² > 0`, continuously differentiable sample paths, and second spectral moment `λ₂`, the expected
Euler characteristic of the excursion set `{t ∈ [0, L] : f t ≥ u}` is
`Ψ(u/σ) + e^{-u²/(2σ²)} L λ₂^{1/2} / (2π σ)`, where `Ψ` is the standard Gaussian tail. -/
theorem lintegral_encard_excursionComponents {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ℝ → Ω → ℝ} (hf : IsGaussianProcess f P)
    (hstat : IsSecondOrderStationary f P) (hc : ∀ t, P[f t] = 0) {σ : ℝ} (hσ : 0 < σ)
    (hvar : Var[f 0; P] = σ ^ 2) (hC1 : ∀ ω, ContDiff ℝ 1 fun t ↦ f t ω) (u : ℝ) {L : ℝ}
    (hL : 0 ≤ L) :
    ∫⁻ ω, (excursionComponents (fun t ↦ f t ω) u L).encard ∂P =
      ENNReal.ofReal ((gaussianReal 0 1).real (Ici (u / σ)) +
        Real.exp (-u ^ 2 / (2 * σ ^ 2)) * L *
          Real.sqrt (Var[fun ω ↦ deriv (fun t ↦ f t ω) 0; P]) / (2 * Real.pi * σ)) := by
  sorry

section Cube

variable {n : ℕ}

/-- Differentiation along the `i`th coordinate direction. -/
def coordDeriv (i : Fin n) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (t : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ g t (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The coordinate derivative is the Fréchet derivative applied to a standard basis vector. -/
lemma coordDeriv_def (i : Fin n) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    coordDeriv i g t = fderiv ℝ g t (EuclideanSpace.basisFun (Fin n) ℝ i) := by rw [coordDeriv]

/-- The gradient and the upper-triangular entries of the Hessian, with each entry listed once. -/
def gradientHessian (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    Fin n ⊕ {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℝ :=
  Sum.elim (fun i ↦ coordDeriv i g t) (fun ij ↦ coordDeriv ij.1.1 (coordDeriv ij.1.2 g) t)

/-- The gradient entry of the vector of first and second coordinate derivatives. -/
lemma gradientHessian_inl (g : EuclideanSpace ℝ (Fin n) → ℝ) (t : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : gradientHessian g t (.inl i) = coordDeriv i g t := by
  simp only [gradientHessian, Sum.elim_inl]

/-- The Hessian entry of the vector of first and second coordinate derivatives. -/
lemma gradientHessian_inr (g : EuclideanSpace ℝ (Fin n) → ℝ) (t : EuclideanSpace ℝ (Fin n))
    (ij : {ij : Fin n × Fin n // ij.1 ≤ ij.2}) :
    gradientHessian g t (.inr ij) = coordDeriv ij.1.1 (coordDeriv ij.1.2 g) t := by
  simp only [gradientHessian, Sum.elim_inr]

open Classical in
/-- SYNOPSIS item 23, expected Euler characteristic on an isotropic Gaussian field's cube.
A mean-square Hölder bound on the Hessian supplies the logarithmic increment condition in
Adler and Taylor (2007), Corollary 11.3.2, p. 281. The formula is their Corollary 11.7.3,
p. 293. We use TauCeti's topological Euler characteristic on spaces of finite CW type; the
excursion set is assumed of finite CW type almost surely, and `χ` is its Euler characteristic
there and `0` elsewhere. The conclusion is that `χ` is integrable with the stated mean. -/
theorem integral_eulerChar_excursion_cube {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hn : 0 < n) {f : EuclideanSpace ℝ (Fin n) → Ω → ℝ}
    (hf : IsGaussianProcess f P) (hfm : Measurable (Function.uncurry f))
    (hc : ∀ t, P[f t] = 0) (hC2 : ∀ ω, ContDiff ℝ 2 (fun t ↦ f t ω))
    (hiso : ∃ K : ℝ → ℝ, ∀ s t, cov[f s, f t; P] = K (dist s t))
    {σ lambda₂ L : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hvar : Var[f 0; P] = σ ^ 2)
    (hLambda : ∀ i, Var[fun ω ↦ coordDeriv i (fun s ↦ f s ω) 0; P] = lambda₂)
    (hnd : ∀ t : EuclideanSpace ℝ (Fin n), (Matrix.of fun a b ↦
      cov[fun ω ↦ gradientHessian (fun s ↦ f s ω) t a,
        fun ω ↦ gradientHessian (fun s ↦ f s ω) t b; P]).PosDef)
    (hH : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ i j (s t : EuclideanSpace ℝ (Fin n)),
        (∫ ω, (coordDeriv i (coordDeriv j (fun v ↦ f v ω)) s -
          coordDeriv i (coordDeriv j (fun v ↦ f v ω)) t) ^ 2 ∂P) ≤ C * dist s t ^ α)
    (u : ℝ)
    (hCW : ∀ᵐ ω ∂P, TauCeti.FiniteCWType ↥{t : EuclideanSpace ℝ (Fin n) |
      (∀ i, t i ∈ Icc 0 L) ∧ u ≤ f t ω}) :
    let χ : Ω → ℝ := fun ω ↦
      if h : TauCeti.FiniteCWType ↥{t : EuclideanSpace ℝ (Fin n) |
          (∀ i, t i ∈ Icc 0 L) ∧ u ≤ f t ω} then
        letI := h
        (TauCeti.eulerChar ↥{t : EuclideanSpace ℝ (Fin n) | (∀ i, t i ∈ Icc 0 L) ∧ u ≤ f t ω} : ℝ)
      else 0
    Integrable χ P ∧ ∫ ω, χ ω ∂P =
      (gaussianReal 0 1).real (Ici (u / σ)) + Real.exp (-u ^ 2 / (2 * σ ^ 2)) *
        ∑ k ∈ Finset.Icc 1 n,
          ((n.choose k : ℝ) * L ^ k * lambda₂ ^ ((k : ℝ) / 2) *
            ((Polynomial.hermite (k - 1)).map (Int.castRingHom ℝ)).eval (u / σ)) /
          ((2 * Real.pi) ^ (((k : ℝ) + 1) / 2) * σ ^ k) := by
  sorry

end Cube

end MSSS
