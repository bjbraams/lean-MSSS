module

public import MSSS.Geostatistics.Kriging
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density

import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Gaussian likelihood for spatial linear models

SYNOPSIS items 42 and 44: consistency and asymptotic normality of maximum likelihood under
increasing-domain asymptotics (Mardia–Marshall), and restricted maximum likelihood.

The data are `𝐘 ∼ N(𝐗β, V(θ))` with `𝐗` of full column rank `q` and `V(θ)` positive definite. The
log-likelihood is `ℓ(β, θ) = -½ log det V(θ) - ½ (𝐘 - 𝐗β)ᵀ V(θ)⁻¹ (𝐘 - 𝐗β)` up to an additive
constant. Partial derivatives of the matrix function `V` are taken entrywise.

## Main definitions

* `MSSS.gaussianLaw m S`: the law `N(m, S)` as a measure on `ι → ℝ`.
* `MSSS.gaussianLogLik S r`: `-½ log det S - ½ rᵀ S⁻¹ r`.
* `MSSS.matrixPartial V i θ`: the entrywise partial derivative `∂V/∂θ_i`.
* `MSSS.frobeniusNorm M`: the Frobenius norm.
* `MSSS.HasConsistentNormalRoots X V β θ`: the conclusion of the Mardia–Marshall theorem.
* `MSSS.remlLogLik S X y`: the restricted log-likelihood.

## Main results

* `MSSS.mardia_marshall`, `MSSS.mardia_marshall_lattice`: SYNOPSIS item 42.
* `MSSS.map_mulVec_gaussianLaw_eq`, `MSSS.log_pdf_eq_remlLogLik`,
  `MSSS.log_pdf_sub_log_pdf_eq_const`, `MSSS.remlLogLik_iid_lt`: SYNOPSIS item 44.

The REML proofs use TauCeti's multivariate Gaussian density and Mathlib's block determinant
formulas and strict logarithm inequality.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Asymptotics
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace MSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian law `N(m, S)` as a measure on `ι → ℝ`. -/
def gaussianLaw (m : ι → ℝ) (S : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (multivariateGaussian (WithLp.toLp 2 m) S).map WithLp.ofLp

instance (m : ι → ℝ) (S : Matrix ι ι ℝ) : IsProbabilityMeasure (gaussianLaw m S) := by
  rw [gaussianLaw]
  infer_instance

/-- The Gaussian log-likelihood `-½ log det S - ½ rᵀ S⁻¹ r` of the residual `r`, up to an
additive constant. -/
def gaussianLogLik (S : Matrix ι ι ℝ) (r : ι → ℝ) : ℝ :=
  -(1 / 2) * Real.log S.det - (1 / 2) * (r ⬝ᵥ (S⁻¹ *ᵥ r))

lemma gaussianLaw_def (m : ι → ℝ) (S : Matrix ι ι ℝ) :
    gaussianLaw m S = (multivariateGaussian (WithLp.toLp 2 m) S).map WithLp.ofLp := by
  rw [gaussianLaw]

lemma gaussianLogLik_def (S : Matrix ι ι ℝ) (r : ι → ℝ) :
    gaussianLogLik S r = -(1 / 2) * Real.log S.det - (1 / 2) * (r ⬝ᵥ (S⁻¹ *ᵥ r)) := by
  rw [gaussianLogLik]

/-! ### The Mardia–Marshall theorem (SYNOPSIS item 42) -/

section MardiaMarshall

variable {p q : ℕ}

/-- The entrywise partial derivative `∂V/∂θ_i` of a matrix function of `θ ∈ ℝᵖ`. -/
def matrixPartial {κ : Type*} (V : (Fin p → ℝ) → Matrix κ κ ℝ) (i : Fin p) (θ : Fin p → ℝ) :
    Matrix κ κ ℝ :=
  Matrix.of fun a b ↦ fderiv ℝ (fun θ' ↦ V θ' a b) θ (Pi.single i 1)

/-- The Frobenius norm `(∑_{a,b} M_{ab}²)^{1/2}`. -/
def frobeniusNorm {κ : Type*} [Fintype κ] (M : Matrix κ κ ℝ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, M a b ^ 2)

omit [Fintype ι] [DecidableEq ι] in
lemma matrixPartial_apply (V : (Fin p → ℝ) → Matrix ι ι ℝ) (i : Fin p) (θ : Fin p → ℝ)
    (a b : ι) : matrixPartial V i θ a b = fderiv ℝ (fun θ' ↦ V θ' a b) θ (Pi.single i 1) := by
  rw [matrixPartial, Matrix.of_apply]

omit [DecidableEq ι] in
lemma frobeniusNorm_def (M : Matrix ι ι ℝ) :
    frobeniusNorm M = Real.sqrt (∑ a, ∑ b, M a b ^ 2) := by
  rw [frobeniusNorm]

/-- The conclusion of the Mardia–Marshall theorem for the models `N(𝐗_n β, V_n(θ))` at the true
parameter `(β, θ)`: there are measurable estimators `φ̂_n` that are roots of the likelihood
equations with probability tending to one, are weakly consistent, and satisfy
`B_n^{1/2} (φ̂_n - φ) ⇒ N(0, I_{q+p})`, where `B_n = diag(𝐗ᵀ V⁻¹ 𝐗, (½ tr(V⁻¹ V_i V⁻¹ V_j)))`
is the Fisher information. Convergence in distribution is tested on bounded continuous
functions. -/
def HasConsistentNormalRoots {κ : ℕ → Type*} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    (X : ∀ n, Matrix (κ n) (Fin q) ℝ) (V : ∀ n, (Fin p → ℝ) → Matrix (κ n) (κ n) ℝ)
    (β : Fin q → ℝ) (θ : Fin p → ℝ) : Prop :=
  ∃ φ : ∀ n, (κ n → ℝ) → (Fin q → ℝ) × (Fin p → ℝ), (∀ n, Measurable (φ n)) ∧
    Tendsto (fun n ↦ gaussianLaw (X n *ᵥ β) (V n θ)
      {y | fderiv ℝ (fun ψ : (Fin q → ℝ) × (Fin p → ℝ) ↦
        gaussianLogLik (V n ψ.2) (y - X n *ᵥ ψ.1)) (φ n y) ≠ 0}) atTop (𝓝 0) ∧
    (∀ ε > 0, Tendsto (fun n ↦ gaussianLaw (X n *ᵥ β) (V n θ)
      {y | ε ≤ dist (φ n y) (β, θ)}) atTop (𝓝 0)) ∧
    ∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin q ⊕ Fin p)) ℝ,
      Tendsto (fun n ↦ ∫ y, g (WithLp.toLp 2 (CFC.sqrt (Matrix.fromBlocks
          ((X n)ᵀ * (V n θ)⁻¹ * X n) 0 0 (Matrix.of fun i j ↦ (1 / 2) * ((V n θ)⁻¹ *
            matrixPartial (V n) i θ * (V n θ)⁻¹ * matrixPartial (V n) j θ).trace)) *ᵥ
          Sum.elim ((φ n y).1 - β) ((φ n y).2 - θ))) ∂gaussianLaw (X n *ᵥ β) (V n θ))
        atTop (𝓝 (∫ u, g u ∂stdGaussian (EuclideanSpace ℝ (Fin q ⊕ Fin p))))

/-- SYNOPSIS item 42, Mardia–Marshall theorem. For observation sets of sizes `n → ∞`, let
`𝐗_n` have full column rank, `V_n(θ)` be positive definite and twice continuously differentiable
on an open parameter set containing the true `θ`, and suppose that (i) the largest absolute
eigenvalues of `V`, `V_i`, `V_{ij}` at `θ` have finite limits, (ii)
`‖V_i‖_F^{-2} = O(n^{-1/2-δ})` for some `δ > 0`, (iii) the limits
`a_{ij} = lim t_{ij} / (t_{ii} t_{jj})^{1/2}`, `t_{ij} = tr(V⁻¹ V_i V⁻¹ V_j)`, exist and form a
nonsingular matrix, and (iv) `(𝐗ᵀ𝐗)⁻¹ → 0`. Then the likelihood equations have a weakly
consistent, asymptotically normal sequence of roots. -/
theorem mardia_marshall {κ : ℕ → Type*} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
    (X : ∀ n, Matrix (κ n) (Fin q) ℝ) (V : ∀ n, (Fin p → ℝ) → Matrix (κ n) (κ n) ℝ)
    {Θ : Set (Fin p → ℝ)} (hΘ : IsOpen Θ) (β : Fin q → ℝ) {θ : Fin p → ℝ} (hθ : θ ∈ Θ)
    (hcard : Tendsto (fun n ↦ Fintype.card (κ n)) atTop atTop)
    (hX : ∀ n, Function.Injective (X n).mulVec) (hV : ∀ n, ∀ θ' ∈ Θ, (V n θ').PosDef)
    (hVd : ∀ n, ContDiffOn ℝ 2 (fun θ' (a b : κ n) ↦ V n θ' a b) Θ)
    (h₁ : (∃ L, Tendsto (fun n ↦ ‖V n θ‖) atTop (𝓝 L)) ∧
      (∀ i, ∃ L, Tendsto (fun n ↦ ‖matrixPartial (V n) i θ‖) atTop (𝓝 L)) ∧
      ∀ i j, ∃ L, Tendsto (fun n ↦ ‖matrixPartial (matrixPartial (V n) j) i θ‖) atTop (𝓝 L))
    (h₂ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, (fun n ↦ (frobeniusNorm (matrixPartial (V n) i θ) ^ 2)⁻¹) =O[atTop]
      fun n ↦ (Fintype.card (κ n) : ℝ) ^ (-1 / 2 - δ))
    (h₃ : ∃ A : Matrix (Fin p) (Fin p) ℝ, A.det ≠ 0 ∧ ∀ i j, Tendsto (fun n ↦
      ((V n θ)⁻¹ * matrixPartial (V n) i θ * (V n θ)⁻¹ * matrixPartial (V n) j θ).trace /
        Real.sqrt (((V n θ)⁻¹ * matrixPartial (V n) i θ * (V n θ)⁻¹ *
            matrixPartial (V n) i θ).trace *
          ((V n θ)⁻¹ * matrixPartial (V n) j θ * (V n θ)⁻¹ * matrixPartial (V n) j θ).trace))
        atTop (𝓝 (A i j)))
    (h₄ : ∀ i j, Tendsto (fun n ↦ ((X n)ᵀ * X n)⁻¹ i j) atTop (𝓝 0)) :
    HasConsistentNormalRoots X V β θ := by
  sorry

/-- The lattice box `∏_k {0, …, L_k - 1} ⊆ ℕ^d`. -/
def latticeBox {d : ℕ} (L : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun k ↦ Finset.range (L k)

lemma latticeBox_def {d : ℕ} (L : Fin d → ℕ) :
    latticeBox L = Fintype.piFinset fun k ↦ Finset.range (L k) := by
  rw [latticeBox]

/-- SYNOPSIS item 42 on a lattice: for a stationary Gaussian field on `ℤ^d` observed on boxes
whose side lengths all tend to infinity, with covariance `c(θ, h)` whose values and first and
second `θ`-derivatives at the true `θ` are absolutely summable over `ℤ^d`, conditions (iii) and
(iv) give a weakly consistent, asymptotically normal sequence of roots of the likelihood
equations. -/
theorem mardia_marshall_lattice {d : ℕ} (L : ℕ → Fin d → ℕ)
    (hL : ∀ k, Tendsto (fun n ↦ L n k) atTop atTop)
    (X : ∀ n, Matrix (latticeBox (L n)) (Fin q) ℝ) (c : (Fin p → ℝ) → (Fin d → ℤ) → ℝ)
    {Θ : Set (Fin p → ℝ)} (hΘ : IsOpen Θ) (β : Fin q → ℝ) {θ : Fin p → ℝ} (hθ : θ ∈ Θ)
    (hX : ∀ n, Function.Injective (X n).mulVec)
    (hV : ∀ n, ∀ θ' ∈ Θ, (Matrix.of fun a b : latticeBox (L n) ↦
      c θ' fun k ↦ (a.1 k : ℤ) - b.1 k).PosDef)
    (hc : ∀ h, ContDiffOn ℝ 2 (fun θ' ↦ c θ' h) Θ)
    (hsum : Summable (fun h ↦ |c θ h|) ∧
      (∀ i, Summable fun h ↦ |fderiv ℝ (fun θ' ↦ c θ' h) θ (Pi.single i 1)|) ∧
      ∀ i j, Summable fun h ↦ |fderiv ℝ (fun θ'' ↦ fderiv ℝ (fun θ' ↦ c θ' h) θ''
        (Pi.single j 1)) θ (Pi.single i 1)|)
    (h₃ : let V : ∀ n, (Fin p → ℝ) → Matrix (latticeBox (L n)) (latticeBox (L n)) ℝ :=
        fun n θ' ↦ Matrix.of fun a b ↦ c θ' fun k ↦ (a.1 k : ℤ) - b.1 k
      ∃ A : Matrix (Fin p) (Fin p) ℝ, A.det ≠ 0 ∧ ∀ i j, Tendsto (fun n ↦
        ((V n θ)⁻¹ * matrixPartial (V n) i θ * (V n θ)⁻¹ * matrixPartial (V n) j θ).trace /
          Real.sqrt (((V n θ)⁻¹ * matrixPartial (V n) i θ * (V n θ)⁻¹ *
              matrixPartial (V n) i θ).trace *
            ((V n θ)⁻¹ * matrixPartial (V n) j θ * (V n θ)⁻¹ * matrixPartial (V n) j θ).trace))
          atTop (𝓝 (A i j)))
    (h₄ : ∀ i j, Tendsto (fun n ↦ ((X n)ᵀ * X n)⁻¹ i j) atTop (𝓝 0)) :
    HasConsistentNormalRoots X
      (fun n θ' ↦ Matrix.of fun a b : latticeBox (L n) ↦ c θ' fun k ↦ (a.1 k : ℤ) - b.1 k)
      β θ := by
  sorry

end MardiaMarshall

/-! ### Restricted maximum likelihood (SYNOPSIS item 44) -/

section REML

variable {q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The **restricted log-likelihood**
`-½ {log det S + log det(𝐗ᵀ S⁻¹ 𝐗) + (𝐲 - 𝐗β̃)ᵀ S⁻¹ (𝐲 - 𝐗β̃)}`, with `β̃` the generalised
least-squares estimate for `S`. -/
def remlLogLik (S : Matrix ι ι ℝ) (X : Matrix ι (Fin q) ℝ) (y : ι → ℝ) : ℝ :=
  -(1 / 2) * (Real.log S.det + Real.log (Xᵀ * S⁻¹ * X).det +
    (y - X *ᵥ (glsMatrix S X *ᵥ y)) ⬝ᵥ (S⁻¹ *ᵥ (y - X *ᵥ (glsMatrix S X *ᵥ y))))

lemma remlLogLik_def (S : Matrix ι ι ℝ) (X : Matrix ι (Fin q) ℝ) (y : ι → ℝ) :
    remlLogLik S X y = -(1 / 2) * (Real.log S.det + Real.log (Xᵀ * S⁻¹ * X).det +
      (y - X *ᵥ (glsMatrix S X *ᵥ y)) ⬝ᵥ (S⁻¹ *ᵥ (y - X *ᵥ (glsMatrix S X *ᵥ y)))) := by
  rw [remlLogLik]

-- Keep the index and covariance hypotheses in the existing interface.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- SYNOPSIS item 44: for `A` with `Aᵀ𝐗 = 0`, the law of `Aᵀ𝐘` does not depend on `β`. -/
theorem map_mulVec_gaussianLaw_eq (X : Matrix ι (Fin q) ℝ) (A : Matrix ι κ ℝ) (hA : Aᵀ * X = 0)
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (β : Fin q → ℝ) :
    (gaussianLaw (X *ᵥ β) S).map (fun y ↦ Aᵀ *ᵥ y) = (gaussianLaw 0 S).map (fun y ↦ Aᵀ *ᵥ y) := by
  have hmeas : Measurable (fun y : ι → ℝ ↦ Aᵀ *ᵥ y) := by
    apply Measurable.of_eval
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hOfLp : Measurable (WithLp.ofLp : EuclideanSpace ℝ ι → ι → ℝ) := by fun_prop
  simp only [gaussianLaw_def, multivariateGaussian, Measure.map_map hmeas hOfLp]
  rw [Measure.map_map (hmeas.comp hOfLp) (by fun_prop),
    Measure.map_map (hmeas.comp hOfLp) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, WithLp.ofLp_add, mulVec_add,
    mulVec_mulVec, hA, zero_mulVec, zero_add]

/-- Reindexing the rows of an equal-size rectangular matrix lets one evaluate a determinant of
its covariance pairing by the square-matrix product formula. -/
lemma det_transpose_mul_mul_of_equiv {R : Type*} [CommRing R] (e : κ ≃ ι)
    (U V : Matrix ι κ R) (S : Matrix ι ι R) :
    (Uᵀ * S * V).det = (U.submatrix e id).det * S.det * (V.submatrix e id).det := by
  have h : (U.submatrix e id)ᵀ * S.submatrix e e * V.submatrix e id = Uᵀ * S * V := by
    simp only [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id]
  rw [← h, det_mul, det_mul, det_transpose, det_submatrix_equiv_self]

omit [Fintype κ] [DecidableEq κ] in
/-- The columns of `S A` and `X` are orthogonal for the inverse-covariance pairing. -/
private lemma reml_contrast_blocks {S : Matrix ι ι ℝ} (hS : S.PosDef)
    {A : Matrix ι κ ℝ} {X : Matrix ι (Fin q) ℝ} (hA : Aᵀ * X = 0) :
    (Matrix.fromCols (S * A) X)ᵀ * S⁻¹ = Matrix.fromRows Aᵀ (Xᵀ * S⁻¹) ∧
      Matrix.fromRows Aᵀ (Xᵀ * S⁻¹) * Matrix.fromCols (S * A) X =
        Matrix.fromBlocks (Aᵀ * S * A) 0 0 (Xᵀ * S⁻¹ * X) := by
  have hSt : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hAt : Xᵀ * A = 0 := by
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose hA
  have hSunit := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  constructor
  · rw [transpose_fromCols, fromRows_mul, transpose_mul, hSt, Matrix.mul_assoc Aᵀ,
      mul_nonsing_inv _ hSunit, Matrix.mul_one]
  · rw [fromRows_mul_fromCols, hA, ← Matrix.mul_assoc Aᵀ,
      ← Matrix.mul_assoc (Xᵀ * S⁻¹), Matrix.mul_assoc Xᵀ S⁻¹ S,
      nonsing_inv_mul _ hSunit, Matrix.mul_one, hAt]

/-- The REML determinant factorisation. -/
private lemma reml_det_eq {S : Matrix ι ι ℝ} (hS : S.PosDef) {X : Matrix ι (Fin q) ℝ}
    (hX : Function.Injective X.mulVec) {A : Matrix ι κ ℝ} (hA : Aᵀ * X = 0)
    (hAr : Function.Injective A.mulVec) (hcard : Fintype.card κ + q = Fintype.card ι) :
    S.det * (Xᵀ * S⁻¹ * X).det =
      (Aᵀ * S * A).det * ((Xᵀ * X).det / (Aᵀ * A).det) := by
  let e : (κ ⊕ Fin q) ≃ ι := Fintype.equivOfCardEq (by simpa using hcard)
  let U := Matrix.fromCols A X
  let B := Matrix.fromCols (S * A) X
  let u := (U.submatrix e id).det
  let v := (B.submatrix e id).det
  let C := Aᵀ * S * A
  let G := Xᵀ * S⁻¹ * X
  have hAt : Xᵀ * A = 0 := by
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose hA
  have h₁ : (Aᵀ * A).det * (Xᵀ * X).det = u * u := by
    have h := det_transpose_mul_mul_of_equiv e U U 1
    dsimp only [U] at h
    rw [Matrix.mul_one, det_one, mul_one, transpose_fromCols, fromRows_mul_fromCols,
      hA, hAt, det_fromBlocks_zero₁₂] at h
    exact h
  have h₂ : C.det * (Xᵀ * X).det = u * v := by
    have h := det_transpose_mul_mul_of_equiv e U B 1
    dsimp only [U, B] at h
    rw [Matrix.mul_one, det_one, mul_one, transpose_fromCols, fromRows_mul_fromCols,
      hA, ← Matrix.mul_assoc Aᵀ, det_fromBlocks_zero₁₂] at h
    exact h
  have h₃ : C.det * G.det * S.det = v * v := by
    obtain ⟨ht, hm⟩ := reml_contrast_blocks hS hA
    have h := det_transpose_mul_mul_of_equiv e B B S⁻¹
    have dh : S⁻¹.det * S.det = 1 := det_nonsing_inv_mul_det S
      ((Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit)
    dsimp only [B] at h
    rw [ht, hm, det_fromBlocks_zero₁₂] at h
    calc
      _ = (v * S⁻¹.det * v) * S.det := congrArg (fun r : ℝ ↦ r * S.det) h
      _ = (v * v) * (S⁻¹.det * S.det) := by ring
      _ = v * v := by rw [dh, mul_one]
  have hAA : (Aᵀ * A).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
      (Matrix.PosDef.one (n := ι) (R := ℝ)).conjTranspose_mul_mul_same hAr
  have hXX : (Xᵀ * X).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
      (Matrix.PosDef.one (n := ι) (R := ℝ)).conjTranspose_mul_mul_same hX
  have hC : C.PosDef := by
    simpa only [C, conjTranspose_eq_transpose_of_trivial] using hS.conjTranspose_mul_mul_same hAr
  have heq : ((Aᵀ * A).det * (Xᵀ * X).det) * (C.det * G.det * S.det) =
      (C.det * (Xᵀ * X).det) * (C.det * (Xᵀ * X).det) := by rw [h₁, h₂, h₃]; ring
  rw [← mul_div_assoc]
  apply (eq_div_iff hAA.det_pos.ne').2
  apply (mul_right_cancel₀ (mul_ne_zero hC.det_pos.ne' hXX.det_pos.ne'))
  linear_combination heq

/-- The inverse-covariance squared norm of the GLS residual is the contrast quadratic form. -/
private lemma reml_quadratic_eq {S : Matrix ι ι ℝ} (hS : S.PosDef)
    {X : Matrix ι (Fin q) ℝ} (hX : Function.Injective X.mulVec) {A : Matrix ι κ ℝ}
    (hA : Aᵀ * X = 0) (hAr : Function.Injective A.mulVec)
    (hcard : Fintype.card κ + q = Fintype.card ι) (y : ι → ℝ) :
    let r := y - X *ᵥ (glsMatrix S X *ᵥ y)
    (r ⬝ᵥ (S⁻¹ *ᵥ r)) = (Aᵀ *ᵥ y) ⬝ᵥ ((Aᵀ * S * A)⁻¹ *ᵥ (Aᵀ *ᵥ y)) := by
  intro r
  let C := Aᵀ * S * A
  let G := Xᵀ * S⁻¹ * X
  let M := Matrix.fromRows Aᵀ (Xᵀ * S⁻¹)
  let B := Matrix.fromCols (S * A) X
  let z := Aᵀ *ᵥ y
  let w := C⁻¹ *ᵥ z
  have hC : C.PosDef := by
    simpa only [C, conjTranspose_eq_transpose_of_trivial] using hS.conjTranspose_mul_mul_same hAr
  have hG : G.PosDef := by
    simpa only [G, conjTranspose_eq_transpose_of_trivial] using
      hS.inv.conjTranspose_mul_mul_same hX
  have hCu := (Matrix.isUnit_iff_isUnit_det _).1 hC.isUnit
  have hGu := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  have hSunit := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  have hMB : M * B = Matrix.fromBlocks C 0 0 G := (reml_contrast_blocks hS hA).2
  have hMinj : Function.Injective M.mulVec := by
    have hdet : IsUnit (M * B).det := by
      rw [hMB, det_fromBlocks_zero₁₂]
      exact hCu.mul hGu
    have hdim : Module.finrank ℝ (ι → ℝ) = Module.finrank ℝ ((κ ⊕ Fin q) → ℝ) := by
      simpa only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin] using hcard.symm
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := M.mulVecLin) hdim).2 ?_
    intro u
    exact ⟨B *ᵥ ((M * B)⁻¹ *ᵥ u), by
      dsimp only [mulVecLin_apply]; rw [mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hdet,
        one_mulVec]⟩
  have hGr : G * glsMatrix S X = Xᵀ * S⁻¹ := by
    rw [glsMatrix_def, ← Matrix.mul_assoc G (G⁻¹ * Xᵀ), ← Matrix.mul_assoc G G⁻¹,
      mul_nonsing_inv _ hGu, Matrix.one_mul]
  have hrA : Aᵀ *ᵥ r = z := by
    dsimp only [r]
    rw [mulVec_sub, mulVec_mulVec, hA, zero_mulVec, sub_zero]
  have hrX : (Xᵀ * S⁻¹) *ᵥ r = 0 := by
    dsimp only [r]
    have hGr' : (Xᵀ * S⁻¹ * X) * glsMatrix S X = Xᵀ * S⁻¹ := hGr
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, hGr', sub_self]
  have hMr : M *ᵥ r = Sum.elim z 0 := by
    simp only [M, fromRows_mulVec, hrA, hrX]
  have hMw : M *ᵥ ((S * A) *ᵥ w) = Sum.elim z 0 := by
    have hMA : M * (S * A) = Matrix.fromRows C (0 : Matrix (Fin q) κ ℝ) := by
      have hAt : Xᵀ * A = 0 := by
        simpa only [transpose_mul, transpose_transpose, transpose_zero] using
          congrArg Matrix.transpose hA
      simp only [M, C, fromRows_mul, ← Matrix.mul_assoc (Xᵀ * S⁻¹),
        Matrix.mul_assoc Xᵀ S⁻¹, nonsing_inv_mul _ hSunit, Matrix.mul_one, hAt, Matrix.mul_assoc Aᵀ]
    rw [mulVec_mulVec, hMA, fromRows_mulVec, zero_mulVec]
    have hCw : C *ᵥ w = z := by
      dsimp only [w]
      rw [mulVec_mulVec, mul_nonsing_inv _ hCu, one_mulVec]
    rw [hCw]
  have hy := hMinj (hMr.trans hMw.symm)
  have hinv : S⁻¹ *ᵥ r = A *ᵥ w := by
    rw [hy, mulVec_mulVec, ← Matrix.mul_assoc, nonsing_inv_mul _ hSunit, Matrix.one_mul]
  rw [hinv, ← dotProduct_transpose_mulVec A, hrA, dotProduct_comm]

/-- SYNOPSIS item 44: let `𝐗` have rank `q` and let `A` be an `n × (n - q)` matrix of rank `n - q`
with `Aᵀ𝐗 = 0`. Up to an additive constant that depends on `A` and `𝐗` but not on `S` or the
data, the log-density of `Aᵀ𝐘 ∼ N(0, AᵀSA)` at `Aᵀ𝐲` is the restricted log-likelihood. -/
theorem log_pdf_eq_remlLogLik {X : Matrix ι (Fin q) ℝ} (hX : Function.Injective X.mulVec)
    {A : Matrix ι κ ℝ} (hA : Aᵀ * X = 0) (hAr : Function.Injective A.mulVec)
    (hcard : Fintype.card κ + q = Fintype.card ι) :
    ∃ c : ℝ, ∀ S : Matrix ι ι ℝ, S.PosDef → ∀ y : ι → ℝ,
      Real.log (TauCeti.Probability.multivariateGaussianPDFReal 0 (Aᵀ * S * A)
        (WithLp.toLp 2 (Aᵀ *ᵥ y))) = c + remlLogLik S X y := by
  have hXX : (Xᵀ * X).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
      (Matrix.PosDef.one (n := ι) (R := ℝ)).conjTranspose_mul_mul_same hX
  have hAA : (Aᵀ * A).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
      (Matrix.PosDef.one (n := ι) (R := ℝ)).conjTranspose_mul_mul_same hAr
  refine ⟨-(Fintype.card κ : ℝ) / 2 * Real.log (2 * Real.pi) +
    (1 / 2) * Real.log ((Xᵀ * X).det / (Aᵀ * A).det), ?_⟩
  intro S hS y
  let C := Aᵀ * S * A
  let G := Xᵀ * S⁻¹ * X
  have hC : C.PosDef := by
    simpa only [C, conjTranspose_eq_transpose_of_trivial] using hS.conjTranspose_mul_mul_same hAr
  have hCpos : 0 < (Aᵀ * S * A).det := hC.det_pos
  have hG : G.PosDef := by
    simpa only [G, conjTranspose_eq_transpose_of_trivial] using hS.inv.conjTranspose_mul_mul_same hX
  have hlogdet : Real.log S.det + Real.log G.det =
      Real.log C.det + Real.log ((Xᵀ * X).det / (Aᵀ * A).det) := by
    rw [← Real.log_mul hS.det_pos.ne' hG.det_pos.ne', reml_det_eq hS hX hA hAr hcard,
      Real.log_mul hC.det_pos.ne' (div_ne_zero hXX.det_pos.ne' hAA.det_pos.ne')]
  have hq := reml_quadratic_eq hS hX hA hAr hcard y
  dsimp only at hq
  rw [TauCeti.Probability.multivariateGaussianPDFReal_def, remlLogLik_def, hq]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hCpos _).ne',
    Real.log_rpow (by positivity), Real.log_rpow hCpos]
  simp only [sub_zero, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.ofLp_toLpLin, Matrix.toEuclideanLin, Matrix.toLin'_apply]
  have hlogdet' : Real.log S.det + Real.log (Xᵀ * S⁻¹ * X).det =
      Real.log (Aᵀ * S * A).det + Real.log ((Xᵀ * X).det / (Aᵀ * A).det) := hlogdet
  rw [hlogdet', dotProduct_comm ((Aᵀ * S * A)⁻¹ *ᵥ (Aᵀ *ᵥ y))]
  ring

/-- SYNOPSIS item 44: the restricted log-likelihoods obtained from two admissible matrices `A`
and `A'` differ by a constant, so the restricted maximum-likelihood estimator does not depend on
the choice of `A`. -/
theorem log_pdf_sub_log_pdf_eq_const {κ' : Type*} [Fintype κ'] [DecidableEq κ']
    {X : Matrix ι (Fin q) ℝ} (hX : Function.Injective X.mulVec) {A : Matrix ι κ ℝ}
    (hA : Aᵀ * X = 0) (hAr : Function.Injective A.mulVec)
    (hcard : Fintype.card κ + q = Fintype.card ι) {A' : Matrix ι κ' ℝ} (hA' : A'ᵀ * X = 0)
    (hAr' : Function.Injective A'.mulVec) (hcard' : Fintype.card κ' + q = Fintype.card ι) :
    ∃ c : ℝ, ∀ S : Matrix ι ι ℝ, S.PosDef → ∀ y : ι → ℝ,
      Real.log (TauCeti.Probability.multivariateGaussianPDFReal 0 (Aᵀ * S * A)
          (WithLp.toLp 2 (Aᵀ *ᵥ y))) -
        Real.log (TauCeti.Probability.multivariateGaussianPDFReal 0 (A'ᵀ * S * A')
          (WithLp.toLp 2 (A'ᵀ *ᵥ y))) = c := by
  obtain ⟨c, hc⟩ := log_pdf_eq_remlLogLik hX hA hAr hcard
  obtain ⟨c', hc'⟩ := log_pdf_eq_remlLogLik hX hA' hAr' hcard'
  exact ⟨c - c', fun S hS y ↦ by rw [hc S hS y, hc' S hS y]; ring⟩

/-- The inverse of a nonzero scalar multiple of the identity matrix. -/
lemma nonsing_inv_smul_one {R : Type*} [Field R] {s : R} (hs : s ≠ 0) :
    (s • (1 : Matrix ι ι R))⁻¹ = s⁻¹ • (1 : Matrix ι ι R) := by
  simpa only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, inv_one] using
    Matrix.inv_smul' (A := (1 : Matrix ι ι R)) (Units.mk0 s hs) (by simp)

/-- The restricted likelihood for independent observations with a common mean, evaluated
using the arithmetic mean and its residual sum of squares. -/
private lemma remlLogLik_iid_eq {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    remlLogLik (s • (1 : Matrix (Fin n) (Fin n) ℝ)) (Matrix.of fun _ (_ : Fin 1) ↦ 1) y =
      -(1 / 2) * (((n : ℝ) - 1) * Real.log s + Real.log n +
        (∑ i, (y i - (∑ j, y j) / n) ^ 2) / s) := by
  let X : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun _ _ ↦ 1
  let S : Matrix (Fin n) (Fin n) ℝ := s • 1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hXX : Xᵀ * X = (n : ℝ) • 1 := by
    ext i j
    simp [X, Matrix.mul_apply, Fin.eq_zero i, Fin.eq_zero j]
  have hS : S⁻¹ = s⁻¹ • 1 := nonsing_inv_smul_one hs.ne'
  have hgram : Xᵀ * S⁻¹ * X = (s⁻¹ * n) • 1 := by
    rw [hS, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hXX, smul_smul]
  have hL : glsMatrix S X = (n : ℝ)⁻¹ • Xᵀ := by
    rw [glsMatrix_def, hgram, nonsing_inv_smul_one (mul_ne_zero (inv_ne_zero hs.ne') hn'.ne'),
      hS, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    rw [mul_inv, inv_inv]
    congr 1
    field_simp
  have hF (i : Fin n) : (X *ᵥ (glsMatrix S X *ᵥ y)) i = (∑ j, y j) / n := by
    rw [hL, Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply]
    simp [X, Matrix.mulVec, dotProduct, div_eq_inv_mul]
  have hR : (y - X *ᵥ (glsMatrix S X *ᵥ y)) ⬝ᵥ
      (S⁻¹ *ᵥ (y - X *ᵥ (glsMatrix S X *ᵥ y))) = (∑ i, (y i - (∑ j, y j) / n) ^ 2) / s := by
    rw [hS, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, Pi.sub_apply, hF, smul_eq_mul, pow_two, div_eq_inv_mul]
  have hdet : S.det = s ^ n := by
    simp [S]
  rw [remlLogLik_def (S := S) (X := X), hR, hdet, hgram, Matrix.det_smul]
  simp only [Fintype.card_fin, Matrix.det_one, mul_one, pow_one]
  rw [Real.log_pow, Real.log_mul (inv_ne_zero hs.ne') hn'.ne', Real.log_inv]
  ring

/-- SYNOPSIS item 44: for independent errors with constant mean (`𝐗 = 𝟏`, `S = s I`), the
restricted log-likelihood has the unique maximiser `s = (n - 1)⁻¹ ∑ (y_i - ȳ)²` over `s > 0`,
for data that are not all equal. -/
theorem remlLogLik_iid_lt {n : ℕ} (hn : 2 ≤ n) (y : Fin n → ℝ) (hy : ∃ i j, y i ≠ y j)
    {s : ℝ} (hs : 0 < s)
    (hne : s ≠ (∑ i, (y i - (∑ j, y j) / n) ^ 2) / (n - 1)) :
    remlLogLik (s • (1 : Matrix (Fin n) (Fin n) ℝ)) (Matrix.of fun _ (_ : Fin 1) ↦ 1) y <
      remlLogLik (((∑ i, (y i - (∑ j, y j) / n) ^ 2) / (n - 1)) •
        (1 : Matrix (Fin n) (Fin n) ℝ)) (Matrix.of fun _ (_ : Fin 1) ↦ 1) y := by
  let R := ∑ i, (y i - (∑ j, y j) / n) ^ 2
  let k := (n : ℝ) - 1
  let s₀ := R / k
  have hR : 0 < R := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) ?_
    intro hzero
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg _).1 hzero.symm
    obtain ⟨i, j, hij⟩ := hy
    have heq (a : Fin n) : y a = (∑ j, y j) / n :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp (hz a (Finset.mem_univ a)))
    exact hij ((heq i).trans (heq j).symm)
  have hk : 0 < k := by
    dsimp only [k]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs₀ : 0 < s₀ := div_pos hR hk
  have hns₀ : s ≠ s₀ := hne
  have hne' : s₀ / s ≠ 1 := by
    intro h
    exact hns₀ (by simpa only [one_mul] using ((div_eq_iff hs.ne').mp h).symm)
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hs₀ hs) hne'
  rw [Real.log_div hs₀.ne' hs.ne'] at hlog
  have hineq := mul_lt_mul_of_pos_left hlog hk
  have hRs : k * (s₀ / s - 1) = R / s - R / s₀ := by
    have hR' : R = s₀ * k := (div_mul_cancel₀ R hk.ne').symm
    calc
      _ = (s₀ * k) / s - (s₀ * k) / s₀ := by field_simp
      _ = _ := by rw [← hR']
  rw [hRs] at hineq
  have hn' : 0 < n := by omega
  have hL := remlLogLik_iid_eq hn' y hs
  have hL₀ := remlLogLik_iid_eq hn' y hs₀
  convert (lt_of_eq_of_lt hL (lt_of_lt_of_eq ?_ hL₀.symm)) using 1
  dsimp only [k, R] at hineq
  linarith

end REML

end MSSS
