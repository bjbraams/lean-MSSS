module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.Gaussian.Multivariate

/-!
# Second-order random fields and Gaussian fields

Basic vocabulary for real random fields indexed by a set `T`: second-order fields,
second-order stationarity on an additive group, mean-square continuity, and the existence and
uniqueness of Gaussian fields with prescribed mean and covariance.

A random field is a family `Z : T → Ω → ℝ` of real random variables on one probability space.
A real covariance kernel `C : T → T → ℝ` is symmetric and positive definite exactly when the
infinite matrix `Matrix.of C` is positive semidefinite in Mathlib's sense (finitely supported
coefficient vectors), which is the formulation used here.

## Main definitions

* `MSSS.IsSecondOrderField Z P`: every `Z t` is square integrable.
* `MSSS.IsSecondOrderStationary Z P`: a second-order field on an additive group with constant
  mean and translation-invariant covariance.
* `MSSS.stationaryCov Z P h`: the stationary covariance `C(h) = Cov(Z h, Z 0)`.
* `MSSS.IsMeanSquareContinuous Z P`: `E (Z t - Z s)² → 0` as `t → s`.

## Main results

* `MSSS.exists_isGaussianProcess_coord`: SYNOPSIS item 2, existence.
* `MSSS.map_eq_of_isGaussianProcess`: SYNOPSIS item 2, uniqueness of the law.
* `MSSS.posSemidef_covariance`: SYNOPSIS item 2, the converse.

The construction uses Mathlib's Kolmogorov extension theorem and restriction of multivariate
Gaussian laws, as in Mathlib's Brownian Gaussian projective family. Uniqueness uses
TauCeti's characterization of a finite-dimensional Gaussian law by its coordinate moments.
Covariance positivity uses Mathlib's variance formula for a finite sum.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MSSS

variable {Ω T : Type*} [MeasurableSpace Ω]

/-- A **second-order field**: every `Z t` is square integrable. -/
def IsSecondOrderField (Z : T → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ t, MemLp (Z t) 2 P

/-- A **second-order stationary field** on an additive group: second order, with constant mean
and covariance invariant under translation of both arguments. -/
def IsSecondOrderStationary {G : Type*} [AddCommGroup G] (Z : G → Ω → ℝ) (P : Measure Ω) :
    Prop :=
  IsSecondOrderField Z P ∧ (∀ s t, P[Z s] = P[Z t]) ∧
    ∀ s t h, cov[Z (s + h), Z (t + h); P] = cov[Z s, Z t; P]

/-- The **stationary covariance** `C(h) = Cov(Z h, Z 0)` of a field on an additive group. -/
def stationaryCov {G : Type*} [AddCommGroup G] (Z : G → Ω → ℝ) (P : Measure Ω) (h : G) : ℝ :=
  cov[Z h, Z 0; P]

/-- A field on a topological space is **mean-square continuous** when
`E (Z t - Z s)² → 0` as `t → s`, for every `s`. -/
def IsMeanSquareContinuous [TopologicalSpace T] (Z : T → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ s, Tendsto (fun t ↦ ∫ ω, (Z t ω - Z s ω) ^ 2 ∂P) (𝓝 s) (𝓝 0)

lemma isSecondOrderField_iff {Z : T → Ω → ℝ} {P : Measure Ω} :
    IsSecondOrderField Z P ↔ ∀ t, MemLp (Z t) 2 P := Iff.rfl

lemma isSecondOrderStationary_iff {G : Type*} [AddCommGroup G] {Z : G → Ω → ℝ}
    {P : Measure Ω} :
    IsSecondOrderStationary Z P ↔ IsSecondOrderField Z P ∧ (∀ s t, P[Z s] = P[Z t]) ∧
      ∀ s t h, cov[Z (s + h), Z (t + h); P] = cov[Z s, Z t; P] := Iff.rfl

lemma stationaryCov_def {G : Type*} [AddCommGroup G] (Z : G → Ω → ℝ) (P : Measure Ω) (h : G) :
    stationaryCov Z P h = cov[Z h, Z 0; P] := by
  rw [stationaryCov]

lemma isMeanSquareContinuous_iff [TopologicalSpace T] {Z : T → Ω → ℝ} {P : Measure Ω} :
    IsMeanSquareContinuous Z P ↔
      ∀ s, Tendsto (fun t ↦ ∫ ω, (Z t ω - Z s ω) ^ 2 ∂P) (𝓝 s) (𝓝 0) := Iff.rfl

/-! ### Gaussian fields with given mean and covariance (SYNOPSIS item 2) -/

/-- SYNOPSIS item 2, existence: for every mean function `m` and every symmetric positive
definite kernel `C` there is a Gaussian field with mean `m` and covariance `C`, realised as the
coordinate process on `T → ℝ`. -/
theorem exists_isGaussianProcess_coord (m : T → ℝ) (C : T → T → ℝ)
    (hC : (Matrix.of C).PosSemidef) :
    ∃ P : Measure (T → ℝ), IsProbabilityMeasure P ∧
      IsGaussianProcess (fun t (ω : T → ℝ) ↦ ω t) P ∧
      (∀ t, ∫ ω, ω t ∂P = m t) ∧
      ∀ s t, cov[fun ω : T → ℝ ↦ ω s, fun ω ↦ ω t; P] = C s t := by
  classical
  let S (I : Finset T) : Matrix I I ℝ := (Matrix.of C).submatrix Subtype.val Subtype.val
  let mean (I : Finset T) : EuclideanSpace ℝ I := WithLp.toLp 2 (I.restrict m)
  have hS I : (S I).PosSemidef := hC.submatrix _
  let ν (I : Finset T) := multivariateGaussian (mean I) (S I)
  let family (I : Finset T) := (ν I).map (EuclideanSpace.equiv I ℝ)
  have (I : Finset T) : IsProbabilityMeasure (family I) := by
    dsimp only [family, ν]
    infer_instance
  have hprojective : IsProjectiveMeasureFamily (α := fun _ : T ↦ ℝ) family := by
    intro I J hJI
    have hrestrict : MeasurePreserving (EuclideanSpace.restrict₂ hJI) (ν I) (ν J) :=
      measurePreserving_restrict₂_multivariateGaussian (hS I) hJI
    have hcomp : Finset.restrict₂ (π := fun _ : T ↦ ℝ) hJI ∘ EuclideanSpace.equiv I ℝ =
        EuclideanSpace.equiv J ℝ ∘ EuclideanSpace.restrict₂ hJI := rfl
    have hmeas : Measurable (Finset.restrict₂ (π := fun _ : T ↦ ℝ) hJI) :=
      Finset.measurable_restrict₂ hJI
    simp only [family]
    rw [Measure.map_map hmeas
      (EuclideanSpace.equiv I ℝ).continuous.measurable, hcomp,
      ← Measure.map_map (EuclideanSpace.equiv J ℝ).continuous.measurable hrestrict.measurable,
      hrestrict.map_eq]
  let P := projectiveLimit (α := fun _ : T ↦ ℝ) family hprojective
  have hP : IsProjectiveLimit P family := isProjectiveLimit_projectiveLimit hprojective
  have hEucl (I : Finset T) : MeasurePreserving
      (fun ω : T → ℝ ↦ (EuclideanSpace.equiv I ℝ).symm (I.restrict ω)) P (ν I) :=
    (MeasurableEquiv.measurePreserving_symm (ν I) (MeasurableEquiv.toLp 2 (I → ℝ)).symm).comp
      ⟨I.measurable_restrict, hP I⟩
  refine ⟨P, inferInstance, ⟨fun I ↦ ⟨I.measurable_restrict.aemeasurable, ?_⟩⟩, ?_, ?_⟩
  · rw [hP I]
    dsimp only [family, ν]
    infer_instance
  · intro t
    let i : ({t} : Finset T) := ⟨t, Finset.mem_singleton_self t⟩
    have heval := (measurePreserving_eval_multivariateGaussian (hS {t}) (i := i)).comp (hEucl {t})
    have hLaw : HasLaw (fun ω : T → ℝ ↦ ω t) _ P :=
      ⟨heval.measurable.aemeasurable, heval.map_eq⟩
    rw [hLaw.integral_eq, integral_id_gaussianReal]
    rfl
  · intro s t
    let I : Finset T := {s, t}
    let i : I := ⟨s, Finset.mem_insert_self s {t}⟩
    let j : I := ⟨t, Finset.mem_insert_of_mem (Finset.mem_singleton_self t)⟩
    have hcov : cov[fun x : EuclideanSpace ℝ I ↦ x i,
        fun x : EuclideanSpace ℝ I ↦ x j; ν I] = S I i j :=
      covariance_eval_multivariateGaussian (μ := mean I) (hS I) i j
    rw [← (hEucl I).map_eq, covariance_map_fun (by fun_prop) (by fun_prop)
      (hEucl I).measurable.aemeasurable] at hcov
    exact hcov

/-- SYNOPSIS item 2, uniqueness: the law of a Gaussian field, as a measure on `T → ℝ`, is
determined by its mean and covariance functions. -/
theorem map_eq_of_isGaussianProcess {Ω' : Type*} [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : T → Ω → ℝ} {Z' : T → Ω' → ℝ} (hZm : ∀ t, Measurable (Z t))
    (hZm' : ∀ t, Measurable (Z' t)) (hZ : IsGaussianProcess Z P)
    (hZ' : IsGaussianProcess Z' P') (hmean : ∀ t, P[Z t] = P'[Z' t])
    (hcov : ∀ s t, cov[Z s, Z t; P] = cov[Z' s, Z' t; P']) :
    P.map (fun ω t ↦ Z t ω) = P'.map (fun ω t ↦ Z' t ω) := by
  classical
  let family (I : Finset T) := P.map (fun ω ↦ I.restrict (Z · ω))
  have (I : Finset T) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  have hfirst : IsProjectiveLimit (α := fun _ : T ↦ ℝ) (P.map (fun ω t ↦ Z t ω)) family :=
    fun I ↦ Measure.map_map I.measurable_restrict (Measurable.of_eval hZm)
  refine hfirst.unique ?_
  intro I
  rw [Measure.map_map I.measurable_restrict (Measurable.of_eval hZm')]
  let e := (EuclideanSpace.equiv I ℝ).symm
  let R (ω : Ω) := I.restrict (Z · ω)
  let R' (ω : Ω') := I.restrict (Z' · ω)
  have hR : Measurable R := Measurable.of_eval fun i ↦ hZm i
  have hR' : Measurable R' := Measurable.of_eval fun i ↦ hZm' i
  let μ := (P.map R).map e
  let μ' := (P'.map R').map e
  have hG : IsGaussian (P.map R) := (hZ.hasGaussianLaw I).isGaussian_map
  have hG' : IsGaussian (P'.map R') := (hZ'.hasGaussianLaw I).isGaussian_map
  have hμG : IsGaussian μ := isGaussian_map_equiv e
  have hμG' : IsGaussian μ' := isGaussian_map_equiv e
  have hμ : μ = P.map (e ∘ R) := Measure.map_map e.continuous.measurable hR
  have hμ' : μ' = P'.map (e ∘ R') := Measure.map_map e.continuous.measurable hR'
  have hm : (∫ y, y ∂μ) = ∫ y, y ∂μ' := by
    have hcoord (u v : EuclideanSpace ℝ I) (heq : ∀ i, u i = v i) : u = v :=
      (WithLp.equiv 2 (I → ℝ)).injective (funext heq)
    apply hcoord
    intro i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (μ := μ)
      IsGaussian.integrable_fun_id
    have h' := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (μ := μ')
      IsGaussian.integrable_fun_id
    simp only [EuclideanSpace.coe_proj] at h h'
    rw [← h, ← h', hμ, hμ',
      integral_map (e.continuous.measurable.comp hR).aemeasurable (by fun_prop),
      integral_map (e.continuous.measurable.comp hR').aemeasurable (by fun_prop)]
    exact hmean i
  have hc : TauCeti.covMatrix μ = TauCeti.covMatrix μ' := by
    ext i j
    simp only [TauCeti.covMatrix_apply, hμ, hμ']
    rw [covariance_map_fun (by fun_prop) (by fun_prop)
      (e.continuous.measurable.comp hR).aemeasurable,
      covariance_map_fun (by fun_prop) (by fun_prop)
      (e.continuous.measurable.comp hR').aemeasurable]
    exact hcov i j
  symm
  apply (MeasurableEquiv.toLp 2 (I → ℝ)).measurableEmbedding.map_injective
  exact (TauCeti.Probability.eq_multivariateGaussian_covMatrix μ).trans
    ((congrArg₂ multivariateGaussian hm hc).trans
      (TauCeti.Probability.eq_multivariateGaussian_covMatrix μ').symm)

/-- SYNOPSIS item 2, converse: the covariance kernel of a second-order field is symmetric and
positive definite. -/
theorem posSemidef_covariance {P : Measure Ω} [IsProbabilityMeasure P] {Z : T → Ω → ℝ}
    (hZ : IsSecondOrderField Z P) :
    (Matrix.of fun s t ↦ cov[Z s, Z t; P]).PosSemidef := by
  rw [Matrix.posSemidef_iff_submatrix_finset]
  intro s
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun c ↦ ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.of_apply, star_trivial]
    exact covariance_comm _ _
  · have hLp (i : s) : MemLp (fun ω ↦ c i * Z i ω) 2 P := (hZ i).const_mul _
    have hv := variance_nonneg (μ := P) (X := fun ω ↦ ∑ i : s, c i * Z i ω)
    rw [variance_fun_sum hLp] at hv
    have hcov (i j : s) : cov[fun ω ↦ c i * Z i ω, fun ω ↦ c j * Z j ω; P] =
        c i * (cov[Z i, Z j; P] * c j) := by
      rw [covariance_const_mul_left, covariance_const_mul_right, mul_comm (c j)]
    simpa only [hcov, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Matrix.submatrix_apply, Matrix.of_apply, Finset.mul_sum] using hv

end MSSS
