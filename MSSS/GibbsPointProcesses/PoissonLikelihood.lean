module

public import MSSS.GibbsPointProcesses.InfiniteVolume
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Order.LiminfLimsup

import TauCeti.MeasureTheory.Integral.Bind
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Likelihood inference for Poisson processes

SYNOPSIS items 105 and 106: the Poisson likelihood, the log-linear model, and Kutoyants'
asymptotic theory of maximum likelihood.

Item 106 is stated only in its fixed-set special case: intensities `n S(ϑ, x)` on a fixed
bounded set `A`, for which the Fisher information is `I_n = n I` with
`I(ϑ) = ∫_A ∇S ∇Sᵀ / S`. The general case of observation sets `A_n` and intensity measures
`Λ^{(n)}_ϑ` with `sup ‖I_n⁻¹‖ → 0` is not stated. The regularity, identifiability, and
moment conditions are collected in `MSSS.IsRegularPoissonFamily`. Convergence in distribution
is tested on bounded continuous functions.

## Main definitions

* `MSSS.poissonDensity W lam`: the density `e^{|W| - ∫_W λ} ∏_{ξ ∈ x} λ(ξ)` with respect to
  `Π_W`.
* `MSSS.logLinearLogLik W C x β`.
* `MSSS.poissonLaw Λ`: the law of a Poisson process with intensity measure `Λ`.
* `MSSS.poissonFisher A S ϑ`, `MSSS.IsRegularPoissonFamily Θ A S`, `MSSS.poissonLogLik A S n ϑ x`.

## Main results

* `MSSS.hasConfigDensity_poisson`, `MSSS.log_poissonDensity`, `MSSS.concaveOn_logLinearLogLik`,
  `MSSS.hasDerivAt_logLinearLogLik`, `MSSS.hasDerivAt_deriv_logLinearLogLik`,
  `MSSS.integral_compositeScore`: SYNOPSIS item 105.
* `MSSS.poisson_lan`, `MSSS.poisson_hajek_leCam`, `MSSS.poisson_mle_asymptotics`:
  SYNOPSIS item 106.

The log-linear derivatives use Mathlib's differentiation under the integral. The composite
score uses TauCeti's integration theorem for mixtures.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric Matrix TauCeti.Probability
open scoped ENNReal Topology MatrixOrder

namespace MSSS

variable {d : ℕ}

/-! ### The Poisson likelihood (SYNOPSIS item 105) -/

/-- The density `f(x) = e^{|W| - ∫_W λ} ∏_{ξ ∈ x} λ(ξ)` of the Poisson process with intensity
`λ` on `W` with respect to the unit-rate Poisson process `Π_W`. -/
def poissonDensity (W : Set (EuclideanSpace ℝ (Fin d))) (lam : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : Finset (EuclideanSpace ℝ (Fin d))) : ℝ :=
  Real.exp ((volume W).toReal - ∫ u in W, lam u) * ∏ ξ ∈ x, lam ξ

/-- The log-likelihood `ℓ(β) = ∑_{x} βᵀ C(x) - ∫_W e^{βᵀ C} + |W|` of the log-linear model
`λ_β(u) = exp(βᵀ C(u))`. -/
def logLinearLogLik {p : ℕ} (W : Set (EuclideanSpace ℝ (Fin d)))
    (C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ) (x : Finset (EuclideanSpace ℝ (Fin d)))
    (β : Fin p → ℝ) : ℝ :=
  (∑ ξ ∈ x, ∑ j, β j * C ξ j) - (∫ u in W, Real.exp (∑ j, β j * C u j)) +
    (volume W).toReal

lemma poissonDensity_def (W : Set (EuclideanSpace ℝ (Fin d))) (lam : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : Finset (EuclideanSpace ℝ (Fin d))) :
    poissonDensity W lam x = Real.exp ((volume W).toReal - ∫ u in W, lam u) * ∏ ξ ∈ x, lam ξ := by
  rw [poissonDensity]

lemma logLinearLogLik_def {p : ℕ} (W : Set (EuclideanSpace ℝ (Fin d)))
    (C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ) (x : Finset (EuclideanSpace ℝ (Fin d)))
    (β : Fin p → ℝ) : logLinearLogLik W C x β =
      (∑ ξ ∈ x, ∑ j, β j * C ξ j) - (∫ u in W, Real.exp (∑ j, β j * C u j)) +
        (volume W).toReal := by
  rw [logLinearLogLik]

/-- SYNOPSIS item 105: a Poisson process with bounded nonnegative intensity `λ` on a bounded `W`
has density `MSSS.poissonDensity W λ` with respect to `Π_W`. -/
theorem hasConfigDensity_poisson {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Finset (EuclideanSpace ℝ (Fin d))}
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWm : MeasurableSet W) (hW : volume W < ∞)
    (hXW : ∀ ω, (X ω : Set (EuclideanSpace ℝ (Fin d))) ⊆ W)
    {lam : EuclideanSpace ℝ (Fin d) → ℝ} (hlam : Measurable lam) (hlam0 : ∀ u, 0 ≤ lam u)
    (hlamb : ∃ M, ∀ u, lam u ≤ M)
    (hX : IsPoissonRandomMeasure P (fun ω ↦ configMeasure (X ω))
      ((volume.restrict W).withDensity fun u ↦ ENNReal.ofReal (lam u))) :
    HasConfigDensity P X W (poissonDensity W lam) := by
  sorry

/-- SYNOPSIS item 105: for a positive intensity the log-likelihood is
`ℓ = ∑_{x} log λ(x) - ∫_W λ + |W|`. -/
theorem log_poissonDensity (W : Set (EuclideanSpace ℝ (Fin d)))
    {lam : EuclideanSpace ℝ (Fin d) → ℝ} (hlam : ∀ u, 0 < lam u)
    (x : Finset (EuclideanSpace ℝ (Fin d))) :
    Real.log (poissonDensity W lam x) =
      (∑ ξ ∈ x, Real.log (lam ξ)) - (∫ u in W, lam u) + (volume W).toReal := by
  have hprod : 0 < ∏ ξ ∈ x, lam ξ := Finset.prod_pos fun ξ _ ↦ hlam ξ
  rw [poissonDensity_def, Real.log_mul (Real.exp_pos _).ne' hprod.ne',
    Real.log_exp, Real.log_prod fun ξ _ ↦ (hlam ξ).ne']
  ring

/-- SYNOPSIS item 105: the log-linear log-likelihood is concave. -/
theorem concaveOn_logLinearLogLik {p : ℕ} {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : volume W < ∞) {C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ} (hC : Measurable C)
    (hCb : ∃ M, ∀ u j, |C u j| ≤ M) (x : Finset (EuclideanSpace ℝ (Fin d))) :
    ConcaveOn ℝ univ (logLinearLogLik W C x) := by
  obtain ⟨M, hM⟩ := hCb
  let : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hW⟩
  let L (β : Fin p → ℝ) (u : EuclideanSpace ℝ (Fin d)) := ∑ j, β j * C u j
  have hLi (β : Fin p → ℝ) : IntegrableOn (fun u ↦ Real.exp (L β u)) W := by
    have hLm : Measurable (L β) := by
      exact Finset.measurable_sum _ fun j _ ↦
        measurable_const.mul ((measurable_pi_apply j).comp hC)
    refine Integrable.of_bound (Real.continuous_exp.measurable.comp hLm).aestronglyMeasurable
      (Real.exp (∑ j, |β j| * M)) (ae_of_all _ fun u ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    calc
      β j * C u j ≤ |β j * C u j| := le_abs_self _
      _ = |β j| * |C u j| := abs_mul _ _
      _ ≤ |β j| * M := mul_le_mul_of_nonneg_left (hM u j) (abs_nonneg _)
  refine ⟨convex_univ, ?_⟩
  intro β _ γ _ a b ha hb hab
  have hmix (u : EuclideanSpace ℝ (Fin d)) :
      L (a • β + b • γ) u = a * L β u + b * L γ u := by
    simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hpoint (u : EuclideanSpace ℝ (Fin d)) :
      Real.exp (L (a • β + b • γ) u) ≤ a * Real.exp (L β u) + b * Real.exp (L γ u) := by
    rw [hmix]
    exact convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab
  have hineq := integral_mono (hLi (a • β + b • γ))
    (((hLi β).const_mul a).add ((hLi γ).const_mul b)) hpoint
  rw [integral_add' ((hLi β).const_mul a) ((hLi γ).const_mul b),
    integral_const_mul, integral_const_mul] at hineq
  have hLL (δ : Fin p → ℝ) : logLinearLogLik W C x δ =
      (∑ ξ ∈ x, L δ ξ) - (∫ u in W, Real.exp (L δ u)) + (volume W).toReal := rfl
  have hsum :
      (∑ ξ ∈ x, L (a • β + b • γ) ξ) = a * (∑ ξ ∈ x, L β ξ) + b * (∑ ξ ∈ x, L γ ξ) := by
    simp only [hmix, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [hLL, hsum, smul_eq_mul]
  linarith [congrArg (fun t : ℝ ↦ t * (volume W).toReal) hab]

/-- A finite linear combination of bounded covariates is measurable and bounded. -/
private lemma logLinear_direction_bound {p : ℕ} {C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ}
    (hC : Measurable C) {M : ℝ} (hM : ∀ u j, |C u j| ≤ M) (v : Fin p → ℝ) :
    Measurable (fun u ↦ ∑ j, v j * C u j) ∧
      ∀ u, |∑ j, v j * C u j| ≤ ∑ j, |v j| * max M 0 := by
  refine ⟨Finset.measurable_sum _ (fun j _ ↦ measurable_const.mul
    ((measurable_pi_apply j).comp hC)), fun u ↦ ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hM u j).trans (le_max_left _ _)) (abs_nonneg _)

/-- Differentiation of the bounded log-linear intensity under the window integral. -/
private lemma hasDerivAt_logLinear_moment {p : ℕ} {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : volume W < ∞) {C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ} (hC : Measurable C)
    (hCb : ∃ M, ∀ u j, |C u j| ≤ M) (β v : Fin p → ℝ) (n : ℕ) (t : ℝ) :
    let a := fun u ↦ ∑ j, β j * C u j
    let b := fun u ↦ ∑ j, v j * C u j
    HasDerivAt (fun s : ℝ ↦ ∫ u in W, (b u) ^ n * Real.exp (a u + s * b u))
      (∫ u in W, (b u) ^ (n + 1) * Real.exp (a u + t * b u)) t := by
  intro a b
  obtain ⟨M, hM⟩ := hCb
  obtain ⟨ha, ha'⟩ := logLinear_direction_bound hC hM β
  obtain ⟨hb, hb'⟩ := logLinear_direction_bound hC hM v
  let A := ∑ j, |β j| * max M 0
  let B := ∑ j, |v j| * max M 0
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (le_max_right _ _)
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict W
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hW⟩
  let F (k : ℕ) (s : ℝ) (u : EuclideanSpace ℝ (Fin d)) :=
    b u ^ k * Real.exp (a u + s * b u)
  have hmeas (k : ℕ) (s : ℝ) : AEStronglyMeasurable (F k s) μ := by
    have h : Measurable (F k s) :=
      (hb.pow_const k).mul (Real.measurable_exp.comp (ha.add (measurable_const.mul hb)))
    exact h.aestronglyMeasurable
  have hbound (k : ℕ) (s : ℝ) (hs : |s| ≤ |t| + 1) (u : EuclideanSpace ℝ (Fin d)) :
      ‖F k s u‖ ≤ B ^ k * Real.exp (A + (|t| + 1) * B) := by
    simp only [F, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hb' u) _) (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le (pow_nonneg hB _)
    refine add_le_add ((le_abs_self _).trans (ha' u)) ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul hs (hb' u) (abs_nonneg _) (by positivity)
  have hF : Integrable (F n t) μ := Integrable.of_bound (hmeas n t) _
    (ae_of_all _ (hbound n t (by linarith)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F n) (F' := F (n + 1)) (bound := fun _ ↦ B ^ (n + 1) * Real.exp (A + (|t| + 1) * B))
    (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall (hmeas n)) hF (hmeas _ t) ?_ (integrable_const _) ?_).2
  · refine ae_of_all _ fun u s hs ↦ hbound _ s ?_ u
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have h := abs_add_le (s - t) t
    rw [sub_add_cancel] at h
    linarith
  · refine ae_of_all _ fun u s _ ↦ ?_
    have hd := ((((hasDerivAt_id s).mul_const (b u)).const_add (a u)).exp).const_mul (b u ^ n)
    simpa only [F, id_eq, one_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hd

/-- The directional score at an arbitrary point on the parameter line. -/
private lemma hasDerivAt_logLinearLogLik_line {p : ℕ} {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : volume W < ∞) {C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ} (hC : Measurable C)
    (hCb : ∃ M, ∀ u j, |C u j| ≤ M) (x : Finset (EuclideanSpace ℝ (Fin d)))
    (β v : Fin p → ℝ) (t : ℝ) :
    let a := fun u ↦ ∑ j, β j * C u j
    let b := fun u ↦ ∑ j, v j * C u j
    HasDerivAt (fun s : ℝ ↦ logLinearLogLik W C x (β + s • v))
      ((∑ ξ ∈ x, b ξ) - ∫ u in W, b u * Real.exp (a u + t * b u)) t := by
  intro a b
  have hsum (s : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
      ∑ j, (β + s • v) j * C u j = a u + s * b u := by
    simp only [a, b, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hLL : (fun s : ℝ ↦ logLinearLogLik W C x (β + s • v)) = fun s ↦
      (∑ ξ ∈ x, (a ξ + s * b ξ)) - (∫ u in W, Real.exp (a u + s * b u)) + (volume W).toReal := by
    funext s
    rw [logLinearLogLik_def]
    simp only [hsum]
  have hdata : HasDerivAt (fun s : ℝ ↦ ∑ ξ ∈ x, (a ξ + s * b ξ)) (∑ ξ ∈ x, b ξ) t :=
    HasDerivAt.fun_sum fun ξ _ ↦ by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const (b ξ)).const_add (a ξ)
  have hI : HasDerivAt (fun s : ℝ ↦ ∫ u in W, Real.exp (a u + s * b u))
      (∫ u in W, b u * Real.exp (a u + t * b u)) t := by
    simpa only [pow_zero, one_mul, zero_add, pow_one] using
      hasDerivAt_logLinear_moment hW hC hCb β v 0 t
  rw [hLL]
  exact (hdata.sub hI).add_const _

/-- SYNOPSIS item 105: the directional derivative of the log-linear log-likelihood is
`∑_j v_j (∑_{x} C_j(x) - ∫_W C_j λ_β)`, so the score equations are
`∫_W C_j λ_β = ∑_{x} C_j(x)`. -/
theorem hasDerivAt_logLinearLogLik {p : ℕ} {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : volume W < ∞) {C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ} (hC : Measurable C)
    (hCb : ∃ M, ∀ u j, |C u j| ≤ M) (x : Finset (EuclideanSpace ℝ (Fin d))) (β v : Fin p → ℝ) :
    HasDerivAt (fun t : ℝ ↦ logLinearLogLik W C x (β + t • v))
      (∑ j, v j * (∑ ξ ∈ x, C ξ j -
        ∫ u in W, C u j * Real.exp (∑ k, β k * C u k))) 0 := by
  obtain ⟨M, hM⟩ := hCb
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict W
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hW⟩
  let a := fun u ↦ ∑ k, β k * C u k
  obtain ⟨ha, ha'⟩ := logLinear_direction_bound hC hM β
  have hI (j : Fin p) : Integrable (fun u ↦ C u j * Real.exp (a u)) μ := by
    refine Integrable.of_bound (((measurable_pi_apply j).comp hC).mul
      (Real.measurable_exp.comp ha)).aestronglyMeasurable
      (max M 0 * Real.exp (∑ k, |β k| * max M 0)) (ae_of_all _ fun u ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul ((hM u j).trans (le_max_left _ _))
      (Real.exp_le_exp.mpr ((le_abs_self _).trans (ha' u))) (Real.exp_pos _).le (le_max_right _ _)
  have hsplit : (∫ u in W, (∑ j, v j * C u j) * Real.exp (a u)) =
      ∑ j, v j * ∫ u in W, C u j * Real.exp (a u) := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun j _ ↦ (hI j).const_mul (v j))]
    simp only [integral_const_mul]
    rfl
  have hsum : (∑ ξ ∈ x, ∑ j, v j * C ξ j) = ∑ j, v j * ∑ ξ ∈ x, C ξ j := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  dsimp only [a] at hsplit
  simpa only [zero_mul, add_zero, hsplit, hsum, mul_sub, Finset.sum_sub_distrib] using
    hasDerivAt_logLinearLogLik_line hW hC ⟨M, hM⟩ x β v 0

/-- SYNOPSIS item 105: the second directional derivative of the log-linear log-likelihood is
`-∫_W (vᵀ C)² λ_β`: the Fisher information `∫_W C Cᵀ λ_β` equals the negative Hessian. -/
theorem hasDerivAt_deriv_logLinearLogLik {p : ℕ} {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : volume W < ∞) {C : EuclideanSpace ℝ (Fin d) → Fin p → ℝ} (hC : Measurable C)
    (hCb : ∃ M, ∀ u j, |C u j| ≤ M) (x : Finset (EuclideanSpace ℝ (Fin d))) (β v : Fin p → ℝ) :
    HasDerivAt (deriv fun t : ℝ ↦ logLinearLogLik W C x (β + t • v))
      (-∫ u in W, (∑ j, v j * C u j) ^ 2 * Real.exp (∑ k, β k * C u k)) 0 := by
  let a := fun u ↦ ∑ j, β j * C u j
  let b := fun u ↦ ∑ j, v j * C u j
  have hline : (deriv fun t : ℝ ↦ logLinearLogLik W C x (β + t • v)) = fun t ↦
      (∑ ξ ∈ x, b ξ) - ∫ u in W, b u * Real.exp (a u + t * b u) :=
    funext fun t ↦ (hasDerivAt_logLinearLogLik_line hW hC hCb x β v t).deriv
  rw [hline]
  have hI : HasDerivAt (fun t : ℝ ↦ ∫ u in W, b u * Real.exp (a u + t * b u))
      (∫ u in W, b u ^ 2 * Real.exp (a u)) 0 := by
    simpa only [pow_one, zero_mul, add_zero] using
      hasDerivAt_logLinear_moment hW hC hCb β v 1 0
  exact hI.const_sub _

/-- SYNOPSIS item 105: for any point process on `W` with intensity function `ρ_θ` differentiable
in `θ` (in direction `v`, with derivative `∂ρ`), the first-order composite score
`∑_{u ∈ X} ∂ρ(u) / ρ(u) - ∫_W ∂ρ` has mean zero. -/
theorem integral_compositeScore {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (EuclideanSpace ℝ (Fin d))} (hηm : Measurable η)
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWm : MeasurableSet W)
    {ρ dρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : ∀ u, 0 < ρ u) (hρm : Measurable ρ)
    (hdρm : Measurable dρ)
    (hint : P.bind η = volume.withDensity fun u ↦ ENNReal.ofReal (ρ u))
    (hdρi : IntegrableOn dρ W)
    (hsc : Integrable (fun ω ↦ ∫ u in W, dρ u / ρ u ∂η ω) P) :
    ∫ ω, (∫ u in W, dρ u / ρ u ∂η ω - ∫ u in W, dρ u) ∂P = 0 := by
  let g := W.indicator (fun u ↦ dρ u / ρ u)
  have hm : Measurable fun u ↦ ENNReal.ofReal (ρ u) := hρm.ennreal_ofReal
  have hfin : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ENNReal.ofReal (ρ u) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hscale (u : EuclideanSpace ℝ (Fin d)) :
      (ENNReal.ofReal (ρ u)).toReal • g u = W.indicator dρ u := by
    by_cases hu : u ∈ W
    · simp [g, hu, ENNReal.toReal_ofReal (hρ u).le, smul_eq_mul,
        mul_comm (ρ u), (hρ u).ne']
    · simp [g, hu]
  have hgi : Integrable g (P.bind η) := by
    rw [hint, integrable_withDensity_iff_integrable_smul' hm hfin]
    refine ⟨(hm.ennreal_toReal.smul ((hdρm.div hρm).indicator hWm)).aestronglyMeasurable, ?_⟩
    simpa only [hscale] using ((integrable_indicator_iff hWm).2 hdρi).hasFiniteIntegral
  have hmean : (∫ ω, ∫ u in W, dρ u / ρ u ∂η ω ∂P) = ∫ u in W, dρ u := by
    simp_rw [← integral_indicator hWm]
    rw [← Measure.integral_bind hηm.aemeasurable hgi, hint,
      integral_withDensity_eq_integral_toReal_smul hm hfin]
    simp only [hscale]
  rw [integral_sub hsc (integrable_const _), hmean, integral_const]
  simp

/-! ### Kutoyants' asymptotic theory (SYNOPSIS item 106) -/

section Kutoyants

variable {p : ℕ}

open Classical in
/-- The law of a Poisson process with intensity measure `Λ`, if one exists; otherwise `0`. -/
def poissonLaw {X : Type*} [MeasurableSpace X] (Λ : Measure X) : Measure (Measure X) :=
  if h : ∃ Q : Measure (Measure X), IsProbabilityMeasure Q ∧ IsPoissonRandomMeasure Q id Λ then
    Classical.choose h else 0

/-- The partial derivative `∂S/∂ϑ_i (ϑ, u)`. -/
def paramPartial (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin p)
    (ϑ : EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ (fun ϑ ↦ S ϑ u) ϑ (EuclideanSpace.single i 1)

/-- The Fisher information `I(ϑ) = ∫_A ∇S ∇Sᵀ / S`. -/
def poissonFisher (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ)
    (ϑ : EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j ↦ ∫ u in A, paramPartial S i ϑ u * paramPartial S j ϑ u / S ϑ u

/-- The log-likelihood `∫_A log(n S(ϑ, u)) x(du) - n ∫_A S(ϑ, u) du + |A|` of the Poisson
process with intensity `n S(ϑ, ·)` on `A` with respect to `Π_A`. -/
def poissonLogLik (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ)
    (ϑ : EuclideanSpace ℝ (Fin p)) (x : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (∫ u in A, Real.log (n * S ϑ u) ∂x) - n * (∫ u in A, S ϑ u) + (volume A).toReal

/-- The law `Q_{n,ϑ}` of the Poisson process with intensity `n S(ϑ, ·)` on `A`. -/
def poissonModel (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ)
    (ϑ : EuclideanSpace ℝ (Fin p)) : Measure (Measure (EuclideanSpace ℝ (Fin d))) :=
  poissonLaw ((volume.restrict A).withDensity fun u ↦ ENNReal.ofReal (n * S ϑ u))

/-- The regularity, identifiability, and information conditions of the Kutoyants theory on an
open bounded parameter set `Θ`: `S` is measurable, positive, and bounded on `A`, with
`0 < inf S`; it is continuously differentiable in `ϑ` with bounded derivative; distinct
parameters are separated, `inf_{‖ϑ' - ϑ‖ > ν} ∫_A (√S(ϑ') - √S(ϑ))² > 0`; and the Fisher
information is uniformly positive definite on compact subsets of `Θ`. -/
def IsRegularPoissonFamily (Θ : Set (EuclideanSpace ℝ (Fin p)))
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IsOpen Θ ∧ Bornology.IsBounded Θ ∧ MeasurableSet A ∧ Bornology.IsBounded A ∧ 0 < volume A ∧
    (∀ ϑ, Measurable (S ϑ)) ∧ (∃ m M : ℝ, 0 < m ∧ ∀ ϑ ∈ closure Θ, ∀ u ∈ A, m ≤ S ϑ u ∧ S ϑ u ≤ M) ∧
    (∀ u, ContDiff ℝ 1 fun ϑ ↦ S ϑ u) ∧
    (∃ M : ℝ, ∀ ϑ ∈ closure Θ, ∀ u ∈ A, ‖fderiv ℝ (fun ϑ ↦ S ϑ u) ϑ‖ ≤ M) ∧
    (∀ ϑ ∈ Θ, ∀ ν > 0, ∃ c > 0, ∀ ϑ' ∈ closure Θ, ν < dist ϑ' ϑ →
      c ≤ ∫ u in A, (Real.sqrt (S ϑ' u) - Real.sqrt (S ϑ u)) ^ 2) ∧
    ∀ K ⊆ Θ, IsCompact K → ∃ c > 0, ∀ ϑ ∈ K, ∀ v : Fin p → ℝ,
      c * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (poissonFisher A S ϑ *ᵥ v)

open Classical in
lemma poissonLaw_def {X : Type*} [MeasurableSpace X] (Λ : Measure X) :
    poissonLaw Λ = if h : ∃ Q : Measure (Measure X), IsProbabilityMeasure Q ∧
      IsPoissonRandomMeasure Q id Λ then Classical.choose h else 0 := by
  rw [poissonLaw]

lemma paramPartial_def (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin p)
    (ϑ : EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin d)) :
    paramPartial S i ϑ u = fderiv ℝ (fun ϑ ↦ S ϑ u) ϑ (EuclideanSpace.single i 1) := by
  rw [paramPartial]

lemma poissonFisher_def (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ)
    (ϑ : EuclideanSpace ℝ (Fin p)) : poissonFisher A S ϑ =
      Matrix.of fun i j ↦ ∫ u in A, paramPartial S i ϑ u * paramPartial S j ϑ u / S ϑ u := by
  rw [poissonFisher]

lemma poissonLogLik_def (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ)
    (ϑ : EuclideanSpace ℝ (Fin p)) (x : Measure (EuclideanSpace ℝ (Fin d))) :
    poissonLogLik A S n ϑ x =
      (∫ u in A, Real.log (n * S ϑ u) ∂x) - n * (∫ u in A, S ϑ u) + (volume A).toReal := by
  rw [poissonLogLik]

lemma poissonModel_def (A : Set (EuclideanSpace ℝ (Fin d)))
    (S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ)
    (ϑ : EuclideanSpace ℝ (Fin p)) : poissonModel A S n ϑ =
      poissonLaw ((volume.restrict A).withDensity fun u ↦ ENNReal.ofReal (n * S ϑ u)) := by
  rw [poissonModel]

lemma isRegularPoissonFamily_def {Θ : Set (EuclideanSpace ℝ (Fin p))}
    {A : Set (EuclideanSpace ℝ (Fin d))}
    {S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ} :
    IsRegularPoissonFamily Θ A S ↔
      IsOpen Θ ∧ Bornology.IsBounded Θ ∧ MeasurableSet A ∧ Bornology.IsBounded A ∧ 0 < volume A ∧
      (∀ ϑ, Measurable (S ϑ)) ∧
      (∃ m M : ℝ, 0 < m ∧ ∀ ϑ ∈ closure Θ, ∀ u ∈ A, m ≤ S ϑ u ∧ S ϑ u ≤ M) ∧
      (∀ u, ContDiff ℝ 1 fun ϑ ↦ S ϑ u) ∧
      (∃ M : ℝ, ∀ ϑ ∈ closure Θ, ∀ u ∈ A, ‖fderiv ℝ (fun ϑ ↦ S ϑ u) ϑ‖ ≤ M) ∧
      (∀ ϑ ∈ Θ, ∀ ν > 0, ∃ c > 0, ∀ ϑ' ∈ closure Θ, ν < dist ϑ' ϑ →
        c ≤ ∫ u in A, (Real.sqrt (S ϑ' u) - Real.sqrt (S ϑ u)) ^ 2) ∧
      ∀ K ⊆ Θ, IsCompact K → ∃ c > 0, ∀ ϑ ∈ K, ∀ v : Fin p → ℝ,
        c * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (poissonFisher A S ϑ *ᵥ v) := Iff.rfl

/-- SYNOPSIS item 106, local asymptotic normality, in the fixed-set special case (intensity
`n S(ϑ, ·)` on a fixed bounded `A`): for `ϑ ∈ Θ` and `u`, with
`Δ_n = n^{-1/2} (∫_A ∇S/S dx - n ∫_A ∇S)`,
`ℓ_n(ϑ + u/√n) - ℓ_n(ϑ) - (uᵀ Δ_n - ½ uᵀ I(ϑ) u) → 0` in `Q_{n,ϑ}`-probability, and
`I(ϑ)^{-1/2} Δ_n ⇒ N(0, I_p)`. -/
theorem poisson_lan {Θ : Set (EuclideanSpace ℝ (Fin p))} {A : Set (EuclideanSpace ℝ (Fin d))}
    {S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ}
    (hS : IsRegularPoissonFamily Θ A S) {ϑ : EuclideanSpace ℝ (Fin p)} (hϑ : ϑ ∈ Θ) :
    let Δ : ℕ → Measure (EuclideanSpace ℝ (Fin d)) → Fin p → ℝ := fun n x i ↦
      (Real.sqrt n)⁻¹ * (∫ u in A, paramPartial S i ϑ u / S ϑ u ∂x -
        n * ∫ u in A, paramPartial S i ϑ u)
    (∀ (u : EuclideanSpace ℝ (Fin p)), ∀ ε > 0,
      Tendsto (fun n ↦ poissonModel A S n ϑ
        {x | ε < |poissonLogLik A S n (ϑ + (Real.sqrt n)⁻¹ • u) x -
        poissonLogLik A S n ϑ x - (WithLp.ofLp u ⬝ᵥ Δ n x -
          (1 / 2) * WithLp.ofLp u ⬝ᵥ (poissonFisher A S ϑ *ᵥ WithLp.ofLp u))|}) atTop (𝓝 0)) ∧
      ∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℝ,
        Tendsto (fun n ↦ ∫ x, g (WithLp.toLp 2 (CFC.sqrt (poissonFisher A S ϑ)⁻¹ *ᵥ Δ n x))
          ∂poissonModel A S n ϑ) atTop (𝓝 (∫ v, g v ∂stdGaussian (EuclideanSpace ℝ (Fin p)))) := by
  sorry

/-- SYNOPSIS item 106, Hájek–Le Cam minimax bound, in the fixed-set special case (intensity
`n S(ϑ, ·)` on a fixed bounded `A`): for any estimators `ϑ̃_n`, every `ϑ ∈ Θ`, and
every `δ > 0`, `liminf_n sup_{‖ϑ' - ϑ‖ < δ} n E_{ϑ'} ‖ϑ̃_n - ϑ'‖² ≥ tr I(ϑ)⁻¹`. -/
theorem poisson_hajek_leCam {Θ : Set (EuclideanSpace ℝ (Fin p))}
    {A : Set (EuclideanSpace ℝ (Fin d))}
    {S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ}
    (hS : IsRegularPoissonFamily Θ A S)
    (est : ℕ → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin p))
    (hest : ∀ n, Measurable (est n)) {ϑ : EuclideanSpace ℝ (Fin p)} (hϑ : ϑ ∈ Θ) {δ : ℝ}
    (hδ : 0 < δ) :
    ENNReal.ofReal (poissonFisher A S ϑ)⁻¹.trace ≤
      liminf (fun n : ℕ ↦ ⨆ ϑ' ∈ ball ϑ δ ∩ Θ,
        ∫⁻ x, ENNReal.ofReal (n * ‖est n x - ϑ'‖ ^ 2) ∂poissonModel A S n ϑ') atTop := by
  sorry

/-- SYNOPSIS item 106, in the fixed-set special case (intensity `n S(ϑ, ·)` on a fixed bounded
`A`): maximum-likelihood estimators `ϑ̂_n` (measurable maximisers of `ℓ_n` over
`closure Θ`) are uniformly consistent on compact subsets of `Θ`, satisfy
`√n I(ϑ)^{1/2} (ϑ̂_n - ϑ) ⇒ N(0, I_p)` with convergence of all moments, and are asymptotically
efficient: the risk `sup_{‖ϑ' - ϑ‖ < δ} n E_{ϑ'} ‖ϑ̂_n - ϑ'‖²` attains the Hájek–Le Cam bound as
`n → ∞` and then `δ → 0`. -/
theorem poisson_mle_asymptotics {Θ : Set (EuclideanSpace ℝ (Fin p))}
    {A : Set (EuclideanSpace ℝ (Fin d))}
    {S : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin d) → ℝ}
    (hS : IsRegularPoissonFamily Θ A S)
    (mle : ℕ → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin p))
    (hmle : ∀ n, Measurable (mle n))
    (hmax : ∀ n x, mle n x ∈ closure Θ ∧
      ∀ ϑ ∈ closure Θ, poissonLogLik A S n ϑ x ≤ poissonLogLik A S n (mle n x) x) :
    (∀ K ⊆ Θ, IsCompact K → ∀ ε > 0, Tendsto (fun n ↦ ⨆ ϑ ∈ K,
      poissonModel A S n ϑ {x | ε < dist (mle n x) ϑ}) atTop (𝓝 0)) ∧
    (∀ ϑ ∈ Θ, ∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, g (WithLp.toLp 2 (Real.sqrt n • (CFC.sqrt (poissonFisher A S ϑ) *ᵥ
          WithLp.ofLp (mle n x - ϑ)))) ∂poissonModel A S n ϑ)
        atTop (𝓝 (∫ v, g v ∂stdGaussian (EuclideanSpace ℝ (Fin p))))) ∧
    (∀ ϑ ∈ Θ, ∀ q : ℝ, 0 < q → Tendsto (fun n : ℕ ↦ ∫ x, ‖WithLp.toLp 2 (Real.sqrt n •
        (CFC.sqrt (poissonFisher A S ϑ) *ᵥ WithLp.ofLp (mle n x - ϑ)))‖ ^ q
          ∂poissonModel A S n ϑ)
      atTop (𝓝 (∫ v, ‖v‖ ^ q ∂stdGaussian (EuclideanSpace ℝ (Fin p))))) ∧
    ∀ ϑ ∈ Θ, Tendsto (fun δ ↦ limsup (fun n : ℕ ↦ ⨆ ϑ' ∈ ball ϑ δ ∩ Θ,
        ∫⁻ x, ENNReal.ofReal (n * ‖mle n x - ϑ'‖ ^ 2) ∂poissonModel A S n ϑ') atTop)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (poissonFisher A S ϑ)⁻¹.trace)) := by
  sorry

end Kutoyants

end MSSS
