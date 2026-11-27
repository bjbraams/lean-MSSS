module

public import MSSS.GibbsPointProcesses.Finite

/-!
# The birth–death Metropolis–Hastings algorithm

SYNOPSIS item 110. Let `h` be an unnormalised density on finite configurations in `W` that is
locally stable with integrable bound `φ*`, `c* = ∫_W φ*`, and `h(∅) > 0`. With probability `p`
a birth of a point `ξ` with density `φ*/c*` is proposed and accepted with probability
`min{1, λ*(x, ξ) (1 - p) c* / (φ*(ξ) p (n(x) + 1))}`; otherwise the death of a uniformly chosen
point `η` is proposed and accepted with probability
`min{1, φ*(η) p n(x) / (λ*(x ∖ {η}, η) (1 - p) c*)}`. A death proposal at `∅` leaves the state
unchanged.

The chain is described through its transition operator on real functions
(`MSSS.birthDeathStep`), and the target through `MSSS.configExpectation`, the expectation under
the normalised density. Total-variation distances are expressed through test functions with
values in `[0, 1]`. In the bound for uniform ergodicity the exponent `m / n₀` is the integer part
`⌊m / n₀⌋`.

## Main definitions

* `MSSS.poissonIntegralReal W g`: `∫ g dΠ_W` for real `g`.
* `MSSS.configExpectation W h g`: `∫ g h dΠ_W / ∫ h dΠ_W`.
* `MSSS.birthAccept`, `MSSS.deathAccept`, `MSSS.birthDeathStep W φ c p h g x`.
* `MSSS.BirthDeathSetting W φ c p h`: the standing assumptions.

## Main results

* `MSSS.birthDeath_reversible`, `MSSS.birthDeath_irreducible`, `MSSS.birthDeath_aperiodic`,
  `MSSS.birthDeath_vUniformlyErgodic`, `MSSS.birthDeath_uniformlyErgodic_iff`,
  `MSSS.birthDeath_tv_bound`: SYNOPSIS item 110.
-/

public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace MSSS

variable {E : Type*} [MeasureSpace E] [DecidableEq E]

/-- The integral `∫ g dΠ_W = ∑_n e^{-|W|}/n! ∫_{W^n} g({x_1, …, x_n}) dx` of a real function. -/
def poissonIntegralReal (W : Set E) (g : Finset E → ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(volume W).toReal) / n.factorial *
    ∫ x in Set.pi univ (fun _ : Fin n ↦ W), g (toConfig x)

/-- The expectation `∫ g h dΠ_W / ∫ h dΠ_W` under the normalised density `h`. -/
def configExpectation (W : Set E) (h g : Finset E → ℝ) : ℝ :=
  poissonIntegralReal W (fun x ↦ g x * h x) / poissonIntegralReal W h

/-- The birth acceptance probability
`min{1, λ*(x, ξ) (1 - p) c* / (φ*(ξ) p (n(x) + 1))}`. -/
def birthAccept (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ) (x : Finset E) (ξ : E) : ℝ :=
  min 1 (papangelou h x ξ * (1 - p) * c / (φ ξ * p * (x.card + 1)))

/-- The death acceptance probability
`min{1, φ*(η) p n(x) / (λ*(x ∖ {η}, η) (1 - p) c*)}`. -/
def deathAccept (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ) (x : Finset E) (η : E) : ℝ :=
  min 1 (φ η * p * x.card / (papangelou h (x.erase η) η * (1 - p) * c))

/-- The transition operator `g ↦ E[g(X_1) | X_0 = x]` of the birth–death Metropolis–Hastings
chain. -/
def birthDeathStep (W : Set E) (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ) (g : Finset E → ℝ)
    (x : Finset E) : ℝ :=
  p * (∫ ξ in W, φ ξ / c * (birthAccept φ c p h x ξ * g (insert ξ x) +
      (1 - birthAccept φ c p h x ξ) * g x)) +
    (1 - p) * (if x = ∅ then g x else (x.card : ℝ)⁻¹ * ∑ η ∈ x,
      (deathAccept φ c p h x η * g (x.erase η) + (1 - deathAccept φ c p h x η) * g x))

lemma poissonIntegralReal_def (W : Set E) (g : Finset E → ℝ) : poissonIntegralReal W g =
    ∑' n : ℕ, Real.exp (-(volume W).toReal) / n.factorial *
      ∫ x in Set.pi univ (fun _ : Fin n ↦ W), g (toConfig x) := by
  rw [poissonIntegralReal]

lemma configExpectation_def (W : Set E) (h g : Finset E → ℝ) : configExpectation W h g =
    poissonIntegralReal W (fun x ↦ g x * h x) / poissonIntegralReal W h := by
  rw [configExpectation]

omit [MeasureSpace E] in
lemma birthAccept_def (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ) (x : Finset E) (ξ : E) :
    birthAccept φ c p h x ξ =
      min 1 (papangelou h x ξ * (1 - p) * c / (φ ξ * p * (x.card + 1))) := by
  rw [birthAccept]

omit [MeasureSpace E] in
lemma deathAccept_def (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ) (x : Finset E) (η : E) :
    deathAccept φ c p h x η =
      min 1 (φ η * p * x.card / (papangelou h (x.erase η) η * (1 - p) * c)) := by
  rw [deathAccept]

lemma birthDeathStep_def (W : Set E) (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ)
    (g : Finset E → ℝ) (x : Finset E) : birthDeathStep W φ c p h g x =
      p * (∫ ξ in W, φ ξ / c * (birthAccept φ c p h x ξ * g (insert ξ x) +
          (1 - birthAccept φ c p h x ξ) * g x)) +
        (1 - p) * (if x = ∅ then g x else (x.card : ℝ)⁻¹ * ∑ η ∈ x,
          (deathAccept φ c p h x η * g (x.erase η) + (1 - deathAccept φ c p h x η) * g x)) := by
  rw [birthDeathStep]

/-- The standing assumptions of SYNOPSIS item 110: `W` has finite positive volume, `h ≥ 0` is
measurable and locally stable with positive integrable `φ*`, `c* = ∫_W φ*`, `h(∅) > 0`, and
`p ∈ (0, 1)`. -/
structure BirthDeathSetting (W : Set E) (φ : E → ℝ) (c p : ℝ) (h : Finset E → ℝ) : Prop where
  /-- `W` is measurable. -/
  measurableSet : MeasurableSet W
  /-- `W` has positive volume. -/
  volume_pos : 0 < volume W
  /-- `W` has finite volume. -/
  volume_lt_top : volume W < ∞
  /-- `φ*` is positive. -/
  phi_pos : ∀ ξ, 0 < φ ξ
  /-- `φ*` is measurable. -/
  phi_measurable : Measurable φ
  /-- `φ*` is integrable on `W`. -/
  phi_integrable : IntegrableOn φ W
  /-- `c* = ∫_W φ*`. -/
  c_eq : c = ∫ ξ in W, φ ξ
  /-- `h` is nonnegative. -/
  h_nonneg : ∀ x, 0 ≤ h x
  /-- `h` is measurable. -/
  h_measurable : IsConfigMeasurable h
  /-- `h` is locally stable with bound `φ*`. -/
  locallyStable : IsLocallyStable W φ h
  /-- `h(∅) > 0`. -/
  h_empty_pos : 0 < h ∅
  /-- `p > 0`. -/
  p_pos : 0 < p
  /-- `p < 1`. -/
  p_lt_one : p < 1

/-- SYNOPSIS item 110: the chain is reversible with respect to `h`:
`∫ (T g) k h dΠ_W = ∫ g (T k) h dΠ_W` for bounded measurable `g`, `k`. -/
theorem birthDeath_reversible {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) {g k : Finset E → ℝ} (hg : IsConfigMeasurable g)
    (hk : IsConfigMeasurable k) (hgb : ∃ M, ∀ x, |g x| ≤ M) (hkb : ∃ M, ∀ x, |k x| ≤ M) :
    poissonIntegralReal W (fun x ↦ birthDeathStep W φ c p h g x * k x * h x) =
      poissonIntegralReal W (fun x ↦ g x * birthDeathStep W φ c p h k x * h x) := by
  sorry

/-- The normalising mass of the birth proposal is positive. -/
private lemma BirthDeathSetting.c_pos {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) : 0 < c := by
  rw [hs.c_eq, integral_pos_iff_support_of_nonneg (fun y ↦ (hs.phi_pos y).le) hs.phi_integrable]
  have hsupport : Function.support φ = Set.univ := by
    ext y
    simp [(hs.phi_pos y).ne']
  rw [hsupport, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact hs.volume_pos

/-- The conditional intensity is nonnegative for the target density. -/
private lemma BirthDeathSetting.papangelou_nonneg {W : Set E} {φ : E → ℝ} {c p : ℝ}
    {h : Finset E → ℝ} (hs : BirthDeathSetting W φ c p h) (x : Finset E) (y : E) :
    0 ≤ papangelou h x y := by
  rw [papangelou_def]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (hs.h_nonneg _) (hs.h_nonneg _)

/-- The birth integral is nonnegative for a nonnegative test function. -/
private lemma birthIntegral_nonneg {W : Set E} {φ : E → ℝ} {c p : ℝ} {h g : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) (hg : ∀ x, 0 ≤ g x) (x : Finset E) :
    0 ≤ ∫ ξ in W, φ ξ / c * (birthAccept φ c p h x ξ * g (insert ξ x) +
      (1 - birthAccept φ c p h x ξ) * g x) := by
  apply integral_nonneg fun ξ ↦ ?_
  have hacc : 0 ≤ birthAccept φ c p h x ξ := by
    rw [birthAccept_def]
    have hstay := sub_nonneg.mpr hs.p_lt_one.le
    exact le_min zero_le_one (div_nonneg
      (mul_nonneg (mul_nonneg (hs.papangelou_nonneg _ _) hstay) hs.c_pos.le)
      (mul_nonneg (mul_nonneg (hs.phi_pos ξ).le hs.p_pos.le) (by positivity)))
  have hre : 0 ≤ 1 - birthAccept φ c p h x ξ := sub_nonneg.mpr (min_le_left _ _)
  exact mul_nonneg (div_nonneg (hs.phi_pos ξ).le hs.c_pos.le)
    (add_nonneg (mul_nonneg hacc (hg _)) (mul_nonneg hre (hg _)))

/-- Every individual death proposal contributes nonnegative weight to a nonnegative test. -/
private lemma deathTerm_nonneg {W : Set E} {φ : E → ℝ} {c p : ℝ} {h g : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) (hg : ∀ x, 0 ≤ g x) (x : Finset E) (y : E) :
    0 ≤ deathAccept φ c p h x y * g (x.erase y) + (1 - deathAccept φ c p h x y) * g x := by
  have hac : 0 ≤ deathAccept φ c p h x y := by
    rw [deathAccept_def]
    have hstay := sub_nonneg.mpr hs.p_lt_one.le
    exact le_min zero_le_one (div_nonneg
      (mul_nonneg (mul_nonneg (hs.phi_pos y).le hs.p_pos.le) (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg (hs.papangelou_nonneg _ _) hstay) hs.c_pos.le))
  exact add_nonneg (mul_nonneg hac (hg _))
    (mul_nonneg (sub_nonneg.mpr (min_le_left _ _)) (hg _))

/-- The transition operator preserves nonnegative test functions. -/
private lemma birthDeathStep_nonneg {W : Set E} {φ : E → ℝ} {c p : ℝ} {h g : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) (hg : ∀ x, 0 ≤ g x) (x : Finset E) :
    0 ≤ birthDeathStep W φ c p h g x := by
  rw [birthDeathStep_def]
  refine add_nonneg (mul_nonneg hs.p_pos.le (birthIntegral_nonneg hs hg x))
    (mul_nonneg (sub_nonneg.mpr hs.p_lt_one.le) ?_)
  split_ifs
  · exact hg _
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun y _ ↦ deathTerm_nonneg hs hg x y)

/-- SYNOPSIS item 110: the chain is irreducible with respect to the point mass at `∅`: from every
configuration `x ⊆ W` with `h(x) > 0` it reaches `∅` with positive probability. -/
theorem birthDeath_irreducible {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) {x : Finset E} (hxW : (x : Set E) ⊆ W) (hx : 0 < h x) :
    ∃ m, 0 < (birthDeathStep W φ c p h)^[m] (fun y ↦ if y = ∅ then 1 else 0) x := by
  let g : Finset E → ℝ := fun y ↦ if y = ∅ then 1 else 0
  let T := birthDeathStep W φ c p h
  have hg (m : ℕ) (y : Finset E) : 0 ≤ T^[m] g y := by
    induction m generalizing y with
    | zero => simp only [Function.iterate_zero_apply, g]; split_ifs <;> norm_num
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact birthDeathStep_nonneg hs ih _
  have hreach : 0 < T^[x.card] g x := by
    induction x using Finset.induction_on with
    | empty => simp [g]
    | @insert a s ha ih =>
      have hmem : a ∈ insert a s := Finset.mem_insert_self _ _
      have hsub : s ⊆ insert a s := Finset.subset_insert _ _
      have hsW : (s : Set E) ⊆ W := fun _ hy ↦ hxW (hsub hy)
      have hspos : 0 < h s := ((isLocallyStable_consequences (fun y ↦ (hs.phi_pos y).le)
        hs.h_nonneg hs.locallyStable).2.1 _ _ hxW hsub hx)
      have hgoal := ih hsW hspos
      have hne : insert a s ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨a, hmem⟩
      have hcard : (0 : ℝ) < (insert a s).card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a, hmem⟩)
      have hA : 0 < deathAccept φ c p h (insert a s) a := by
        have hpap : 0 < papangelou h s a := by
          rw [papangelou_def, ite_eq_right hspos.ne']
          exact div_pos hx hspos
        rw [deathAccept_def, Finset.erase_insert ha]
        exact lt_min zero_lt_one (div_pos (mul_pos (mul_pos (hs.phi_pos a) hs.p_pos) hcard)
          (mul_pos (mul_pos hpap (sub_pos.mpr hs.p_lt_one)) hs.c_pos))
      rw [Finset.card_insert_of_notMem ha, ← Nat.succ_eq_add_one, Function.iterate_succ_apply']
      dsimp only [T]
      rw [birthDeathStep_def, ite_eq_right hne]
      refine add_pos_of_nonneg_of_pos (mul_nonneg hs.p_pos.le (birthIntegral_nonneg hs (hg _) _))
        (mul_pos (sub_pos.mpr hs.p_lt_one) (mul_pos (inv_pos.mpr hcard) ?_))
      refine Finset.sum_pos' (fun y _ ↦ deathTerm_nonneg hs (hg _) _ y) ⟨a, hmem, ?_⟩
      exact add_pos_of_pos_of_nonneg (mul_pos hA (by simpa only [Finset.erase_insert ha]))
        (mul_nonneg (sub_nonneg.mpr (min_le_left _ _)) (hg _ _))
  exact ⟨x.card, hreach⟩

/-- SYNOPSIS item 110: the chain is aperiodic: it stays at `∅` with positive probability. -/
theorem birthDeath_aperiodic {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) :
    0 < birthDeathStep W φ c p h (fun y ↦ if y = ∅ then 1 else 0) ∅ := by
  let g : Finset E → ℝ := fun y ↦ if y = ∅ then 1 else 0
  have hg (y : Finset E) : 0 ≤ g y := by dsimp only [g]; split_ifs <;> norm_num
  have hstep : 0 < birthDeathStep W φ c p h g ∅ := by
    rw [birthDeathStep_def, ite_eq_left rfl]
    have he : g ∅ = 1 := by simp [g]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hs.p_pos.le (birthIntegral_nonneg hs hg _))
      (mul_pos (sub_pos.mpr hs.p_lt_one) (he.symm ▸ zero_lt_one))
  exact hstep

/-- SYNOPSIS item 110: for every `β > 1` the chain is `V`-uniformly ergodic with
`V(x) = β^{n(x)}`: there are `R` and `r < 1` with `|T^m g(x) - π(g)| ≤ R V(x) r^m` for all
measurable `|g| ≤ V`; in particular it is geometrically ergodic. -/
theorem birthDeath_vUniformlyErgodic {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) {β : ℝ} (hβ : 1 < β) :
    ∃ R r : ℝ, 0 ≤ R ∧ 0 ≤ r ∧ r < 1 ∧ ∀ g : Finset E → ℝ, IsConfigMeasurable g →
      (∀ y, |g y| ≤ β ^ y.card) → ∀ x : Finset E, (x : Set E) ⊆ W → 0 < h x → ∀ m,
        |(birthDeathStep W φ c p h)^[m] g x - configExpectation W h g| ≤
          R * β ^ x.card * r ^ m := by
  sorry

/-- SYNOPSIS item 110: the chain is uniformly ergodic if and only if `n(x) ≤ n₀` on `{h > 0}`
for some `n₀`. -/
theorem birthDeath_uniformlyErgodic_iff {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) :
    (∃ R r : ℝ, 0 ≤ R ∧ 0 ≤ r ∧ r < 1 ∧ ∀ g : Finset E → ℝ, IsConfigMeasurable g →
      (∀ y, |g y| ≤ 1) → ∀ x : Finset E, (x : Set E) ⊆ W → 0 < h x → ∀ m,
        |(birthDeathStep W φ c p h)^[m] g x - configExpectation W h g| ≤ R * r ^ m) ↔
      ∃ n₀ : ℕ, ∀ x : Finset E, (x : Set E) ⊆ W → 0 < h x → x.card ≤ n₀ := by
  sorry

/-- SYNOPSIS item 110: if `n(x) ≤ n₀` on `{h > 0}` with `n₀ ≥ 1`, the total-variation distance
to the target after `m` steps is at most `(1 - min{1 - p, p / c*}^{n₀})^{⌊m / n₀⌋}`. -/
theorem birthDeath_tv_bound {W : Set E} {φ : E → ℝ} {c p : ℝ} {h : Finset E → ℝ}
    (hs : BirthDeathSetting W φ c p h) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (hbd : ∀ x : Finset E, (x : Set E) ⊆ W → 0 < h x → x.card ≤ n₀) {g : Finset E → ℝ}
    (hg : IsConfigMeasurable g) (hg01 : ∀ y, 0 ≤ g y ∧ g y ≤ 1) {x : Finset E}
    (hxW : (x : Set E) ⊆ W) (hx : 0 < h x) (m : ℕ) :
    |(birthDeathStep W φ c p h)^[m] g x - configExpectation W h g| ≤
      (1 - min (1 - p) (p / c) ^ n₀) ^ (m / n₀) := by
  sorry

end MSSS
