module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import TauCeti.Data.Finset.Basic
import TauCeti.Topology.Algebra.InfiniteSum.PiProd

/-!
# Markov random fields on finite graphs

SYNOPSIS items 47, 49, 50, and the exact part of item 65: Brook's factorisation lemma, the
Hammersley–Clifford theorem, Besag's auto-models, and the coding factorisation.

The site set `S` is finite and the state spaces `E i` are countable, so a density is a
probability mass function `π` on `Ω = ∏ E i`. The full conditional at site `i` is
`π_i(y ∣ x_{-i}) = π(x with x_i := y) / ∑_z π(x with x_i := z)`. Densities with respect to a
product reference measure on `ℝ^S` are not treated in this file.
Brook's factorisation uses Mathlib's telescoping finite product and positivity of a
summable nonnegative series. The Hammersley–Clifford proof uses Mathlib's powerset
splitting and TauCeti's alternating interval sum for finite sets. The four-cycle example uses
Mathlib's decidability of finite adjacency and clique predicates. The auto-model argument uses
Mathlib's finite subset sums and one-site update identities. The coding-set proof uses
TauCeti's summability criterion for finite products of nonnegative summable functions.

The asymptotic part of item 65 (consistency of maximum pseudolikelihood and coding estimators,
asymptotic normality of the coding estimator, and the coding likelihood-ratio test) is not
stated: the synopsis gives its hypotheses only qualitatively.

## Main definitions

* `MSSS.IsDensity π`, `MSSS.fullConditional π i x y`, `MSSS.marginal π i a`.
* `MSSS.SatisfiesPositivity π`: the support of `π` is the product of its marginal supports.
* `MSSS.IsMarkovRandomField G π`: every full conditional at `i` depends on `x_{-i}` only through
  the neighbours of `i` on conditioning configurations of positive mass.
* `MSSS.canonicalPotential π a A x`: the canonical (Möbius) potential relative to `a`.
* `MSSS.setConditional π A x z`: the conditional mass of `x_A = z_A` given `x_{S∖A}`.

## Main results

* `MSSS.brook_factorization`, `MSSS.eq_of_fullConditional_eq`: SYNOPSIS item 47.
* `MSSS.isMarkovRandomField_iff_factorization`,
  `MSSS.isMarkovRandomField_iff_canonicalPotential`, `MSSS.isMarkovRandomField_of_factorization`,
  `MSSS.setConditional_eq_of_eqOn_boundary`, `MSSS.exists_markovRandomField_not_factorization`:
  SYNOPSIS item 49.
* `MSSS.exists_autoModel`, `MSSS.fullConditional_autoModelDensity`,
  `MSSS.fullConditional_autoLogistic`:
  SYNOPSIS item 50.
* `MSSS.setConditional_codingSet`: SYNOPSIS item 65 (coding sets).
-/

public section

noncomputable section

open Finset

namespace MSSS

variable {S : Type*} [Fintype S] [DecidableEq S] {E : S → Type*}

/-- `π` is a probability mass function on `∏ E i`. -/
def IsDensity (π : (∀ i, E i) → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ HasSum π 1

/-- The **full conditional** `π_i(y ∣ x_{-i})`. -/
def fullConditional (π : (∀ i, E i) → ℝ) (i : S) (x : ∀ i, E i) (y : E i) : ℝ :=
  π (Function.update x i y) / ∑' z : E i, π (Function.update x i z)

/-- The marginal mass `π(x_i = a)`. -/
def marginal (π : (∀ i, E i) → ℝ) (i : S) (a : E i) : ℝ :=
  ∑' x : {x : ∀ i, E i // x i = a}, π x

/-- The **positivity condition**: the support of `π` is the product of its marginal supports. -/
def SatisfiesPositivity (π : (∀ i, E i) → ℝ) : Prop :=
  ∀ x, (∀ i, 0 < marginal π i (x i)) → 0 < π x

/-- `π` is a **Markov random field** for the graph `G` if its full conditionals agree
on positive-mass conditioning configurations that agree on the neighbours. -/
def IsMarkovRandomField (G : SimpleGraph S) (π : (∀ i, E i) → ℝ) : Prop :=
  ∀ i x x', (∀ j, G.Adj i j → x j = x' j) →
    0 < (∑' z : E i, π (Function.update x i z)) →
    0 < (∑' z : E i, π (Function.update x' i z)) →
    ∀ y, fullConditional π i x y = fullConditional π i x' y

/-- The **canonical potential** relative to the reference configuration `a`,
`V_A(x) = ∑_{B ⊆ A} (-1)^{|A ∖ B|} log π(x_B a_{S∖B})`. -/
def canonicalPotential (π : (∀ i, E i) → ℝ) (a : ∀ i, E i) (A : Finset S) (x : ∀ i, E i) : ℝ :=
  ∑ B ∈ A.powerset, (-1) ^ (A.card - B.card) * Real.log (π fun j ↦ if j ∈ B then x j else a j)

/-- The conditional mass `π(x_A = z_A ∣ x_{S∖A})`. -/
def setConditional (π : (∀ i, E i) → ℝ) (A : Finset S) (x z : ∀ i, E i) : ℝ :=
  π (fun j ↦ if j ∈ A then z j else x j) /
    ∑' a : (∀ i : A, E i), π fun j ↦ if hj : j ∈ A then a ⟨j, hj⟩ else x j

omit [Fintype S] [DecidableEq S] in
lemma isDensity_def {π : (∀ i, E i) → ℝ} : IsDensity π ↔ (∀ x, 0 ≤ π x) ∧ HasSum π 1 := Iff.rfl

omit [Fintype S] in
lemma fullConditional_def (π : (∀ i, E i) → ℝ) (i : S) (x : ∀ i, E i) (y : E i) :
    fullConditional π i x y =
      π (Function.update x i y) / ∑' z : E i, π (Function.update x i z) := by
  rw [fullConditional]

omit [Fintype S] [DecidableEq S] in
lemma marginal_def (π : (∀ i, E i) → ℝ) (i : S) (a : E i) :
    marginal π i a = ∑' x : {x : ∀ i, E i // x i = a}, π x := by
  rw [marginal]

omit [Fintype S] [DecidableEq S] in
lemma satisfiesPositivity_def {π : (∀ i, E i) → ℝ} :
    SatisfiesPositivity π ↔ ∀ x, (∀ i, 0 < marginal π i (x i)) → 0 < π x := Iff.rfl

omit [Fintype S] in
lemma isMarkovRandomField_def {G : SimpleGraph S} {π : (∀ i, E i) → ℝ} :
    IsMarkovRandomField G π ↔ ∀ i x x', (∀ j, G.Adj i j → x j = x' j) →
      0 < (∑' z : E i, π (Function.update x i z)) →
      0 < (∑' z : E i, π (Function.update x' i z)) →
      ∀ y, fullConditional π i x y = fullConditional π i x' y := Iff.rfl

omit [Fintype S] in
lemma canonicalPotential_def (π : (∀ i, E i) → ℝ) (a : ∀ i, E i) (A : Finset S)
    (x : ∀ i, E i) : canonicalPotential π a A x = ∑ B ∈ A.powerset,
      (-1) ^ (A.card - B.card) * Real.log (π fun j ↦ if j ∈ B then x j else a j) := by
  rw [canonicalPotential]

omit [Fintype S] in
lemma setConditional_def (π : (∀ i, E i) → ℝ) (A : Finset S) (x z : ∀ i, E i) :
    setConditional π A x z = π (fun j ↦ if j ∈ A then z j else x j) /
      ∑' a : (∀ i : A, E i), π fun j ↦ if hj : j ∈ A then a ⟨j, hj⟩ else x j := by
  rw [setConditional]

/-! ### Brook's lemma (SYNOPSIS item 47) -/

omit [Fintype S] [DecidableEq S] in
/-- A positive configuration gives a positive site marginal. -/
lemma IsDensity.marginal_pos {π : (∀ i, E i) → ℝ} (hπ : IsDensity π)
    {x : ∀ i, E i} (hx : 0 < π x) (i : S) : 0 < marginal π i (x i) := by
  rw [marginal]
  exact (hπ.2.summable.comp_injective Subtype.coe_injective).tsum_pos
    (fun y ↦ hπ.1 y) ⟨x, rfl⟩ hx

omit [Fintype S] in
/-- The normalising sum in a full conditional is positive if the configuration has positive
mass. -/
lemma IsDensity.tsum_update_pos {π : (∀ i, E i) → ℝ} (hπ : IsDensity π)
    {x : ∀ i, E i} (hx : 0 < π x) (i : S) :
    0 < ∑' z : E i, π (Function.update x i z) := by
  exact (hπ.2.summable.comp_injective (Function.update_injective x i)).tsum_pos
    (fun z ↦ hπ.1 _) (x i) (by simpa only [Function.comp_apply, Function.update_eq_self] using hx)

omit [Fintype S] in
/-- The full conditional at the current state detects positivity of the configuration. -/
lemma IsDensity.fullConditional_self_pos_iff {π : (∀ i, E i) → ℝ} (hπ : IsDensity π)
    (i : S) (x : ∀ i, E i) : 0 < fullConditional π i x (x i) ↔ 0 < π x := by
  rw [fullConditional_def, Function.update_eq_self]
  constructor
  · intro hp
    contrapose! hp
    exact div_nonpos_of_nonpos_of_nonneg hp (tsum_nonneg fun _ ↦ hπ.1 _)
  · intro hp
    exact div_pos hp (hπ.tsum_update_pos hp i)

omit [Fintype S] in
/-- With equal full conditionals, the likelihood ratio is constant across a positive
one-coordinate update. -/
lemma IsDensity.div_eq_div_update {π π' : (∀ i, E i) → ℝ}
    (hπ : IsDensity π) (hπ' : IsDensity π')
    (h : ∀ i x y, fullConditional π i x y = fullConditional π' i x y)
    {x : ∀ i, E i} (hx : 0 < π x) (hx' : 0 < π' x) (i : S) (y : E i)
    (hy : 0 < π (Function.update x i y)) :
    π' (Function.update x i y) / π (Function.update x i y) = π' x / π x := by
  have hcond :
      fullConditional π i x y / fullConditional π i x (x i) =
        fullConditional π' i x y / fullConditional π' i x (x i) := by
    rw [h i x y, h i x (x i)]
  simp only [fullConditional_def, Function.update_eq_self,
    div_div_div_cancel_right₀ (hπ.tsum_update_pos hx i).ne',
    div_div_div_cancel_right₀ (hπ'.tsum_update_pos hx' i).ne'] at hcond
  apply (div_eq_div_iff hy.ne' hx.ne').mpr
  simpa only [mul_comm] using ((div_eq_div_iff hx.ne' hx'.ne').mp hcond).symm

/-- SYNOPSIS item 47, Brook's factorisation lemma: for `π` with the positivity condition and
`x, y` in its support, `π(x)/π(y)` is the product over `i` of the ratios of the full
conditionals at `x_i` and `y_i` given `x_1, …, x_{i-1}, y_{i+1}, …, y_n`. -/
theorem brook_factorization {n : ℕ} {E : Fin n → Type*} [∀ i, Countable (E i)]
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : SatisfiesPositivity π) {x y : ∀ i, E i}
    (hx : 0 < π x) (hy : 0 < π y) :
    π x / π y = ∏ i, fullConditional π i (fun j ↦ if j < i then x j else y j) (x i) /
      fullConditional π i (fun j ↦ if j < i then x j else y j) (y i) := by
  let path (m : ℕ) (j : Fin n) : E j := if (j : ℕ) < m then x j else y j
  have hp (m : ℕ) : 0 < π (path m) := hpos _ (fun j ↦ by
    by_cases hj : (j : ℕ) < m
    · simpa only [path, ite_eq_left hj] using hπ.marginal_pos hx j
    · simpa only [path, ite_eq_right hj] using hπ.marginal_pos hy j)
  have hzero : path 0 = y := by
    funext j
    simp only [path, Nat.not_lt_zero, ite_false]
  have hlast : path n = x := by
    funext j
    simp only [path, ite_eq_left j.isLt]
  let mass (m : ℕ) : ℝˣ := Units.mk0 (π (path m)) (hp m).ne'
  symm
  calc
    _ = ∏ i : Fin n, ((mass (i + 1) / mass i : ℝˣ) : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      have hyi : Function.update (path i) i (y i) = path i := by
        apply Function.update_eq_self_iff.mpr
        simp only [path, lt_irrefl, ite_false]
      have hxi : Function.update (path i) i (x i) = path ((i : ℕ) + 1) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, path, Nat.lt_succ_self, ite_true]
        · rw [Function.update_of_ne hj]
          have hval : (j : ℕ) ≠ i := fun h ↦ hj (Fin.ext h)
          simp only [path, Nat.lt_succ_iff_lt_or_eq, hval, or_false]
      have hratio : fullConditional π i (path i) (x i) / fullConditional π i (path i) (y i) =
          ((mass (i + 1) / mass i : ℝˣ) : ℝ) := by
        rw [fullConditional_def, fullConditional_def, hxi, hyi,
          div_div_div_cancel_right₀ (hπ.tsum_update_pos (hp i) i).ne']
        simp only [mass, Units.val_div_eq_div_val, Units.val_mk0]
      exact hratio
    _ = ((mass n / mass 0 : ℝˣ) : ℝ) := by
      rw [← Units.coe_prod, Fin.prod_univ_eq_prod_range (fun m ↦ mass (m + 1) / mass m),
        Finset.prod_range_div]
    _ = π x / π y := by
      simp only [mass, Units.val_div_eq_div_val, Units.val_mk0, hlast, hzero]

/-- SYNOPSIS item 47: two densities with the positivity condition and the same full
conditionals coincide. -/
theorem eq_of_fullConditional_eq [∀ i, Countable (E i)] {π π' : (∀ i, E i) → ℝ}
    (hπ : IsDensity π) (hπ' : IsDensity π') (hpos : SatisfiesPositivity π)
    (hpos' : SatisfiesPositivity π')
    (h : ∀ i x y, fullConditional π i x y = fullConditional π' i x y) : π = π' := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · let _ := hS
    funext x
    have uniqueMass (p : (∀ i, E i) → ℝ) (hp : IsDensity p) : p x = 1 := by
      rw [← hp.2.tsum_eq, tsum_eq_single x (fun y hy ↦ (hy (Subsingleton.elim _ _)).elim)]
    exact (uniqueMass π hπ).trans (uniqueMass π' hπ').symm
  obtain ⟨i⟩ := hS
  have hs (z : ∀ i, E i) : 0 < π z ↔ 0 < π' z := by
    rw [← hπ.fullConditional_self_pos_iff i, ← hπ'.fullConditional_self_pos_iff i, h]
  obtain ⟨x, hx⟩ : ∃ x, 0 < π x := by
    by_contra! hzero
    have hz (x) : π x = 0 := le_antisymm (hzero x) (hπ.1 x)
    have ht := hπ.2.tsum_eq
    simp only [hz, tsum_zero] at ht
    exact zero_ne_one ht
  let c := π' x / π x
  have hmul (y : ∀ i, E i) : π' y = c * π y := by
    by_cases hy : 0 < π y
    · let path (A : Finset S) (j : S) : E j := if j ∈ A then y j else x j
      have hp {p : (∀ i, E i) → ℝ} (hd : IsDensity p) (hsupp : SatisfiesPositivity p)
          (hpx : 0 < p x) (hpy : 0 < p y) (A : Finset S) : 0 < p (path A) :=
        hsupp _ fun j ↦ by
        by_cases hj : j ∈ A
        · simpa only [path, ite_eq_left hj] using hd.marginal_pos hpy j
        · simpa only [path, ite_eq_right hj] using hd.marginal_pos hpx j
      have hpath := hp hπ hpos hx hy
      have hpath' := hp hπ' hpos' ((hs x).mp hx) ((hs y).mp hy)
      have hratio (A : Finset S) : π' (path A) / π (path A) = c := by
        induction A using Finset.induction_on with
        | empty => simp only [path, notMem_empty, ite_false, c]
        | insert j A hj ih =>
          have hu : Function.update (path A) j (y j) = path (insert j A) := by
            funext k
            by_cases hk : k = j
            · subst k
              simp only [Function.update_self, path, mem_insert_self, ite_true]
            · simp only [Function.update_of_ne hk, path, mem_insert, hk, false_or]
          have hup : 0 < π (Function.update (path A) j (y j)) := hu ▸ hpath (insert j A)
          have heq := hπ.div_eq_div_update hπ' h (hpath A) (hpath' A) j (y j) hup
          rw [hu, ih] at heq
          exact heq
      have heq := hratio univ
      simp only [path, mem_univ, ite_true] at heq
      exact (div_eq_iff hy.ne').mp heq
    · have hz := le_antisymm (le_of_not_gt hy) (hπ.1 y)
      have hz' := le_antisymm (le_of_not_gt ((hs y).not.mp hy)) (hπ'.1 y)
      rw [hz, hz', mul_zero]
  have hc : HasSum π' c := by
    simpa only [mul_one, ← hmul] using hπ.2.mul_left c
  have hc1 : c = 1 := hc.unique hπ'.2
  funext y
  rw [hmul, hc1, one_mul]

/-! ### The Hammersley–Clifford theorem (SYNOPSIS item 49) -/

omit [Fintype S] in
/-- Matching neighbours and current values gives the same likelihood ratio for an update. -/
private lemma IsMarkovRandomField.div_update_eq {G : SimpleGraph S} {π : (∀ i, E i) → ℝ}
    (hG : IsMarkovRandomField G π) (hπ : IsDensity π) (hpos : ∀ x, 0 < π x)
    (i : S) (x x' : ∀ i, E i) (hn : ∀ j, G.Adj i j → x j = x' j)
    (hi : x i = x' i) (y : E i) :
    π (Function.update x i y) / π x = π (Function.update x' i y) / π x' := by
  have hcond := hG i x x' hn (hπ.tsum_update_pos (hpos x) i)
    (hπ.tsum_update_pos (hpos x') i)
  have h := congrArg₂ (· / ·) (hcond y) (hcond (x i))
  rwa [fullConditional_def, fullConditional_def, fullConditional_def, fullConditional_def,
    Function.update_eq_self, hi, Function.update_eq_self,
    div_div_div_cancel_right₀ (hπ.tsum_update_pos (hpos x) i).ne',
    div_div_div_cancel_right₀ (hπ.tsum_update_pos (hpos x') i).ne'] at h

omit [Fintype S] in
/-- A non-clique has an absent edge, so the two corresponding log-density differences cancel. -/
private lemma canonicalPotential_eq_zero_of_not_isClique {G : SimpleGraph S}
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : ∀ x, 0 < π x)
    (hG : IsMarkovRandomField G π) (a x : ∀ i, E i) {A : Finset S}
    (hA : ¬ G.IsClique (A : Set S)) : canonicalPotential π a A x = 0 := by
  simp only [SimpleGraph.isClique_iff, Set.Pairwise, mem_coe] at hA
  push Not at hA
  obtain ⟨i, hi, j, hj, hij, hnon⟩ := hA
  let p (B : Finset S) (k : S) := if k ∈ B then x k else a k
  let sign (A B : Finset S) : ℝ := (-1) ^ (A.card - B.card)
  have hsplit {i : S} {B : Finset S} (hi : i ∉ B) (f : Finset S → ℝ) :
      (∑ T ∈ (insert i B).powerset, sign (insert i B) T * f T) =
        ∑ T ∈ B.powerset, sign B T * (f (insert i T) - f T) := by
    rw [sum_powerset_insert hi, ← sum_add_distrib]
    refine sum_congr rfl fun T hT ↦ ?_
    have hiT : i ∉ T := fun hiT ↦ hi (mem_powerset.mp hT hiT)
    have hcard := card_le_card (mem_powerset.mp hT)
    simp only [sign, card_insert_of_notMem hi, card_insert_of_notMem hiT, Nat.add_sub_add_right]
    have hsub : B.card + 1 - T.card = B.card - T.card + 1 := by omega
    rw [hsub, pow_succ]
    ring
  rw [canonicalPotential_def, ← insert_erase hi,
    hsplit (notMem_erase i A) (fun B ↦ Real.log (π (p B)))]
  have hj' : j ∈ A.erase i := mem_erase.mpr ⟨hij.symm, hj⟩
  rw [← insert_erase hj', hsplit (notMem_erase j (A.erase i))]
  refine sum_eq_zero fun T hT ↦ ?_
  have hiT : i ∉ T := fun hiT ↦ notMem_erase i A
    (mem_of_mem_erase (mem_powerset.mp hT hiT))
  have hiT' : i ∉ insert j T := by simp only [mem_insert, hij, false_or, hiT, not_false_eq_true]
  have hup (B : Finset S) : Function.update (p B) i (x i) = p (insert i B) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [Function.update_self, p, mem_insert_self, ite_true]
    · simp only [Function.update_of_ne hk, p, mem_insert, hk, false_or]
  have hn (k : S) (hk : G.Adj i k) : p T k = p (insert j T) k := by
    have hkj : k ≠ j := fun hkj ↦ hnon (hkj ▸ hk)
    simp only [p, mem_insert, hkj, false_or]
  have heq : p T i = p (insert j T) i := by simp only [p, hiT, hiT', ite_false]
  have hr := hG.div_update_eq hπ hpos i (p T) (p (insert j T)) hn heq (x i)
  rw [hup, hup] at hr
  have hlog := congrArg Real.log hr
  rw [Real.log_div (hpos _).ne' (hpos _).ne', Real.log_div (hpos _).ne' (hpos _).ne'] at hlog
  rw [hlog, sub_self, mul_zero]

omit [Fintype S] in
/-- A canonical potential depends only on the coordinates of its indexing set. -/
private lemma canonicalPotential_congr {π : (∀ i, E i) → ℝ} {a x x' : ∀ i, E i}
    {T : Finset S} (h : ∀ i ∈ T, x i = x' i) :
    canonicalPotential π a T x = canonicalPotential π a T x' := by
  rw [canonicalPotential_def, canonicalPotential_def]
  refine sum_congr rfl fun U hU ↦ ?_
  refine congrArg (fun v ↦ (-1) ^ (T.card - U.card) * Real.log (π v)) ?_
  funext i
  by_cases hi : i ∈ U
  · simp only [hi, ite_true, h i (mem_powerset.mp hU hi)]
  · simp only [hi, ite_false]

/-- Möbius inversion reconstructs the log density from the canonical potentials. -/
private lemma sum_canonicalPotential (π : (∀ i, E i) → ℝ) (a x : ∀ i, E i) :
    ∑ A : Finset S, canonicalPotential π a A x = Real.log (π x) := by
  let f (B : Finset S) := Real.log (π fun j ↦ if j ∈ B then x j else a j)
  calc
    ∑ A : Finset S, canonicalPotential π a A x =
        ∑ B : Finset S, ∑ A ∈ Icc B univ, (-1 : ℝ) ^ (A.card - B.card) * f B := by
      simp only [canonicalPotential]
      refine sum_comm' (t' := univ) (s' := fun B ↦ Icc B univ)
        (fun A B ↦ ?_)
      simp only [mem_univ, mem_powerset, mem_Icc, subset_univ, and_true, true_and]
    _ = f univ := by
      -- Apply TauCeti's alternating sum formula on inclusion intervals.
      simp only [← sum_mul, sum_Icc_neg_one_pow_card_sub_card_left, ite_mul, one_mul, zero_mul,
        sum_ite_eq', mem_univ, ite_true]
    _ = Real.log (π x) := by simp only [f, mem_univ, ite_true]

/-- Clique factors outside a site cancel on conditioning configurations of positive mass. -/
private lemma isMarkovRandomField_of_clique_product (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} {φ : Finset S → (∀ i, E i) → ℝ}
    (hloc : ∀ C x x', (∀ j ∈ C, x j = x' j) → φ C x = φ C x')
    (hcl : ∀ C : Finset S, ¬ G.IsClique (C : Set S) → ∀ x, φ C x = 1)
    (hprod : ∀ x, π x = ∏ C : Finset S, φ C x) : IsMarkovRandomField G π := by
  intro i x x' hn hx hx' y
  let R (x : ∀ i, E i) := ∏ C ∈ (univ : Finset (Finset S)).filter (fun C ↦ i ∉ C), φ C x
  let P (x : ∀ i, E i) (y : E i) :=
    ∏ C ∈ (univ : Finset (Finset S)).filter (fun C ↦ i ∈ C), φ C (Function.update x i y)
  have hsplit (x : ∀ i, E i) (y : E i) : π (Function.update x i y) = R x * P x y := by
    rw [hprod, ← prod_filter_mul_prod_filter_not _ (fun C ↦ i ∈ C), mul_comm]
    refine congrArg (· * P x y) (prod_congr rfl fun C hC ↦ ?_)
    refine hloc _ _ _ fun j hj ↦ ?_
    have hji : j ≠ i := fun hji ↦ (mem_filter.mp hC).2 (hji ▸ hj)
    simp only [Function.update_of_ne hji]
  have hR (u : ∀ i, E i) (hu : 0 < ∑' z : E i, π (Function.update u i z)) : R u ≠ 0 := by
    intro hzero
    simp only [hsplit, hzero, zero_mul, tsum_zero, lt_irrefl] at hu
  have hP (y : E i) : P x y = P x' y := by
    refine prod_congr rfl fun C hC ↦ ?_
    by_cases h : G.IsClique (C : Set S)
    · refine hloc _ _ _ fun j hj ↦ ?_
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hji, hn j (h (mem_filter.mp hC).2 hj (Ne.symm hji))]
    · rw [hcl C h, hcl C h]
  simp only [fullConditional_def, hsplit, tsum_mul_left, mul_div_mul_left _ _ (hR x hx),
    mul_div_mul_left _ _ (hR x' hx'), hP]

/-- Exponentiating the canonical potentials gives a positive local clique factorisation. -/
private lemma exists_pos_factorization_of_canonicalPotential (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} (hpos : ∀ x, 0 < π x) (a : ∀ i, E i)
    (hzero : ∀ A : Finset S, ¬ G.IsClique (A : Set S) → ∀ x, canonicalPotential π a A x = 0) :
    ∃ φ : Finset S → (∀ i, E i) → ℝ, (∀ C x, 0 < φ C x) ∧
      (∀ C x x', (∀ j ∈ C, x j = x' j) → φ C x = φ C x') ∧
      (∀ C : Finset S, ¬ G.IsClique (C : Set S) → ∀ x, φ C x = 1) ∧
      ∀ x, π x = ∏ C : Finset S, φ C x := by
  refine ⟨fun A x ↦ Real.exp (canonicalPotential π a A x), fun _ _ ↦ Real.exp_pos _, ?_, ?_, ?_⟩
  · intro A x x' hx
    exact congrArg Real.exp (canonicalPotential_congr hx)
  · intro A hA x
    simp only [hzero A hA x, Real.exp_zero]
  · intro x
    simp only [← Real.exp_sum, sum_canonicalPotential, Real.exp_log (hpos x)]

/-- SYNOPSIS item 49, Hammersley–Clifford theorem: a positive density is a Markov random field
for `G` if and only if it factorises as a product of positive functions `φ_C(x_C)` over the
cliques `C` (the factors on non-cliques being `1`). -/
theorem isMarkovRandomField_iff_factorization [∀ i, Countable (E i)] (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : ∀ x, 0 < π x) :
    IsMarkovRandomField G π ↔ ∃ φ : Finset S → (∀ i, E i) → ℝ, (∀ C x, 0 < φ C x) ∧
      (∀ C x x', (∀ j ∈ C, x j = x' j) → φ C x = φ C x') ∧
      (∀ C : Finset S, ¬ G.IsClique (C : Set S) → ∀ x, φ C x = 1) ∧
      ∀ x, π x = ∏ C : Finset S, φ C x := by
  constructor
  · intro hG
    have hne : Nonempty (∀ i, E i) := by
      by_contra h
      let : IsEmpty (∀ i, E i) := not_nonempty_iff.mp h
      have hz := hπ.2.tsum_eq
      simp only [tsum_empty, zero_ne_one] at hz
    let a : ∀ i, E i := Classical.choice hne
    exact exists_pos_factorization_of_canonicalPotential G hpos a
      (fun _ hA x ↦ canonicalPotential_eq_zero_of_not_isClique hπ hpos hG a x hA)
  · rintro ⟨φ, -, hloc, hcl, hprod⟩
    exact isMarkovRandomField_of_clique_product G hloc hcl hprod

/-- SYNOPSIS item 49: equivalently, a positive density is a Markov random field for `G` if and
only if its canonical potential vanishes on every non-clique. -/
theorem isMarkovRandomField_iff_canonicalPotential [∀ i, Countable (E i)] (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : ∀ x, 0 < π x) (a : ∀ i, E i) :
    IsMarkovRandomField G π ↔
      ∀ A : Finset S, ¬ G.IsClique (A : Set S) → ∀ x, canonicalPotential π a A x = 0 := by
  constructor
  · exact fun hG _ hA x ↦ canonicalPotential_eq_zero_of_not_isClique hπ hpos hG a x hA
  · intro hzero
    exact (isMarkovRandomField_iff_factorization G hπ hpos).2
      (exists_pos_factorization_of_canonicalPotential G hpos a hzero)

/-- SYNOPSIS item 49: without positivity, any nonnegative clique factorisation `∏_C φ_C(x_C)`
defines a Markov random field, and its normalisation is a density whenever the product is
summable with positive sum. -/
theorem isMarkovRandomField_of_factorization [∀ i, Countable (E i)] (G : SimpleGraph S)
    (φ : Finset S → (∀ i, E i) → ℝ) (hφ : ∀ C x, 0 ≤ φ C x)
    (hloc : ∀ C x x', (∀ j ∈ C, x j = x' j) → φ C x = φ C x')
    (hcl : ∀ C : Finset S, ¬ G.IsClique (C : Set S) → ∀ x, φ C x = 1) :
    IsMarkovRandomField G (fun x ↦ ∏ C : Finset S, φ C x) ∧
      (Summable (fun x ↦ ∏ C : Finset S, φ C x) → 0 < ∑' x, ∏ C : Finset S, φ C x →
        IsDensity fun x ↦ (∏ C : Finset S, φ C x) / ∑' x', ∏ C : Finset S, φ C x') := by
  refine ⟨isMarkovRandomField_of_clique_product G hloc hcl (fun _ ↦ rfl), ?_⟩
  intro hsum hz
  refine ⟨fun x ↦ div_nonneg (Finset.prod_nonneg fun C _ ↦ hφ C x) hz.le, ?_⟩
  simpa only [div_self hz.ne'] using hsum.hasSum.div_const (∑' x, ∏ C : Finset S, φ C x)

-- Preserve the finite-site signature of the stated theorem.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 49: for a positive Markov random field, the conditional law of `x_A` given
`x_{S∖A}` depends only on `x_{∂A}`. -/
theorem setConditional_eq_of_eqOn_boundary [∀ i, Countable (E i)] (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : ∀ x, 0 < π x)
    (hG : IsMarkovRandomField G π) (A : Finset S) {x x' : ∀ i, E i}
    (h : ∀ j ∉ A, (∃ i ∈ A, G.Adj i j) → x j = x' j) :
    setConditional π A x = setConditional π A x' := by
  let v (w : ∀ i, E i) (j : S) := if j ∈ A then x j else w j
  let c : ℝ := π (v x) / π (v x')
  have hc : c ≠ 0 := (div_pos (hpos _) (hpos _)).ne'
  have hp (z : ∀ i, E i) :
      π (fun j ↦ if j ∈ A then z j else x j) =
        c * π (fun j ↦ if j ∈ A then z j else x' j) := by
    let p (B : Finset S) (w : ∀ i, E i) (j : S) := if j ∈ B then z j else v w j
    have hp' (B : Finset S) (hB : B ⊆ A) : π (p B x) / π (p B x') = c := by
      induction B using Finset.induction_on with
      | empty => simp only [p, notMem_empty, ite_false, c]
      | @insert i B hi ih =>
        have hiA := hB (mem_insert_self i B)
        have hn : ∀ j, G.Adj i j → p B x j = p B x' j := by
          intro j hj
          by_cases hjA : j ∈ A
          · simp only [p, v, hjA, ite_true]
          · have hjB : j ∉ B := fun hjB ↦ hjA (hB (mem_insert_of_mem hjB))
            simp only [p, v, hjA, hjB, ite_false, h j hjA ⟨i, hiA, hj⟩]
        have hu (w : ∀ i, E i) : Function.update (p B w) i (z i) = p (insert i B) w := by
          funext j
          by_cases hj : j = i
          · subst j
            simp only [Function.update_self, p, mem_insert_self, ite_true]
          · simp only [Function.update_of_ne hj, p, mem_insert, hj, false_or]
        have hbase : p B x i = p B x' i := by simp only [p, v, hi, hiA, ite_false, ite_true]
        have hr := hG.div_update_eq hπ hpos i (p B x) (p B x') hn hbase (z i)
        rw [hu x, hu x'] at hr
        rw [← ih ((subset_insert i B).trans hB)]
        exact (div_eq_div_iff (hpos _).ne' (hpos _).ne').2
          (((div_eq_div_iff (hpos _).ne' (hpos _).ne').1 hr).trans (mul_comm _ _))
    have hr := (div_eq_iff (hpos _).ne').1 (hp' A Subset.rfl)
    have hu (w : ∀ i, E i) : p A w = fun j ↦ if j ∈ A then z j else w j := by
      funext j
      by_cases hj : j ∈ A <;> simp only [p, v, hj, ite_true, ite_false]
    simpa only [hu] using hr
  funext z
  have ha (a : ∀ i : A, E i) :
      π (fun j ↦ if hj : j ∈ A then a ⟨j, hj⟩ else x j) =
        c * π (fun j ↦ if hj : j ∈ A then a ⟨j, hj⟩ else x' j) := by
    let a' (j : S) := if hj : j ∈ A then a ⟨j, hj⟩ else x j
    have hsplice (w : ∀ i, E i) :
        (fun j ↦ if j ∈ A then a' j else w j) =
          (fun j ↦ if hj : j ∈ A then a ⟨j, hj⟩ else w j) := by
      funext j
      by_cases hj : j ∈ A <;> simp only [a', hj, ite_true, ite_false, dite_true, dite_false]
    simpa only [hsplice] using hp a'
  simp only [setConditional_def, hp, ha, tsum_mul_left]
  exact mul_div_mul_left _ _ hc

/-- The three configurations in the support of the four-cycle example. -/
private def fourCycleSupport : Finset (Fin 4 → Bool) :=
  {![true, false, false, false], ![false, true, false, false], ![false, false, true, true]}

/-- Among the three supported configurations, a site's neighbours determine that site. -/
private lemma fourCycleSupport_agree (i : Fin 4) (x x' : Fin 4 → Bool)
    (hx : x ∈ fourCycleSupport) (hx' : x' ∈ fourCycleSupport)
    (hn : ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → x j = x' j) : x i = x' i := by
  revert i x x'
  decide

/-- Each clique projection of the all-false configuration occurs in the support. -/
private lemma fourCycleSupport_clique (C : Finset (Fin 4))
    (hC : (SimpleGraph.cycleGraph 4).IsClique (C : Set (Fin 4))) :
    ∃ x ∈ fourCycleSupport, ∀ j ∈ C, x j = false := by
  revert C
  decide

/-- The density uniform on the three configurations of the four-cycle example. -/
private def fourCycleDensity (x : Fin 4 → Bool) : ℝ :=
  if x ∈ fourCycleSupport then 1 / 3 else 0

/-- The uniform mass on the four-cycle support is a probability mass function. -/
private lemma isDensity_fourCycleDensity : IsDensity (E := fun _ ↦ Bool) fourCycleDensity := by
  have hcard : fourCycleSupport.card = 3 := by decide
  refine ⟨fun x ↦ by dsimp only [fourCycleDensity]; split <;> norm_num, ?_⟩
  convert hasSum_fintype fourCycleDensity using 1
  simp only [fourCycleDensity, ← Finset.sum_filter, filter_mem_eq_inter, univ_inter,
    sum_const, hcard]
  norm_num

/-- Replacing a coordinate does not change the other coordinates of the four-cycle. -/
private lemma fourCycle_update_neighbours (i : Fin 4) (x : Fin 4 → Bool) (y : Bool) :
    ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → Function.update x i y j = x j :=
  fun _ hj ↦ Function.update_of_ne hj.ne' _ _

/-- A positive conditioning fibre of the four-cycle example has one supported extension. -/
private lemma fourCycleDensity_fibre (i : Fin 4) (x : Fin 4 → Bool)
    (h : 0 < ∑' z : Bool, fourCycleDensity (Function.update x i z)) :
    ∃ z : Bool, Function.update x i z ∈ fourCycleSupport ∧
      ∀ y, fullConditional (E := fun _ ↦ Bool) fourCycleDensity i x y =
        if y = z then 1 else 0 := by
  have hex : ∃ z : Bool, Function.update x i z ∈ fourCycleSupport := by
    by_contra! hn
    simp only [fourCycleDensity, hn, ite_false, tsum_zero, lt_irrefl] at h
  obtain ⟨z, hz⟩ := hex
  have hface (y : Bool) : Function.update x i y ∈ fourCycleSupport ↔ y = z := by
    constructor
    · intro hy
      simpa only [Function.update_self] using fourCycleSupport_agree i _ _ hy hz (fun j hj ↦
        (fourCycle_update_neighbours i x y j hj).trans
          (fourCycle_update_neighbours i x z j hj).symm)
    · rintro rfl
      exact hz
  refine ⟨z, hz, fun y ↦ ?_⟩
  rw [fullConditional_def]
  simp only [fourCycleDensity, hface]
  split <;> norm_num

/-- Every positive conditioning fibre of the four-cycle example has a neighbour-determined law. -/
private lemma isMarkovRandomField_fourCycleDensity :
    IsMarkovRandomField (E := fun _ ↦ Bool) (SimpleGraph.cycleGraph 4) fourCycleDensity := by
  intro i x x' hn hx hx' y
  obtain ⟨z, hz, h⟩ := fourCycleDensity_fibre i x hx
  obtain ⟨z', hz', h'⟩ := fourCycleDensity_fibre i x' hx'
  have heq : z = z' := by
    simpa only [Function.update_self] using fourCycleSupport_agree i _ _ hz hz' (fun j hj ↦
      (fourCycle_update_neighbours i x z j hj).trans <|
        (hn j hj).trans (fourCycle_update_neighbours i x' z' j hj).symm)
  rw [h y, h' y, heq]

/-- SYNOPSIS item 49: positivity cannot be dropped. On the `2 × 2` grid (the `4`-cycle) with
binary states there is a Markov random field without a nonnegative clique factorisation. -/
theorem exists_markovRandomField_not_factorization :
    ∃ π : (Fin 4 → Bool) → ℝ, IsDensity π ∧ IsMarkovRandomField (SimpleGraph.cycleGraph 4) π ∧
      ¬ ∃ φ : Finset (Fin 4) → (Fin 4 → Bool) → ℝ, (∀ C x, 0 ≤ φ C x) ∧
        (∀ C x x', (∀ j ∈ C, x j = x' j) → φ C x = φ C x') ∧
        (∀ C : Finset (Fin 4), ¬ (SimpleGraph.cycleGraph 4).IsClique (C : Set (Fin 4)) →
          ∀ x, φ C x = 1) ∧
        ∀ x, π x = ∏ C : Finset (Fin 4), φ C x := by
  refine ⟨fourCycleDensity, isDensity_fourCycleDensity, isMarkovRandomField_fourCycleDensity, ?_⟩
  rintro ⟨φ, hφ, hloc, hcl, hprod⟩
  let a : Fin 4 → Bool := fun _ ↦ false
  have ha : a ∉ fourCycleSupport := by decide
  have hpos : 0 < ∏ C : Finset (Fin 4), φ C a := by
    apply Finset.prod_pos
    intro C _
    by_cases hC : (SimpleGraph.cycleGraph 4).IsClique (C : Set (Fin 4))
    · obtain ⟨x, hx, h⟩ := fourCycleSupport_clique C hC
      rw [hloc C a x (fun j hj ↦ (h j hj).symm)]
      by_contra! hz
      have hzero := le_antisymm hz (hφ C x)
      have hm := hprod x
      rw [fourCycleDensity, ite_eq_left hx, ← Finset.prod_erase_mul _ _ (Finset.mem_univ C),
        hzero, mul_zero] at hm
      norm_num at hm
    · simpa only [hcl C hC a] using (zero_lt_one : (0 : ℝ) < 1)
  rw [← hprod a, fourCycleDensity, ite_eq_right ha] at hpos
  exact lt_irrefl _ hpos

/-! ### Auto-models (SYNOPSIS item 50) -/

section AutoModel

variable [∀ i, Countable (E i)] [∀ i, Zero (E i)]

/-- The exponent `∑_i (α_i B_i(x_i) + C_i(x_i)) + ∑_{i<j} β_{ij} B_i(x_i) B_j(x_j)` of an
auto-model, the pair sum written as half the sum over ordered pairs `i ≠ j`. -/
def autoModel (α : S → ℝ) (β : S → S → ℝ) (B C : ∀ i, E i → ℝ) (x : ∀ i, E i) : ℝ :=
  ∑ i, (α i * B i (x i) + C i (x i)) +
    (1 / 2) * ∑ i, ∑ j ∈ univ.erase i, β i j * B i (x i) * B j (x j)

omit [∀ i, Countable (E i)] [∀ i, Zero (E i)] in
lemma autoModel_def (α : S → ℝ) (β : S → S → ℝ) (B C : ∀ i, E i → ℝ) (x : ∀ i, E i) :
    autoModel α β B C x = ∑ i, (α i * B i (x i) + C i (x i)) +
      (1 / 2) * ∑ i, ∑ j ∈ univ.erase i, β i j * B i (x i) * B j (x j) := by
  rw [autoModel]

/-- A symmetric interaction supported on the pairs incident to `i` is counted twice. -/
private lemma sum_interaction_incident (f : S → S → ℝ) (i : S)
    (hs : ∀ j k, f j k = f k j) (hz : ∀ j k, j ≠ i → k ≠ i → f j k = 0) :
    (∑ j, ∑ k ∈ univ.erase j, f j k) = 2 * ∑ k ∈ univ.erase i, f i k := by
  rw [← sum_erase_add _ _ (mem_univ i)]
  have h (j : S) (hj : j ∈ univ.erase i) : (∑ k ∈ univ.erase j, f j k) = f i j := by
    have hj' := ne_of_mem_erase hj
    rw [sum_eq_single i, hs j i]
    · exact fun k _ hk ↦ hz j k hj' hk
    · exact fun hi ↦ (hi (mem_erase.mpr ⟨hj'.symm, mem_univ i⟩)).elim
  rw [sum_congr rfl h, two_mul]

omit [∀ i, Countable (E i)] [∀ i, Zero (E i)] in
/-- Separating the interaction at a site gives its contribution to a one-coordinate update. -/
private lemma autoModel_update_sub (α : S → ℝ) {β : S → S → ℝ}
    (hβ : ∀ i j, β i j = β j i) (B C : ∀ i, E i → ℝ) (i : S) (x : ∀ i, E i)
    (y z : E i) :
    autoModel α β B C (Function.update x i y) - autoModel α β B C (Function.update x i z) =
      (α i + ∑ j ∈ univ.erase i, β i j * B j (x j)) * (B i y - B i z) +
        (C i y - C i z) := by
  let t (w : ∀ i, E i) (j k : S) := β j k * B j (w j) * B k (w k)
  let f (j k : S) := t (Function.update x i y) j k - t (Function.update x i z) j k
  have ht (w : ∀ i, E i) (j k : S) : t w j k = t w k j := by
    simp only [t]
    rw [hβ j k]
    ring
  have hpair := sum_interaction_incident f i (fun j k ↦ by simp only [f, ht _ j k])
    (fun j k hj hk ↦ by simp only [f, t, Function.update_of_ne hj, Function.update_of_ne hk,
      sub_self])
  have hi : (∑ k ∈ univ.erase i, f i k) =
      (∑ k ∈ univ.erase i, β i k * B k (x k)) * (B i y - B i z) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    simp only [f, t, Function.update_self, Function.update_of_ne (ne_of_mem_erase hk)]
    ring
  rw [hi] at hpair
  have hone :
      (∑ j, (α j * B j (Function.update x i y j) + C j (Function.update x i y j) -
        (α j * B j (Function.update x i z j) + C j (Function.update x i z j)))) =
      α i * B i y + C i y - (α i * B i z + C i z) := by
    rw [sum_eq_single i]
    · simp only [Function.update_self]
    · intro j _ hj
      simp only [Function.update_of_ne hj, sub_self]
    · exact fun hi ↦ (hi (mem_univ i)).elim
  simp only [autoModel]
  rw [add_sub_add_comm, ← sum_sub_distrib, hone, ← mul_sub, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [hpair]
  ring

/-- A singleton has only the empty subset and itself. -/
lemma powerset_singleton_eq {T : Type*} [DecidableEq T] (i : T) :
    ({i} : Finset T).powerset = {∅, {i}} := by
  ext A
  rw [mem_powerset, subset_singleton_iff, mem_insert, mem_singleton]

omit [Fintype S] [∀ i, Countable (E i)] [∀ i, Zero (E i)] in
/-- A singleton potential is the log-density change of the corresponding update. -/
private lemma canonicalPotential_singleton {π : (∀ i, E i) → ℝ} (a x : ∀ i, E i) (i : S) :
    canonicalPotential π a {i} x = Real.log (π (Function.update a i (x i))) - Real.log (π a) := by
  rw [canonicalPotential_def, powerset_singleton_eq,
    sum_pair (by simp : (∅ : Finset S) ≠ {i})]
  have hu : (fun j ↦ if j ∈ ({i} : Finset S) then x j else a j) = Function.update a i (x i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [mem_singleton_self, ite_true, Function.update_self]
    · simp only [mem_singleton, hji, ite_false, Function.update_of_ne hji]
  simp only [card_singleton, card_empty, Nat.sub_zero, pow_one, neg_mul, one_mul, notMem_empty,
    ite_false, Nat.sub_self, pow_zero, hu]
  ring

omit [Fintype S] [∀ i, Countable (E i)] [∀ i, Zero (E i)] in
/-- A pair potential is a mixed log-density difference at the reference configuration. -/
private lemma canonicalPotential_pair {π : (∀ i, E i) → ℝ} (a x : ∀ i, E i) {i j : S}
    (hij : i ≠ j) :
    canonicalPotential π a {i, j} x =
      (Real.log (π (Function.update (Function.update a j (x j)) i (x i))) -
        Real.log (π (Function.update a j (x j)))) - canonicalPotential π a {i} x := by
  rw [canonicalPotential_def, sum_powerset_insert (by simpa only [mem_singleton] using hij),
    powerset_singleton_eq, sum_pair (by simp : (∅ : Finset S) ≠ {j}),
    sum_pair (by simp : (∅ : Finset S) ≠ {j}), canonicalPotential_singleton]
  have hu (k : S) : (fun l ↦ if l ∈ ({k} : Finset S) then x l else a l) =
      Function.update a k (x k) := by
    funext l
    by_cases h : l = k
    · subst l
      simp only [mem_singleton_self, ite_true, Function.update_self]
    · simp only [mem_singleton, h, ite_false, Function.update_of_ne h]
  have huv : (fun l ↦ if l ∈ ({i, j} : Finset S) then x l else a l) =
      Function.update (Function.update a j (x j)) i (x i) := by
    funext l
    by_cases h : l = i
    · subst l
      simp only [mem_insert_self, ite_true, Function.update_self]
    · simp only [mem_insert, h, false_or, Function.update_of_ne h, ← hu j]
  simp only [insert_empty_eq, card_pair hij,
    card_singleton, card_empty, notMem_empty, ite_false, hu, huv]
  norm_num
  ring

omit [Fintype S] [∀ i, Countable (E i)] in
/-- The exponential-family specification gives the log-mass change from the reference
value at a site. -/
private lemma log_update_sub_of_log_fullConditional {π : (∀ i, E i) → ℝ} (hπ : IsDensity π)
    (hpos : ∀ x, 0 < π x) (A D : S → (∀ i, E i) → ℝ) (B C : ∀ i, E i → ℝ)
    (hB0 : ∀ i, B i 0 = 0) (hC0 : ∀ i, C i 0 = 0)
    (hA : ∀ i x y, A i (Function.update x i y) = A i x)
    (hD : ∀ i x y, D i (Function.update x i y) = D i x)
    (hexp : ∀ i x, Real.log (fullConditional π i x (x i)) =
      A i x * B i (x i) + C i (x i) + D i x)
    (i : S) (x : ∀ i, E i) (y : E i) :
    Real.log (π (Function.update x i y)) - Real.log (π (Function.update x i 0)) =
      A i x * B i y + C i y := by
  have hf (v : E i) : Real.log (π (Function.update x i v)) -
      Real.log (∑' z : E i, π (Function.update x i z)) =
        A i x * B i v + C i v + D i x := by
    simpa only [fullConditional_def, Function.update_self, Function.update_idem,
      Real.log_div (hpos _).ne' (hπ.tsum_update_pos (hpos x) i).ne', hA, hD] using
      hexp i (Function.update x i v)
  have hy := hf y
  have hz := hf 0
  rw [hB0, hC0, mul_zero, zero_add, zero_add] at hz
  linarith only [hy, hz]

omit [∀ i, Countable (E i)] [∀ i, Zero (E i)] in
/-- A sum supported on sets of size at most two containing a site separates into the singleton
and one term for each other site. -/
lemma sum_finset_eq_singleton_add_sum_pair {M : Type*} [AddCommMonoid M]
    (f : Finset S → M) (i : S)
    (hz : ∀ T, i ∉ T ∨ 2 < T.card → f T = 0) :
    (∑ T, f T) = f {i} + ∑ j ∈ univ.erase i, f {i, j} := by
  let s : Finset S := univ.erase i
  let p (j : S) := ({i, j} : Finset S)
  have hp (j : S) (hj : j ∈ s) : i ∈ p j ∧ (p j).card = 2 := by
    have hji := ne_of_mem_erase hj
    exact ⟨mem_insert_self _ _, card_pair hji.symm⟩
  have hinj : Set.InjOn p (s : Set S) := by
    intro a ha b hb hab
    have ha' : a ≠ i := ne_of_mem_erase ha
    have hm : a ∈ p b := hab ▸ mem_insert_of_mem (mem_singleton_self a)
    simpa only [p, mem_insert, ha', false_or, mem_singleton] using hm
  have hi : ({i} : Finset S) ∉ s.image p := by
    intro h
    obtain ⟨j, hj, heq⟩ := mem_image.mp h
    have hcard := (hp j hj).2
    rw [heq, card_singleton] at hcard
    contradiction
  rw [← sum_image hinj, ← sum_insert hi]
  refine (sum_subset (subset_univ _) fun T _ ht ↦ hz T ?_).symm
  by_contra! h
  have hT : ({i} : Finset S) ⊆ T := singleton_subset_iff.mpr h.1
  have hc : T.card = 1 ∨ T.card = 2 := by
    have hcard := card_le_card hT
    rw [card_singleton] at hcard
    omega
  rcases hc with h1 | h2
  · have hu := eq_of_subset_of_card_le hT (by simp only [card_singleton, h1, le_refl])
    exact ht (hu ▸ mem_insert_self _ _)
  · apply ht
    apply mem_insert_of_mem
    have he := card_erase_of_mem h.1
    rw [h2] at he
    obtain ⟨j, hj⟩ := card_eq_one.mp he
    have hji : j ≠ i := ne_of_mem_erase (show j ∈ T.erase i from hj ▸ mem_singleton_self j)
    exact mem_image.mpr ⟨j, mem_erase.mpr ⟨hji, mem_univ _⟩,
      calc
        p j = insert i (T.erase i) := by rw [hj]
        _ = T := insert_erase h.1⟩

omit [Fintype S] [∀ i, Countable (E i)] in
/-- The interaction of two sites is their single-site log-mass change after subtracting
the change at the zero configuration. -/
private lemma canonicalPotential_pair_expFamily {π : (∀ i, E i) → ℝ}
    (A : S → (∀ i, E i) → ℝ) (B C : ∀ i, E i → ℝ)
    (hlog : ∀ i x y,
      Real.log (π (Function.update x i y)) - Real.log (π (Function.update x i 0)) =
        A i x * B i y + C i y) (x : ∀ i, E i) {i j : S} (hij : i ≠ j) :
    canonicalPotential π 0 {i, j} x =
      (A i (Function.update 0 j (x j)) - A i 0) * B i (x i) := by
  have hz (w : ∀ i, E i) (hw : w i = 0) : Function.update w i 0 = w :=
    Function.update_eq_self_iff.mpr hw.symm
  have h := hlog i (Function.update 0 j (x j)) (x i)
  rw [hz _ (by rw [Function.update_of_ne hij, Pi.zero_apply])] at h
  have h₀ := hlog i 0 (x i)
  rw [hz _ rfl] at h₀
  rw [canonicalPotential_pair _ _ hij, canonicalPotential_singleton, h, h₀]
  ring

omit [Fintype S] [∀ i, Countable (E i)] in
/-- Symmetry of the pair potentials and a nonzero test value at each site give symmetric
interaction coefficients. -/
private lemma exists_pair_coefficients {π : (∀ i, E i) → ℝ}
    (A : S → (∀ i, E i) → ℝ) (B : ∀ i, E i → ℝ) (hBne : ∀ i, ∃ e, B i e ≠ 0)
    (hpair : ∀ x : (∀ i, E i), ∀ i j, i ≠ j →
      canonicalPotential π 0 {i, j} x = (A i (Function.update 0 j (x j)) - A i 0) * B i (x i)) :
    ∃ β : S → S → ℝ, (∀ i j, β i j = β j i) ∧
      ∀ x : (∀ i, E i), ∀ i j, i ≠ j →
        canonicalPotential π 0 {i, j} x = β i j * B i (x i) * B j (x j) := by
  choose w hw using hBne
  let a (i j : S) (y : E j) := A i (Function.update 0 j y) - A i 0
  let β (i j : S) := a i j (w j) / B j (w j)
  have heq (i j : S) (hij : i ≠ j) (u : E i) (v : E j) :
      a i j v * B i u = a j i u * B j v := by
    let x := Function.update (Function.update (0 : ∀ k, E k) i u) j v
    have h := hpair x i j hij
    rw [pair_comm, hpair x j i hij.symm] at h
    simpa only [a, x, Function.update_self, Function.update_of_ne hij] using h.symm
  have hβ (i j : S) : β i j = β j i := by
    by_cases hij : i = j
    · subst j
      rfl
    · exact (div_eq_div_iff (hw j) (hw i)).2 (heq i j hij (w i) (w j))
  refine ⟨β, hβ, fun x i j hij ↦ ?_⟩
  rw [hpair x i j hij]
  have hcoef : a i j (x j) = β i j * B j (x j) := by
    rw [hβ i j]
    dsimp only [β]
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff (hw i)).2 (heq i j hij (w i) (x j))
  calc
    (A i (Function.update 0 j (x j)) - A i 0) * B i (x i) = a i j (x j) * B i (x i) := rfl
    _ = β i j * B i (x i) * B j (x j) := by rw [hcoef]; ring

omit [∀ i, Countable (E i)] in
/-- With higher-order potentials zero, changing one coordinate alters only its singleton
and its incident pair potentials. -/
private lemma log_update_sub_eq_canonicalPotential {π : (∀ i, E i) → ℝ}
    (hpair : ∀ T : Finset S, 2 < T.card → ∀ x, canonicalPotential π 0 T x = 0)
    (i : S) (x : ∀ i, E i) (y z : E i) :
    let w := Function.update x i y
    let v := Function.update x i z
    Real.log (π w) - Real.log (π v) =
      (canonicalPotential π 0 {i} w - canonicalPotential π 0 {i} v) +
        ∑ j ∈ univ.erase i, (canonicalPotential π 0 {i, j} w -
          canonicalPotential π 0 {i, j} v) := by
  intro w v
  rw [← sum_canonicalPotential π 0 w, ← sum_canonicalPotential π 0 v, ← sum_sub_distrib]
  refine sum_finset_eq_singleton_add_sum_pair _ i fun T hT ↦ ?_
  rcases hT with h | h
  · have heq : canonicalPotential π 0 T w = canonicalPotential π 0 T v := by
      apply canonicalPotential_congr
      intro j hj
      have hji : j ≠ i := fun hji ↦ h (hji ▸ hj)
      simp only [w, v, Function.update_of_ne hji]
    rw [heq, sub_self]
  · rw [hpair T h w, hpair T h v, sub_self]

omit [∀ i, Countable (E i)] in
/-- The singleton and pair coefficients recover the one-site parameter of the conditional law. -/
private lemma eq_site_parameter_of_pair_potential {π : (∀ i, E i) → ℝ}
    (A : S → (∀ i, E i) → ℝ) (B C : ∀ i, E i → ℝ)
    (hB0 : ∀ i, B i 0 = 0) (hC0 : ∀ i, C i 0 = 0) (hBne : ∀ i, ∃ e, B i e ≠ 0)
    (hlog : ∀ i x y,
      Real.log (π (Function.update x i y)) - Real.log (π (Function.update x i 0)) =
        A i x * B i y + C i y)
    (hpair : ∀ T : Finset S, 2 < T.card → ∀ x, canonicalPotential π 0 T x = 0)
    {β : S → S → ℝ}
    (hβ : ∀ x : (∀ i, E i), ∀ i j, i ≠ j →
      canonicalPotential π 0 {i, j} x = β i j * B i (x i) * B j (x j)) (i : S) (x : ∀ i, E i) :
    A i x = A i 0 + ∑ j ∈ univ.erase i, β i j * B j (x j) := by
  obtain ⟨u, hu⟩ := hBne i
  have hs (w : ∀ i, E i) :
      canonicalPotential π 0 {i} w = A i 0 * B i (w i) + C i (w i) := by
    rw [canonicalPotential_singleton]
    have hz : Function.update (0 : ∀ k, E k) i 0 = 0 :=
      Function.update_eq_self_iff.mpr rfl
    simpa only [hz] using hlog i 0 (w i)
  have h := log_update_sub_eq_canonicalPotential hpair i x u 0
  dsimp only at h
  rw [hlog i x u, hs, hs] at h
  simp only [Function.update_self, hB0, hC0, mul_zero, zero_add, sub_zero] at h
  have heq : (∑ j ∈ univ.erase i, (canonicalPotential π 0 {i, j} (Function.update x i u) -
        canonicalPotential π 0 {i, j} (Function.update x i 0))) =
        (∑ j ∈ univ.erase i, β i j * B j (x j)) * B i u := by
    rw [sum_mul]
    refine sum_congr rfl fun j hj ↦ ?_
    have hji := ne_of_mem_erase hj
    simp only [hβ _ i j hji.symm, Function.update_self, Function.update_of_ne hji,
      hB0, mul_zero, zero_mul, sub_zero]
    ring
  rw [heq] at h
  apply mul_right_cancel₀ hu
  linear_combination h

omit [∀ i, Countable (E i)] in
/-- Two log weights with the same coordinate-update differences differ by their value at zero. -/
private lemma log_weight_eq_at_zero_of_update_sub {π : (∀ i, E i) → ℝ}
    (w : (∀ i, E i) → ℝ) (h : ∀ i x y,
      Real.log (π (Function.update x i y)) - Real.log (π (Function.update x i 0)) =
        w (Function.update x i y) - w (Function.update x i 0)) (x : ∀ i, E i) :
    Real.log (π x) - w x = Real.log (π 0) - w 0 := by
  let f (T : Finset S) (j : S) : E j := if j ∈ T then x j else 0
  have hf (T : Finset S) : Real.log (π (f T)) - w (f T) = Real.log (π 0) - w 0 := by
    induction T using Finset.induction_on with
    | empty =>
      have he : f ∅ = 0 := by
        funext j
        simp only [f, notMem_empty, ite_false, Pi.zero_apply]
      rw [he]
    | @insert i T hi ih =>
      have hup : Function.update (f T) i (x i) = f (insert i T) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self, f, mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hji, f, mem_insert, hji, false_or]
      have hz : Function.update (f T) i 0 = f T := Function.update_eq_self_iff.mpr
        (by simp only [f, hi, ite_false])
      have hu := h i (f T) (x i)
      rw [hup, hz] at hu
      linear_combination hu + ih
  simpa only [f, mem_univ, ite_true] using hf univ

-- Preserve the countable state spaces of the original theorem statement.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 50, Besag's auto-models: for a positive Markov random field whose canonical
potential (relative to `0`) vanishes on cliques of more than two sites and whose full
conditionals are one-parameter exponential families
`log π_i(x_i ∣ x_{-i}) = A_i(x_{-i}) B_i(x_i) + C_i(x_i) + D_i(x_{-i})` with
`B_i(0) = C_i(0) = 0` and `B_i` not identically zero, there are `α_i` and symmetric `β_{ij}`,
zero unless `i ∼ j`, with `A_i(x_{-i}) = α_i + ∑_{j ≠ i} β_{ij} B_j(x_j)` and
`π(x) = π(0) exp(autoModel α β B C x)`. -/
theorem exists_autoModel (G : SimpleGraph S) {π : (∀ i, E i) → ℝ} (hπ : IsDensity π)
    (hpos : ∀ x, 0 < π x) (hG : IsMarkovRandomField G π)
    (hpair : ∀ A : Finset S, 2 < A.card → ∀ x, canonicalPotential π 0 A x = 0)
    (A D : S → (∀ i, E i) → ℝ) (B C : ∀ i, E i → ℝ) (hB0 : ∀ i, B i 0 = 0)
    (hC0 : ∀ i, C i 0 = 0) (hBne : ∀ i, ∃ e, B i e ≠ 0)
    (hA : ∀ i x y, A i (Function.update x i y) = A i x)
    (hD : ∀ i x y, D i (Function.update x i y) = D i x)
    (hexp : ∀ i x, Real.log (fullConditional π i x (x i)) =
      A i x * B i (x i) + C i (x i) + D i x) :
    ∃ (α : S → ℝ) (β : S → S → ℝ), (∀ i j, β i j = β j i) ∧
      (∀ i j, i ≠ j → ¬ G.Adj i j → β i j = 0) ∧
      (∀ i x, A i x = α i + ∑ j ∈ univ.erase i, β i j * B j (x j)) ∧
      ∀ x, π x = π 0 * Real.exp (autoModel α β B C x) := by
  have hlog := log_update_sub_of_log_fullConditional hπ hpos A D B C hB0 hC0 hA hD hexp
  obtain ⟨β, hβ, hV⟩ := exists_pair_coefficients A B hBne
    (fun x _ _ hij ↦ canonicalPotential_pair_expFamily A B C hlog x hij)
  have hαβ := eq_site_parameter_of_pair_potential A B C hB0 hC0 hBne hlog hpair hV
  refine ⟨fun i ↦ A i 0, β, hβ, ?_, hαβ, ?_⟩
  · intro i j hij hnj
    obtain ⟨u, hu⟩ := hBne i
    obtain ⟨v, hv⟩ := hBne j
    let x := Function.update (Function.update (0 : ∀ k, E k) i u) j v
    have hnot : ¬ G.IsClique ({i, j} : Finset S) := by
      intro hc
      exact hnj (hc (mem_insert_self i _) (mem_insert_of_mem (mem_singleton_self j)) hij)
    have hzero := canonicalPotential_eq_zero_of_not_isClique hπ hpos hG 0 x hnot
    rw [hV x i j hij] at hzero
    simp only [x, Function.update_of_ne hij, Function.update_self] at hzero
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hv)).resolve_right hu
  · intro x
    let w := autoModel (fun i ↦ A i 0) β B C
    have hd : ∀ i x y,
        Real.log (π (Function.update x i y)) - Real.log (π (Function.update x i 0)) =
          w (Function.update x i y) - w (Function.update x i 0) := by
      intro i x y
      rw [hlog i x y, autoModel_update_sub _ hβ, hαβ i x, hB0, hC0, sub_zero, sub_zero]
    have h := log_weight_eq_at_zero_of_update_sub w hd x
    have hw : w 0 = 0 := by simp only [w, autoModel_def, Pi.zero_apply, hB0, hC0, mul_zero,
      add_zero, Finset.sum_const_zero]
    rw [hw, sub_zero, sub_eq_iff_eq_add] at h
    rw [← Real.exp_log (hpos x), h, Real.exp_add, Real.exp_log (hpos 0)]

-- Preserve the existing state-space instances in the statement.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 50, converse: for symmetric `β` and a normalisable joint law
`π ∝ exp(autoModel α β B C)`, the full conditionals are the exponential families with
`A_i(x_{-i}) = α_i + ∑_{j ≠ i} β_{ij} B_j(x_j)`. -/
theorem fullConditional_autoModelDensity (α : S → ℝ) {β : S → S → ℝ}
    (hβ : ∀ i j, β i j = β j i) (B C : ∀ i, E i → ℝ)
    (hsum : Summable fun x ↦ Real.exp (autoModel α β B C x)) (i : S) (x : ∀ i, E i)
    (y : E i) :
    fullConditional (fun x ↦ Real.exp (autoModel α β B C x) /
        ∑' x', Real.exp (autoModel α β B C x')) i x y =
      Real.exp ((α i + ∑ j ∈ univ.erase i, β i j * B j (x j)) * B i y + C i y) /
        ∑' z : E i, Real.exp ((α i + ∑ j ∈ univ.erase i, β i j * B j (x j)) * B i z + C i z) := by
  let a : ℝ := α i + ∑ j ∈ univ.erase i, β i j * B j (x j)
  let r (z : E i) : ℝ := a * B i z + C i z
  let c : ℝ := autoModel α β B C (Function.update x i y) - r y
  have hfactor (z : E i) :
      Real.exp (autoModel α β B C (Function.update x i z)) = Real.exp c * Real.exp (r z) := by
    rw [← Real.exp_add]
    congr 1
    have h := autoModel_update_sub α hβ B C i x z y
    dsimp only [a, c, r]
    linear_combination h
  have hnorm : (∑' x', Real.exp (autoModel α β B C x')) ≠ 0 :=
    (hsum.tsum_pos (fun _ ↦ (Real.exp_pos _).le) x (Real.exp_pos _)).ne'
  rw [fullConditional_def, tsum_div_const, div_div_div_cancel_right₀ hnorm]
  simp only [hfactor, tsum_mul_left]
  exact mul_div_mul_left _ _ (Real.exp_pos c).ne'

end AutoModel

/-- SYNOPSIS item 50, the auto-logistic model: on `{0, 1}^S` the normalised law
`π ∝ exp(∑ α_i x_i + ∑_{i<j} β_{ij} x_i x_j)` exists for all `α` and symmetric `β`, and
`π_i(1 ∣ x_{-i}) = e^{η_i} / (1 + e^{η_i})` with `η_i = α_i + ∑_{j ≠ i} β_{ij} x_j`. -/
theorem fullConditional_autoLogistic (α : S → ℝ) {β : S → S → ℝ} (hβ : ∀ i j, β i j = β j i)
    (i : S) (x : S → Bool) :
    let w : (S → Bool) → ℝ := fun x ↦ Real.exp (∑ i, α i * (if x i then 1 else 0) +
      (1 / 2) * ∑ i, ∑ j ∈ univ.erase i,
        β i j * (if x i then 1 else 0) * (if x j then 1 else 0))
    let η := α i + ∑ j ∈ univ.erase i, β i j * (if x j then 1 else 0)
    IsDensity (fun x ↦ w x / ∑ x', w x') ∧
      fullConditional (E := fun _ ↦ Bool) (fun x ↦ w x / ∑ x', w x') i x true =
        Real.exp η / (1 + Real.exp η) := by
  let B : S → Bool → ℝ := fun _ b ↦ if b then 1 else 0
  let C : S → Bool → ℝ := fun _ _ ↦ 0
  have hw (u : S → Bool) :
      Real.exp (autoModel α β B C u) =
        Real.exp (∑ j, α j * (if u j then 1 else 0) +
          (1 / 2) * ∑ j, ∑ k ∈ univ.erase j,
            β j k * (if u j then 1 else 0) * (if u k then 1 else 0)) := by
    simp only [autoModel, B, C, add_zero]
  dsimp only
  simp only [← hw]
  refine ⟨⟨fun u ↦ div_nonneg (Real.exp_pos _).le
    (sum_nonneg fun _ _ ↦ (Real.exp_pos _).le), ?_⟩, ?_⟩
  · have hsum : 0 < ∑ u : S → Bool, Real.exp (autoModel α β B C u) :=
      sum_pos (fun u _ ↦ Real.exp_pos _) ⟨x, mem_univ x⟩
    have hs := hasSum_fintype (fun u : S → Bool ↦ Real.exp (autoModel α β B C u) /
      (∑ v : S → Bool, Real.exp (autoModel α β B C v)))
    simpa only [div_eq_mul_inv, ← sum_mul, mul_inv_cancel₀ hsum.ne'] using hs
  · let : Zero Bool := ⟨false⟩
    have h := fullConditional_autoModelDensity α hβ B C (hasSum_fintype _).summable i x true
    rw [tsum_fintype] at h
    rw [h]
    simp [tsum_fintype, B, C, add_comm]

/-! ### Coding sets (SYNOPSIS item 65) -/

omit [Fintype S] in
open Filter in
/-- The product of normalised single-site conditionals sums to one over a finite set of sites. -/
private lemma tsum_prod_fullConditional {C : Finset S} {π : (∀ i, E i) → ℝ} (x : ∀ i, E i)
    (hπ : IsDensity π) (hx : 0 < π x) :
    (∑' z : ∀ i : C, E i, ∏ i : C, fullConditional π i x (z i)) = 1 := by
  classical
  let f (i : C) (y : E i) := fullConditional π i x y
  have hf (i : C) : HasSum (f i) 1 := by
    have h := (hπ.2.summable.comp_injective (Function.update_injective x (i : S))).hasSum
    unfold f
    simpa only [Function.comp_apply, fullConditional_def,
      div_self (hπ.tsum_update_pos hx (i : S)).ne'] using
        h.div_const (∑' y : E i, π (Function.update x (i : S) y))
  have h0 (i : C) : 0 ≤ f i := fun y ↦
    div_nonneg (hπ.1 _) (hπ.tsum_update_pos hx (i : S)).le
  let box := fun s : ∀ i : C, Finset (E i) ↦ Fintype.piFinset s
  have hbox : Tendsto box atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone (f := box)
      (fun _ _ h ↦ Fintype.piFinset_subset _ _ h)
    exact fun z ↦ ⟨fun i ↦ {z i}, Fintype.mem_piFinset.2 fun i ↦ mem_singleton_self _⟩
  have hproj (i : C) : Tendsto (fun s : ∀ i : C, Finset (E i) ↦ s i) atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone
      (f := fun s : ∀ i : C, Finset (E i) ↦ s i) (fun _ _ h ↦ Pi.le_def.1 h i)
    exact fun a ↦ ⟨Function.update (fun _ ↦ ∅) i {a}, by simp⟩
  -- TauCeti supplies summability and the cofinal finite boxes identify the sum.
  have h₁ := (Summable.prod_pi_of_nonneg (fun i ↦ (hf i).summable) h0).hasSum.comp hbox
  have h₂ := tendsto_finsetProd (univ : Finset C) fun i _ ↦ (hf i).comp (hproj i)
  dsimp only [Function.comp_def, box] at h₁
  exact tendsto_nhds_unique h₁ (by
    simpa only [Function.comp_apply, Finset.prod_univ_sum, Finset.prod_const_one] using h₂)

omit [Fintype S] in
/-- The mass of a configuration updated on a coding set is the baseline mass times the
product of the corresponding single-site likelihood ratios. -/
private lemma codingSet_mass_ratio [∀ i, Countable (E i)] (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : ∀ x, 0 < π x)
    (hG : IsMarkovRandomField G π) {C : Finset S}
    (hC : ∀ i ∈ C, ∀ j ∈ C, ¬ G.Adj i j) (x z : ∀ i, E i) :
    π (fun j ↦ if j ∈ C then z j else x j) =
      (π x / ∏ i ∈ C, fullConditional π i x (x i)) *
        ∏ i ∈ C, fullConditional π i x (z i) := by
  let p (B : Finset S) (j : S) := if j ∈ B then z j else x j
  let f (i : S) (y : E i) := fullConditional π i x y
  have hstep (B : Finset S) (hB : B ⊆ C) :
      π (p B) = π x * ∏ i ∈ B, f i (z i) / f i (x i) := by
    induction B using Finset.induction_on with
    | empty => simp only [p, notMem_empty, ite_false, prod_empty, mul_one]
    | @insert i B hi ih =>
      have hn : ∀ j, G.Adj i j → p B j = x j := by
        intro j hj
        have hnot : j ∉ B := fun hjB ↦
          hC i (hB (mem_insert_self _ _)) j (hB (mem_insert_of_mem hjB)) hj
        simp only [p, hnot, ite_false]
      have hpi : p B i = x i := by simp only [p, hi, ite_false]
      have hu : Function.update (p B) i (z i) = p (insert i B) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, p, mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hj, p, mem_insert, hj, false_or]
      have hr := hG.div_update_eq hπ hpos i (p B) x hn hpi (z i)
      have hf :
          π (Function.update x i (z i)) / π x = f i (z i) / f i (x i) := by
        simp only [f, fullConditional_def, Function.update_eq_self,
          div_div_div_cancel_right₀ (hπ.tsum_update_pos (hpos x) i).ne']
      rw [hu, hf, div_eq_iff (hpos (p B)).ne'] at hr
      rw [hr, ih ((subset_insert i B).trans hB), prod_insert hi]
      ring
  simpa only [f, prod_div_distrib, div_mul_eq_mul_div, mul_div_assoc] using hstep C Subset.rfl

-- Preserve the finite-site parameter of the original statement.
set_option linter.unusedSectionVars false in
/-- SYNOPSIS item 65: for a positive Markov random field and a coding set `C` (no two of its
sites are neighbours), the variables `x_i`, `i ∈ C`, are conditionally independent given
`x_{S∖C}`, with laws `π_i(· ∣ x_{∂i})`. -/
theorem setConditional_codingSet [∀ i, Countable (E i)] (G : SimpleGraph S)
    {π : (∀ i, E i) → ℝ} (hπ : IsDensity π) (hpos : ∀ x, 0 < π x)
    (hG : IsMarkovRandomField G π) {C : Finset S}
    (hC : ∀ i ∈ C, ∀ j ∈ C, ¬ G.Adj i j) (x z : ∀ i, E i) :
    setConditional π C x z = ∏ i ∈ C, fullConditional π i x (z i) := by
  let f (i : S) (y : E i) := fullConditional π i x y
  let c := π x / ∏ i ∈ C, f i (x i)
  have hc : c ≠ 0 :=
    (div_pos (hpos x) (prod_pos fun i _ ↦ (hπ.fullConditional_self_pos_iff i x).2 (hpos x))).ne'
  have hnorm : (∑' a : ∀ i : C, E i, ∏ i : C, f i (a i)) = 1 :=
    tsum_prod_fullConditional x hπ (hpos x)
  have hsp (a : ∀ i : C, E i) :
      π (fun j ↦ if hj : j ∈ C then a ⟨j, hj⟩ else x j) = c * ∏ i : C, f i (a i) := by
    let a' (j : S) := if hj : j ∈ C then a ⟨j, hj⟩ else x j
    have hu : (fun j ↦ if j ∈ C then a' j else x j) = a' := by
      funext j
      by_cases hj : j ∈ C <;> simp only [a', hj, ite_true, ite_false, dite_false]
    have hp : (∏ i ∈ C, f i (a' i)) = ∏ i : C, f i (a i) := by
      rw [← prod_coe_sort]
      exact prod_congr rfl fun i _ ↦ by simp only [a', i.property, dite_true]
    simpa only [hu, ← hp] using codingSet_mass_ratio G hπ hpos hG hC x a'
  rw [setConditional_def, codingSet_mass_ratio G hπ hpos hG hC x z]
  simp only [hsp, tsum_mul_left, hnorm, mul_one]
  exact mul_div_cancel_left₀ _ hc

end MSSS
