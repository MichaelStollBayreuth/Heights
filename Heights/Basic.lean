-- import Heights.Auxiliary
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Tactic.Positivity.Core

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.LinearAlgebra.Projectivization.Basic

import Mathlib.Algebra.Order.Group.CompleteLattice

import Mathlib.Algebra.FiniteSupport.Basic

-- import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We have a `Multiset` of archimedean absolute values on `K` (with values in `ℝ`).
* We also have a `Set` of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`, where the first product is over the multiset of archimedean
  absolute values.

We realize this implementation via the class `Height.AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `Height.mulHeight₁ x` and `Height.logHeight₁ x` for `x : K`.
  This is the height of an element of `K`.
* `Height.mulHeight x` and `Height.logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K` (for `x ≠ 0`).
* `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to any finite subtype containing the support of `x`.
* `Projectivization.mulHeight` and `Projectivization.logHeight` on
  `Projectivization K (ι → K)` (with a finite type `ι`). This is the height of a point
  on projective space (with fixed basis).

## Main results

* Behavior of `mulHeight` and `logHeight` under component-wise exponentiation
  (and as a consequence, the corresponding statements for `mulHeight₁` and `logHeight₁`).
* Scaling invariance of `mulHeight` and `logHeight` (allowing to define heights on
  points in projective space).
* A bound for `mulHeight₁` and `logHeight₁` of sums of two or arbitrarily many elements.

## TODO

* PR bounds for products => #35923
* PR `{mul|log}Height_sumElim_zero_eq` => #35922
* PR bounds for linear maps.
* PR upper and lower bounds for polynomial maps.

-/

noncomputable section

section aux

/- private lemma le_mul_max_max_left (a b : ℝ) : a ≤ (max a 1) * (max b 1) :=
  calc
    a = a * 1 := (mul_one a).symm
    _  ≤ _ := by gcongr <;> grind -/

/- private lemma le_mul_max_max_right (a b : ℝ) : b ≤ (max a 1) * (max b 1) := by
  rw [mul_comm]
  exact le_mul_max_max_left b a -/

/- private lemma one_le_mul_max_max (a b : ℝ) : 1 ≤ (max a 1) * (max b 1) :=
  calc
    (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ _ := by gcongr <;> grind -/

namespace Height

variable {K : Type*} [Field K]

open AdmissibleAbsValues Function

-- @[fun_prop]
/- lemma AdmissibleAbsValues.hasFiniteMulSupport {x : K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ v.val x).mulSupport.Finite :=
  mulSupport_finite hx -/

-- use `NonnegHomClass`
lemma iSup_eq_iSup_subtype {ι K M : Type*} [Finite ι] [Zero K] [Zero M]
    [ConditionallyCompleteLattice M] {x : ι → K} (hx : x ≠ 0) {v : K → M}
    (hv₀ : v 0 = 0) (hv : ∀ k, 0 ≤ v k) :
    ⨆ i, v (x i) =  ⨆ i : {j // x j ≠ 0}, v (x i) := by
  obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := ne_iff.mp hx
  have : Nonempty {j // x j ≠ 0} := .intro ⟨i, hi⟩
  have : Nonempty ι := .intro i
  refine le_antisymm ?_ <| ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl
  refine ciSup_le fun j ↦ ?_
  rcases eq_or_ne (x j) 0 with h | h
  · rw [h, hv₀]
    exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨i, hi⟩ (hv ..)
  · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl

lemma iSup_abv_eq_iSup_subtype {ι : Type*} [Finite ι] (v : AbsoluteValue K ℝ) {x : ι → K}
    (hx : x ≠ 0) :
    ⨆ i, v (x i) =  ⨆ i : {j // x j ≠ 0}, v (x i) :=
  iSup_eq_iSup_subtype hx v.map_zero v.nonneg

variable [AdmissibleAbsValues K]

-- Finiteness of the multiplicative support for some relevant functions.
@[fun_prop]
lemma mulSupport_iSup_nonarchAbsVal_finite {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  simp only [iSup_abv_eq_iSup_subtype _ hx]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| ne_iff.mp hx
  fun_prop (disch := grind)

/- @[fun_prop]
lemma mulSupport_max_nonarchAbsVal_finite (x : K) :
    (fun v : nonarchAbsVal ↦ max (v.val x) 1).HasFiniteMulSupport := by
  fun_prop -/

-- #35922
lemma mulHeight_sumElim_zero_eq {ι : Type*} (ι' : Type*) [Finite ι] [Finite ι'] (x : ι → K) :
    mulHeight (Sum.elim x (0 : ι' → K)) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := ne_iff.mp hx
  have : Nonempty ι := .intro i
  have hx' : Sum.elim x (0 : ι' → K) ≠ 0 := ne_iff.mpr ⟨.inl i, by simpa using hi⟩
  rw [mulHeight_eq hx, mulHeight_eq hx']
  have H (v : AbsoluteValue K ℝ) :  ⨆ j, v (Sum.elim x (0 : ι' → K) j) = ⨆ i, v (x i) := by
    refine le_antisymm ?_ <| ciSup_le fun i ↦ Finite.le_ciSup_of_le (.inl i) le_rfl
    refine ciSup_le fun j ↦ ?_
    cases j with
    | inl i => exact Finite.le_ciSup_of_le i le_rfl
    | inr _ => simpa using Real.iSup_nonneg_of_nonnegHomClass ..
  congr <;> ext1 v
  · exact H v
  · exact H v.val

-- #35922
open Real in
lemma logHeight_sumElim_zero_eq {ι : Type*} (ι' : Type*) [Finite ι] [Finite ι'] (x : ι → K) :
    logHeight (Sum.elim x (0 : ι' → K)) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_sumElim_zero_eq]

/-!
### Bounds for the height of sums of field elements
-/


/- -- The "local" version of the height bound for `x + y` for archimedean `v`.
private lemma max_abv_add_one_le (v : AbsoluteValue K ℝ) (x y : K) :
    max (v (x + y)) 1 ≤ 2 * (max (v x) 1 * max (v y) 1) := by
  refine sup_le ((v.add_le x y).trans ?_) <| (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
  · rw [two_mul]
    exact add_le_add (le_mul_max_max_left ..) (le_mul_max_max_right ..)
  · exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two -/

/- -- The "local" version of the height bound for `x + y` for nonarch)imedean `v`.
private lemma max_abv_add_one_le_of_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (x y : K) :
    max (v (x + y)) 1 ≤ (max (v x) 1 * max (v y) 1) := by
  refine sup_le ?_ <| one_le_mul_max_max ..
  exact (hv x y).trans <| sup_le (le_mul_max_max_left ..) (le_mul_max_max_right ..) -/

/- private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two] -/



end Height

-- open Finite in
-- lemma Real.ciSup_mul_le {ι : Type*} [Finite ι] {x y : ι → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
--     ⨆ i, x i * y i ≤ (⨆ i, x i) * ⨆ i, y i := by
--   rcases isEmpty_or_nonempty ι with hι | hι
--   · simp
--   exact ciSup_le fun i ↦ mul_le_mul (le_ciSup x i) (le_ciSup y i) (hy i) <| iSup_nonneg hx

end aux

namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-!
### Height bound for products
-/

-- #35922
@[simp]
lemma mulHeight_eq_one_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι → K) :
    mulHeight x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i
  rw [← mulHeight_smul_eq_mulHeight x (inv_ne_zero hi)]
  convert mulHeight_one
  ext1 j
  simpa [Subsingleton.elim j i] using inv_mul_cancel₀ hi

-- #35922
@[simp]
lemma logHeight_eq_zero_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι → K) :
    logHeight x = 0 := by
  simp [logHeight_eq_log_mulHeight]

-- from here: #35923

/-- The multiplicative height of a pointwise product of tuples is bounded by the product
of their multiplicative heights. -/
lemma mulHeight_mul_le {ι : Type*} [Finite ι] (x y : ι → K) :
    mulHeight (x * y) ≤ mulHeight x * mulHeight y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mulHeight y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using one_le_mulHeight x
  rw [← mulHeight_fun_mul_eq hx hy,
    show x * y = (fun a ↦ x a.1 * y a.2) ∘ fun i ↦ (i, i) by ext1; simp]
  exact mulHeight_comp_le ..

/-- The logarithmic height of a pointwise product of tuples is bounded by the sum
of their logarithmic heights. -/
lemma logHeight_mul_le {ι : Type*} [Finite ι] (x y : ι → K) :
    logHeight (x * y) ≤ logHeight x + logHeight y := by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) <| mulHeight_mul_le ..

/-- The multiplicative height of `x * y` is at most the product of the multiplicative heights
of `x` and `y`. -/
lemma mulHeight₁_mul_le (x y : K) : mulHeight₁ (x * y) ≤ mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁_eq_mulHeight]
  rw [show ![x * y, 1] = ![x, 1] * ![y, 1] by ext i; fin_cases i <;> simp]
  exact mulHeight_mul_le ![x, 1] ![y, 1]

/-- The logarithmic height of `x * y` is at most the sum of the logarithmic heights
of `x` and `y`. -/
lemma logHeight₁_mul_le (x y : K) : logHeight₁ (x * y) ≤ logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact log_le_log (by positivity) <| mulHeight₁_mul_le ..

/-- The multiplicative height of a product of field elements is bounded above by the product
of their multiplicative heights. -/
lemma mulHeight₁_prod_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    mulHeight₁ (∏ a ∈ s, x a) ≤ ∏ a ∈ s, mulHeight₁ (x a) := by
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.prod_insert hb]
    grw [← ih]
    exact mulHeight₁_mul_le (x b) (∏ a ∈ s, x a)

open Real in
/-- The logarithmic height of a product of field elements is bounded above by the sum
of their logarithmic heights. -/
lemma logHeight₁_prod_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    logHeight₁ (∏ a ∈ s, x a) ≤ ∑ a ∈ s, logHeight₁ (x a) := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_prod (fun a _ ↦ by positivity)]
  exact log_le_log (by positivity) <| mulHeight₁_prod_le s x

/-- The multiplicative height of the pointwise negative of a tuple
equals its multiplicative height. -/
@[simp]
lemma mulHeight_neg {ι : Type*} [Finite ι] (x : ι → K) : mulHeight (-x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp [mulHeight_eq hx, mulHeight_eq <| neg_ne_zero.mpr hx]

/-- The logarithmic height of the pointwise negative of a tuple
equals its logarithmic height. -/
@[simp]
lemma logHeight_neg {ι : Type*} [Finite ι] (x : ι → K) : logHeight (-x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

-- end #35923

end Height

#exit

/-!
### Height bounds for values of polynomials

This is better done as a special case of results on polynomial maps on tuples.
See MvPolynomial.lean.
-/

namespace Polynomial

open Height

variable {K : Type*} [Field K]

open Finset in
-- The "local" bound for archimedean absolute values.
private lemma max_abv_eval_one_le (p : K[X]) (x : K) (v : AbsoluteValue K ℝ) :
    max (v (p.eval x)) 1 ≤ max (p.sum fun _ c ↦ v c) 1 * (max (v x) 1) ^ p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine max_le ?_ ?_
  · rw [eval_eq_sum_range, sum_over_range p fun _ ↦ v.map_zero]
    grw [v.sum_le]
    simp_rw [v.map_mul, v.map_pow]
    calc
      _ ≤ ∑ n ∈ range (p.natDegree + 1), v (p.coeff n) * (max (v x) 1) ^ n := by gcongr; grind
      _ ≤ (∑ n ∈ range (p.natDegree + 1), v (p.coeff n)) * (max (v x) 1) ^ p.natDegree := by
          rw [sum_mul]
          gcongr <;> grind
      _ ≤ _ := by gcongr; grind
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · exact le_max_right ..
    · rw [MonotoneOn.map_sup pow_left_monotoneOn] <;> simp

open Finset in
-- The "local" bound for nonarchimedean absolute values.
private lemma max_abv_eval_one_le_of_nonarch (p : K[X]) (x : K) {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) :
    max (v (p.eval x)) 1 ≤
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v (p.coeff n)) 1 *
        (max (v x) 1) ^ p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine max_le ?_ ?_
  · rw [eval_eq_sum_range]
    grw [hv.apply_sum_le_sup_of_isNonarchimedean nonempty_range_add_one]
    simp_rw [v.map_mul, v.map_pow]
    calc
      _ ≤ (range (p.natDegree + 1)).sup' nonempty_range_add_one
            fun n ↦ v (p.coeff n) * (max (v x) 1) ^ n := by gcongr; grind
      _ ≤ ((range (p.natDegree + 1)).sup' nonempty_range_add_one
            fun n ↦ v (p.coeff n)) * (max (v x) 1) ^ p.natDegree := by
          rw [sup'_mul₀ (by positivity) _ _ nonempty_range_add_one]
          gcongr <;> grind
      _ ≤ _ := by
          gcongr
          refine Finset.sup'_le nonempty_range_add_one _ fun n hn ↦ ?_
          grw [← le_max_left]
          exact Finset.le_sup' (fun n ↦ v (p.coeff n)) hn
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · exact le_max_right ..
    · rw [MonotoneOn.map_sup pow_left_monotoneOn] <;> simp

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues Finset Function

/-- The constant in the height bound on values of `p`. -/
def mulHeight₁Bound (p : K[X]) : ℝ :=
  (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
    ∏ᶠ v : nonarchAbsVal,
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1

lemma mulHeight₁Bound_eq (p : K[X]) :
    p.mulHeight₁Bound =
      (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
      ∏ᶠ v : nonarchAbsVal,
        max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1 :=
  rfl

@[simp]
lemma mulHeight₁Bound_zero : (0 : K[X]).mulHeight₁Bound = 1 := by
  simp [Polynomial.mulHeight₁Bound]

lemma one_le_mulHeight₁Bound (p : K[X]) : 1 ≤ p.mulHeight₁Bound := by
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun _ h ↦ ?_) ?_
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
    exact le_max_right ..
  · exact one_le_finprod fun _ ↦ le_max_right ..

-- @[fun_prop]
private lemma mulSupport_max_sup'_nonarchAbsVal_finite (p : K[X]) :
    (fun v : nonarchAbsVal ↦
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1)
      |>.mulSupport.Finite := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have h (v : AbsoluteValue K ℝ) :
      (range (p.natDegree + 1)).sup' nonempty_range_add_one (fun n ↦ v (p.coeff n)) =
        (p.support).sup' (support_nonempty.mpr hp) fun n ↦ v (p.coeff n) := by
    refine le_antisymm (Finset.sup'_le nonempty_range_add_one _ fun i hi ↦ ?_) ?_
    · by_cases h : i ∈ p.support
      · exact Finset.le_sup' (fun i ↦ v (p.coeff i)) h
      · simp only [mem_support_iff, ne_eq, not_not] at h
        simp only [h, AbsoluteValue.map_zero, le_sup'_iff, mem_support_iff, apply_nonneg, and_true]
        exact ⟨p.natDegree, Polynomial.coeff_natDegree (p := p) ▸ leadingCoeff_ne_zero.mpr hp⟩
    · refine Finset.sup'_mono _ (fun i hi ↦ ?_) (support_nonempty.mpr hp)
      exact mem_range_succ_iff.mpr <| le_natDegree_of_mem_supp i hi
  simp only [h]
  refine finite_mulSupport_max ?_ finite_mulSupport_one
  refine finite_mulSupport_sup' p.support (fun _ _ ↦ ?_) (support_nonempty.mpr hp)
  exact mulSupport_finite (by grind)
  -- fun_prop (disch := grind)
  /- refine (Set.Finite.union ?_ ?_).subset <| mulSupport_max ..
  · have : ∀ i ∈ p.support, (fun v : nonarchAbsVal ↦ v.val (p.coeff i)).mulSupport.Finite :=
      fun i hi ↦ mulSupport_finite <| mem_support_iff.mp hi
    refine (p.support.finite_toSet.biUnion this).subset fun v hv ↦ ?_
    simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at hv ⊢
    contrapose! hv
    exact Finset.sup'_eq_of_forall _ (fun i ↦ v.val (p.coeff i)) hv
  · exact mulSupport_fun_one (M := ℝ) ▸ Set.finite_empty -/

open Multiset in
/-- The multiplicative height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree`. -/
lemma mulHeight₁_eval_le (p : K[X]) (x : K) :
    mulHeight₁ (p.eval x) ≤ p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree := by
  simp only [mulHeight₁_eq, p.mulHeight₁Bound_eq]
  have H : (fun v : nonarchAbsVal ↦ max (v.val x) 1 ^ p.natDegree).mulSupport.Finite :=
    finite_mulSupport_pow (mulSupport_max_nonarchAbsVal_finite _) _
    -- (mulSupport_max_nonarchAbsVal_finite x).subset <| mulSupport_pow ..
  calc
    _ ≤ (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1 * (max (v x) 1) ^ p.natDegree).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      exact prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) fun _ _ ↦ max_abv_eval_one_le ..
    _ ≤ _ * ∏ᶠ (v : ↑nonarchAbsVal), max ((Finset.range (p.natDegree + 1)).sup' nonempty_range_add_one
          fun n ↦ v.val (p.coeff n)) 1 * (max (v.val x) 1) ^ p.natDegree := by
      refine mul_le_mul_of_nonneg_left ?_ <| Multiset.prod_nonneg fun a ha ↦ ?_
      · refine finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _) (fun v ↦ by grind) ?_ ?_
        · -- change HasFiniteMulSupport _
          -- fun_prop
          exact finite_mulSupport_mul (mulSupport_max_sup'_nonarchAbsVal_finite p) H
          -- refine Set.Finite.subset ?_ <| mulSupport_mul ..
          -- exact p.mulSupport_max_sup'_nonarchAbsVal_finite.union H
        · exact Pi.le_def.mpr fun v ↦ max_abv_eval_one_le_of_nonarch p x (isNonarchimedean _ v.prop)
      · obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
        positivity
    _ = _ := by
      rw [prod_map_mul, mul_pow, prod_map_pow,
        finprod_mul_distrib p.mulSupport_max_sup'_nonarchAbsVal_finite H,
          -- (by change HasFiniteMulSupport _; fun_prop),
        finprod_pow (mulSupport_max_nonarchAbsVal_finite x)]
      ring

open Real

/-- The logarithmic height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `log p.mulHeight₁Bound + p.natDegree * logHeight₁ x`. -/
lemma logHeight₁_eval_le (p : K[X]) (x : K) :
    logHeight₁ (p.eval x) ≤ log p.mulHeight₁Bound + p.natDegree * logHeight₁ x := by
  simp_rw [logHeight₁_eq_log_mulHeight₁]
  have : p.mulHeight₁Bound ≠ 0 := by grind [one_le_mulHeight₁Bound]
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight₁_eval_le p x

end Polynomial


-- #exit
