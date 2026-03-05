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

* PR bounds for linear maps: #35925
* PR upper bounds for polynomial maps: #35927
* PR lower bounds for polynomial maps: #35940
* PR bounds for the height of ![x*y, x+y, 1]: #35941

-/

noncomputable section


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
