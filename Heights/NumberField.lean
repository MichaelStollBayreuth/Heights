import Mathlib.NumberTheory.Height.NumberField
import Heights.Basic
/-!
# Instances of AdmissibleAbsValues

We provide instances of `Height.AdmissibleAbsValues` for

* algebraic number fields.

## TODO

* Fields of rational functions in `n` variables.

* Finite extensions of fields with `Height.AdmissibleAbsValues`.

-/

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K]

variable  [NumberField K]

open AdmissibleAbsValues

lemma sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val := by
  classical
  rw [Finset.sum_multiset_map_count]
  exact Finset.sum_bij' (fun w hw ↦ ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ ↦ v.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun v _ ↦ by simp [v.isInfinitePlace, archAbsVal])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun w hw ↦ by
      simp only [archAbsVal, Multiset.mem_toFinset, mem_multisetInfinitePlace] at hw ⊢
      simp [count_multisetInfinitePlace_eq_mult ⟨w, hw⟩]

lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl

open Real in
-- For the next PR
/-- This is the familiar definition of the logarithmic height on a number field. -/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v ↦ log⁺ (v x)]

end NumberField
