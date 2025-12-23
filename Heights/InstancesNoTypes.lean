import Heights.BasicNoTypes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

open Height Classical

variable {K : Type*} [Field K] [NumberField K]

def IsFinitePlace (w : AbsoluteValue K ℝ) : Prop :=
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

def IsInfinitePlace (w : AbsoluteValue K ℝ) : Prop :=
    ∃ (φ : K →+* ℂ), place φ = w

variable (K) in
noncomputable
def finsetInfinitePlace : Finset (AbsoluteValue K ℝ) :=
  (Set.finite_coe_iff.mp <| Finite.of_fintype (InfinitePlace K)).toFinset

lemma mem_finsetInfinitePlace (v : AbsoluteValue K ℝ) :
    v ∈ finsetInfinitePlace K ↔ IsInfinitePlace v := by
  rw [finsetInfinitePlace, IsInfinitePlace, Set.Finite.mem_toFinset]
  exact Iff.rfl

omit [NumberField K] in
lemma isInfinitePlace (v : InfinitePlace K) : IsInfinitePlace v.val := by
  simp [IsInfinitePlace, v.prop]

omit [NumberField K] in
lemma isInfinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsInfinitePlace v ↔ ∃ w : InfinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ isInfinitePlace w⟩

noncomputable
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := finsetInfinitePlace K
  weight v := if h : IsInfinitePlace v then InfinitePlace.mult ⟨v, h⟩ else 1
  weight_pos v hv := by simp_all [mem_finsetInfinitePlace, InfinitePlace.mult_pos]
  nonarchAbsVal := {v | IsFinitePlace v}
  strong_triangle_ineq v hv := FinitePlace.add_le ⟨v, by simpa using hv⟩
  mulSupport_nonarchAbsVal_finite := FinitePlace.mulSupport_finite
  product_formula {x} hx := by
    convert prod_abs_eq_one hx
    refine Finset.prod_bij' (fun w hw ↦ ⟨w, (mem_finsetInfinitePlace w).mp hw⟩)
      (fun v _ ↦ v.val) (by grind) (fun v _ ↦ by simp [mem_finsetInfinitePlace, isInfinitePlace])
      (by grind) (by simp) fun w hw ↦ ?_
    replace hw : IsInfinitePlace w := by simpa [mem_finsetInfinitePlace] using hw
    simp only [hw, ↓reduceDIte, InfinitePlace.coe_apply]

end NumberField
