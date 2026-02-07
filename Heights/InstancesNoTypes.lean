import Heights.BasicNoTypes
import Mathlib.NumberTheory.NumberField.ProductFormula

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

variable {K : Type*} [Field K] [NumberField K]

/- /-- A predicate singling out finite places among the absolute values on a number field `K`. -/
def IsFinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

/-- A predicate singling out infinite places among the absolute values on a number field `K`. -/
def IsInfinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ (φ : K →+* ℂ), place φ = w -/

variable (K) in
/-- The infinite places of a number field `K` as a `Finset` of absolute values on `K`. -/
noncomputable def finsetInfinitePlace : Finset (AbsoluteValue K ℝ) := by
  classical
  exact Finset.image Subtype.val (.univ : Finset (InfinitePlace K))

@[simp]
lemma mem_finsetInfinitePlace {v : AbsoluteValue K ℝ} :
    v ∈ finsetInfinitePlace K ↔ IsInfinitePlace v := by
  simp [finsetInfinitePlace, IsInfinitePlace]

/- omit [NumberField K] in
lemma InfinitePlace.isInfinitePlace (v : InfinitePlace K) : IsInfinitePlace v.val := by
  simp [IsInfinitePlace, v.prop]

omit [NumberField K] in
lemma isInfinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsInfinitePlace v ↔ ∃ w : InfinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isInfinitePlace⟩ -/

variable [∀ v : AbsoluteValue K ℝ, Decidable (IsInfinitePlace v)]

/-- The weight of an absolute value `v` on a number field `K`,
equal to its multiplicity when `v` is an infinite place, the junk value `1` otherwise. -/
noncomputable def weight' (v : AbsoluteValue K ℝ) : ℕ :=
  if h : IsInfinitePlace v then InfinitePlace.mult ⟨v, h⟩ else 1

variable (K) in
lemma prod_finsetInfinitePlace_eq {f : AbsoluteValue K ℝ → ℝ} :
    ∏ v ∈ finsetInfinitePlace K, f v ^ weight' v = ∏ v : InfinitePlace K, f v.val ^ v.mult :=
  Finset.prod_bij' (fun w hw ↦ ⟨w, mem_finsetInfinitePlace.mp hw⟩)
    (fun v _ ↦ v.val) (by grind) (fun v _ ↦ by simp [v.isInfinitePlace])
    (by grind) (by simp) fun w hw ↦ by simp [weight', mem_finsetInfinitePlace.mp hw]

noncomputable
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := finsetInfinitePlace K
  weight := weight'
  weight_pos v hv := by simp_all [weight', InfinitePlace.mult_pos]
  nonarchAbsVal := {v | IsFinitePlace v}
  strong_triangle_ineq v hv := FinitePlace.add_le ⟨v, by simpa using hv⟩
  mulSupport_nonarchAbsVal_finite := FinitePlace.mulSupport_finite
  product_formula {x} hx := prod_finsetInfinitePlace_eq K ▸ prod_abs_eq_one hx

end NumberField
