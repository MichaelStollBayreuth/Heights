import Heights.BasicMultiset
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

/-- A predicate singling out infinite places among the absolute values on a number field `K`. -/
def IsInfinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ φ : K →+* ℂ, place φ = w

lemma InfinitePlace.isInfinitePlace (v : InfinitePlace K) : IsInfinitePlace v.val := by
  simp [IsInfinitePlace, v.prop]

lemma isInfinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsInfinitePlace v ↔ ∃ w : InfinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isInfinitePlace⟩

variable  [NumberField K]

/-- A predicate singling out finite places among the absolute values on a number field `K`. -/
def IsFinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

variable (K) in
/-- The infinite places of a number field `K` as a `Multiset` of absolute values on `K`,
with multiplicity given by `InfinitePlace.mult`. -/
noncomputable def multisetInfinitePlace : Multiset (AbsoluteValue K ℝ) :=
  .bind (.univ : Finset (InfinitePlace K)).val fun v ↦ .replicate v.mult v.val

@[simp]
lemma mem_multisetInfinitePlace {v : AbsoluteValue K ℝ} :
    v ∈ multisetInfinitePlace K ↔ IsInfinitePlace v := by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

lemma count_multisetInfinitePlace_eq_mult [DecidableEq (AbsoluteValue K ℝ)]
    [DecidableEq (InfinitePlace K)] (v : InfinitePlace K) :
    (multisetInfinitePlace K).count v.val = v.mult := by
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

variable (K) in
lemma prod_multisetInfinitePlace_eq {M : Type*} [CommMonoid M] {f : AbsoluteValue K ℝ → M} :
    ((multisetInfinitePlace K).map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult := by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw ↦ ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ ↦ v.val) (fun _ _ ↦ Finset.mem_univ _) (fun v _ ↦ by simp [v.isInfinitePlace])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun w hw ↦ by rw [count_multisetInfinitePlace_eq_mult ⟨w, _⟩]

noncomputable
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using hv⟩
  mulSupport_finite := FinitePlace.mulSupport_finite
  product_formula {x} hx := prod_multisetInfinitePlace_eq (M := ℝ) K ▸ prod_abs_eq_one hx

end NumberField
