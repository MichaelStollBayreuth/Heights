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

lemma FinitePlace.isFinitePlace (v : FinitePlace K) : IsFinitePlace v.val := by
  simp [IsFinitePlace, v.prop]

lemma isFinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsFinitePlace v ↔ ∃ w : FinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isFinitePlace⟩

lemma FinitePlace.coe_apply (v : FinitePlace K) (x : K) : v x = v.val x := rfl

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

-- For the user-facing version, see `prod_archAbsVal_eq` below.
variable (K) in
private lemma prod_multisetInfinitePlace_eq {M : Type*} [CommMonoid M] {f : AbsoluteValue K ℝ → M} :
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

lemma prod_archAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (AdmissibleAbsValues.archAbsVal.map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult :=
  prod_multisetInfinitePlace_eq K

lemma prod_nonarchAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∏ᶠ v : AdmissibleAbsValues.nonarchAbsVal, f v.val) = ∏ᶠ v : FinitePlace K, f v.val :=
  rfl

/-- This is the familiar definition of the multiplicative height on a number field. -/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) * ∏ᶠ v : FinitePlace K, max (v x) 1 := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, mulHeight₁, prod_archAbsVal_eq,
    prod_nonarchAbsVal_eq (f := fun v ↦ max (v x) 1)]

/-- This is the familiar definition of the multiplicative height on tuples
of number field elements. -/
lemma mulHeight_eq {ι : Type*} (x : ι → K) :
    mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, mulHeight, prod_archAbsVal_eq,
    prod_nonarchAbsVal_eq (f := fun v ↦ ⨆ i, v (x i))]

end NumberField
