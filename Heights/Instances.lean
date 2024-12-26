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
### Missing API

We collect a number of API lemmas for functions of the form `Sum.elim f g`.
-/

variable {α β γ M : Type*}

lemma Function.sumElim_apply (f : α → γ → M) (g : β → γ → M) (x : α ⊕ β) (y : γ) :
    Sum.elim f g x y = Sum.elim (f · y) (g · y) x := by
  cases x with
  | inl a => rfl
  | inr b => rfl

lemma Function.sumElim_apply' (f : α → γ → M) (g : β → γ → M) (y : γ) :
    (Sum.elim f g · y) = Sum.elim (f · y) (g · y) :=
  funext (sumElim_apply f g · y)

lemma MonoidWithZeroHom.sumElim_apply' [MonoidWithZero γ] [MonoidWithZero M]
    (f : α → γ →*₀ M) (g : β → γ →*₀ M) (y : γ) :
    (Sum.elim f g · y) = Sum.elim (f · y) (g · y) := by
  ext1 x
  cases x with
  | inl a => rfl
  | inr b => rfl

@[to_additive]
lemma Function.mulSupport_sumElim [One M] {f : α → M} {g : β → M} :
    (Sum.elim f g).mulSupport = Sum.inl '' f.mulSupport ∪ Sum.inr '' g.mulSupport := by
  ext1 x
  cases x with
  | inl a => simp
  | inr b => simp

@[to_additive]
lemma Function.mulSupport_sumElim_finite [One M] {f : α → M} {g : β → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    (Sum.elim f g).mulSupport.Finite := by
  rw [mulSupport_sumElim]
  exact Set.finite_union.mpr ⟨hf.image Sum.inl, hg.image Sum.inr⟩

@[to_additive]
lemma Function.mulSupport_sumElim_finite' [Finite β] [One M] (f : β → M) :
    (Function.mulSupport (Sum.elim (fun _ : α ↦ 1) f)).Finite := by
  refine mulSupport_sumElim_finite ?_ <| Set.toFinite _
  rw [mulSupport_one]
  exact Set.finite_empty

@[to_additive]
lemma finprod_sum [CommMonoid M] {f : α → M} {g : β → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    ∏ᶠ x, Sum.elim f g x = (∏ᶠ a, f a) * ∏ᶠ b, g b := by
  have hfg := Function.mulSupport_sumElim_finite hf hg
  rw [finprod_eq_prod_of_mulSupport_subset _ (Set.Finite.coe_toFinset hfg).symm.subset,
    finprod_eq_prod_of_mulSupport_subset _ (Set.Finite.coe_toFinset hf).symm.subset,
    finprod_eq_prod_of_mulSupport_subset _ (Set.Finite.coe_toFinset hg).symm.subset,
    ← Finset.prod_sum_elim]
  congr
  refine Finset.eq_disjSum_iff.mpr ⟨?_, ?_⟩ <;> exact Finset.ext_iff.mpr fun _ ↦ by simp

/-!
### Instance for number fields
-/

open Height AdmissibleAbsValues NumberField

variable {K : Type*} [Field K] [NumberField K]

-- Helper lemmas

private
lemma NumberField.FinitePlace.nnabs_comp_apply (v : FinitePlace K) (x : K) :
    ((Real.nnabs.comp v.val.toMonoidWithZeroHom) x : ℝ) = v x := by
  simp only [MonoidWithZeroHom.coe_comp, AbsoluteValue.coe_toMonoidWithZeroHom,
    Function.comp_apply, apply_nonneg, Real.nnabs_of_nonneg, Real.coe_toNNReal', sup_of_le_left]
  rfl

private
lemma NumberField.FinitePlace.mulSupport_finite' {x : K} (hx : x ≠ 0) :
    (Function.mulSupport
      fun v : FinitePlace K ↦ (Real.nnabs.comp v.val.toMonoidWithZeroHom) x).Finite := by
  convert mulSupport_finite hx
  rw [← Function.mulSupport_comp_eq (g := ((↑) : NNReal → ℝ)) NNReal.coe_eq_one, Function.comp_def]
  simp only [nnabs_comp_apply]

omit [NumberField K] in
private
lemma NumberField.InfinitePlace.nnabs_comp_apply (v : InfinitePlace K) (x : K) :
    (Real.nnabs.comp v.val.toMonoidWithZeroHom).comp (powMonoidWithZeroHom v.mult_ne_zero) x =
      v x ^ v.mult:= by
  simp only [MonoidWithZeroHom.coe_comp, AbsoluteValue.coe_toMonoidWithZeroHom,
    coe_powMonoidWithZeroHom, Function.comp_apply, AbsoluteValue.map_pow, apply_nonneg, pow_nonneg,
    Real.nnabs_of_nonneg, Real.coe_toNNReal', sup_of_le_left]
  rfl

-- The `Real.nnabs.comp ⋯` below could be avoided by using `R`-valued absolute values
-- in `AdmissibleAbsValues` (instead of `ℝ≥0`-valued ones).
-- Compare [Variant.lean](Heights/Variant.lean).
noncomputable
instance NumberField.instAdmissibleAbsValues :
    AdmissibleAbsValues K where
      Vals := FinitePlace K ⊕ InfinitePlace K
      absValue := Sum.elim (fun v ↦ Real.nnabs.comp v.val.toMonoidWithZeroHom)
        fun v ↦ (Real.nnabs.comp v.val.toMonoidWithZeroHom).comp <|
          powMonoidWithZeroHom v.mult_ne_zero
      triangleIneqBound := Sum.elim (fun _ ↦ 1) fun v ↦ 2 ^ v.mult
      weak_triangle_inequality w x y := by
        cases w with
        | inl v =>
            simpa only [Sum.elim_inl, ← NNReal.coe_le_coe, one_mul, NNReal.coe_max,
              v.nnabs_comp_apply] using NonarchimedeanHomClass.map_add_le_max v x y
        | inr v =>
            simp only [Sum.elim_inr, ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_pow,
              NNReal.coe_ofNat, NNReal.coe_max, v.nnabs_comp_apply]
            calc
            _ ≤ (v x + v y) ^ v.mult := pow_le_pow_left₀ (apply_nonneg v _) (v.val.add_le' ..) _
            _ ≤ (2 * (v x ⊔ v y)) ^ v.mult := by
              gcongr
              rcases le_total (v x) (v y) with h | h <;>
              { simp only [h, sup_of_le_right, sup_of_le_left]; linarith }
            _ = 2 ^ v.mult * (v x ^ v.mult ⊔ v y ^ v.mult) := by
              rw [mul_pow]
              congr
              rcases le_total (v x) (v y) with h | h <;>
              { simp only [h, sup_of_le_right, right_eq_sup, sup_of_le_left, left_eq_sup]
                gcongr }
      mulSupport_ineqBounds_finite := Function.mulSupport_sumElim_finite' _
      mulSupport_absValues_finite hx := by
        rw [MonoidWithZeroHom.sumElim_apply']
        exact Function.mulSupport_sumElim_finite (FinitePlace.mulSupport_finite' hx) <|
          Set.toFinite _
      product_formula hx := by
        apply_fun ((↑) : NNReal → ℝ) using NNReal.coe_injective
        rw [NNReal.coe_one, ← prod_abs_eq_one hx, mul_comm, MonoidWithZeroHom.sumElim_apply',
          finprod_sum ((FinitePlace.mulSupport_finite' hx)) (Set.toFinite _)]
        push_cast
        have (x : NNReal) : NNReal.toRealHom x = NNReal.toRealHom.toMonoidHom x := rfl
        simp_rw [← NNReal.coe_toRealHom, this]
        congr
        · rw [MonoidHom.map_finprod _ (FinitePlace.mulSupport_finite' hx)]
          simp only [← this, NNReal.coe_toRealHom, FinitePlace.nnabs_comp_apply]
        · rw [finprod_eq_prod_of_fintype, map_prod]
          simp only [← this, NNReal.coe_toRealHom, InfinitePlace.nnabs_comp_apply]
