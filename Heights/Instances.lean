import Heights.Basic

/-!
# Instances of AdmissibleAbsValues

We provide instances of `Height.AdmissibleAbsValues` for

* algebraic number fields.

## TODO

* Fields of rational functions in `n` variables.

* Finite extensions of fields with `Height.AdmissibleAbsValues`.

-/

lemma Function.sumElim_apply {α β γ M : Type*} (f : α → γ → M) (g : β → γ → M) (x : α ⊕ β) (y : γ) :
    (Sum.elim f g) x y = Sum.elim (f · y) (g · y) x := by
  -- rfl -- tactic 'rfl' failed
  -- apply? -- apply? didn't find any relevant lemmas
  -- simp -- simp made no progress
  cases x with
  | inl a => rfl
  | inr b => rfl

lemma Function.sumElim_apply' {α β γ M : Type*} (f : α → γ → M) (g : β → γ → M) (y : γ) :
    ((Sum.elim f g) · y) = Sum.elim (f · y) (g · y) :=
  funext fun x ↦ sumElim_apply f g x y

lemma MonoidWithZeroHom.sumElim_apply' {α β γ M : Type*} [MonoidWithZero γ] [MonoidWithZero M]
    (f : α → γ →*₀ M) (g : β → γ →*₀ M) (y : γ) :
    ((Sum.elim f g) · y) = Sum.elim (f · y) (g · y) := by
  ext1 x
  sorry

lemma Function.mulSupport_sumElim_finite {M α β : Type*} [One M] {f : α → M} {g : β → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    (Sum.elim f g).mulSupport.Finite := by
  sorry

lemma finprod_sum {M α β : Type*} [CommMonoid M] {f : α → M} {g : β → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) :
    ∏ᶠ x, Sum.elim f g x = (∏ᶠ a, f a) * ∏ᶠ b, g b := by
  sorry

lemma NumberField.FinitePlace.add_le {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    (x y : K) :
    v (x + y) ≤ max (v x) (v y) := by
  simp_rw [← NumberField.FinitePlace.norm_embedding_eq, map_add]
  rcases le_total ‖embedding v.maximalIdeal x‖ ‖embedding v.maximalIdeal y‖ with h | h
  · refine le_sup_of_le_right ?_
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact sup_of_le_right h ▸ Valuation.map_add_le_max' Valued.v ..
  · refine le_sup_of_le_left ?_
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact sup_of_le_left h ▸ Valuation.map_add_le_max' Valued.v ..

open Height AdmissibleAbsValues NumberField

variable {K : Type*} [Field K] [NumberField K]

instance : NonarchimedeanHomClass (FinitePlace K) K ℝ where
  map_add_le_max v a b := FinitePlace.add_le v a b

noncomputable
instance NumberField.instAdmissibleAbsValues :
    AdmissibleAbsValues K where
      Vals := FinitePlace K ⊕ InfinitePlace K
      absValue := Sum.elim (fun v ↦ Real.nnabs.comp v.val.toMonoidWithZeroHom)
        fun v ↦ (Real.nnabs.comp v.val.toMonoidWithZeroHom).comp <| powMonoidWithZeroHom v.mult_ne_zero
      triangleIneqBound := Sum.elim (fun _ ↦ 1) fun v ↦ 2 ^ v.mult
      weak_triangle_inequality w := by
        cases w with
        | inl v =>
            intro x y
            simp only [Sum.elim_inl, MonoidWithZeroHom.coe_comp,
              AbsoluteValue.coe_toMonoidWithZeroHom, Function.comp_apply, apply_nonneg,
              Real.nnabs_of_nonneg, one_mul, Real.toNNReal_le_toNNReal_iff]
            rw [Real.toNNReal_le_iff_le_coe]
            push_cast
            rw [Real.coe_toNNReal _ (v.val.nonneg x), Real.coe_toNNReal _ (v.val.nonneg y)]
            exact NonarchimedeanHomClass.map_add_le_max v x y
        | inr v =>
            intro x y
            simp only [Sum.elim_inr, MonoidWithZeroHom.coe_comp,
              AbsoluteValue.coe_toMonoidWithZeroHom, coe_powMonoidWithZeroHom, Function.comp_apply,
              AbsoluteValue.map_pow, apply_nonneg, pow_nonneg, Real.nnabs_of_nonneg]
            rw [Real.toNNReal_le_iff_le_coe]
            push_cast
            rw [Real.coe_toNNReal _ <| pow_nonneg (v.val.nonneg x) _,
              Real.coe_toNNReal _ <| pow_nonneg (v.val.nonneg y) _]
            calc
            _ ≤ (v x + v y) ^ v.mult := by
              gcongr
              exact v.val.add_le' x y
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
      mulSupport_ineqBounds_finite := by
        simp only [Function.mulSupport]
        sorry
      mulSupport_absValues_finite hx := by
        rw [MonoidWithZeroHom.sumElim_apply']
        refine Function.mulSupport_sumElim_finite ?_ <| Set.toFinite _
        convert NumberField.FinitePlace.mulSupport_finite hx
        refine Set.ext fun v ↦ ?_
        simp only [MonoidWithZeroHom.coe_comp, AbsoluteValue.coe_toMonoidWithZeroHom,
          Function.comp_apply, apply_nonneg, Real.nnabs_of_nonneg, Function.mem_mulSupport, ne_eq,
          Real.toNNReal_eq_one, not_iff_not]
        rfl
      product_formula hx := by
        apply_fun ((↑) : NNReal → ℝ) using NNReal.coe_injective
        simp only [NNReal.coe_one]
        rw [← prod_abs_eq_one hx, mul_comm]
        sorry
