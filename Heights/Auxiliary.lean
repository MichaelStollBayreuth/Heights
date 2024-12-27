import Mathlib

/-!
### Auxiliary statements

These fill API gaps in Mathlib and should eventually go there.
-/

section aux

variable {α β : Type*}

lemma max_eq_iSup [ConditionallyCompleteLattice α] (a b : α) : max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

lemma Real.iSup_pow_of_nonneg [Fintype α] [Nonempty α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
    (⨆ a, f a) ^ n = ⨆ a, (f a ^ n) := by
  have H a : ((f a).toNNReal  : ℝ) = f a := Real.coe_toNNReal (f a) (hf a)
  conv => enter [1, 1, 1, a]; rw [← H]
  conv => enter [2, 1, a]; rw [← H]
  norm_cast
  exact Monotone.map_ciSup_of_continuousAt ((continuous_pow n).continuousAt)
    (pow_left_mono n) (Finite.bddAbove_range _)

@[to_additive]
lemma finprod_mono [OrderedCommMonoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (Set.Finite.union hf hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  have hf₁ : f.mulSupport ⊆ s := by
    simp only [Set.coe_toFinset, Set.subset_union_left, s]
  have hg₁ : g.mulSupport ⊆ s := by
    simp only [Set.coe_toFinset, Set.subset_union_right, s]
  rw [finprod_eq_finset_prod_of_mulSupport_subset f hf₁,
    finprod_eq_finset_prod_of_mulSupport_subset g hg₁]
  exact Finset.prod_le_prod' fun i _ ↦ h i

/-- Monotonicity of `finprod`. See `finprod_mono` for a variant
where `β` is a `OrderedCommMonoid`. -/
lemma finprod_mono' [CommMonoidWithZero β] [PartialOrder β] [ZeroLEOneClass β] [PosMulMono β]
    {f g : α → β} (hf : f.mulSupport.Finite) (hf₀ : ∀ a, 0 ≤ f a)
    (hg : g.mulSupport.Finite) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (Set.Finite.union hf hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  have hf₁ : f.mulSupport ⊆ s := by
    simp only [Set.coe_toFinset, Set.subset_union_left, s]
  have hg₁ : g.mulSupport ⊆ s := by
    simp only [Set.coe_toFinset, Set.subset_union_right, s]
  rw [finprod_eq_finset_prod_of_mulSupport_subset f hf₁,
    finprod_eq_finset_prod_of_mulSupport_subset g hg₁]
  exact Finset.prod_le_prod (fun i _ ↦ hf₀ i) fun i _ ↦ h i

@[to_additive]
lemma Function.mulSupport_mul_finite [Monoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (Function.mulSupport fun a ↦ f a * g a).Finite :=
  (hf.union hg).subset <| mulSupport_mul f g

lemma one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
    [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ ↦ one_le_mul_of_one_le_of_one_le) hf

lemma Finset.one_le_prod [DecidableEq α] (s : Finset α) {M : Type*} [CommMonoidWithZero M]
    [Preorder M] [ZeroLEOneClass M] [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s h ih => simpa [h] using one_le_mul_of_one_le_of_one_le (hf a) ih

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

lemma AbsoluteValue.iSup_eq_subtype (v : AbsoluteValue K ℝ) {x : ι → K} (hx : x ≠ 0) :
    ⨆ i, v (x i) = ⨆ i : {j // x j ≠ 0}, v (x i) := by
  have ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty {j // x j ≠ 0} := Nonempty.intro ⟨i, hi⟩
  have : Nonempty ι := Nonempty.intro i
  apply le_antisymm
  · refine ciSup_le fun j ↦ ?_
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, AbsoluteValue.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, AbsoluteValue.nonneg ..⟩
    · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl

lemma AbsoluteValue.max_one_eq_iSup (v : AbsoluteValue K ℝ) (x : K) :
    v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
  have H (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
  simp_rw [H]
  exact max_eq_iSup (v x) 1

variable [NumberField K]

lemma NumberField.FinitePlace.add_le (v : FinitePlace K) (x y : K) :
    v (x + y) ≤ max (v x) (v y) := by
  simp_rw [← NumberField.FinitePlace.norm_embedding_eq, map_add]
  rcases le_total ‖embedding v.maximalIdeal x‖ ‖embedding v.maximalIdeal y‖ with h | h
  · refine le_sup_of_le_right ?_
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact sup_of_le_right h ▸ Valuation.map_add_le_max' Valued.v ..
  · refine le_sup_of_le_left ?_
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact sup_of_le_left h ▸ Valuation.map_add_le_max' Valued.v ..

instance : NonarchimedeanHomClass (NumberField.FinitePlace K) K ℝ where
  map_add_le_max v a b := NumberField.FinitePlace.add_le v a b

end aux
