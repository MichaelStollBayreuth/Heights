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

section Mathlib.Analysis.SpecialFunctions.Pow.Real

-- #20608

namespace Real

lemma rpow_right_inj {x y z : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  rcases hx₁.lt_or_lt with h | h
  · exact le_antisymm ((rpow_le_rpow_left_iff_of_base_lt_one hx₀ h).mp H.symm.le) <|
      (rpow_le_rpow_left_iff_of_base_lt_one hx₀ h).mp H.le
  · exact le_antisymm ((rpow_le_rpow_left_iff h).mp H.le) ((rpow_le_rpow_left_iff h).mp H.symm.le)

lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_natCast, ← rpow_mul hx, mul_comm y]

lemma rpow_zpow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_intCast, ← rpow_mul hx, mul_comm y]

end Real

end Mathlib.Analysis.SpecialFunctions.Pow.Real

section Mathlib.Algebra.Order.Archimedean.Basic

-- #20612

variable {α : Type*} [LinearOrderedSemifield α] [Archimedean α] [ExistsAddOfLE α]

lemma exists_pow_btwn_of_lt_mul {a b c : α} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b ≤ 1)
    (hc₀ : 0 < c) (hc₁ : c < 1) :
    ∃ n : ℕ, a < c ^ n ∧ c ^ n < b := by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this ≠ 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| Left.mul_lt_of_le_of_lt_one_of_pos hb₁ hc₁ hb₀).false
  rw [(Nat.succ_pred_eq_of_ne_zero hn).symm, pow_succ, mul_lt_mul_right hc₀] at H
  exact Nat.find_min this (Nat.sub_one_lt hn) H

lemma exists_zpow_btwn_of_lt_mul {a b c : α} (h : a < b * c) (hb₀ : 0 < b) (hc₀ : 0 < c)
    (hc₁ : c < 1) :
    ∃ n : ℤ, a < c ^ n ∧ c ^ n < b := by
  rcases le_or_lt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb₀ hc₁
    exact ⟨n, ha.trans_lt (zpow_pos hc₀ _), mod_cast hn⟩
  · rcases le_or_lt b 1 with hb₁ | hb₁
    · obtain ⟨n, hn⟩ := exists_pow_btwn_of_lt_mul h hb₀ hb₁ hc₀ hc₁
      exact ⟨n, mod_cast hn⟩
    · rcases lt_or_le a 1 with ha₁ | ha₁
      · refine ⟨0, ?_⟩
        rw [zpow_zero]
        exact ⟨ha₁, hb₁⟩
      · have : b⁻¹ < a⁻¹ * c := by rwa [lt_inv_mul_iff₀' ha, inv_mul_lt_iff₀ hb₀]
        obtain ⟨n, hn₁, hn₂⟩ :=
          exists_pow_btwn_of_lt_mul this (inv_pos_of_pos ha) (inv_le_one_of_one_le₀ ha₁) hc₀ hc₁
        refine ⟨-n, ?_, ?_⟩
        · rwa [lt_inv_comm₀ (pow_pos hc₀ n) ha, ← zpow_natCast, ← zpow_neg] at hn₂
        · rwa [inv_lt_comm₀ hb₀ (pow_pos hc₀ n), ← zpow_natCast, ← zpow_neg] at hn₁

end Mathlib.Algebra.Order.Archimedean.Basic

section Mathlib.Topology.Algebra.Module.FiniteDimension

variable  {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [TopologicalAddGroup E'] [ContinuousSMul 𝕜 E'] [T2Space E']

/-- The homeomorphism induced by a linear isomorphism between two finite-dimensional vector spaces
over a complete nontrivially normed field. -/
def FiniteDimensional.homeomorph_of_linearEquiv (f : E ≃ₗ[𝕜] E') : E ≃ₜ E' :=
  Homeomorph.mk f f.toLinearMap.continuous_of_finiteDimensional <| by
    have : FiniteDimensional 𝕜 E' := Module.Finite.equiv f
    exact f.symm.toLinearMap.continuous_of_finiteDimensional

end Mathlib.Topology.Algebra.Module.FiniteDimension

-- more API lemmas

section

lemma Algebra.charpoly_aeval_self_eq_zero {F R : Type*} [Field F] [Ring R]
    [Algebra F R] [FiniteDimensional F R] (x : R) :
    (LinearMap.mulLeft F x).charpoly.aeval x = 0 := by
  let p := (LinearMap.mulLeft F x).charpoly
  have : p.aeval (LinearMap.mulLeft F x) = 0 := LinearMap.aeval_self_charpoly _
  apply_fun (· 1) at this
  simp only [Polynomial.aeval_endomorphism, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply,
    mul_one, LinearMap.zero_apply] at this
  rw [Polynomial.sum_eq_of_subset _ (p := p) (by simp) Polynomial.supp_subset_range_natDegree_succ] at this
  rwa [Polynomial.aeval_eq_sum_range]

lemma LinearMap.charpoly_eraseLead_natDegree_le {F R : Type*} [Field F] [AddCommGroup R]
    [Nontrivial R] [Module F R] [FiniteDimensional F R] (f : R →ₗ[F] R) :
  f.charpoly.eraseLead.natDegree + 1 ≤ Module.finrank F R := by
  have hnd := f.charpoly_natDegree
  by_cases hnc : f.charpoly.nextCoeff = 0
  · have : 0 < Module.finrank F R := Module.finrank_pos
    have := Polynomial.natDegree_eraseLead_le_of_nextCoeff_eq_zero hnc
    omega
  · exact hnd ▸ (Polynomial.natDegree_eraseLead_add_one hnc).le

end

section Mathlib.Analysis.Normed.Ring.WithAbs

variable {R : Type*} [Ring R]

lemma AbsoluteValue.norm_eq_abv (v : AbsoluteValue R ℝ) (x : WithAbs v) :
    ‖x‖ = v (WithAbs.equiv v x) := rfl

namespace WithAbs

@[simp]
theorem equiv_one (v : AbsoluteValue R ℝ) : (WithAbs.equiv v) 1 = 1 := rfl

@[simp]
theorem equiv_symm_one (v : AbsoluteValue R ℝ) : (WithAbs.equiv v).symm 1 = 1 := rfl

@[simp]
theorem equiv_pow {v : AbsoluteValue R ℝ} (x : WithAbs v) (n : ℕ) :
    (WithAbs.equiv v) (x ^ n) = (WithAbs.equiv v) x ^ n := rfl

@[simp]
theorem equiv_symm_pow {v : AbsoluteValue R ℝ} (x : R) (n : ℕ) :
    (WithAbs.equiv v).symm (x ^ n) = (WithAbs.equiv v).symm x ^ n := rfl

variable {F : Type*} [Field F]

@[simp]
theorem equiv_zpow {v : AbsoluteValue F ℝ} (x : WithAbs v) (n : ℤ) :
    (WithAbs.equiv v) (x ^ n) = (WithAbs.equiv v) x ^ n := rfl

@[simp]
theorem equiv_symm_zpow {v : AbsoluteValue F ℝ} (x : F) (n : ℤ) :
    (WithAbs.equiv v).symm (x ^ n) = (WithAbs.equiv v).symm x ^ n := rfl

variable {S : Type*}

instance commRing {R : Type*} [CommRing R] (v : AbsoluteValue R ℝ) : CommRing (WithAbs v) :=
  inferInstanceAs <| CommRing R

instance module_left [AddCommGroup S] [Module R S] {v : AbsoluteValue R ℝ} :
    Module (WithAbs v) S :=
  inferInstanceAs <| Module R S

instance module_right [Ring S] [Module R S] (v : AbsoluteValue S ℝ) : Module R (WithAbs v) :=
  inferInstanceAs <| Module R S

instance algebra_left {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (v : AbsoluteValue R ℝ) :
    Algebra (WithAbs v) S :=
  inferInstanceAs <| Algebra R S

instance algebra_right {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (v : AbsoluteValue S ℝ) :
    Algebra R (WithAbs v) :=
  inferInstanceAs <| Algebra R S

-- these two require heavier imports

instance fd_left [AddCommGroup S] [Module F S] [FiniteDimensional F S] {v : AbsoluteValue F ℝ} :
    FiniteDimensional (WithAbs v) S :=
  inferInstanceAs <| FiniteDimensional F S

instance fd_right [Ring S] [Module F S] [FiniteDimensional F S] (v : AbsoluteValue S ℝ) :
    FiniteDimensional F (WithAbs v) :=
  inferInstanceAs <| FiniteDimensional F S

--

@[simp]
lemma equiv_smul [Ring S] [Module R S] {v : AbsoluteValue S ℝ} (c : R) (x : WithAbs v) :
    WithAbs.equiv v (c • x) = c • WithAbs.equiv v x := rfl

@[simp]
lemma equiv_symm_smul [Ring S] [Module R S] {v : AbsoluteValue S ℝ} (c : R) (x : S) :
    (WithAbs.equiv v).symm (c • x) = c • (WithAbs.equiv v).symm x := rfl

@[simp]
lemma equiv_apply_algebraMap {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    {v : AbsoluteValue R ℝ} (v' : AbsoluteValue S ℝ) (x : WithAbs v) :
    WithAbs.equiv v' (algebraMap (WithAbs v) (WithAbs v') x) =
      algebraMap R S (WithAbs.equiv v x) :=
  rfl

end WithAbs

end Mathlib.Analysis.Normed.Ring.WithAbs

namespace AbsoluteValue

/-!
### API lemmas for absolute values
-/

section API

variable {R : Type*} [Semiring R] {S : Type*} [OrderedSemiring S]

section nontrivial

-- #20588

/-- An absolute value on a semiring `R` without zero divisors is *nontrivial* if it takes
a value `≠ 1` on a nonzero element.

This has the advantage over `v ≠ .trivial` that it does not require decidability
of `· = 0` in `R`. -/
def IsNontrivial (v : AbsoluteValue R S) : Prop :=
  ∃ x ≠ 0, v x ≠ 1

lemma isNontrivial_iff_ne_trivial [DecidableEq R] [NoZeroDivisors R] [Nontrivial S]
    (v : AbsoluteValue R S) :
    v.IsNontrivial ↔ v ≠ .trivial := by
  refine ⟨fun ⟨x, hx₀, hx₁⟩ h ↦ hx₁ <| h.symm ▸ trivial_apply hx₀, fun H ↦ ?_⟩
  contrapose! H
  simp only [IsNontrivial] at H
  push_neg at H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

lemma not_isNontrivial_iff (v : AbsoluteValue R S) :
    ¬ v.IsNontrivial ↔ ∀ x ≠ 0, v x = 1 := by
  simp only [IsNontrivial]
  push_neg
  rfl

@[simp]
lemma not_isNontrivial_apply {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x : R} (hx : x ≠ 0) :
    v x = 1 :=
  v.not_isNontrivial_iff.mp hv _ hx

lemma IsNontrivial.exists_abv_gt_one {F : Type*} [Field F] {v : AbsoluteValue F ℝ}
    (h : v.IsNontrivial) :
    ∃ x, 1 < v x := by
  obtain ⟨x, hx₀, hx₁⟩ := h
  rcases hx₁.lt_or_lt with h | h
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ <| v.pos hx₀).mpr h
  · exact ⟨x, h⟩

lemma IsNontrivial.exists_abv_lt_one {F : Type*} [Field F] {v : AbsoluteValue F ℝ}
    (h : v.IsNontrivial) :
    ∃ x ≠ 0, v x < 1 := by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
  have hy₀ := v.ne_zero_iff.mp <| (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

end nontrivial

end API
