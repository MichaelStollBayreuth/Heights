import Mathlib

/-!
### Auxiliary statements

These fill API gaps in Mathlib and should eventually go there.
-/

section aux

variable {α β : Type*}

lemma max_eq_iSup [ConditionallyCompleteLattice α] (a b : α) : max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

-- [Mathlib.Analysis.SpecialFunctions.Pow.Real]
lemma Real.max_map_rpow {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    max (x ^ c) (y ^ c) = max x y ^ c := by
  rcases le_total x y with h | h
  · simpa only [h, sup_of_le_right, sup_eq_right] using Real.rpow_le_rpow hx h hc
  · simpa only [h, sup_of_le_left, sup_eq_left] using Real.rpow_le_rpow hy h hc

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

section completion

variable {F : Type*} [NormedField F]

-- This is needed to get `Field v.Completion`
instance NormedField.instCompletableTopField : CompletableTopField F where
  t0 := (inferInstanceAs <| T0Space _).t0
  nice f hc hn := by
    rw [Metric.cauchy_iff] at hc ⊢
    obtain ⟨hf₁, hf₂⟩ := hc
    refine ⟨Filter.map_neBot, ?_⟩
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.inf_eq_bot_iff.mp hn
    obtain ⟨ε, hε₀, hε⟩ := Metric.mem_nhds_iff.mp hU
    intro δ hδ₀
    obtain ⟨t, ht₁, ht₂⟩ := hf₂ (δ * ε * ε) (by positivity)
    let t' := t ∩ V
    have h : ∀ x ∈ t', ∀ y ∈ t', dist x y < δ * ε * ε :=
      fun x hx y hy ↦
        ht₂ x (Set.mem_of_mem_inter_left hx) y (Set.mem_of_mem_inter_left hy)
    simp_rw [Filter.mem_map]
    refine ⟨(· ⁻¹) ⁻¹' t', by simpa only [Set.inv_preimage, inv_inv] using Filter.inter_mem ht₁ hV,
      fun x hx y hy ↦ ?_⟩
    simp only [Set.inv_preimage, Set.mem_inv] at hx hy
    specialize h x⁻¹ hx y⁻¹ hy
    rw [dist_eq_norm_sub] at h ⊢
    have hinv {z : F} (hz : z⁻¹ ∈ t') : z⁻¹ ∉ Metric.ball 0 ε :=
      fun H ↦ (Set.mem_empty_iff_false _).mp <|
        hUV ▸ Set.mem_inter (hε H) (Set.mem_of_mem_inter_right hz)
    have h₀ {z : F} (hz : z⁻¹ ∈ t') : z ≠ 0 := by
      rintro rfl
      exact inv_zero (G₀ := F) ▸ hinv hz <| Metric.mem_ball_self hε₀
    have Hε {z : F} (hz : z⁻¹ ∈ t') : ‖z‖ ≤ ε⁻¹ := by
      refine le_inv_of_le_inv₀ hε₀ ?_
      simpa only [Metric.mem_ball, dist_zero_right, norm_inv, not_lt] using hinv hz
    have hx₀ := h₀ hx
    have hy₀ := h₀ hy
    rw [inv_sub_inv hx₀ hy₀, norm_div, norm_mul, norm_sub_rev,
      div_lt_iff₀ (by simp [hx₀, hy₀])] at h
    refine h.trans_le ?_
    rw [mul_assoc, mul_assoc, ← mul_assoc ε]
    conv_rhs => rw [← mul_one δ]
    gcongr
    calc ε * ε * (‖x‖ * ‖y‖)
    _ ≤ ε * ε * (ε⁻¹ * ε⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (Hε hx) (Hε hy) (norm_pos_iff.mpr hy₀).le (inv_pos_of_pos hε₀).le)
        (mul_pos hε₀ hε₀).le
    _ = 1 := by rw [mul_mul_mul_comm, mul_inv_cancel₀ hε₀.ne', one_mul]

noncomputable
example {F  : Type*} [Field F] {v : AbsoluteValue F ℝ} : Field v.Completion := inferInstance

end completion

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

-- #20642

variable {R : Type*} [Ring R]

namespace WithAbs

lemma norm_eq_abv (v : AbsoluteValue R ℝ) (x : WithAbs v) :
    ‖x‖ = v (WithAbs.equiv v x) := rfl

variable {F S : Type*} [Field F]

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

/-- The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute value `v`
to `R'`. -/
def algEquiv {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (v : AbsoluteValue S ℝ) :
    (WithAbs v) ≃ₐ[R] S := AlgEquiv.refl (A₁ := S)

-- these two require heavier imports (so are not part of #20642)

instance fd_left [AddCommGroup S] [Module F S] [FiniteDimensional F S] {v : AbsoluteValue F ℝ} :
    FiniteDimensional (WithAbs v) S :=
  inferInstanceAs <| FiniteDimensional F S

instance fd_right [Ring S] [Module F S] [FiniteDimensional F S] (v : AbsoluteValue S ℝ) :
    FiniteDimensional F (WithAbs v) :=
  inferInstanceAs <| FiniteDimensional F S

--

/- @[simp]
lemma equiv_smul [Ring S] [Module R S] {v : AbsoluteValue S ℝ} (c : R) (x : WithAbs v) :
    equiv v (c • x) = c • equiv v x := rfl

@[simp]
lemma equiv_symm_smul [Ring S] [Module R S] {v : AbsoluteValue S ℝ} (c : R) (x : S) :
    (equiv v).symm (c • x) = c • (equiv v).symm x := rfl

@[simp]
lemma equiv_apply_algebraMap {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    {v : AbsoluteValue R ℝ} (v' : AbsoluteValue S ℝ) (x : WithAbs v) :
    equiv v' (algebraMap (WithAbs v) (WithAbs v') x) = algebraMap R S (equiv v x) :=
  rfl -/

end WithAbs

end Mathlib.Analysis.Normed.Ring.WithAbs

namespace AbsoluteValue

/-!
### API lemmas for absolute values
-/

section API

variable {R : Type*} [Semiring R] {S : Type*} [OrderedSemiring S]

section nonarchimedean

variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ}

/-- A version of `AbsoluteValue.isEquiv_def` that uses `AbsoluteValue.IsEquiv`. -/
lemma isEquiv_def' {v' : AbsoluteValue R ℝ} : v ≈ v' ↔ v.IsEquiv v' := Iff.rfl

lemma isEquiv_def {v' : AbsoluteValue R ℝ} : v ≈ v' ↔ ∃ c : ℝ, c > 0 ∧ (v · ^ c) = v' := Iff.rfl

lemma isNonarchimedean_of_isEquiv {v' : AbsoluteValue R ℝ} (h₁ : v ≈ v')
    (h₂ : IsNonarchimedean v) :
    IsNonarchimedean v' := by
  intro x y
  specialize h₂ x y
  obtain ⟨c, hc₀, hc⟩ := h₁
  simp_rw [← hc, Real.max_map_rpow (v.nonneg x) (v.nonneg y) hc₀.le]
  exact Real.rpow_le_rpow (v.nonneg _) h₂ hc₀.le

lemma isNontrivial_of_archimedean (h : ¬ IsNonarchimedean v) : v.IsNontrivial := by
  contrapose! h
  rw [not_isNontrivial_iff] at h
  intro x y
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · simp [hx, hy, hxy]
  simp [hx, hy, hxy, h]

lemma le_one_on_nat_of_isNonarchimedean [Nontrivial R] (h : IsNonarchimedean v) (n : ℕ) : v n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    exact (h n 1).trans <| by simp [ih]

lemma le_one_on_nat_of_bounded [Nontrivial R] {B : ℝ} (h : ∀ n : ℕ, v n ≤ B) (n : ℕ) : v n ≤ 1 := by
  contrapose! h
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B h
  exact ⟨n ^ m, by rwa [Nat.cast_pow, map_pow]⟩

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ}

open IsUltrametricDist in
lemma isNonarchimedean_of_le_one_on_nat (h : ∀ n : ℕ, v n ≤ 1) : IsNonarchimedean v :=
  have H (n : ℕ) : ‖(n : WithAbs v)‖ ≤ 1 := h n
  isUltrametricDist_iff_isNonarchimedean_norm.mp <|
    isUltrametricDist_of_forall_norm_natCast_le_one H

lemma isNonarchimedean_of_bounded_on_nat {B : ℝ} (h : ∀ n : ℕ, v n ≤ B) : IsNonarchimedean v :=
  isNonarchimedean_of_le_one_on_nat <| le_one_on_nat_of_bounded h

/-- An absolute value on a field is nonarchimedean if and only if it is bounded by `1`
on the image of `ℕ`. -/
lemma isNonarchimedean_iff_le_one_on_nat : IsNonarchimedean v ↔ ∀ n : ℕ, v n ≤ 1 :=
  ⟨le_one_on_nat_of_isNonarchimedean, isNonarchimedean_of_bounded_on_nat⟩

/-- A field with an archimedean absolute value has characteristic zero. -/
lemma charZero_of_archimedean (h : ¬ IsNonarchimedean v) : CharZero F := by
  contrapose! h
  let p := ringChar F
  have : CharP (WithAbs v) p := ringChar.charP F
  have : NeZero p := ⟨mt (CharP.ringChar_zero_iff_CharZero _).mp h⟩
  let φ := ZMod.castHom (dvd_refl p) (WithAbs v)
  obtain ⟨B, hB⟩ : ∃ B, ∀ a : ZMod p, ‖φ a‖ ≤ B := Finite.exists_le _
  have H (n : ℕ) : ‖(n : WithAbs v)‖ ≤ B := map_natCast φ n ▸ hB n
  exact isNonarchimedean_of_bounded_on_nat H

end nonarchimedean

end API

end AbsoluteValue

section rat

open AbsoluteValue

namespace Rat.AbsoluteValue

lemma isNonarchimedean_padic (p : ℕ) [Fact p.Prime] :
    IsNonarchimedean (padic p) :=
  isNonarchimedean_of_le_one_on_nat fun n ↦ padic_le_one p n

lemma padic_of_isNonarchimedean {v : AbsoluteValue ℚ ℝ}
    (h : IsNonarchimedean v) (h' : v.IsNontrivial) :
    ∃ (p : ℕ) (_ : Fact p.Prime), v ≈ padic p := by
  refine (equiv_padic_of_bounded h' ?_).exists
  exact le_one_on_nat_of_isNonarchimedean h

/-- A nontrivial absolute value on `ℚ` is nonarchimedean if and only if it is equivalent to
a `p`-adic absolute value for some prime `p`. -/
lemma isNonarchimedean_iff_equiv_padic {v : AbsoluteValue ℚ ℝ} (h : v.IsNontrivial) :
    IsNonarchimedean v ↔ ∃ (p : ℕ) (_ : Fact p.Prime), v ≈ padic p :=
  ⟨fun a ↦ padic_of_isNonarchimedean a h,
    fun ⟨p, _, hp⟩ ↦ isNonarchimedean_of_isEquiv (Setoid.symm hp) <| isNonarchimedean_padic p⟩

/-- An archimedean absolute value on `ℚ` must be equivalent to the standard absolute value. -/
lemma real_of_archimedean {v : AbsoluteValue ℚ ℝ} (h : ¬ IsNonarchimedean v) :
    v ≈ real := by
  refine Or.resolve_right (equiv_real_or_padic v <| isNontrivial_of_archimedean h) fun H ↦ ?_
  obtain ⟨p, _, hp⟩ := H.exists
  exact h <| isNonarchimedean_of_isEquiv (Setoid.symm hp) <| isNonarchimedean_padic p

open Completion Topology in
noncomputable
def ringEquiv_completion_real : real.Completion ≃+* ℝ := by
  let f : WithAbs real →+* ℝ := (algebraMap ℚ ℝ).comp (WithAbs.equiv real)
  have hf (x : WithAbs real) : ‖f x‖ = real x := rfl
  let e := extensionEmbedding_of_comp hf
  refine RingEquiv.ofBijective e ⟨e.injective, ?_⟩
  have : IsClosedEmbedding e := isClosedEmbedding_extensionEmbedding_of_comp hf
  exact RingHom.fieldRange_eq_top_iff.mp <| Real.subfield_eq_of_closed this.isClosed_range

end Rat.AbsoluteValue

end rat

section UniformSpace.Completion.mapRingHom

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
variable {β : Type*} [Ring β] [UniformSpace β] [TopologicalRing β] [UniformAddGroup β]
variable {γ : Type*} [Ring γ] [UniformSpace γ] [TopologicalRing γ] [UniformAddGroup γ]

lemma continuous_mapRingHom {f : α →+* β} (hf : Continuous f) : Continuous (mapRingHom f hf) := by
  simpa only [mapRingHom, extensionHom, DFunLike.coe] using continuous_extension

lemma mapRingHom_id : mapRingHom (RingHom.id α) continuous_id = RingHom.id _ := by
  ext1 x
  simp only [mapRingHom, extensionHom, RingHomCompTriple.comp_eq, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, RingHom.id_apply]
  exact congrFun (extension_unique (uniformContinuous_coe α) uniformContinuous_id (fun _ ↦ rfl)) x

lemma mapRingHom_comp {f : α →+* β} {g : β →+* γ} (hf : Continuous f) (hg : Continuous g) :
    mapRingHom (g.comp f) (RingHom.coe_comp .. ▸ Continuous.comp hg hf) =
      (mapRingHom g hg).comp (mapRingHom f hf) := by
  ext1 x
  simp only [mapRingHom, extensionHom, RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Function.comp_apply]
  convert congrFun (extension_unique (f := ⇑coeRingHom ∘ ⇑g ∘ ⇑f)
    (g := (mapRingHom g hg).comp (mapRingHom f hf)) ?_ ?_ (fun a ↦ ?_)) x
  · refine UniformContinuous.comp (uniformContinuous_coe _) <| UniformContinuous.comp ?_ ?_
    · exact uniformContinuous_addMonoidHom_of_continuous hg
    · exact uniformContinuous_addMonoidHom_of_continuous hf
  · rw [RingHom.coe_comp]
    refine UniformContinuous.comp ?_ ?_ <;>
      simpa [mapRingHom, extensionHom] using uniformContinuous_extension
  · simp [Function.comp_apply, RingHom.coe_comp, mapRingHom, extensionHom_coe, coeRingHom]

/-- A ring isomorphism that is also a homeomorphism between two topological rings induces
a ring isomorphism between their completions. -/
noncomputable
def mapRingEquiv (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm):
    Completion α ≃+* Completion β := by
  refine RingEquiv.ofRingHom (mapRingHom f.toRingHom hf) (mapRingHom f.symm.toRingHom hf')
    ?_ ?_ <;>
  { rw [← mapRingHom_comp]
    simpa [RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm] using mapRingHom_id
  }

end UniformSpace.Completion

end UniformSpace.Completion.mapRingHom
