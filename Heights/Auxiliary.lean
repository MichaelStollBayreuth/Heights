import Mathlib

/-!
### Auxiliary statements

These fill API gaps in Mathlib and should eventually go there.
-/

section general

open Filter in
lemma Real.le_of_forall_pow_le_mul_pow {a b x y : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : ∀ᶠ (N : ℕ) in atTop, x ^ N ≤ (a * N + b) * y ^ N) :
    x ≤ y := by
  replace h : ∀ᶠ (N : ℕ) in atTop, x ≤ (a * N + b) ^ (1 / N : ℝ) * y := by
    rw [eventually_atTop] at h ⊢
    obtain ⟨m, hm⟩ := h
    refine ⟨max 1 m, fun n hn ↦ ?_⟩
    specialize hm n <| le_of_max_le_right hn
    have hn' : 1 ≤ n := le_of_max_le_left hn
    have : MonotoneOn (fun x : ℝ ↦ x ^ (1 / n : ℝ)) {x | 0 ≤ x} :=
      Real.strictMonoOn_rpow_Ici_of_exponent_pos (by positivity) |>.monotoneOn
    have H₁ : x ^ n ∈ {x | 0 ≤ x} := by
      simp only [Set.mem_setOf_eq]
      exact pow_nonneg hx n
    have H₂ : (a * n + b) * y ^ n ∈ {x | 0 ≤ x} := by
      simp only [Set.mem_setOf_eq]
      positivity
    have := this H₁ H₂ hm
    dsimp only at this
    rwa [← Real.rpow_natCast_mul hx, mul_one_div_cancel (by norm_cast; omega),
      Real.rpow_one,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
      mul_one_div_cancel (by norm_cast; omega), Real.rpow_one] at this
  refine ge_of_tendsto ?_ h
  conv => enter [3]; rw [← one_mul y]
  refine Tendsto.mul ?_ tendsto_const_nhds
  have := tendsto_rpow_div_mul_add a 1 (-b) zero_ne_one
  have hn : Tendsto (fun x : ℝ ↦ (a * x + b)) atTop atTop :=
    tendsto_atTop_add_const_right atTop b <| Tendsto.const_mul_atTop ha tendsto_id
  refine (this.comp (hn.comp tendsto_natCast_atTop_atTop)).congr fun N ↦ ?_
  rcases eq_or_ne N 0 with rfl | hN₀
  · simp
  simp only [one_mul, Function.comp_apply, add_neg_cancel_right]
  congr 1
  field_simp

end general

namespace Isometry

lemma isHomeomorph_ofBijective {α β F : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [FunLike F α β] {f : F} (hf : Isometry f) (hb : Function.Bijective f) :
    IsHomeomorph f := by
  obtain ⟨g, hg₁, hg₂⟩ := Function.bijective_iff_has_inverse.mp hb
  exact IsHomeomorph.mk hf.continuous
    (IsOpenMap.of_inverse (hf.right_inv hg₂).continuous hg₂ hg₁) hb

lemma isHomeomorph_ofEquiv {α β E : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [EquivLike E α β] {f : E} (hf : Isometry f) :
    IsHomeomorph f :=
  hf.isHomeomorph_ofBijective <| EquivLike.bijective f

end Isometry

namespace IsHomeomorph

lemma right_inv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {g : Y → X}
    (h : Function.RightInverse g f) (hh : IsHomeomorph f) :
    IsHomeomorph g := by
  obtain ⟨e, he⟩ := isHomeomorph_iff_exists_homeomorph.mp hh
  refine isHomeomorph_iff_exists_homeomorph.mpr ⟨e.symm, ?_⟩
  ext1 y
  nth_rewrite 1 [← h y]
  apply_fun e
  simp [he]

lemma ringEquiv_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Semiring X]
    [Semiring Y] {e : X ≃+* Y} (h : IsHomeomorph e) :
    IsHomeomorph e.symm :=
  h.right_inv fun x ↦ e.apply_symm_apply x

end IsHomeomorph

namespace RingHom

lemma bijective_of_bijective_comp {R₁ R₂ R₃ R₄ : Type*} [NonAssocSemiring R₁] [NonAssocSemiring R₂]
    [NonAssocSemiring R₃] [NonAssocSemiring R₄] {e₁ : R₁ ≃+* R₂} {e₂ : R₂ →+* R₃} {e₃ : R₃ ≃+* R₄}
    (h : Function.Bijective (e₃.toRingHom.comp <| e₂.comp e₁.toRingHom)) :
    Function.Bijective e₂ := by
  let e : R₁ →+* R₄ := e₃.toRingHom.comp <| e₂.comp e₁.toRingHom
  have : e₂ = e₃.symm.toRingHom.comp (e.comp e₁.symm.toRingHom) := by ext1; simp [e]
  simpa [this]

end RingHom

section Rat

-- maybe unnecessary...
@[simp]
lemma Rat.castHom_apply {R : Type*} [DivisionRing R] [CharZero R] (x : ℚ) :
  castHom R x = x := rfl

end Rat

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
lemma finprod_mono [CommMonoid β] [PartialOrder β] [IsOrderedMonoid β] {f g : α → β} (hf : f.mulSupport.Finite)
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

section Mathlib.Topology.Algebra.Module.FiniteDimension

variable  {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul 𝕜 E'] [T2Space E']

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

namespace WithAbs

/-- The identity map of `F` as a ring isomorphism between normed field structures on `F` induce
by two absolute values- -/
abbrev equiv₂ {R : Type*} [Semiring R] (v₁ v₂ : AbsoluteValue R ℝ) : WithAbs v₁ ≃+* WithAbs v₂ :=
  (equiv v₁).trans (equiv v₂).symm

@[simp]
lemma equiv₂_symm_eq {R : Type*} [Semiring R] (v₁ v₂ : AbsoluteValue R ℝ) :
    (equiv₂ v₁ v₂).symm = equiv₂ v₂ v₁ := by
  ext1
  simp

@[simp]
lemma apply_equiv {R α : Type*} [Semiring R] (f : R → α) (v : AbsoluteValue R ℝ) (x : R) :
    f (equiv v x) = f x := rfl

section equal

variable {R : Type*} [Ring R] {v v' : AbsoluteValue R ℝ} (h : v = v')

include h in
lemma uniformContinuous_equiv₂_of_eq : UniformContinuous (equiv₂ v v') := by
  apply Isometry.uniformContinuous
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [h]
  simp

include h in
lemma continuous_equiv₂_of_eq : Continuous (equiv₂ v v') :=
  (uniformContinuous_equiv₂_of_eq h).continuous

end equal

instance charZero {R : Type*} [Semiring R] [CharZero R] {v : AbsoluteValue R ℝ} :
    CharZero (WithAbs v) :=
  inferInstanceAs <| CharZero R

variable {F S : Type*} [Field F]

-- these two require heavier imports (so are not part of #20642)

instance fd_left [AddCommGroup S] [Module F S] [FiniteDimensional F S] {v : AbsoluteValue F ℝ} :
    FiniteDimensional (WithAbs v) S :=
  inferInstanceAs <| FiniteDimensional F S

instance fd_right [Ring S] [Module F S] [FiniteDimensional F S] (v : AbsoluteValue S ℝ) :
    FiniteDimensional F (WithAbs v) :=
  inferInstanceAs <| FiniteDimensional F S

-- #find_home fd_left -- [Mathlib.NumberTheory.NumberField.Completion]

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

lemma norm_equiv_eq {v v' : AbsoluteValue F ℝ} (h : v = v') (x : WithAbs v) :
    ‖(algebraMap (WithAbs v') v'.Completion).comp (WithAbs.equiv v).toRingHom x‖ = v x := by
  simp [h]
  rfl

end WithAbs

end Mathlib.Analysis.Normed.Ring.WithAbs

namespace UniformSpace.Completion

-- @[simp]
lemma coeFun_extensionHom {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α]
    [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [Ring β] [IsUniformAddGroup β]
    [IsTopologicalRing β] (f : α →+* β) (hf : Continuous ⇑f) [CompleteSpace β] [T0Space β] :
    ⇑(extensionHom f hf) = Completion.extension f := rfl

end UniformSpace.Completion

namespace RingEquiv

lemma trans_symm_comp_trans_symm {R R' R'' : Type*} [Semiring R] [Semiring R'] [Semiring R'']
     (f : R ≃+* R') (f' : R'' ≃+* R'):
    ⇑(f.trans f'.symm) ∘ ⇑(f'.trans f.symm) = id := by
  ext1
  simp

end RingEquiv


section UniformSpace.Completion.mapRingHom

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
variable {β : Type*} [Ring β] [UniformSpace β] [IsTopologicalRing β] [IsUniformAddGroup β]
variable {γ : Type*} [Ring γ] [UniformSpace γ] [IsTopologicalRing γ] [IsUniformAddGroup γ]

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

/-!
### API lemmas for absolute values
-/

namespace AbsoluteValue

section API

namespace Completion

section general

variable {F : Type*} [Field F] (v : AbsoluteValue F ℝ)

@[simp]
lemma norm_coe (x : WithAbs v) : ‖(x : v.Completion)‖ = ‖x‖ :=
  UniformSpace.Completion.norm_coe x

end general

section equal

open WithAbs

variable {F : Type*} [Field F] {v v' : AbsoluteValue F ℝ} (h : v = v')

noncomputable
def ringHom_of_eq : v.Completion →+* v'.Completion :=
  extensionEmbedding_of_comp <| WithAbs.norm_equiv_eq h

lemma coeFun_ringHom_of_eq :
    ⇑(ringHom_of_eq h) = UniformSpace.Completion.map ⇑(equiv₂ v v') := rfl

open UniformSpace.Completion in
lemma ringHom_of_eq_comp_symm :
    (ringHom_of_eq h).comp (ringHom_of_eq h.symm) = RingHom.id _ := by
  apply RingHom.coe_inj
  rw [RingHom.coe_comp, coeFun_ringHom_of_eq, coeFun_ringHom_of_eq, RingHom.coe_id,
    map_comp (uniformContinuous_equiv₂_of_eq h) (uniformContinuous_equiv₂_of_eq h.symm),
    RingEquiv.trans_symm_comp_trans_symm]
  simp

noncomputable
def ringEquiv_of_eq : v.Completion ≃+* v'.Completion :=
  UniformSpace.Completion.mapRingEquiv (equiv₂ v v')
    (continuous_equiv₂_of_eq h) (continuous_equiv₂_of_eq h.symm)
  -- RingEquiv.ofRingHom (ringHom_of_eq h) (ringHom_of_eq h.symm)
  --   (ringHom_of_eq_comp_symm h) (ringHom_of_eq_comp_symm h.symm)

lemma coeFun_ringEquiv_of_eq :
    ⇑(ringEquiv_of_eq h) = UniformSpace.Completion.map ⇑(equiv₂ v v') := rfl

lemma ringEquiv_of_eq_apply_ringEquiv_of_eq_apply (x : v'.Completion) :
    ringEquiv_of_eq h (ringEquiv_of_eq h.symm x) = x :=
  congrFun (congrArg (⇑) <| ringHom_of_eq_comp_symm h) x

lemma isometry_ringEquiv_of_eq : Isometry <| ringEquiv_of_eq h := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [congrFun (coeFun_ringEquiv_of_eq h) x]
  revert x
  rw [← funext_iff]
  refine UniformSpace.Completion.ext (UniformSpace.Completion.continuous_map).norm
    continuous_id'.norm fun x ↦ ?_
  rw [h] -- take the cheap way out
  simp

noncomputable
def isometryEquiv_of_eq : v.Completion ≃ᵢ v'.Completion :=
  IsometryEquiv.mk' (ringEquiv_of_eq h) (ringEquiv_of_eq h.symm)
    (ringEquiv_of_eq_apply_ringEquiv_of_eq_apply h) <| isometry_ringEquiv_of_eq h

end equal

end Completion

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

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

lemma norm_algebraMap_comp_eq_real (x : WithAbs real) :
    ‖(algebraMap ℚ ℝ).comp (WithAbs.equiv real) x‖ = real x := rfl

open Completion in
noncomputable
def ringHom_completion_real : real.Completion →+* ℝ :=
  extensionEmbedding_of_comp norm_algebraMap_comp_eq_real

open Completion Topology in
lemma ringHom_completion_real_surjective : Function.Surjective ringHom_completion_real := by
  have : IsClosedEmbedding ringHom_completion_real :=
    isClosedEmbedding_extensionEmbedding_of_comp norm_algebraMap_comp_eq_real
  exact RingHom.fieldRange_eq_top_iff.mp <| Real.subfield_eq_of_closed this.isClosed_range

open Completion Topology in
noncomputable
def ringEquiv_completion_real : real.Completion ≃+* ℝ :=
  RingEquiv.ofBijective ringHom_completion_real
    ⟨ringHom_completion_real.injective, ringHom_completion_real_surjective⟩

lemma isometry_ringEquiv_completion_real : Isometry ringEquiv_completion_real := by
  refine AddMonoidHomClass.isometry_of_norm ringEquiv_completion_real fun x ↦ ?_
  simp only [ringEquiv_completion_real, RingEquiv.coe_ofBijective, ringHom_completion_real]
  refine (AddMonoidHomClass.isometry_iff_norm _).mp ?_ x
  exact AbsoluteValue.Completion.isometry_extensionEmbedding_of_comp norm_algebraMap_comp_eq_real

open Completion Topology in
lemma isHomeomorph_ringEquiv_completion_real : IsHomeomorph ringEquiv_completion_real := by
  simp only [ringEquiv_completion_real, RingEquiv.coe_ofBijective]
  have := isClosedEmbedding_extensionEmbedding_of_comp norm_algebraMap_comp_eq_real
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨this.toIsEmbedding, ringEquiv_completion_real.surjective⟩

end Rat.AbsoluteValue

end rat

namespace AbsoluteValue

section weak

-- Set up the data of a "weak absolute value" of a semiring `R`.
variable {R : Type*} [CommSemiring R] {v : R → ℝ} (hm : ∀ x y, v (x * y) = v x * v y)
  (hn : ∀ x, 0 ≤ v x) (h₀ : ∀ x, v x = 0 ↔ x = 0) (ha : ∀ x y, v (x + y) ≤ 2 * max (v x) (v y))

include hn h₀ ha

open Finset in
lemma abv_finsetSum_le_mul_max (f : ℕ → R) {N : ℕ} (hN : 0 < N) :
    v (∑ i ∈ range N, f i) ≤
      2 * N * (range N).sup' (nonempty_range_iff.mpr hN.ne') fun i ↦ v (f i) := by
  have key (f : ℕ → R) (n : ℕ) : v (∑ i ∈ range (2 ^n), f i) ≤
      2 ^ n * (range (2 ^ n)).sup' (nonempty_range_iff.mpr n.two_pow_pos.ne') fun i ↦ v (f i) := by
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      have H₁ : 2 ^ n ≤ 2 ^ (n + 1) := by
        rw [pow_succ', Nat.two_mul]
        exact Nat.le_add_right ..
      rw [← sum_range_add_sum_Ico f H₁, sum_Ico_eq_sum_range]
      have H₂ : 2 ^ (n + 1) - 2 ^ n = 2 ^ n := by
        rw [pow_succ', Nat.two_mul]
        exact Nat.add_sub_self_left ..
      rw [H₂, pow_succ', mul_assoc]
      refine (ha ..).trans ?_
      gcongr (2 * ?_)
      have hnr := nonempty_range_iff.mpr n.two_pow_pos.ne'
      have : (range (2 ^ (n + 1))).sup'
          (nonempty_range_iff.mpr (n + 1).two_pow_pos.ne') (fun i ↦ v (f i)) =
            max ((range (2 ^ n)).sup' hnr (fun i ↦ v (f i)))
              ((range (2 ^ n)).sup' hnr fun i ↦ v (f (2 ^ n + i))) := by
        have : range (2 ^ (n + 1)) = range (2 ^ n) ∪ Ico (2 ^ n) (2 ^ (n + 1)) := by
          rw [range_eq_Ico]
          exact (Ico_union_Ico_eq_Ico (Nat.zero_le _) H₁).symm
        simp_rw [this]
        have H : (Ico (2 ^ n) (2 ^ (n + 1))).Nonempty := by
          rw [nonempty_Ico, ← one_mul (2 ^ n), pow_succ']
          gcongr
          exact one_lt_two
        rw [sup'_union hnr H]
        congr 1
        -- `rw` does not work
        erw [sup'_comp_eq_image (f := fun i ↦ 2 ^ n + i) hnr (fun i ↦ v (f i)),
          sup'_comp_eq_image (f := id) ?_ (fun i ↦ v (f i))]
        refine sup'_congr ?_ ?_ fun i hi ↦ rfl
        · simp only [image_id, range_eq_Ico, image_add_left_Ico, add_zero, pow_succ']
          congr 2
          exact Nat.two_mul _
        · exact H
      rw [this, mul_max_of_nonneg _ _ (mod_cast (2 ^ n).zero_le)]
      gcongr <;> exact ih _
  rcases le_or_gt N 1 with hN₁ | hN₁
  · replace hN₁ : N = 1 := by omega
    simp only [hN₁, range_one, sum_singleton, Nat.cast_one, mul_one, sup'_singleton]
    nth_rewrite 1 [← one_mul (v (f 0))]
    gcongr
    · exact hn (f 0)
    · exact one_le_two
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, 2 ^ m < N ∧ N ≤ 2 ^ (m + 1) := by
    induction N with
    | zero => exact hN.false.elim
    | succ n ih =>
      rcases eq_or_ne n 0 with rfl | hn
      · norm_num at hN₁
      replace hN₁ : 0 < n := by omega
      rcases eq_or_ne n 1 with rfl | hn₁
      · exact ⟨0, by norm_num, by norm_num⟩
      have hn₁ : 1 < n := by omega
      obtain ⟨m, hm₁, hm₂⟩ := ih hN₁ hn₁
      rcases lt_or_eq_of_le hm₂ with hm | rfl
      · exact ⟨m, by omega⟩
      · exact ⟨m + 1, by omega⟩
  have HN := nonempty_range_iff.mpr hN.ne'
  let g i := if i < N then f i else 0
  have hg₁ : ∑ i ∈ range N, f i = ∑ i ∈ range (2 ^ (m + 1)), g i := by
    have : ∀ i ≥ N, g i = 0 := by
      intro i hi
      replace hi : ¬ i < N := Nat.not_lt.mpr hi
      simp [g, hi]
    rw [Finset.eventually_constant_sum this hm₂]
    refine sum_congr rfl fun i hi ↦ ?_
    simp [g, mem_range.mp hi]
  have hg₂ : (range N).sup' HN (fun i ↦ v (f i)) =
      (range (2 ^ (m + 1))).sup'
        (nonempty_range_iff.mpr (m + 1).two_pow_pos.ne') fun i ↦ v (g i) := by
    rcases eq_or_lt_of_le hm₂ with rfl | hm₂
    · refine sup'_congr (nonempty_range_iff.mpr (m + 1).two_pow_pos.ne') rfl fun i hi ↦ ?_
      simp [g, mem_range.mp hi]
    have : range (2 ^ (m + 1)) = range N ∪ Ico N (2 ^ (m + 1)) := by
      rw [range_eq_Ico, eq_comm]
      exact Ico_union_Ico_eq_Ico N.zero_le hm₂.le
    simp_rw [this]
    have H₁ : (Ico N (2 ^ (m + 1))).Nonempty := by simpa
    rw [sup'_union HN H₁]
    have H₂ : ((Ico N (2 ^ (m + 1))).sup' H₁ fun x ↦ v (g x)) ≤
        ((range N).sup' HN fun x ↦ v (g x)) := by
      refine sup'_le H₁ (fun x ↦ v (g x)) fun i hi ↦ ?_
      simp only [mem_Ico] at hi
      have hi' : ¬ i < N := Nat.not_lt.mpr hi.1
      simp only [hi', ↓reduceIte, le_sup'_iff, mem_range, g, (h₀ 0).mpr rfl]
      exact ⟨0, hN, hn _⟩
    rw [max_eq_left H₂]
    refine sup'_congr HN rfl fun i hi ↦ ?_
    simp [g, mem_range.mp hi]
  rw [hg₁, hg₂]
  refine (key g (m + 1)).trans ?_
  gcongr
  · exact le_sup'_of_le _ (mem_range.mpr (m + 1).two_pow_pos) <| hn (g 0)
  · rw [pow_succ']
    gcongr
    exact_mod_cast hm₁.le

include hm

lemma abv_natCast_le (n : ℕ) : v n ≤ 2 * n := by
  rcases n.eq_zero_or_pos with rfl | hn₀
  · simp [(h₀ 0).mpr rfl]
  have : (n : R) = ∑ i ∈ Finset.range n, 1 := by
    refine (Finset.sum_range_induction (fun k ↦ 1) Nat.cast Nat.cast_zero (fun n ↦ ?_) n).symm
    simp
  rw [this]
  have : v 1 ≤ 1 := by
    by_contra! h
    have : v 1 ^ 2 = v 1 := by
      calc
      _ = v 1 * v 1 := by rw[sq]
      _ = v (1 * 1) := (hm 1 1).symm
      _ = v 1 := by rw [mul_one]
    rcases eq_zero_or_one_of_sq_eq_self this with h' | h' <;> linarith only [h, h']
  refine (abv_finsetSum_le_mul_max hn h₀ ha _ hn₀).trans ?_
  simp only [Finset.sup'_const]
  nth_rewrite 2 [← mul_one (2 * (n : ℝ))]
  gcongr

variable [Nontrivial R]

omit hn ha in
lemma abv_one : v 1 = 1 := by
  have : v 1 ^ 2 = v 1 := by
    calc
    _ = v 1 * v 1 := by rw[sq]
    _ = v (1 * 1) := (hm 1 1).symm
    _ = v 1 := by rw [mul_one]
  exact (eq_zero_or_one_of_sq_eq_self this).resolve_left <| (h₀ 1).not.mpr one_ne_zero

omit hn ha in
lemma abv_pow (x : R) (n : ℕ) : v (x ^ n) = v x ^ n := by
  induction n with
  | zero => simp [abv_one hm h₀]
  | succ n ih => rw [pow_succ, hm, ih, ← pow_succ]


open Filter Topology in
lemma add_le_add_of_add_le_two_mul_max  (x y : R) : v (x + y) ≤ v x + v y := by
  have hx : 0 ≤ v x := hn x
  have hy : 0 ≤ v y := hn y
  have key (N : ℕ) : v (x + y) ^ N ≤ 2 * (N + 1) * (2 * (v x + v y) ^ N) := by
    have hN : (Finset.range (N + 1)).Nonempty := by simp
    rw [← abv_pow hm h₀, add_pow x y]
    refine (abv_finsetSum_le_mul_max hn h₀ ha _ (N := N + 1) N.zero_lt_succ).trans ?_
    have H (i) (hi : i ∈ Finset.range (N + 1)) : v (N.choose i) ≤ 2 * N.choose i :=
      abv_natCast_le hm hn h₀ ha _
    have H' (i) (hi : i ∈ Finset.range (N + 1)) :
        v (x ^ i * y ^ (N - i) * N.choose i) ≤ 2 * (v x ^ i * v y ^ (N - i) * N.choose i) := by
      simp only [hm, abv_pow hm h₀]
      rw [mul_comm 2, mul_assoc (v x ^ i * v y ^ (N - i))]
      gcongr (v x ^ i * v y ^ (N - i) * ?_)
      rw [mul_comm]
      exact H i hi
    push_cast
    gcongr
    refine (Finset.sup'_mono_fun (hs := hN) H').trans ?_
    rw [add_pow, Finset.mul_sum]
    refine Finset.sup'_le hN _ fun i hi ↦ ?_
    refine Finset.single_le_sum (f := fun i ↦ 2 * (v x ^ i * v y ^ (N - i) * ↑(N.choose i))) (fun a h ↦ ?_) hi
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    positivity
  refine Real.le_of_forall_pow_le_mul_pow zero_lt_four zero_le_four (hn _) (add_nonneg hx hy) ?_
  convert Eventually.of_forall key using 3 with N
  ring

/-- A "weak absolute value" (satisfying the weaker triangle inequality
`v (x + y) ≤ 2 * max (v x) (v y)`) is actually an absolute value. -/
def of_add_le_two_mul_max : AbsoluteValue R ℝ where
      toFun := v
      map_mul' := hm
      nonneg' := hn
      eq_zero' := h₀
      add_le' := add_le_add_of_add_le_two_mul_max hm hn h₀ ha

end weak

lemma abv_natCast_strictMono_of_not_isNonarchimedean {R : Type*} [Field R] {v : AbsoluteValue R ℝ}
    (hv : ¬ IsNonarchimedean v) :
    StrictMono (v ∘ NatCast.natCast) := by
  intro m n h
  simp only [Function.comp_apply]
  have := v.isNonarchimedean_iff_le_one_on_nat.not.mp hv
  push_neg at this
  obtain ⟨k, hk⟩ := this

  sorry

lemma abv_add_le_abv_two_mul_max {R : Type*} [Field R]
    {v : AbsoluteValue R ℝ} (hv : ¬ IsNonarchimedean v) (x y : R) :
    v (x + y) ≤ v 2 * max (v x) (v y) := by
  refine Real.le_of_forall_pow_le_mul_pow zero_lt_one zero_le_one (v.nonneg _) (by positivity) <|
     Filter.Eventually.of_forall fun N ↦ ?_
  rw [← v.map_pow, add_pow, one_mul, ← smul_eq_mul]
  norm_cast
  conv => enter [2]; rw [← Finset.card_range (N + 1)]
  refine (v.sum_le ..).trans <| (Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ ?_)
  rw [v.map_mul, mul_comm _ (v (N.choose i)), mul_pow]
  gcongr
  · rw [← v.map_pow]
    have : N.choose i ≤ 2 ^ N := (N.choose_le_succ i).trans <| N.choose_succ_le_two_pow i
    convert (abv_natCast_strictMono_of_not_isNonarchimedean hv).monotone this
    simp
  · rw [v.map_mul, v.map_pow, v.map_pow]
    simp only [Finset.mem_range, Nat.lt_add_one_iff] at hi
    nth_rewrite 2 [(Nat.add_sub_of_le hi).symm]
    rw [pow_add]
    gcongr
    exacts [le_max_left .., le_max_right ..]

end AbsoluteValue
