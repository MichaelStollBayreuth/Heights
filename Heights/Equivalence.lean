import Heights.Auxiliary

/-!
# Two absolute values are equivalent iff they induce the same topology

This is Theorem 1.1 in Conrad's notes. We split the interesting direction (same topology
implies equivalence) into two steps:

* `AbsoluteValue.abv_lt_one_iff_of_isHomeomorph`: if `v₁` and `v₂` induce the same
  topology, then `{x | v₁ x < 1} = {x | v₂ x < 1}`.

* `AbsoluteValue.isEquiv_of_abv_lt_one_iff`: if `{x | v₁ x < 1} = {x | v₂ x < 1}`,
  then `v₁ ≈ v₂`.

The main result is `AbsoluteValue.isEquiv_iff_isHomeomorph`.
-/


/-!
### More API for AbsoluteValue.IsEquiv
-/

section isEquiv

namespace AbsoluteValue

variable {R : Type*} [Semiring R]

/-- The exponent `c` in the definition of equivalence of absolute values. -/
noncomputable
def IsEquiv.exponent {v v' : AbsoluteValue R ℝ} (h : v ≈ v') : ℝ :=
  Classical.choose h

lemma IsEquiv.exponent_pos {v v' : AbsoluteValue R ℝ} (h : v ≈ v') : 0 < exponent h :=
  (Classical.choose_spec h).1

lemma IsEquiv.exponent_def {v v' : AbsoluteValue R ℝ} (h : v ≈ v') (x : R) :
    v x ^ exponent h = v' x :=
  congrFun (Classical.choose_spec h).2 x

lemma rpow_add_le (v : AbsoluteValue R ℝ) {e : ℝ} (h₀ : 0 < e) (h₁ : e ≤ 1) (x y : R) :
    v (x + y) ^ e ≤ v x ^ e + v y ^ e := by
  calc
  _ ≤ (v x + v y) ^ e := Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) h₀.le
  _ ≤ v x ^ e + v y ^ e := Real.rpow_add_le_add_rpow (v.nonneg _) (v.nonneg _) h₀.le h₁

lemma rpow_add_le_of_isNonarchimedean {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v) {e : ℝ}
    (he : 0 < e) (x y : R) :
    v (x + y) ^ e ≤ v x ^ e ⊔ v y ^ e := by
  calc
  _ ≤ (v x ⊔ v y) ^ e := Real.rpow_le_rpow (v.nonneg _) (hv x y) he.le
  _ = v x ^ e ⊔ v y ^ e := (Real.max_map_rpow (v.nonneg _) (v.nonneg _) he.le).symm

@[simps]
noncomputable
def rpow (v : AbsoluteValue R ℝ) {e : ℝ} (h₀ : 0 < e) (h₁ : e ≤ 1) : AbsoluteValue R ℝ where
  toFun := (v ·) ^ e
  map_mul' x y := by simp only [Pi.pow_apply, v.map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _)]
  nonneg' x := by simpa only [Pi.pow_apply] using Real.rpow_nonneg (v.nonneg _) _
  eq_zero' x := by simp [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg _), v.eq_zero, h₀.ne']
  add_le' x y := by simpa only [Pi.pow_apply] using rpow_add_le v h₀ h₁ x y

@[simps]
noncomputable
def rpow_of_isNonarchimedean {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v) {e : ℝ}
    (he : 0 < e) :
    AbsoluteValue R ℝ where
  toFun := (v ·) ^ e
  map_mul' x y := by simp only [Pi.pow_apply, v.map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _)]
  nonneg' x := by simpa only [Pi.pow_apply] using Real.rpow_nonneg (v.nonneg _) _
  eq_zero' x := by simp [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg _), v.eq_zero, he.ne']
  add_le' x y := by
    simp only [Pi.pow_apply]
    exact (rpow_add_le_of_isNonarchimedean hv he x y).trans <|
      max_le_add_of_nonneg (by positivity) (by positivity)

lemma isEquiv_rpow (v : AbsoluteValue R ℝ) {e : ℝ} (h₀ : 0 < e) (h₁ : e ≤ 1) :
    v.rpow h₀ h₁ ≈ v :=
  Setoid.symm ⟨e, h₀, rfl⟩

lemma isEquiv_rpow_of_isNonarchimedean {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v) {e : ℝ}
    (he : 0 < e) :
    v.rpow_of_isNonarchimedean hv he ≈ v :=
  Setoid.symm <| ⟨e, he, rfl⟩

lemma isNonarchimedean_rpow_of_isNonarchimedean {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v)
    {e : ℝ} (he : 0 < e) :
    IsNonarchimedean (v.rpow_of_isNonarchimedean hv he) := by
  intro x y
  simpa only [rpow_of_isNonarchimedean, coe_mk, MulHom.coe_mk, Pi.pow_apply]
    using rpow_add_le_of_isNonarchimedean hv he x y

end AbsoluteValue

namespace Rat.AbsoluteValue

/-- If an absolute value `v` on `ℚ` is equivalent to the standard absolute value `|·|`,
then `v = |·| ^ e` for some `0 < e ≤ 1`. -/
lemma eq_rpow_of_isEquiv_real {v : AbsoluteValue ℚ ℝ} (hv : v ≈ real) :
    ∃ (e : ℝ) (h₀ : 0 < e) (h₁ : e ≤ 1), v = real.rpow h₀ h₁ := by
  obtain ⟨e, he₀, he⟩ := Setoid.symm hv
  refine ⟨e, he₀, ?_, by ext1; simp [← congrFun he, AbsoluteValue.rpow]⟩
  have h₂ := congrFun he 2
  simp only [real_eq_abs, Nat.abs_ofNat, cast_ofNat] at h₂
  have h : (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) := by
    calc
    _ = v 2 := h₂
    _ = v (1 + 1) := by rw [one_add_one_eq_two]
    _ ≤ v 1 + v 1 := v.add_le 1 1
    _ = 1 + 1 := by rw [v.map_one]
    _ = 2 ^ (1 : ℝ) := by rw [Real.rpow_one, one_add_one_eq_two]
  exact (Real.strictMono_rpow_of_base_gt_one one_lt_two).le_iff_le.mp h

end Rat.AbsoluteValue

end isEquiv

namespace AbsoluteValue

/-!
### Two absolute values are equivalent iff they induce the same topology

This is Theorem 1.1 in Conrad's notes.

The main result is `AbsoluteValue.isEquiv_iff_isHomeomorph`.
-/

section withAbs

open WithAbs

variable {R : Type*} [Ring R]

open Filter Topology in
/-- The sequence of `n`th powers of an element `x` converges to zero in the topology induced
by an absolute value `v` if and only if `v x < 1`. -/
lemma tendsto_nhds_zero_iff_abv_lt_one [Nontrivial R] (v : AbsoluteValue R ℝ) (x : R) :
    Tendsto (fun n : ℕ ↦ (WithAbs.equiv v).symm x ^ n) atTop (𝓝 0) ↔ v x < 1 := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [Metric.tendsto_atTop] at H
    obtain ⟨n, hn⟩ := H 1 zero_lt_one
    simp only [ge_iff_le, dist_zero_right, norm_eq_abv, map_pow, RingEquiv.apply_symm_apply] at hn
    replace hn := hn n le_rfl
    refine (pow_lt_one_iff_of_nonneg (v.nonneg x) ?_).mp hn
    rintro rfl
    simp at hn
  · refine tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_
    rwa [norm_eq_abv]

variable {F : Type*} [Field F]

/-- An absolute value `v` induces the discrete topology on a field `F` if and only if
`v` is trivial. -/
lemma discrete_iff_not_isNontrivial {v : AbsoluteValue F ℝ} :
    DiscreteTopology (WithAbs v) ↔ ¬ v.IsNontrivial := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨fun ⟨ε, hε₀, hε₁⟩ ↦ ?_, fun H ↦ ⟨1 / 2, one_half_pos, fun y hy ↦ ?_⟩⟩
  · simp only [dist_zero_right, norm_eq_abv] at hε₁
    rw [not_isNontrivial_iff]
    intro x hx₀
    by_contra! h
    have H {y : F} (hy₀ : y ≠ 0) (hy : v y < 1) : False := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε₀ hy
      rw [← v.map_pow] at hn
      exact hy₀ <| pow_eq_zero <| hε₁ _ hn
    rcases h.lt_or_lt with h | h
    · exact H hx₀ h
    · replace h := inv_lt_one_of_one_lt₀ h
      rw [← map_inv₀] at h
      exact H (inv_ne_zero hx₀) h
  · rw [dist_zero_right, norm_eq_abv] at hy
    rcases eq_or_ne y 0 with rfl | hy₀
    · rfl
    · have : WithAbs.equiv v y ≠ 0 := hy₀
      simp only [H, not_false_eq_true, ne_eq, this, not_isNontrivial_apply] at hy
      contrapose! hy
      exact one_half_lt_one.le

/-- A field with a nontrivial absolute value on it is a nontrivially normed field. -/
noncomputable
def IsNontrivial.nontriviallyNormedField {v : AbsoluteValue F ℝ} (hv : v.IsNontrivial) :
    NontriviallyNormedField (WithAbs v) where
  __ := WithAbs.normedField v
  non_trivial := hv.exists_abv_gt_one

noncomputable
instance _root_.WithAbs.nontriviallynormedField {v : AbsoluteValue F ℝ} [Fact <| v.IsNontrivial] :
    NontriviallyNormedField (WithAbs v) :=
  (Fact.out : v.IsNontrivial).nontriviallyNormedField

end withAbs

section equiv_trivial

variable {R : Type*} [Ring R]

lemma isEquiv_iff_eq_of_not_isNontrivial {v₁ v₂ : AbsoluteValue R ℝ} (h : ¬ v₁.IsNontrivial) :
    v₁ ≈ v₂ ↔ v₁ = v₂ := by
  refine ⟨fun ⟨c, hc₀, hc₁⟩ ↦ ?_, fun H ↦ H ▸ isEquiv_refl v₂⟩
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [h, hx, ← hc₁]

lemma eq_of_not_isNontrivial {v₁ v₂ : AbsoluteValue R ℝ} (h₁ : ¬ v₁.IsNontrivial)
    (h₂ : ¬ v₂.IsNontrivial) :
    v₁ = v₂ := by
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [h₁, h₂, hx]

end equiv_trivial

section equiv

variable {F : Type*} [Field F]

open WithAbs

lemma continuous_equiv₂ {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    Continuous (WithAbs.equiv₂ v₁ v₂) := by
  obtain ⟨c, hc₀, hc₁⟩ := h
  rw [Metric.continuous_iff]
  simp only [dist_eq_norm_sub, norm_eq_abv, WithAbs.equiv₂, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  intro x ε hε₀
  conv =>
    enter [1, δ, 2, y, 2, 1]
    rw [← map_sub, RingEquiv.coe_trans, Function.comp_apply, RingEquiv.apply_symm_apply]
  refine ⟨ε ^ (1 / c), Real.rpow_pos_of_pos hε₀ _, fun y h ↦ ?_⟩
  let x' := WithAbs.equiv v₁ x
  let y' := WithAbs.equiv v₁ y
  have hx : x = (WithAbs.equiv v₁).symm x' := rfl
  have hy : y = (WithAbs.equiv v₁).symm y' := rfl
  rw [hx, hy, ← map_sub, RingEquiv.apply_symm_apply] at h
  rw [map_sub, hx, hy]
  simp only [Equiv.apply_symm_apply, ← hc₁]
  calc v₁ (y' - x') ^ c
  _ < (ε ^ (1 / c)) ^ c := by gcongr
  _ = ε := by rw [← Real.rpow_mul hε₀.le, one_div_mul_cancel hc₀.ne', Real.rpow_one]

/-- Two equivalent absolute values on a field `F` induce the same topology.
This defines the identity map `F → F` as a homeomorphism between the two topologies. -/
def homeomorph_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    WithAbs v₁ ≃ₜ WithAbs v₂ where
  toFun := (WithAbs.equiv v₂).symm ∘ WithAbs.equiv v₁
  invFun := (WithAbs.equiv v₁).symm ∘ WithAbs.equiv v₂
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_equiv₂ h
  continuous_invFun := continuous_equiv₂ (Setoid.symm h)

lemma homeomorph_of_isEquiv_toFun_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    ⇑(homeomorph_of_isEquiv h) = ⇑(equiv₂ v₁ v₂) :=
  rfl

open Filter Topology in
/-- If two absolute values on a field `F` induce the same topology and an element of `F` has
absolute value less than one with respect to the first absolute value, then also with respect
to the second absolute value. -/
lemma abv_lt_one_of_isHomeomorph {v₁ v₂ : AbsoluteValue F ℝ}
    (h : IsHomeomorph (WithAbs.equiv₂ v₁ v₂)) {x : F} (hx : v₁ x < 1) :
    v₂ x < 1 := by
  let x₁ : WithAbs v₁ := (WithAbs.equiv v₁).symm x
  let x₂ : WithAbs v₂ := (WithAbs.equiv v₂).symm x
  have hx₁ : Tendsto (fun n : ℕ ↦ x₁ ^ n) atTop (𝓝 0) :=
    (tendsto_nhds_zero_iff_abv_lt_one v₁ x).mpr hx
  have hx₂ : Tendsto (fun n : ℕ ↦ x₂ ^ n) atTop (𝓝 0) := by
    have (n : ℕ) : x₂ ^ n = (WithAbs.equiv₂ v₁ v₂) (x₁ ^ n) := rfl
    simp_rw [this]
    refine Tendsto.comp (g := (WithAbs.equiv₂ v₁ v₂)) ?_ hx₁
    exact Continuous.tendsto h.continuous 0
  exact (tendsto_nhds_zero_iff_abv_lt_one v₂ x).mp hx₂

/--If two absolute values on a field `F` induce the same topology, then the sets of elements
of absolute value less than one agree for both absolute values. -/
lemma abv_lt_one_iff_of_isHomeomorph {v₁ v₂ : AbsoluteValue F ℝ}
    (h : IsHomeomorph (WithAbs.equiv₂ v₁ v₂)) (x : F) :
    v₁ x < 1 ↔ v₂ x < 1 := by
  refine ⟨abv_lt_one_of_isHomeomorph h, abv_lt_one_of_isHomeomorph ?_⟩
  obtain ⟨φ, hφ⟩ := isHomeomorph_iff_exists_homeomorph.mp h
  refine isHomeomorph_iff_exists_homeomorph.mpr ⟨φ.symm, ?_⟩
  apply_fun (fun f ↦ (φ.symm ∘ f) ∘ (WithAbs.equiv₂ v₂ v₁)) at hφ
  simp only [Homeomorph.symm_comp_self, CompTriple.comp_eq] at hφ
  rw [hφ, Function.comp_assoc, ← WithAbs.equiv₂_symm_eq, ← RingEquiv.coe_trans,
    RingEquiv.self_trans_symm]
  simp

open Real in
/-- If the sets of elements of absolute value less than one agree for two absolute values
on a field `F`, then the two absolute values are equivalent. -/
lemma isEquiv_of_abv_lt_one_iff {v₁ v₂ : AbsoluteValue F ℝ} (h : ∀ x, v₁ x < 1 ↔ v₂ x < 1) :
    v₁ ≈ v₂ := by
  by_cases H : ∃ x ≠ 0, v₁ x < 1
  · obtain ⟨c, hc₀, hc₁⟩ := H
    have hc₂ := (h c).mp hc₁
    have hcv₁ := v₁.pos hc₀
    have hcv₁' := v₁.nonneg c
    have hcv₂ := v₂.pos hc₀
    let e := logb (v₁ c) (v₂ c)
    have he : v₁ c ^ e = v₂ c := rpow_logb hcv₁ hc₁.ne hcv₂
    have he₀ : 0 < e := logb_pos_of_base_lt_one hcv₁ hc₁ hcv₂ hc₂
    have key (y : F) : ¬ v₁ y ^ e < v₂ y := by
      intro hy
      have hyv₁ := v₁.nonneg y
      have hy₀ : y ≠ 0 := v₂.ne_zero_iff.mp ((rpow_nonneg hyv₁ e).trans_lt hy).ne'
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hcv₂ <| (div_lt_one (v₂.pos hy₀)).mpr hy
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℤ, v₁ (y ^ n) ^ e < v₂ c ^ m ∧ v₂ c ^ m < v₂ (y ^ n) := by
        have hv₂y := v₂.pos <| pow_ne_zero n hy₀
        refine exists_zpow_btwn_of_lt_mul ?_ hv₂y hcv₂ hc₂
        rwa [div_pow, ← v₂.map_pow, div_lt_iff₀ hv₂y, rpow_pow_comm hyv₁,
          mul_comm, ← v₁.map_pow] at hn
      rw [← he, rpow_zpow_comm hcv₁', rpow_lt_rpow_iff (v₁.nonneg _) (zpow_nonneg hcv₁' m) he₀,
        ← div_lt_one (zpow_pos hcv₁ m), ← map_zpow₀, ← map_div₀] at hm₁
      rw [← map_zpow₀, ← one_lt_div (v₂.pos (by exact zpow_ne_zero m hc₀)), ← map_div₀] at hm₂
      exact (h _).mp hm₁ |>.trans hm₂ |>.false
    simp only [not_lt] at key
    refine ⟨e, he₀, funext fun x ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa only [AbsoluteValue.map_zero, le_refl] using zero_rpow he₀.ne'
    · refine le_antisymm ?_ (key x)
      have := key x⁻¹
      simp only [map_inv₀, inv_rpow (v₁.nonneg _)] at this
      rwa [inv_le_inv₀ (v₂.pos hx₀) <| rpow_pos_of_pos (v₁.pos hx₀) e] at this
  · -- both are trivial
    have H₁ := mt IsNontrivial.exists_abv_lt_one H
    have H' : ¬∃ x, x ≠ 0 ∧ v₂ x < 1 := by
      simp_all only [not_false_eq_true, ne_eq, not_exists, not_and, not_lt, implies_true]
    have H₂ := mt IsNontrivial.exists_abv_lt_one H'
    classical
    rw [of_not_not <| (isNontrivial_iff_ne_trivial v₁).not.mp H₁,
      of_not_not <| (isNontrivial_iff_ne_trivial v₂).not.mp H₂]

open Filter Topology in
/-- Two absolute values on a field are equivalent if and only if they induce the same topology. -/
-- (This is Theorem 1.1 in the reference.)
lemma isEquiv_iff_isHomeomorph (v₁ v₂ : AbsoluteValue F ℝ) :
    v₁ ≈ v₂ ↔ IsHomeomorph (WithAbs.equiv₂ v₁ v₂) := by
  refine ⟨fun H ↦ ?_, fun H ↦ isEquiv_of_abv_lt_one_iff <| abv_lt_one_iff_of_isHomeomorph H⟩
  exact isHomeomorph_iff_exists_homeomorph.mpr ⟨homeomorph_of_isEquiv H, rfl⟩

/-- The induced ring homomorphism between two completions with respect to equivalent
absolute values. -/
noncomputable
def ringHom_completion_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    v₁.Completion →+* v₂.Completion :=
  UniformSpace.Completion.mapRingHom (WithAbs.equiv₂ v₁ v₂) <|
    ((isEquiv_iff_isHomeomorph v₁ v₂).mp h).continuous

/-- The induced ring isomorphism between two completions with respect to equivalent
absolute values. -/
noncomputable
def ringEquiv_completion_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    v₁.Completion ≃+* v₂.Completion := by
  refine UniformSpace.Completion.mapRingEquiv (WithAbs.equiv₂ v₁ v₂) ?_ ?_
  · rw [← homeomorph_of_isEquiv_toFun_eq h]
    exact Homeomorph.continuous (homeomorph_of_isEquiv h)
  · rw [WithAbs.equiv₂_symm_eq, ← homeomorph_of_isEquiv_toFun_eq (Setoid.symm h)]
    exact Homeomorph.continuous (homeomorph_of_isEquiv (Setoid.symm h))

lemma ringEquiv_completion_coe_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    (ringEquiv_completion_of_isEquiv h).toRingHom = ringHom_completion_of_isEquiv h :=
  rfl

lemma ringEquiv_completion_coeFun_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    ⇑(ringEquiv_completion_of_isEquiv h) = ringHom_completion_of_isEquiv h :=
  rfl

lemma ringEquiv_completion_symm_coeFun_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    ⇑(ringEquiv_completion_of_isEquiv h).symm = ringHom_completion_of_isEquiv (Setoid.symm h) :=
  rfl

open UniformSpace.Completion in
/-- The induced ring isomorphism between two completions with respect to equivalent
absolute values is a homeomorphism. -/
lemma isHomeomorph_ringEquiv_completion {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    IsHomeomorph (ringEquiv_completion_of_isEquiv h) := by
  refine isHomeomorph_iff_exists_inverse.mpr
    ⟨?_, (ringEquiv_completion_of_isEquiv h).symm, ?_, ?_, ?_⟩
  · rw [ringEquiv_completion_coeFun_eq, ringHom_completion_of_isEquiv]
    exact continuous_mapRingHom (continuous_equiv₂ h)
  · simp [Function.LeftInverse]
  · simp [Function.RightInverse, Function.LeftInverse]
  · rw [ringEquiv_completion_symm_coeFun_eq, ringHom_completion_of_isEquiv]
    exact continuous_mapRingHom (continuous_equiv₂ (Setoid.symm h))

lemma uniformContinuous_equiv₂_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    UniformContinuous (equiv₂ v₁ v₂) :=
  uniformContinuous_of_continuousAt_zero _ (continuous_equiv₂ h).continuousAt

/-- If `v₁` and `v₂` are equivalent absolute values on `F`, then `WithAbs.equiv₂ v₁ v₂`
is an equivalence of uniformities. This gives the `UniformEquiv`. -/
def uniformEquivOfIsEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    WithAbs v₁ ≃ᵤ WithAbs v₂ :=
  UniformEquiv.mk (equiv₂ v₁ v₂) (uniformContinuous_equiv₂_of_isEquiv h)
    (uniformContinuous_equiv₂_of_isEquiv <| Setoid.symm h)

/-- The underlying equivalence of `uniformEquivOfIsEquiv h` is `WithAbs.equiv₂ _ _`. -/
lemma uniformEquiv_eq_equiv₂ {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    (uniformEquivOfIsEquiv h).toEquiv = (equiv₂ v₁ v₂).toEquiv :=
  rfl

/-- If `v₁` and `v₂` are equivalent absolute values on `F` and `F` is complete
with respect to `v₁`, then `F` is also complete with respect to `v₂`. -/
lemma completeSpace_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂)
    [CompleteSpace (WithAbs v₁)] :
    CompleteSpace (WithAbs v₂) :=
  (uniformEquivOfIsEquiv h).completeSpace_iff.mp ‹CompleteSpace (WithAbs v₁)›

end equiv
