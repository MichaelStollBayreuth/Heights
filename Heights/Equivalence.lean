import Heights.Auxiliary

/-!
# Two absolute values are equivalent iff they induce the same topology

This is Theorem 1.1 in Conrad's notes. The result is now in Mathlib as
`AbsoluteValue.isEquiv_iff_isHomeomorph`.
-/


/-!
### More API for AbsoluteValue.IsEquiv
-/

section isEquiv

namespace AbsoluteValue

variable {R : Type*} [Field R]

/-- The exponent `c` in the definition of equivalence of absolute values. -/
noncomputable
def IsEquiv.exponent {v v' : AbsoluteValue R ℝ} (h : v ≈ v') : ℝ :=
  Classical.choose <| isEquiv_iff_exists_rpow_eq.mp h

lemma IsEquiv.exponent_pos {v v' : AbsoluteValue R ℝ} (h : v ≈ v') : 0 < exponent h :=
  (Classical.choose_spec <| isEquiv_iff_exists_rpow_eq.mp h).1

lemma IsEquiv.exponent_def {v v' : AbsoluteValue R ℝ} (h : v ≈ v') (x : R) :
    v x ^ exponent h = v' x :=
  congrFun (Classical.choose_spec <| isEquiv_iff_exists_rpow_eq.mp h).2 x

/- lemma IsEquiv.isNontrivial {v v' : AbsoluteValue R ℝ} (h : v ≈ v') (h' : v.IsNontrivial) :
    v'.IsNontrivial := by
  obtain ⟨x, hx₀, hx₁⟩ := h'
  refine ⟨x, hx₀, ?_⟩
  rw [← exponent_def h]
  contrapose! hx₁
  apply_fun (· ^ (exponent h)⁻¹) at hx₁
  rwa [Real.one_rpow, Real.rpow_rpow_inv (AbsoluteValue.nonneg ..) h.exponent_pos.ne'] at hx₁ -/

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
  Setoid.symm <| isEquiv_iff_exists_rpow_eq.mpr ⟨e, h₀, rfl⟩

lemma isEquiv_rpow_of_isNonarchimedean {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v) {e : ℝ}
    (he : 0 < e) :
    v.rpow_of_isNonarchimedean hv he ≈ v :=
  Setoid.symm <| isEquiv_iff_exists_rpow_eq.mpr ⟨e, he, rfl⟩

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
  obtain ⟨e, he₀, he⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp <| Setoid.symm hv
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

section withAbs

open WithAbs

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
    rcases h.lt_or_gt with h | h
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
instance _root_.WithAbs.nontriviallynormedField {v : AbsoluteValue F ℝ} [Fact v.IsNontrivial] :
    NontriviallyNormedField (WithAbs v) :=
  (Fact.out : v.IsNontrivial).nontriviallyNormedField

end withAbs

section equiv_trivial

variable {R : Type*} [Field R]

lemma isEquiv_iff_eq_of_not_isNontrivial {v₁ v₂ : AbsoluteValue R ℝ} (h : ¬ v₁.IsNontrivial) :
    v₁ ≈ v₂ ↔ v₁ = v₂ := by
  refine ⟨fun H ↦ ?_, fun H ↦ H ▸ IsEquiv.refl v₂⟩
  obtain ⟨c, hc₀, hc₁⟩ := isEquiv_iff_exists_rpow_eq.mp H
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

lemma continuous_equivWithAbs {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    Continuous (equivWithAbs v₁ v₂) :=
  isEquiv_iff_isHomeomorph v₁ v₂ |>.mp h |>.continuous

/-- Two equivalent absolute values on a field `F` induce the same topology.
This defines the identity map `F → F` as a homeomorphism between the two topologies. -/
def homeomorph_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    WithAbs v₁ ≃ₜ WithAbs v₂ where
  toFun := WithAbs.equivWithAbs v₁ v₂
  invFun := WithAbs.equivWithAbs v₂ v₁
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_equivWithAbs h
  continuous_invFun := continuous_equivWithAbs (Setoid.symm h)

lemma homeomorph_of_isEquiv_toFun_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    ⇑(homeomorph_of_isEquiv h) = ⇑(equivWithAbs v₁ v₂) :=
  rfl

/-- The induced ring homomorphism between two completions with respect to equivalent
absolute values. -/
noncomputable
def ringHom_completion_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    v₁.Completion →+* v₂.Completion :=
  UniformSpace.Completion.mapRingHom (equivWithAbs v₁ v₂) <|
    ((isEquiv_iff_isHomeomorph v₁ v₂).mp h).continuous

/-- The induced ring isomorphism between two completions with respect to equivalent
absolute values. -/
noncomputable
def ringEquiv_completion_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    v₁.Completion ≃+* v₂.Completion := by
  refine UniformSpace.Completion.mapRingEquiv (equivWithAbs v₁ v₂) ?_ ?_
  · rw [← homeomorph_of_isEquiv_toFun_eq h]
    exact Homeomorph.continuous (homeomorph_of_isEquiv h)
  · rw [WithAbs.equivWithAbs_symm, ← homeomorph_of_isEquiv_toFun_eq (Setoid.symm h)]
    exact Homeomorph.continuous (homeomorph_of_isEquiv (Setoid.symm h))

lemma ringEquiv_completion_coe_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    (ringEquiv_completion_of_isEquiv h).toRingHom = ringHom_completion_of_isEquiv h :=
  rfl

lemma ringEquiv_completion_coeFun_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    (ringEquiv_completion_of_isEquiv h).toRingHom = ringHom_completion_of_isEquiv h :=
  rfl

lemma ringEquiv_completion_symm_coeFun_eq {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    (ringEquiv_completion_of_isEquiv h).symm.toRingHom =
      ringHom_completion_of_isEquiv (Setoid.symm h) :=
  rfl

open UniformSpace.Completion in
/-- The induced ring isomorphism between two completions with respect to equivalent
absolute values is a homeomorphism. -/
lemma isHomeomorph_ringEquiv_completion {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    IsHomeomorph (ringEquiv_completion_of_isEquiv h) := by
  refine isHomeomorph_iff_exists_inverse.mpr
    ⟨?_, (ringEquiv_completion_of_isEquiv h).symm, ?_, ?_, ?_⟩
  · rw [show ⇑(ringEquiv_completion_of_isEquiv h) = ⇑(ringEquiv_completion_of_isEquiv h).toRingHom
         from rfl]
    rw [congrArg DFunLike.coe (ringEquiv_completion_coeFun_eq ..), ringHom_completion_of_isEquiv]
    exact continuous_mapRingHom (continuous_equivWithAbs h)
  · simp [Function.LeftInverse]
  · simp [Function.RightInverse, Function.LeftInverse]
  · rw [show ⇑(ringEquiv_completion_of_isEquiv h).symm =
          ⇑(ringEquiv_completion_of_isEquiv h).symm.toRingHom from rfl]
    rw [ringEquiv_completion_symm_coeFun_eq, ringHom_completion_of_isEquiv]
    exact continuous_mapRingHom (continuous_equivWithAbs (Setoid.symm h))

lemma uniformContinuous_equivWithAbs_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    UniformContinuous (equivWithAbs v₁ v₂) :=
  uniformContinuous_of_continuousAt_zero _ (continuous_equivWithAbs h).continuousAt

/-- If `v₁` and `v₂` are equivalent absolute values on `F`, then `WithAbs.equivWithAbs v₁ v₂`
is an equivalence of uniformities. This gives the `UniformEquiv`. -/
def uniformEquivOfIsEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    WithAbs v₁ ≃ᵤ WithAbs v₂ :=
  UniformEquiv.mk (equivWithAbs v₁ v₂) (uniformContinuous_equivWithAbs_of_isEquiv h)
    (uniformContinuous_equivWithAbs_of_isEquiv <| Setoid.symm h)

/-- The underlying equivalence of `uniformEquivOfIsEquiv h` is `WithAbs.equivWithAbs _ _`. -/
lemma uniformEquiv_eq_equiv₂ {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    (uniformEquivOfIsEquiv h).toEquiv = (equivWithAbs v₁ v₂).toEquiv :=
  rfl

/-- If `v₁` and `v₂` are equivalent absolute values on `F` and `F` is complete
with respect to `v₁`, then `F` is also complete with respect to `v₂`. -/
lemma completeSpace_of_isEquiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂)
    [CompleteSpace (WithAbs v₁)] :
    CompleteSpace (WithAbs v₂) :=
  (uniformEquivOfIsEquiv h).completeSpace_iff.mp ‹CompleteSpace (WithAbs v₁)›

end equiv
