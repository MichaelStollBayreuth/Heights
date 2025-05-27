import Heights.Equivalence

/-!
# Extensions of absolute values

Let `F` be a field with an absolute value `v` on it, and let `F'` be a field extension of `F`
of finite degree.
The goal here is to show that there are finitely many possibilities to extend `v`
to an absolute value `v'` on `F'` and that
`∏ v', v' x ^ localDegree F v' = v (Algebra.norm F' x)`,
where `localDegree F v'` is the degree of the extension of completions `F'_v' / F_v`.

We follow [Brian Conrad's notes}(http://math.stanford.edu/~conrad/676Page/handouts/ostrowski.pdf),
Sections 6 and 7.
-/

/-!
### Auxiliary lemmas
-/

section restrict

namespace AbsoluteValue

variable {F R S : Type*} [Field F] [Semiring R] [Nontrivial R] [Algebra F R] [Semiring S]
  [PartialOrder S] [IsOrderedRing S]

omit [Nontrivial R] [IsOrderedRing S] in
lemma comp_apply {R' : Type*} [Semiring R'] (v : AbsoluteValue R S) {f : R' →+* R}
    (hf : Function.Injective f) (x : R') :
  v.comp hf x = v (f x) := rfl

variable (F) in
/-- The restriction to a field `F` of an absolute value on an `F`-algebra `R`. -/
def restrict (v : AbsoluteValue R S) : AbsoluteValue F S :=
  v.comp (RingHom.injective (algebraMap F R))

omit [IsOrderedRing S] in
@[simp]
lemma apply_algebraMap (v : AbsoluteValue R S) (x : F) :
    v (algebraMap F R x) = v.restrict F x := rfl

omit [IsOrderedRing S] in
lemma isNontrivial_of_restrict (v : AbsoluteValue R S) (h : (v.restrict F).IsNontrivial) :
    v.IsNontrivial := by
  obtain ⟨x, hx₀, hx₁⟩ := h
  exact ⟨algebraMap F R x, (map_ne_zero _).mpr hx₀, hx₁⟩

/-- Two equivalent extensions from `F` to `R` of the same nontrivial absolute value
must be equal. -/
lemma eq_of_equivalent_and_restrict_eq {v₁ v₂ : AbsoluteValue R ℝ} (h₁ : v₁ ≈ v₂)
    (h₂ : v₁.restrict F = v₂.restrict F) (h₃ : (v₁.restrict F).IsNontrivial) :
    v₁ = v₂ := by
  obtain ⟨c, hc₀, hc₁⟩ := h₁
  obtain ⟨x, hx⟩ := h₃.exists_abv_gt_one
  suffices c = 1 by simpa [this] using hc₁
  have H : v₁ (algebraMap F R x) = v₂ (algebraMap F R x) := by
    simp only [apply_algebraMap, h₂]
  rw [← congrFun hc₁, apply_algebraMap, eq_comm] at H
  nth_rewrite 2 [← Real.rpow_one (v₁.restrict F x)] at H
  exact (Real.rpow_right_inj (zero_lt_one.trans hx) hx.ne').mp H

/-- The extension of the trivial absolute value on a field `F` to a finite-dimensional `F`-algebra
that is a division ring is trivial. -/
lemma trivial_of_finiteDimensional_of_restrict {R : Type*} [DivisionRing R] [Nontrivial R]
    [Algebra F R] [FiniteDimensional F R] {v : AbsoluteValue F ℝ} {v' : AbsoluteValue R ℝ}
    (h : v'.restrict F = v) (hv : ¬ v.IsNontrivial) :
    ¬ v'.IsNontrivial := by
  rw [not_isNontrivial_iff] at hv ⊢
  suffices key : ∀ {x} (hx : x ≠ 0), v' x ≤ 1 by
    intro x hx
    refine le_antisymm (key hx) ?_
    rw [← inv_inv x, map_inv₀, one_le_inv₀ <| v'.pos <| inv_ne_zero hx]
    exact key <| inv_ne_zero hx
  intro x hx₀
  by_contra! hx
  let n := Module.finrank F R
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n < v' (x ^ m) := by
    simpa only [v'.map_pow] using pow_unbounded_of_one_lt _ hx
  contrapose! hm; clear hm
  have hxm : x ^ m ≠ 0 := pow_ne_zero m hx₀
  -- write `x ^ m` as a linear combination of `≤ n` terms `c • (x ^ m) ^ (-i)` with `i ≥ 0`
  let p := (LinearMap.mulLeft F (x ^ m)).charpoly
  have hp₁ : p.Monic := LinearMap.charpoly_monic _
  have hpn : p.natDegree = n := LinearMap.charpoly_natDegree _
  have H : p.aeval (x ^ m) = 0 := Algebra.charpoly_aeval_self_eq_zero _
  rw [← p.eraseLead_add_C_mul_X_pow, Polynomial.aeval_add, Polynomial.aeval_eq_sum_range,
    add_eq_zero_iff_eq_neg', hp₁.leadingCoeff, map_one, one_mul, map_pow, Polynomial.aeval_X] at H
  apply_fun (· * (x ^ m) ^ (-n + 1 : ℤ)) at H
  rw [hpn, ← zpow_natCast, ← zpow_add' (.inl hxm), add_neg_cancel_left, zpow_one, neg_mul,
    Finset.sum_mul] at H
  conv at H => enter [2, 1, 2, i]; rw [smul_mul_assoc, ← zpow_natCast, ← zpow_add' (.inl hxm)]
  rw [H, v'.map_neg]; clear H
  have pel : p.eraseLead.natDegree + 1 ≤ n := LinearMap.charpoly_eraseLead_natDegree_le _
  have pel' : (p.eraseLead.natDegree + 1 : ℝ) ≤ n := mod_cast pel
  have help (N : ℕ) : (N + 1 : ℝ) = ∑ i ∈ Finset.range (N + 1), 1 := by simp
  refine (v'.sum_le ..).trans (LE.le.trans ?_ pel')
  conv_rhs => rw [help]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  rw [Algebra.smul_def, v'.map_mul, apply_algebraMap, h]
  rcases eq_or_ne (p.eraseLead.coeff i) 0 with H | H
  · simp [H]
  · simp only [ne_eq, H, not_false_eq_true, hv, map_zpow₀, v'.map_pow, one_mul]
    simp only [Finset.mem_range] at hi
    exact zpow_le_one_of_nonpos₀ (one_le_pow₀ hx.le) <| by omega

variable {F' : Type*} [Ring F'] [Algebra F F'] {v : AbsoluteValue F ℝ}

@[simp]
lemma equiv_symm_apply_algebraMap (v' : AbsoluteValue F' ℝ) (x : WithAbs v) :
    (WithAbs.equiv v').symm (algebraMap F F' (WithAbs.equiv v x)) =
      algebraMap (WithAbs v) (WithAbs v') x :=
  rfl

variable [Nontrivial F']

open WithAbs

@[simp]
lemma apply_algebraMap_withAbs {v' : AbsoluteValue F' ℝ} (h : v'.restrict F = v) (x : WithAbs v) :
    v' (WithAbs.equiv v' (algebraMap (WithAbs v) (WithAbs v') x)) = v (WithAbs.equiv v x) := by
  rw [← h, ← equiv_symm_apply_algebraMap, RingEquiv.apply_symm_apply, apply_algebraMap]

@[fun_prop]
lemma continuous_algebraMap {v' : AbsoluteValue F' ℝ} (h : v'.restrict F = v) :
    Continuous <| algebraMap (WithAbs v) (WithAbs v') := by
  rw [continuous_iff_continuous_dist]
  conv => enter [1, x]; simp only [← equiv_symm_apply_algebraMap v']
  simp_rw [dist_eq_norm_sub, norm_eq_abv, map_sub, RingEquiv.apply_symm_apply, ← map_sub,
    apply_algebraMap, h, ← norm_eq_abv, ← dist_eq_norm_sub]
  exact continuous_dist

instance continuousSMul {v' : AbsoluteValue F' ℝ} [Fact <| v'.restrict F = v] :
    ContinuousSMul (WithAbs v) (WithAbs v') where
  continuous_smul := (continuous_algebraMap_iff_smul _ _).mp <| continuous_algebraMap Fact.out

lemma isNonarchmedean_restrict_iff {F' : Type*} [Field F'] [Algebra F F']
    {v : AbsoluteValue F' ℝ} :
    IsNonarchimedean (v.restrict F) ↔ IsNonarchimedean v := by
  have H (n : ℕ) : v.restrict F n = v n := by
    rw [← apply_algebraMap]
    congr
    exact algebraMap.coe_natCast n
  simp_rw [isNonarchimedean_iff_le_one_on_nat, H]

lemma eq_of_isEquiv_of_eq_restrict {v₁ v₂ : AbsoluteValue F' ℝ} (h : v₁ ≈ v₂)
    (h' : v₁.restrict F = v₂.restrict F) (h'' : (v₁.restrict F).IsNontrivial) :
    v₁ = v₂ := by
  obtain ⟨c, hc₁, hc₂⟩ := h
  suffices c = 1 by simpa [this] using hc₂
  obtain ⟨x, hx⟩ := h''.exists_abv_gt_one
  have hx' : v₂ (algebraMap F F' x) = v₁.restrict F x := by rw [apply_algebraMap, h']
  apply_fun (· (algebraMap F F' x)) at hc₂
  simp only [apply_algebraMap, hx'] at hc₂
  nth_rewrite 2 [← Real.rpow_one (v₁.restrict F x)] at hc₂
  rwa [Real.rpow_right_inj (zero_lt_one.trans hx) hx.ne'] at hc₂

end AbsoluteValue

end restrict

section complete

namespace AbsoluteValue
/-!
### The complete case

If `F` is complete with respect to an absolute value `v` and `F'/F` is a finite extension,
then there is a unique extension of `v` to an absolute value `v'` on `F'`, and `F'`
is complete with respect to `v'`.
-/

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
variable (v : AbsoluteValue F ℝ) [CompleteSpace (WithAbs v)]

/- lemma _root_.WithAbs.complete [CompleteSpace (WithAbs v)] [FiniteDimensional F F']
    [Fact v.IsNontrivial] (v' : AbsoluteValue F' ℝ) [Fact <| v'.restrict F = v] :
    CompleteSpace (WithAbs v') :=
  FiniteDimensional.complete (WithAbs v) (WithAbs v') -/

variable {v} in
private lemma isEquiv_of_restrict_eq {v₁ v₂ : AbsoluteValue F' ℝ} (h : v.IsNontrivial)
    (h₁ : v₁.restrict F = v) (h₂ : v₂.restrict F = v) :
    v₁ ≈ v₂ := by
  rw [equiv_iff_isHomeomorph]
  let e : WithAbs v₁ ≃ₗ[WithAbs v] WithAbs v₂ := {
    toFun := WithAbs.equiv₂ v₁ v₂
    map_add' x y := rfl
    map_smul' c x := rfl
    invFun := WithAbs.equiv₂ v₂ v₁
    left_inv x := rfl
    right_inv x := rfl
  }
  have : Fact v.IsNontrivial := ⟨h⟩
  have : Fact <| v₁.restrict F = v := ⟨h₁⟩
  have : Fact <| v₂.restrict F = v := ⟨h₂⟩
  exact isHomeomorph_iff_exists_homeomorph.mpr ⟨FiniteDimensional.homeomorph_of_linearEquiv e, rfl⟩

-- Lemma 6.1, "at most one"
private lemma lemma_6_1_a : Subsingleton ({ v' : AbsoluteValue F' ℝ // v'.restrict F = v }) := by
  refine subsingleton_iff.mpr fun v₁ v₂ ↦ ?_
  by_cases hv : v.IsNontrivial
  · have hr : v₁.val.restrict F = v₂.val.restrict F := by rw [v₁.prop, v₂.prop]
    ext1
    refine eq_of_equivalent_and_restrict_eq ?_ hr (by rwa [v₁.prop])
    exact isEquiv_of_restrict_eq hv v₁.prop v₂.prop
  · have hv₁ := trivial_of_finiteDimensional_of_restrict v₁.prop hv
    have hv₂ := trivial_of_finiteDimensional_of_restrict v₂.prop hv
    ext1
    exact eq_of_not_isNontrivial hv₁ hv₂



section GelfandMazur

/-!
### A version of the Gelfand-Mazur Theorem

We show that a complete field with real-valued archimedean absolute value must be
isomorphic either to `ℝ` or to `ℂ` with a power of its usual absolute value.
-/

section

variable {F : Type*} [Field F] {v₁ v₂ : AbsoluteValue F ℝ}

/-- The absolute value extending `v` on the completion of `F` with respect to `v`. -/
noncomputable
def Completion.absoluteValue (v : AbsoluteValue F ℝ) : AbsoluteValue v.Completion ℝ :=
  NormedField.toAbsoluteValue v.Completion

lemma Completion.absoluteValue_eq_norm (v : AbsoluteValue F ℝ) (x : v.Completion) :
    absoluteValue v x = ‖x‖ := rfl

noncomputable
instance Completion.instAlgebra (v : AbsoluteValue F ℝ) : Algebra (WithAbs v) v.Completion :=
  UniformSpace.Completion.algebra' _

noncomputable
instance Completion.instAlgebra' (v : AbsoluteValue F ℝ) : Algebra F v.Completion :=
  Completion.instAlgebra v

@[simp]
lemma Completion.absoluteValue_restrict (v : AbsoluteValue F ℝ) :
    (absoluteValue v).restrict F = v := by
  ext1 x
  rw [restrict, comp_apply, absoluteValue_eq_norm, show (algebraMap F v.Completion) x = x from rfl,
    UniformSpace.Completion.norm_coe]
  rfl

end


open Completion Rat.AbsoluteValue WithAbs in
/-- If `v` is an absolute value on `ℝ` such that `(ℝ, v)` is complete and the restriction of `v`
to `ℚ` is equivalent to the standard archimedean absolute value, then `v` is equivalent to
the standard absolute value of `ℝ`. -/
lemma Real.isEquiv_abs_of_restrict {v : AbsoluteValue ℝ ℝ} [CompleteSpace (WithAbs v)]
    (h : v.restrict ℚ ≈ real) :
    v ≈ .abs := by
  -- Get chain `ℝ ≃ real.Completion ≃ (v.restrict ℚ).Completion → (ℝ,v)`
  -- of equivalences / maps of normed rings (`e₂⁻¹`, `e₁⁻¹`, `e₃` below).
  -- Then the composition is a ring homomorphism `ℝ →+* ℝ` and therefore the identity.
  -- So the last homomorphism is an isomorphism as well, and everything is a homeomorphism.
  let e₁ : (restrict ℚ v).Completion ≃+* real.Completion := ringEquiv_completion_of_isEquiv h
  have He₁ : IsHomeomorph e₁ := isHomeomorph_ringEquiv_completion h
  let e₂ : real.Completion ≃+* ℝ := ringEquiv_completion_real
  have He₂ : IsHomeomorph e₂ := isHomeomorph_ringEquiv_completion_real
  let e₃ : (v.restrict ℚ).Completion →+* WithAbs v :=
    extensionEmbedding_of_comp (f := (Rat.castHom _).comp (equiv (v.restrict ℚ))) fun _ ↦ rfl
  let e : ℝ →+* WithAbs v := e₃.comp (e₂.symm.trans e₁.symm).toRingHom
  let e₀ : ℝ →+* ℝ := (equiv v).toRingHom.comp e
  have he₀ : e₀ = RingHom.id ℝ := Subsingleton.elim ..
  have he₀' : Function.Bijective e₀ := by
    simpa only [he₀, RingHom.coe_id] using Function.bijective_id
  have He₃ : IsHomeomorph e₃ :=
    (isometry_extensionEmbedding_of_comp fun _ ↦ rfl).isHomeomorph_ofBijective <|
      e₃.bijective_of_bijective_comp he₀'
  have He : IsHomeomorph e := by
    simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_ringHom_trans, RingHom.coe_comp,
      RingHom.coe_coe]
    exact He₃.comp <| (He₁.right_inv e₁.apply_symm_apply).comp (He₂.right_inv e₂.apply_symm_apply)
  let e₄ : WithAbs .abs ≃+* ℝ := equiv .abs
  have He₄ : IsHomeomorph e₄ :=
    ((AddMonoidHomClass.isometry_iff_norm e₄).mpr (congrFun rfl)).isHomeomorph_ofEquiv
  symm
  -- Use that two absoloute values are equivalent iff the identity map
  -- between the two topological spaces is a homeomorphism.
  refine (equiv_iff_isHomeomorph .abs v).mpr ?_
  have he : e = (equiv v).symm := by
    suffices e = (equiv v).symm.toRingHom.comp e₀ by
      simpa only [he₀, RingEquiv.toRingHom_eq_coe, RingHomCompTriple.comp_eq] using this
    ext1 x
    simpa [e₀] using (RingEquiv.symm_apply_apply (equiv v) (e x)).symm
  have H : ⇑(equiv₂ .abs v) = e.comp e₄.toRingHom := by simp [equiv₂, he, e₄]
  simpa only [H, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe] using He.comp He₄

open Rat.AbsoluteValue in
/-- If `v` is an absolute value on `ℝ` such that `(ℝ, v)` is complete and the restriction of `v`
to `ℚ` is equal to the standard archimedean absolute value,
then `v` is the standard absolute value of `ℝ`. -/
lemma Real.eq_abs_of_restrict_eq_ratReal {v : AbsoluteValue ℝ ℝ} [CompleteSpace (WithAbs v)]
    (h : v.restrict ℚ = real) :
    v = .abs := by
  have h' : v.restrict ℚ ≈ real := by rw [h]
  refine eq_of_isEquiv_of_eq_restrict (isEquiv_abs_of_restrict h') h ?_
  rw [h]
  exact ⟨2, two_ne_zero, by simp⟩

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ} [CompleteSpace (WithAbs v)]

/-- A field `F` that is complete w.r.t. an archimedean absolute value is an `ℝ`-algebra. -/
lemma algebra_of_archimedean (h : ¬ IsNonarchimedean v) :
    ∃ e : ℝ →+* F, letI : Algebra ℝ F := e.toAlgebra; v.restrict ℝ ≈ .abs := by
  have : CharZero F := charZero_of_archimedean h
  have : CharZero (WithAbs v) := charZero_of_archimedean h
  let e₀ := Rat.castHom (WithAbs v)
  let _ : Algebra ℚ (WithAbs v) := e₀.toAlgebra
  let v₀ := v.restrict ℚ
  have hv₀ : ¬ IsNonarchimedean v₀ := mt isNonarchmedean_restrict_iff.mp h
  replace hv₀ : v₀ ≈ Rat.AbsoluteValue.real := Rat.AbsoluteValue.real_of_archimedean hv₀
  let e₁ : v₀.Completion →+* WithAbs v :=
    Completion.extensionEmbedding_of_comp (f := e₀) fun _ ↦ rfl
  let e₂ := ringEquiv_completion_of_isEquiv hv₀
  let e₃ := Rat.AbsoluteValue.ringEquiv_completion_real
  refine ⟨e₁.comp (e₃.symm.trans e₂.symm).toRingHom, ?_⟩

  sorry


theorem equiv_R_or_C_of_complete_archimedean (h : ¬ IsNonarchimedean v) :
    (∃ e : ℝ ≃+* F, letI : Algebra ℝ F := RingHom.toAlgebra e; v.restrict ℝ ≈ .abs)
      ∨ ∃ e : ℂ ≃+* F, letI : Algebra ℂ F := RingHom.toAlgebra e;
        v.restrict ℂ ≈ NormedField.toAbsoluteValue ℂ := by
  obtain ⟨e, he⟩ := algebra_of_archimedean h
  let inst := e.toAlgebra

  stop
  by_cases H : Nonempty (ℂ →+* F)
  · obtain ⟨f⟩ := H
    let instA : Algebra ℂ F := f.toAlgebra
    let inst : NormedAlgebra ℂ (WithAbs v) := by
      refine NormedAlgebra.mk fun r x ↦ ?_

    sorry
  · sorry

-- #check NormedRing.algEquivComplexOfComplete
-- #check NormedAlgebra

end GelfandMazur

end AbsoluteValue

end complete
