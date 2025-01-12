import Heights.Auxiliary

/-!
# Two absolute values are equivalent iff they induce the same topology

This is Theorem 1.1 in Conrad's notes. We split the interesting direction (same topology
implies equivalence) into two steps:

* `AbsoluteValue.abv_lt_one_iff_of_isHomeomorph`: if `v₁` and `v₂` induce the same
  topology, then `{x | v₁ x < 1} = {x | v₂ x < 1}`.

* `AbsoluteValue.equiv_of_abv_lt_one_iff`: if `{x | v₁ x < 1} = {x | v₂ x < 1}`,
  then `v₁ ≈ v₂`.

The main result is `AbsoluteValue.equiv_iff_isHomeomorph`.
-/

namespace AbsoluteValue

/-!
### More API for AboluteValue.IsEquiv
-/

section isEquiv

variable {R : Type*} [Semiring R]

lemma rpow_add_le (v : AbsoluteValue R ℝ) {e : ℝ} (h₀ : 0 < e) (h₁ : e ≤ 1) (x y : R) :
    v (x + y) ^ e ≤ v x ^ e + v y ^ e := by
  calc
  _ ≤ (v x + v y) ^ e := Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) h₀.le
  _ ≤ v x ^ e + v y ^ e := Real.rpow_add_le_add_rpow (v.nonneg _) (v.nonneg _) h₀.le h₁

noncomputable
def rpow (v : AbsoluteValue R ℝ) {e : ℝ} (h₀ : 0 < e) (h₁ : e ≤ 1) : AbsoluteValue R ℝ where
  toFun := (v ·) ^ e
  map_mul' x y := by simp only [Pi.pow_apply, v.map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _)]
  nonneg' x := by simpa only [Pi.pow_apply] using Real.rpow_nonneg (v.nonneg _) _
  eq_zero' x := by simp [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg _), v.eq_zero, h₀.ne']
  add_le' x y := by simpa only [Pi.pow_apply] using rpow_add_le v h₀ h₁ x y

end isEquiv

/-!
### Auxiliary lemmas
-/

section restrict

variable {F R S : Type*} [Field F] [Semiring R] [Nontrivial R] [Algebra F R] [OrderedSemiring S]

variable (F) in
/-- The restriction to a field `F` of an absolute value on an `F`-algebra `R`. -/
def restrict (v : AbsoluteValue R S) : AbsoluteValue F S :=
  v.comp (RingHom.injective (algebraMap F R))

@[simp]
lemma apply_algebraMap (v : AbsoluteValue R S) (x : F) :
    v (algebraMap F R x) = v.restrict F x := rfl

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
      algebraMap (WithAbs v) (WithAbs v') x := by
  rw [← WithAbs.equiv_apply_algebraMap v', Equiv.symm_apply_apply]

variable [Nontrivial F']

open WithAbs

@[simp]
lemma apply_algebraMap_withAbs {v' : AbsoluteValue F' ℝ} (h : v'.restrict F = v) (x : WithAbs v) :
    v' (WithAbs.equiv v' (algebraMap (WithAbs v) (WithAbs v') x)) = v (WithAbs.equiv v x) := by
  rw [WithAbs.equiv_apply_algebraMap, apply_algebraMap, h]

@[fun_prop]
lemma continuous_algebraMap {v' : AbsoluteValue F' ℝ} (h : v'.restrict F = v) :
    Continuous <| algebraMap (WithAbs v) (WithAbs v') := by
  rw [continuous_iff_continuous_dist]
  conv => enter [1, x]; simp only [← equiv_symm_apply_algebraMap v']
  simp_rw [dist_eq_norm_sub, norm_eq_abv, WithAbs.equiv_sub, Equiv.apply_symm_apply, ← map_sub,
    apply_algebraMap, h, ← WithAbs.equiv_sub, ← norm_eq_abv, ← dist_eq_norm_sub]
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

end restrict

/-!
### Two absolute values are equivalent iff they induce the same topology

This is Theorem 1.1 in Conrad's notes.

The main result is `AbsoluteValue.equiv_iff_isHomeomorph`.
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
    simp only [dist_zero_right, norm_eq_abv, WithAbs.equiv_pow, Equiv.apply_symm_apply] at H
    obtain ⟨n, hn⟩ := H 1 zero_lt_one
    replace hn := hn n le_rfl
    rw [map_pow] at hn
    refine (pow_lt_one_iff_of_nonneg (v.nonneg x) ?_).mp hn
    rintro rfl
    simp at hn
  · refine tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_
    rwa [norm_eq_abv, Equiv.apply_symm_apply]

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
instance _root_.WihAbs.nontriviallynormedField {v : AbsoluteValue F ℝ} [Fact <| v.IsNontrivial] :
    NontriviallyNormedField (WithAbs v) :=
  (Fact.out : v.IsNontrivial).nontriviallyNormedField

end withAbs

section equiv_trivial

variable {R : Type*} [Ring R]

lemma equiv_iff_eq_of_not_isNontrivial {v₁ v₂ : AbsoluteValue R ℝ} (h : ¬ v₁.IsNontrivial) :
    v₁ ≈ v₂ ↔ v₁ = v₂ := by
  refine ⟨fun ⟨c, hc₀, hc₁⟩ ↦ ?_, fun H ↦ H ▸ equiv_refl v₂⟩
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

/-- The identity map of `F` as a map between normed field structures on `F` induced by two
absolute values- -/
abbrev _root_.WithAbs.equiv₂ (v₁ v₂ : AbsoluteValue F ℝ) : WithAbs v₁ ≃ WithAbs v₂ :=
  (WithAbs.equiv v₁).trans (WithAbs.equiv v₂).symm

private lemma continuous_withAbs_equiv₂ {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) :
    Continuous (WithAbs.equiv₂ v₁ v₂) := by
  obtain ⟨c, hc₀, hc₁⟩ := h
  rw [Metric.continuous_iff]
  simp only [dist_eq_norm_sub, norm_eq_abv, WithAbs.equiv₂, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  intro x ε hε₀
  conv => enter [1, δ, 2, y, 2, 1]; rw [← WithAbs.equiv_symm_sub, ← WithAbs.equiv_sub]
  refine ⟨ε ^ (1 / c), Real.rpow_pos_of_pos hε₀ _, fun y h ↦ ?_⟩
  let x' := WithAbs.equiv v₁ x
  let y' := WithAbs.equiv v₁ y
  have hx : x = (WithAbs.equiv v₁).symm x' := rfl
  have hy : y = (WithAbs.equiv v₁).symm y' := rfl
  rw [hx, hy, ← WithAbs.equiv_symm_sub, Equiv.apply_symm_apply] at h
  rw [Equiv.apply_symm_apply, WithAbs.equiv_sub, hx, hy]
  simp only [Equiv.apply_symm_apply, ← hc₁]
  calc v₁ (y' - x') ^ c
  _ < (ε ^ (1 / c)) ^ c := by gcongr
  _ = ε := by rw [← Real.rpow_mul hε₀.le, one_div_mul_cancel hc₀.ne', Real.rpow_one]

/-- Two equivalent absolute values on a field `F` induce the same topology.
This defines the identity map `F → F` as a homeomorphism between the two topologies. -/
def homeomorph_of_equiv {v₁ v₂ : AbsoluteValue F ℝ} (h : v₁ ≈ v₂) : WithAbs v₁ ≃ₜ WithAbs v₂ where
  toFun := (WithAbs.equiv v₂).symm ∘ WithAbs.equiv v₁
  invFun := (WithAbs.equiv v₁).symm ∘ WithAbs.equiv v₂
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_withAbs_equiv₂ h
  continuous_invFun := continuous_withAbs_equiv₂ (Setoid.symm h)

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
  apply_fun (fun f ↦ (φ.symm ∘ f) ∘ (WithAbs.equiv v₁).symm ∘ WithAbs.equiv v₂) at hφ
  simp only [Homeomorph.symm_comp_self, CompTriple.comp_eq] at hφ
  rw [Equiv.coe_trans, hφ]
  ext1 x
  simp

open Real in
/-- If the sets of elements of absolute value less than one agree for two absolute values
on a field `F`, then the two absolute values are equivalent. -/
lemma equiv_of_abv_lt_one_iff {v₁ v₂ : AbsoluteValue F ℝ} (h : ∀ x, v₁ x < 1 ↔ v₂ x < 1) :
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
lemma equiv_iff_isHomeomorph (v₁ v₂ : AbsoluteValue F ℝ) :
    v₁ ≈ v₂ ↔ IsHomeomorph (WithAbs.equiv₂ v₁ v₂) := by
  refine ⟨fun H ↦ ?_, fun H ↦ equiv_of_abv_lt_one_iff <| abv_lt_one_iff_of_isHomeomorph H⟩
  exact isHomeomorph_iff_exists_homeomorph.mpr
    ⟨homeomorph_of_equiv H, by simp [homeomorph_of_equiv]⟩
end equiv
