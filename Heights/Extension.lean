import Heights.Equivalence
import Mathlib.Analysis.Normed.Algebra.GelfandMazur

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

lemma Finset.sum_range_two_mul (n : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k ∈ range (2 * n), f k =
      ∑ k ∈ range n, f (2 * k) + ∑ k ∈ range n, f (2 * k + 1) := by
  rw [← sum_filter_add_sum_filter_not _ Even]
  congr 1
  · refine sum_bij' (fun k _ ↦ k / 2) (fun k _ ↦ 2 * k) (fun k hk ↦ ?_)
      (fun k hk ↦ ?_ ) (fun k hk ↦ ?_) (fun k hk ↦ ?_) (fun k hk ↦ ?_) <;>
      simp only [mem_filter, mem_range] at hk ⊢
    · omega
    · simp only [Nat.ofNat_pos, mul_lt_mul_iff_right₀, even_two, Even.mul_right, and_true] at hk ⊢
      omega
    · exact Nat.two_mul_div_two_of_even hk.2
    · omega
    · rw [Nat.two_mul_div_two_of_even hk.2]
  · refine sum_bij' (fun k _ ↦ k / 2) (fun k _ ↦ 2 * k + 1) (fun k hk ↦ ?_)
      (fun k hk ↦ ?_ ) (fun k hk ↦ ?_) (fun k hk ↦ ?_) (fun k hk ↦ ?_) <;>
      simp only [mem_filter, mem_range, Nat.not_even_iff_odd] at hk ⊢
    · omega
    · simp only [odd_two_mul_add_one, and_true]
      omega
    · exact Nat.two_mul_div_two_add_one_of_odd hk.2
    · omega
    · rw [Nat.two_mul_div_two_add_one_of_odd hk.2]

lemma Complex.cpow_inv_ofReal_mul_ofReal (z : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    (z ^ (x⁻¹ : ℂ)) ^ (x : ℂ) = z := by
  rw [← cpow_mul, inv_mul_cancel₀ (by norm_cast; linarith), cpow_one]
  -- side goals
  · rw [← ofReal_inv, im_mul_ofReal, ← div_eq_mul_inv, lt_div_iff₀ (by linarith)]
    calc
    _ ≤ -Real.pi := mul_le_of_one_le_right (neg_nonpos.mpr Real.pi_nonneg) hx
    _ < (log z).im := neg_pi_lt_log_im z
  · rw [← ofReal_inv, im_mul_ofReal, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    calc
    _ ≤ Real.pi := log_im_le_pi z
    _ ≤ Real.pi * x := by refine le_mul_of_one_le_right Real.pi_nonneg hx

lemma IsPrimitiveRoot.map_nthRootsFinset {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {x : F} (hx : x ∈ Polynomial.nthRootsFinset n 1) :
    ∃ y ∈ Polynomial.nthRootsFinset n (1 : K), algebraMap K F y = x := by
  let ξ := algebraMap K F ζ
  have hξ : IsPrimitiveRoot ξ n := hζ.map_of_injective <| FaithfulSMul.algebraMap_injective ..
  rw [Polynomial.mem_nthRootsFinset (NeZero.pos n)] at hx
  obtain ⟨k, _, hk⟩ := hξ.eq_pow_of_pow_eq_one hx
  refine ⟨ζ ^ k, ?_, hk ▸ algebraMap.coe_pow ζ k⟩
  rw [Polynomial.mem_nthRootsFinset (NeZero.pos n), pow_right_comm, hζ.pow_eq_one, one_pow]

open Topology Filter in
lemma Real.tendsto_mul_pow_div_one_sub_pow {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    Tendsto (fun n : ℕ ↦ n * x ^ n / (1 - x ^ n)) atTop (𝓝 0) := by
  conv => enter [1, n]; rw [div_eq_mul_inv]
  conv => enter [3, 1]; rw [show (0 : ℝ) = 0 * (1 - 0)⁻¹ by simp]
  exact (tendsto_self_mul_const_pow_of_lt_one hx₀ hx₁).mul <|
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hx₀ hx₁).const_sub 1).inv₀ (by simp)

open Topology Filter in
lemma Real.tendsto_two_pow_mul_pow_div_one_sub_pow {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    Tendsto (fun n : ℕ ↦ 2 ^ n * x ^ 2 ^ n / (1 - x ^ 2 ^ n)) atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ ↦ 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  convert (tendsto_mul_pow_div_one_sub_pow hx₀ hx₁).comp this with n
  simp

/- lemma norm_natCast_le {E : Type*} [SeminormedRing E] [NormOneClass E] (n : ℕ) :
    ‖(n : E)‖ ≤ n := by
  induction n with
  | zero => simp [norm_zero]
  | succ n ih =>
    push_cast
    refine (norm_add_le ..).trans ?_
    rw [norm_one]
    exact add_le_add_right ih 1 -/

section restrict

namespace AbsoluteValue

section

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S]

lemma comp_apply {R' : Type*} [Semiring R'] (v : AbsoluteValue R S) {f : R' →+* R}
    (hf : Function.Injective f) (x : R') :
  v.comp hf x = v (f x) := rfl

variable {F : Type*} [Field F] [Nontrivial R]

/-- The pull-back of an absolute value on a (semi)ring `R` to a field `F`
via a ring homomorphism `F →+* R`. -/
def comap (v : AbsoluteValue R S) (f : F →+* R) : AbsoluteValue F S :=
  v.comp (RingHom.injective f)


lemma comap_comp {F' : Type*} [Field F'] (v : AbsoluteValue R S) (f : F →+* F') (g : F' →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f := by
  ext1
  simp [comap, comp_apply]

@[simp]
lemma comap_apply (v : AbsoluteValue R S) (f : F →+* R) (x : F) :
    v.comap f x = v (f x) := rfl

@[simp]
lemma comap_equiv_comp (v : AbsoluteValue R S) (f : F →+* R) :
    v.comap ((WithAbs.equiv v).toRingHom.comp f) = v.comap f :=
  rfl

open WithAbs in
lemma isometry_comap {F' : Type*} [Field F'] (v : AbsoluteValue F' ℝ) (f : F →+* F') :
    Isometry ((equiv v).symm.toRingHom.comp (f.comp (equiv (v.comap f)).toRingHom)) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  simp [WithAbs.norm_eq_abv]

lemma isNontrivial_of_comap (v : AbsoluteValue R S) (f : F →+* R) (h : (v.comap f).IsNontrivial) :
    v.IsNontrivial := by
  obtain ⟨x, hx₀, hx₁⟩ := h
  exact ⟨f x, (map_ne_zero _).mpr hx₀, hx₁⟩

lemma isEquiv_comap {v v' : AbsoluteValue R ℝ} (f : F →+* R) (h : v ≈ v') :
    v.comap f ≈ v'.comap f := by
  simpa [comap, comp, isEquiv_def', IsEquiv] using fun x y ↦ h (f x) (f y)

/-- Two equivalent extensions from `F` to `R` of the same nontrivial absolute value
must be equal. -/
lemma eq_of_isEquiv_of_comap_eq {R : Type*} [Field R] {v₁ v₂ : AbsoluteValue R ℝ} (h₁ : v₁ ≈ v₂)
    (f : F →+* R) (h₂ : v₁.comap f = v₂.comap f) (h₃ : (v₁.comap f).IsNontrivial) :
    v₁ = v₂ := by
  obtain ⟨c, hc₀, hc₁⟩ := isEquiv_iff_exists_rpow_eq.mp h₁
  obtain ⟨x, hx⟩ := h₃.exists_abv_gt_one
  suffices c = 1 by simpa [this] using hc₁
  have H : v₁ (f x) = v₂ (f x) := by
    simp only [← comap_apply, h₂]
  rw [← congrFun hc₁, ← comap_apply, eq_comm] at H
  nth_rewrite 2 [← Real.rpow_one (v₁.comap f x)] at H
  exact (Real.rpow_right_inj (zero_lt_one.trans hx) hx.ne').mp H

end

section

variable {F R : Type*} [Field F] [Field R] {v : AbsoluteValue F ℝ} {v' : AbsoluteValue R ℝ}
  (f : F →+* R) (h : v'.comap f ≈ v)

private
lemma ofIsEquivComap_map_mul' (x y : R) :
    letI c := IsEquiv.exponent h
    v' (x * y) ^ c = v' x ^ c * v' y ^ c := by
  rw [v'.map_mul, Real.mul_rpow (v'.nonneg x) (v'.nonneg y)]

private
lemma ofIsEquivComap_nonneg' (x : R) :
    letI c := IsEquiv.exponent h
    0 ≤ v' x ^ c :=
  Real.rpow_nonneg (v'.nonneg x) _

private
lemma ofIsEquivComap_eq_zero' (x : R) :
    letI c := IsEquiv.exponent h
    v' x ^ c = 0 ↔ x = 0 := by
  simp [Real.rpow_eq_zero_iff_of_nonneg (v'.nonneg x), v'.eq_zero, (IsEquiv.exponent_pos <| h).ne']

/-- If an absolute value `v` on `F` is equivalent to the pull-back
of an absolute value `v'` on `R`, then we can construct an absolute value on `R`
whose pull-back to `F` is `v`. -/
noncomputable
def ofIsEquivComap : AbsoluteValue R ℝ where
      toFun x := v' x ^ IsEquiv.exponent h
      map_mul' := ofIsEquivComap_map_mul' f h
      nonneg' := ofIsEquivComap_nonneg' f h
      eq_zero' := ofIsEquivComap_eq_zero' f h
      add_le' x y := by
        set c := IsEquiv.exponent h with hc
        have hc₁ : 0 < c := IsEquiv.exponent_pos h
        by_cases hna : IsNonarchimedean v'
        · let v'' := rpow_of_isNonarchimedean hna hc₁
          have H (x : R) : v' x ^ c = v'' x := by simp [v'', c]
          simp only [H, v''.add_le]
        · refine add_le_add_of_add_le_two_mul_max (ofIsEquivComap_map_mul' f h)
            (ofIsEquivComap_nonneg' f h) (ofIsEquivComap_eq_zero' f h) (fun x y ↦ ?_) x y
          have H₁ : v' 2 ^ c ≤ 2 := by
            have := IsEquiv.exponent_def h 2
            simp only [comap_apply, map_ofNat] at this
            rw [this]
            exact v.apply_nat_le_self 2
          have H₂ := Real.rpow_le_rpow (v'.nonneg _) (abv_add_le_abv_two_mul_max hna x y) hc₁.le
          rw [← hc] at *
          rw [Real.mul_rpow (v'.nonneg 2) (le_max_iff.mpr <| .inl (v'.nonneg x))] at H₂
          refine H₂.trans ?_
          gcongr
          exact ((Real.monotoneOn_rpow_Ici_of_exponent_nonneg hc₁.le).map_max
            (v'.nonneg x) (v'.nonneg y)).le

lemma ofIsEquivComap_def : (ofIsEquivComap f h).comap f = v := by
  ext1 x
  simpa [ofIsEquivComap] using IsEquiv.exponent_def h x

lemma ofIsEquivComap_isEquiv : ofIsEquivComap f h ≈ v' :=
  Setoid.symm <| isEquiv_def.mpr ⟨IsEquiv.exponent h, IsEquiv.exponent_pos h, rfl⟩

-- v.comap ((equiv v).toRingHom.comp ↑(e.trans (algEquiv₂ (ofIsEquivComap (algebraMap ℝ F) hv) v))) ≈
--   (ofIsEquivComap (algebraMap ℝ F) hv).comap ((equiv (ofIsEquivComap (algebraMap ℝ F) hv)).toRingHom.comp ↑e)


end

variable {F R S : Type*} [Field F] [Nontrivial R] [Semiring R] [Algebra F R] [Semiring S] [PartialOrder S]

variable (F) in
/-- The restriction to a field `F` of an absolute value on an `F`-algebra `R`. -/
def restrict (v : AbsoluteValue R S) : AbsoluteValue F S :=
  v.comap (algebraMap F R)

--@[simp] -- switch sides?
lemma apply_algebraMap (v : AbsoluteValue R S) (x : F) :
    v (algebraMap F R x) = v.restrict F x := rfl

lemma isNontrivial_of_restrict (v : AbsoluteValue R S) (h : (v.restrict F).IsNontrivial) :
    v.IsNontrivial :=
  isNontrivial_of_comap v (algebraMap F R) h

/-- Two equivalent extensions from `F` to `R` of the same nontrivial absolute value
must be equal. -/
lemma eq_of_isEquiv_of_restrict_eq {R : Type*} [Field R] [Algebra F R] {v₁ v₂ : AbsoluteValue R ℝ}
    (h₁ : v₁ ≈ v₂) (h₂ : v₁.restrict F = v₂.restrict F) (h₃ : (v₁.restrict F).IsNontrivial) :
    v₁ = v₂ :=
  eq_of_isEquiv_of_comap_eq h₁ (algebraMap F R) h₂ h₃

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

section complex_real

lemma Complex.abv_restrict_real : (NormedField.toAbsoluteValue ℂ).restrict ℝ = .abs := by
  ext1 x
  simp only [restrict, comap_apply, Complex.coe_algebraMap, abs_apply]
  change ‖(x : ℂ)‖ = |x|
  rw [Complex.norm_real, Real.norm_eq_abs]

end complex_real

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

lemma isNonarchmedean_comap_iff {F' : Type*} [Field F'] {v : AbsoluteValue F' ℝ} {f : F →+* F'} :
    IsNonarchimedean (v.comap f) ↔ IsNonarchimedean v := by
  have H (n : ℕ) : v.comap f n = v n := by
    rw [comap_apply, map_natCast f n]
  simp_rw [isNonarchimedean_iff_le_one_on_nat, H]

lemma isNonarchmedean_restrict_iff {F' : Type*} [Field F'] [Algebra F F']
    {v : AbsoluteValue F' ℝ} :
    IsNonarchimedean (v.restrict F) ↔ IsNonarchimedean v :=
  isNonarchmedean_comap_iff (f := algebraMap F F')

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

lemma isometry_equiv_realAbs : Isometry (WithAbs.equiv (R := ℝ) .abs) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr (congrFun rfl)

lemma isHomeomorph_equiv_realAbs : IsHomeomorph (WithAbs.equiv (R := ℝ) .abs) :=
  Isometry.isHomeomorph_ofEquiv isometry_equiv_realAbs

instance : CompleteSpace (WithAbs (R := ℝ) .abs) := by
  let f := (WithAbs.equiv (R := ℝ) .abs)
  have H₁ : IsHomeomorph f := isHomeomorph_equiv_realAbs
  have H₂ : IsHomeomorph f.symm := H₁ -- not sure why this works...
  refine (UniformEquiv.completeSpace_iff ?_).mp (inferInstance : CompleteSpace ℝ)
  refine UniformEquiv.mk f.symm ?_ ?_
  · exact uniformContinuous_of_continuousAt_zero f.symm.toRingHom H₂.continuous.continuousAt
  · exact uniformContinuous_of_continuousAt_zero f.toRingHom H₁.continuous.continuousAt

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
  rw [isEquiv_def', isEquiv_iff_isHomeomorph]
  let e : WithAbs v₁ ≃ₗ[WithAbs v] WithAbs v₂ := {
    toFun := WithAbs.equivWithAbs v₁ v₂
    map_add' x y := rfl
    map_smul' c x := rfl
    invFun := WithAbs.equivWithAbs v₂ v₁
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
    refine eq_of_isEquiv_of_restrict_eq ?_ hr (by rwa [v₁.prop])
    exact isEquiv_of_restrict_eq hv v₁.prop v₂.prop
  · have hv₁ := trivial_of_finiteDimensional_of_restrict v₁.prop hv
    have hv₂ := trivial_of_finiteDimensional_of_restrict v₂.prop hv
    ext1
    exact eq_of_not_isNontrivial hv₁ hv₂

end AbsoluteValue

section prelim

section

open AbsoluteValue

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
  rw [← apply_algebraMap, absoluteValue_eq_norm, show (algebraMap F v.Completion) x = x from rfl,
    UniformSpace.Completion.norm_coe]
  rfl

end


namespace AbsoluteValue

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ}

open WithAbs

lemma comap_eq_of_isometry {F' : Type*} [Field F'] {v' : AbsoluteValue F' ℝ}
    {f : WithAbs v →+* WithAbs v'} (h : Isometry f) :
    v'.comap ((equiv v').toRingHom.comp (f.comp (equiv v).symm.toRingHom)) = v := by
  ext1 x
  rw [comap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← norm_eq_abv, (AddMonoidHomClass.isometry_iff_norm _).mp h, norm_eq_abv]
  simp

lemma comap_completion_eq_of_isometry {F' : Type*} [Field F'] (v' : AbsoluteValue F' ℝ)
    {f : v.Completion →+* F'} (h : Isometry ((equiv v').symm.toRingHom.comp f)) :
    v'.comap f = Completion.absoluteValue v := by
  ext1 x
  rw [comap_apply]
  have := (AddMonoidHomClass.isometry_iff_norm _).mp h x
  simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    norm_eq_abv, RingEquiv.apply_symm_apply, ← Completion.absoluteValue_eq_norm] using this

lemma isometry_equiv_comap {F' : Type*} [Field F'] (f : F' ≃+* v.Completion) :
    Isometry ((equiv ((Completion.absoluteValue v).comap f)).trans f) := by
  have H : Isometry (equiv (Completion.absoluteValue v)) :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr (congrFun rfl)
  replace H := H.comp <| isometry_comap (Completion.absoluteValue v) f.toRingHom
  simpa only [RingEquiv.coe_trans, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
    RingHom.coe_coe] using H

lemma isHomeomorph_equiv_comap {F' : Type*} [Field F'] (f : F' ≃+* v.Completion) :
    IsHomeomorph ((equiv ((Completion.absoluteValue v).comap f)).trans f) :=
  (isometry_equiv_comap f).isHomeomorph_ofEquiv

variable [CompleteSpace (WithAbs v)]

open RingEquiv Rat.AbsoluteValue in
/-- A field `F` that is complete w.r.t. an archimedean absolute value is an `ℝ`-algebra
such that the pull-back of its absolute value to `ℝ` is equivalent to the standard
absolute value. -/
lemma algebra_of_archimedean (h : ¬ IsNonarchimedean v) :
    ∃ e : ℝ →+* F, v.comap e ≈ .abs := by
  -- We have the canonical ring homomorphism `e₀ : ℚ → F`.
  have : CharZero (WithAbs v) := charZero_of_archimedean h
  let e₀ := Rat.castHom (WithAbs v)
  -- We pull back `v` from `F` to `ℚ` to obtain `v₀`.
  let v₀ := v.comap e₀
  -- Then `v₀` is equivalent to the archimedean absolute value on `ℚ`.
  have hv₀ : v₀ ≈ real := real_of_archimedean <| mt isNonarchmedean_comap_iff.mp h
  -- By functoriality of the completion, we obtain a ring homomorphism and isometry
  -- `e₁ : v₀.Completion → F`.
  let e₁ : v₀.Completion →+* WithAbs v :=
    Completion.extensionEmbedding_of_comp (f := e₀) fun _ ↦ rfl
  have he₁ : Isometry e₁ := Completion.isometry_extensionEmbedding_of_comp fun _ ↦ rfl
  -- The pull-back ov `v` under `e₁` is the absolute value of the completion.
  have H₁ : v.comap e₁ = Completion.absoluteValue v₀ :=
    comap_completion_eq_of_isometry v he₁
  -- We can identify `v₀.Completion` with `ℝ` via a ring isomorphism and
  -- homeomorphism `e₄ : ℝ → v₀.Completion` (built in two steps).
  let e₂ := ringEquiv_completion_of_isEquiv hv₀
  let e₃ := ringEquiv_completion_real
  let e₄ := e₃.symm.trans e₂.symm
  have He₃ : IsHomeomorph e₃ := isHomeomorph_ringEquiv_completion_real
  have He₂ : IsHomeomorph e₂ := isHomeomorph_ringEquiv_completion hv₀
  have He₄ : IsHomeomorph e₄ := by
    simp only [coe_trans, e₄]
    exact He₂.ringEquiv_symm.comp He₃.ringEquiv_symm
  -- The pull-back of the absolute value of the completion to `ℝ` under `e₄`
  -- is equivalent to the standard absolute value.
  have H₂ : (Completion.absoluteValue v₀).comap e₄ ≈ .abs := by
    refine (isEquiv_iff_isHomeomorph _ .abs).mpr ?_
    simp only [equivWithAbs, coe_trans]
    refine isHomeomorph_equiv_realAbs.ringEquiv_symm.comp ?_
    convert He₄.ringEquiv_symm.comp <|isHomeomorph_equiv_comap e₄
    rw [coe_trans, ← Function.comp_assoc, ← coe_trans, self_trans_symm, coe_refl,
      Function.id_comp]
  -- Finally, we take `e = e₁ ∘ e₄` and reduce to the statement `H₂` above.
  exact ⟨e₁.comp e₄, by rwa [comap_comp, H₁]⟩

end AbsoluteValue

end prelim

section GelfandMazur

/-!
### A version of the Gelfand-Mazur Theorem

Let `F` be a field that is complete with respect to an archimedean absolute value `v`.
Then `F` is isomorphic, as a field with absolute value, to either `ℝ` or `ℂ` with
an absolute value that is equivalent to the standard absolute value.

One can fairly easily conclude from the assumptions that `F` is an `ℝ`-algebra
and that the restriction of `v` to `ℝ` is equivalent to the standard absolute value.
There is then an absolute value `v'` on `F` that is equivalent to `v` and restricts
to the standard absolute value on `ℝ`; in this way, `F` is a normed `ℝ`-algebra.
So we will use this assumption in the following. The main ingredient is the
Gelfand-Mazur Theorem in the following version:

If a field `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`.
-/

namespace Real

section restrict

variable {F : Type*} [Field F] [Algebra ℝ F] {v : AbsoluteValue F ℝ}

noncomputable
def normedAlgebraOfAbsoluteValue (hv : v.restrict ℝ = .abs) : NormedAlgebra ℝ (WithAbs v) where
  __ := WithAbs.instAlgebra_right v --‹Algebra ℝ (WithAbs v)›
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    refine le_of_eq ?_
    congr
    rw [WithAbs.norm_eq_abv, show ‖r‖ = AbsoluteValue.abs r from rfl, ← hv]
    rfl

lemma algebraEquiv_eq_algebraMap (e : ℝ ≃ₐ[ℝ] F) : e = algebraMap ℝ F := by
  have : (e.symm : F →+* ℝ).comp (algebraMap ℝ F) = RingHom.id ℝ := Subsingleton.elim ..
  ext1 x
  apply_fun (· x) at this
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply] at this
  nth_rewrite 1 [← this]
  -- set y := algebraMap ℝ F x -- without that, `simp` does not close the goal
  simp only [RingHom.coe_coe, AlgEquiv.apply_symm_apply]

open AbsoluteValue WithAbs

/-- A version of the **Gelfand-Mazur Theorem** over the reals:
A field `F` that is an `ℝ`-algebra and has an absolute value `v` whose pull-back to `ℝ` is
the standard absolute value is either isomorphic to `ℝ` (via the algebra map)
or is isomorphic to `ℂ` as an `ℝ`-algebra in such a way that the pull-back of `v` to `ℂ`
is the standard absolute value of `ℂ`. -/
theorem nonempty_algEquiv_or_of_restrict_eq (hv : v.restrict ℝ = .abs) :
    (∃ e : ℝ ≃ₐ[ℝ] WithAbs v, v.comap ((equiv v).toRingHom.comp e) = .abs) ∨
      ∃ e : ℂ ≃ₐ[ℝ] WithAbs v, v.comap ((equiv v).toRingHom.comp e) =
        NormedField.toAbsoluteValue ℂ := by
  let inst := normedAlgebraOfAbsoluteValue hv
  rcases NormedAlgebra.Real.nonempty_algEquiv_or (WithAbs v) with hℝ | hℂ
  · left
    let e := Classical.choice hℝ
    refine ⟨e.symm, ?_⟩
    have he : (e.symm : ℝ →+* WithAbs v) = algebraMap ℝ (WithAbs v) :=
      algebraEquiv_eq_algebraMap e.symm
    rw [RingEquiv.toRingHom_eq_coe, he, ← hv]
    rfl
  · right
    let e := Classical.choice hℂ
    refine ⟨e.symm, ?_⟩
    let inst' : Algebra ℂ (WithAbs v) := RingHom.toAlgebra e.symm
    have he : e.symm = algebraMap ℂ (WithAbs v) := rfl
    have instST : IsScalarTower ℝ ℂ (WithAbs v) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      rw [← he]
      ext1 x
      change algebraMap ℝ (WithAbs v) x = e.symm (algebraMap ℝ ℂ x)
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    let vℂ : AbsoluteValue ℂ ℝ := v.comap ((equiv v).toRingHom.comp e.symm)
    have hvℂ : vℂ.restrict ℝ = .abs := by
      simp only [vℂ, ← hv, restrict, ← comap_comp]
      congr
      let instF : Algebra ℂ F := ((equiv v).toRingHom.comp (algebraMap ℂ (WithAbs v))).toAlgebra
      have : IsScalarTower ℝ ℂ F := inferInstanceAs <| IsScalarTower ℝ ℂ (WithAbs v)
      exact (IsScalarTower.algebraMap_eq ℝ ℂ F).symm
    have H₁ : (⟨_, hvℂ⟩ : { v' // restrict ℝ v' = AbsoluteValue.abs }) =
        ⟨_, Complex.abv_restrict_real⟩ :=
      (lemma_6_1_a (F := ℝ) (F' := ℂ) .abs).elim ..
    exact congrArg Subtype.val H₁

/-- A version of the **Gelfand-Mazur Theorem** over the reals:
A field `F` that is an `ℝ`-algebra and has an absolute value `v` whose pull-back to `ℝ` is
equivalent to the standard absolute value is either isomorphic to `ℝ` (via the algebra map)
or is isomorphic to `ℂ` as an `ℝ`-algebra in such a way that the pull-back of `v` to `ℂ`
is equivalent to the standard absolute value of `ℂ`. -/
theorem nonempty_algEquiv_or_of_restrict_isEquiv (hv : v.restrict ℝ ≈ .abs) :
    (∃ e : ℝ ≃ₐ[ℝ] WithAbs v, v.comap ((equiv v).toRingHom.comp e) ≈ .abs) ∨
      ∃ e : ℂ ≃ₐ[ℝ] WithAbs v, v.comap ((equiv v).toRingHom.comp e) ≈
        NormedField.toAbsoluteValue ℂ := by
  let v' := ofIsEquivComap (algebraMap ℝ F) hv
  have hv' : restrict ℝ v' = .abs := ofIsEquivComap_def ..
  have Hv' : v ≈ v' := Setoid.symm <| ofIsEquivComap_isEquiv (algebraMap ℝ F) hv
  let inst := normedAlgebraOfAbsoluteValue hv'
  rcases nonempty_algEquiv_or_of_restrict_eq hv' with ⟨e, he⟩ | ⟨e, he⟩
  · exact .inl ⟨e.trans (algEquiv₂ v' v), he ▸ isEquiv_comap _ Hv'⟩
  · exact .inr ⟨e.trans (algEquiv₂ v' v), he ▸ isEquiv_comap _ Hv'⟩

end restrict

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ}

open AbsoluteValue WithAbs

/-- **Ostrowski's Theorem** (a different one from `Rat.AbsoluteValue.equiv_real_or_padic`):
A field `F` that is complete with respect to an archimedean absolute value `v`
is either isomorphic to `ℝ` or to `ℂ`; in both cases, `v` pulls back to an absolute value
that is equivalent to the standard absolute value on `ℝ` or `ℂ`, respectively. -/
theorem nonempty_algEquiv_or_of_complete_of_nonarch [CompleteSpace (WithAbs v)]
    (h : ¬IsNonarchimedean v) :
    (∃ e : ℝ ≃+* WithAbs v, v.comap ((equiv v).toRingHom.comp e) ≈ .abs) ∨
      ∃ e : ℂ ≃+* WithAbs v, v.comap ((equiv v).toRingHom.comp e) ≈
        NormedField.toAbsoluteValue ℂ := by
  obtain ⟨f, hf⟩ := algebra_of_archimedean h
  let inst : Algebra ℝ F := f.toAlgebra
  rcases nonempty_algEquiv_or_of_restrict_isEquiv hf with ⟨e, he⟩ | ⟨e, he⟩
  · exact .inl ⟨↑e, he⟩
  . exact .inr ⟨↑e, he⟩

end Real
