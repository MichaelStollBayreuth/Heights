import Heights.Equivalence
import Heights.GelfandMazur

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
    · simp only [Nat.ofNat_pos, mul_lt_mul_left, even_two, Even.mul_right, and_true] at hk ⊢
      omega
    · exact Nat.two_mul_div_two_of_even hk.2
    · omega
    · rw [Nat.two_mul_div_two_of_even hk.2]
  · refine sum_bij' (fun k _ ↦ k / 2) (fun k _ ↦ 2 * k + 1) (fun k hk ↦ ?_)
      (fun k hk ↦ ?_ ) (fun k hk ↦ ?_) (fun k hk ↦ ?_) (fun k hk ↦ ?_) <;>
      simp only [mem_filter, mem_range, Nat.not_even_iff_odd] at hk ⊢
    · omega
    · simp only [odd_two_mul_add_one, not_false_eq_true, and_true]
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
    Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two
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
  obtain ⟨c, hc₀, hc⟩ := h
  refine ⟨c, hc₀, ?_⟩
  ext1 x
  simp [comap, comp, congrFun hc (f x)]

/-- Two equivalent extensions from `F` to `R` of the same nontrivial absolute value
must be equal. -/
lemma eq_of_isEquiv_of_comap_eq {v₁ v₂ : AbsoluteValue R ℝ} (h₁ : v₁ ≈ v₂) (f : F →+* R)
    (h₂ : v₁.comap f = v₂.comap f) (h₃ : (v₁.comap f).IsNontrivial) :
    v₁ = v₂ := by
  obtain ⟨c, hc₀, hc₁⟩ := h₁
  obtain ⟨x, hx⟩ := h₃.exists_abv_gt_one
  suffices c = 1 by simpa [this] using hc₁
  have H : v₁ (f x) = v₂ (f x) := by
    simp only [← comap_apply, h₂]
  rw [← congrFun hc₁, ← comap_apply, eq_comm] at H
  nth_rewrite 2 [← Real.rpow_one (v₁.comap f x)] at H
  exact (Real.rpow_right_inj (zero_lt_one.trans hx) hx.ne').mp H

section

variable {R : Type*} [Field R] {v : AbsoluteValue F ℝ} {v' : AbsoluteValue R ℝ}
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

end


variable [Algebra F R]

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
lemma eq_of_isEquiv_of_restrict_eq {v₁ v₂ : AbsoluteValue R ℝ} (h₁ : v₁ ≈ v₂)
    (h₂ : v₁.restrict F = v₂.restrict F) (h₃ : (v₁.restrict F).IsNontrivial) :
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
  rw [isEquiv_iff_isHomeomorph]
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
    refine eq_of_isEquiv_of_restrict_eq ?_ hr (by rwa [v₁.prop])
    exact isEquiv_of_restrict_eq hv v₁.prop v₂.prop
  · have hv₁ := trivial_of_finiteDimensional_of_restrict v₁.prop hv
    have hv₂ := trivial_of_finiteDimensional_of_restrict v₂.prop hv
    ext1
    exact eq_of_not_isNontrivial hv₁ hv₂

end AbsoluteValue

section GelfandMazur

/-!
### A version of the Gelfand-Mazur Theorem

We show that a complete field with real-valued archimedean absolute value must be
isomorphic either to `ℝ` or to `ℂ` with a power of its usual absolute value.
-/

namespace Real

variable {F : Type*} [Field F] [Algebra ℝ F] {v : AbsoluteValue F ℝ}

section restrict_equal

variable (hv : v.restrict ℝ = .abs)

noncomputable
def normedAlgebraOfAbsoluteValue : NormedAlgebra ℝ (WithAbs v) where
  __ := WithAbs.instAlgebra_right v --‹Algebra ℝ (WithAbs v)›
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    refine le_of_eq ?_
    congr
    rw [WithAbs.norm_eq_abv, show ‖r‖ = AbsoluteValue.abs r from rfl, ← hv]
    rfl

lemma normedAlgebraOfAbsoluteValue_toAlgebra_eq :
    (normedAlgebraOfAbsoluteValue hv).toAlgebra = WithAbs.instAlgebra_right v :=
  rfl

end restrict_equal

-- variable (hv : v.restrict ℝ ≈ .abs)

open AbsoluteValue WithAbs in
theorem GelfandMazur [CompleteSpace (WithAbs v)] (hv : v.restrict ℝ ≈ .abs) :
    (∃ e : ℝ ≃ₐ[ℝ] WithAbs v, v.comap (e.toRingEquiv.trans (equiv v)).toRingHom ≈ .abs) ∨
      ∃ e : ℂ ≃ₐ[ℝ] WithAbs v, v.comap (e.toRingEquiv.trans (equiv v)).toRingHom ≈
        NormedField.toAbsoluteValue ℂ := by
  let v' := ofIsEquivComap (algebraMap ℝ F) hv
  have hv' : restrict ℝ v' = .abs := ofIsEquivComap_def ..
  let inst := normedAlgebraOfAbsoluteValue hv'
  rcases GelfandMazur.nonempty_algEquiv_or (F := WithAbs v') with hℝ | hℂ
  · left
    let e := Classical.choice hℝ
    have he (r : ℝ) : e.symm r = algebraMap ℝ (WithAbs v') r := by
      apply_fun ⇑e
      simp
    refine ⟨e.symm.trans (algEquiv₂ (F := ℝ) v' v), ?_⟩
    have : v.comap ((e.symm.trans (algEquiv₂ v' v)).toRingEquiv.trans (equiv v)).toRingHom =
        v.restrict ℝ := by
      ext1 x
      simp [he, restrict]
    rwa [this]
  · right
    let e := Classical.choice hℂ
    have he (r : ℝ) : e.symm r = algebraMap ℝ (WithAbs v') r := by
      apply_fun ⇑e
      simp
    refine ⟨e.symm.trans (algEquiv₂ (F := ℝ) v' v), ?_⟩
    have H : (v.comap ((e.symm.trans (algEquiv₂ v' v)).toRingEquiv.trans (equiv v)).toRingHom).comap
             (algebraMap ℝ ℂ) = v.restrict ℝ := by
      ext1 x
      simp [he, restrict]
    let inst' : Algebra ℂ F := RingHom.toAlgebra e.symm.toRingHom
    have h (x : ℝ) : algebraMap ℂ F (algebraMap ℝ ℂ x) = algebraMap ℝ F x := by
      have hh (z : ℂ) :e.symm.toRingEquiv.toRingHom z = e.symm z := rfl
      erw [show algebraMap ℂ F = e.symm.toRingHom from rfl, hh, he] -- defeq abuse?
      simp only [Algebra.id.map_eq_id, RingHom.id_apply]
      rfl
    -- let inst'' : IsScalarTower ℝ ℂ F := sorry
    have H' : v.comap ((e.symm.trans (algEquiv₂ v' v)).toRingEquiv.trans (equiv v)).toRingHom =
        v.restrict ℂ := by
      have : (v.restrict ℂ).restrict ℝ = v.restrict ℝ  := by
        ext1
        simp only [restrict, comap_apply, h]
      have inst₉ : CompleteSpace (WithAbs (restrict ℝ v)) := sorry
      have heq := isEquiv_of_restrict_eq ((Setoid.symm hv).isNontrivial ⟨2, two_ne_zero, by norm_num⟩) this H

      sorry
    sorry

end Real

namespace Complex

section

variable {F : Type*} [Field F] [Algebra ℂ F] {v : AbsoluteValue F ℝ}

section restrict_equal

variable (hv : v.restrict ℂ = NormedField.toAbsoluteValue ℂ)

noncomputable
def normedAlgebraOfAbsoluteValue : NormedAlgebra ℂ (WithAbs v) where
  __ := ‹Algebra ℂ (WithAbs v)›
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    refine le_of_eq ?_
    congr
    rw [WithAbs.norm_eq_abv, show ‖r‖ = NormedField.toAbsoluteValue ℂ r from rfl, ← hv]
    rfl

noncomputable
def algEquivComplex [CompleteSpace (WithAbs v)] : ℂ ≃ₐ[ℂ] WithAbs v :=
  letI inst := normedAlgebraOfAbsoluteValue hv
  NormedRing.algEquivComplexOfComplete fun {_} ↦ isUnit_iff_ne_zero

lemma comap_algEquivComplex [CompleteSpace (WithAbs v)] :
    v.comap ((algEquivComplex hv).toRingEquiv.trans (WithAbs.equiv v)).toRingHom =
      NormedField.toAbsoluteValue ℂ :=
  hv ▸ rfl

end restrict_equal

section

open AbsoluteValue in
theorem GelfandMazur (hv : v.restrict ℂ ≈ NormedField.toAbsoluteValue ℂ) [CompleteSpace (WithAbs v)] :
    ∃ e : ℂ ≃ₐ[ℂ] WithAbs v, v.comap (e.toRingEquiv.trans (WithAbs.equiv v)).toRingHom ≈
      NormedField.toAbsoluteValue ℂ := by
  let v' := ofIsEquivComap (algebraMap ℂ F) hv
  have hv' : restrict ℂ v' = NormedField.toAbsoluteValue ℂ := ofIsEquivComap_def ..
  have : CompleteSpace (WithAbs v') :=
    completeSpace_of_isEquiv <| Setoid.symm (ofIsEquivComap_isEquiv (algebraMap ℂ F) hv)
  let e := (algEquivComplex hv').trans <| (WithAbs.algEquiv v').trans (WithAbs.algEquiv v).symm
  refine ⟨e, ?_⟩
  have H : (e.toRingEquiv.trans (WithAbs.equiv v)).toRingHom = algebraMap ℂ F := rfl
  rw [H]
  exact hv

end


section

variable {F : Type*} [Field F]

open Polynomial in
lemma irreducible_sq_add_one (h : ∀ x : F, x ^ 2 ≠ -1) :
    Irreducible (X ^ 2 + 1 : Polynomial F) := by
  set p : Polynomial F := X ^ 2 + 1
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x ↦ ?_
  · have : p.natDegree = 2 := by simp only [p]; compute_degree!
    simp [this]
  · specialize h x
    contrapose! h
    simp only [p, IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at h
    exact (neg_eq_of_add_eq_zero_left h).symm

variable [Algebra ℝ F]

noncomputable
def algebraOfAlgebraReal {i : F} (hi : i ^ 2 = -1) : Algebra ℂ F := RingHom.toAlgebra {
  toFun z := z.re • 1 + z.im • i
  map_one' := by simp
  map_mul' w z := by
    simp only [Complex.mul_re, Complex.mul_im, mul_add, Algebra.mul_smul_comm, mul_one, smul_add,
      add_mul, Algebra.smul_mul_assoc, one_mul, smul_smul]
    rw [← sq, hi]
    module
  map_zero' := by simp
  map_add' w z := by
    simp only [Complex.add_re, Complex.add_im]
    module
}

open Polynomial in
noncomputable
def algebraAdjoinRootOfAlgebraReal (h : ∀ x : F, x ^ 2 ≠ -1) :
    Algebra ℂ (AdjoinRoot (X ^ 2 + 1 : Polynomial F)) := by
  letI p : Polynomial F := X ^ 2 + 1
  letI instF : Fact (Irreducible p) := ⟨irreducible_sq_add_one h⟩
  let i := AdjoinRoot.root p
  have hr : i ^ 2 = -1 := by
    refine (neg_eq_of_add_eq_zero_left ?_).symm
    simpa [p] using AdjoinRoot.isRoot_root p
  exact algebraOfAlgebraReal hr

noncomputable
def fieldAdjoinRootOfAlgebraReal (h : ∀ x : F, x ^ 2 ≠ -1) :
    Field (AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F)) :=
  haveI : Fact (Irreducible (Polynomial.X ^ 2 + 1 : Polynomial F)) := ⟨irreducible_sq_add_one h⟩
  AdjoinRoot.instField

end

#exit

section

variable {F : Type*} [NormedField F] [NormedAlgebra ℝ F]

#check TensorProduct ℝ ℂ F

#synth Algebra ℂ (TensorProduct ℝ ℂ F)

#synth NormedAlgebra ℂ (TensorProduct ℝ ℂ F)

#synth Module F <| AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F)

noncomputable
def xyz : AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F) ≃ₗ[F] Fin 2 → F := by
  letI p : Polynomial F := Polynomial.X ^ 2 + 1
  have hp₀ : p ≠ 0 := Polynomial.Monic.ne_zero <| by simp only [p]; monicity!
  letI pb := AdjoinRoot.powerBasis hp₀
  have hpb : pb.dim = 2 := by
    simp [pb, p]
    compute_degree!
  exact (hpb ▸ (AdjoinRoot.powerBasis hp₀).basis.repr).trans
    (Finsupp.linearEquivFunOnFinite F F (Fin 2))

lemma xyz_mul (x y : AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F)) :
    xyz (x * y) = ![xyz x 0 * xyz y 0 - xyz x 1 * xyz y 1, xyz x 0 * xyz y 1 + xyz x 1 * xyz y 0] := by
  ext1 i
  fin_cases i
  · simp
    sorry
  · sorry


open Polynomial in
noncomputable
def normFunAdjoinRootOfAlgebraReal --(h : ∀ x : F, x ^ 2 ≠ -1)
    (x : AdjoinRoot (X ^ 2 + 1 : Polynomial F)) : ℝ := by
  letI p : Polynomial F := Polynomial.X ^ 2 + 1
  have hp₀ : p ≠ 0 := Polynomial.Monic.ne_zero <| by simp only [p]; monicity!
  letI pb := AdjoinRoot.powerBasis hp₀
  have hpb : pb.dim = 2 := by
    simp [pb, p]
    compute_degree!
  letI r := pb.basis.repr x
  exact Real.sqrt (‖r ⟨0, by omega⟩‖ ^ 2 + ‖r ⟨1, by omega⟩‖ ^ 2)

noncomputable
instance normAdjoinRootOfAlgebraReal : --(h : ∀ x : F, x ^ 2 ≠ -1) :
    Norm (AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F)) where
      norm := normFunAdjoinRootOfAlgebraReal --h

open Polynomial in
lemma normFunAdjoinRootOfAlgebraReal_mul (x y : AdjoinRoot (X ^ 2 + 1 : Polynomial F)) :
    ‖x * y‖ = ‖x‖ * ‖y‖ := by
  simp only [normAdjoinRootOfAlgebraReal, normFunAdjoinRootOfAlgebraReal, AdjoinRoot.powerBasis_dim]

  sorry

def normedFieldAdjoinRootOfAlgebraReal  {F : Type*} [NormedField F] [Algebra ℝ F]
    (h : ∀ x : F, x ^ 2 ≠ -1) :
    NormedField <| AdjoinRoot (.X ^ 2 + 1 : Polynomial F) where
      __ := fieldAdjoinRootOfAlgebraReal h
      __ := normAdjoinRootOfAlgebraReal h
      -- 'dist', 'dist_self', 'dist_comm', 'dist_triangle', 'eq_of_dist_eq_zero', 'dist_eq', 'norm_mul'

def normedAlgebraAdjoinRootOfNormedAlgebraReal {F : Type*} [NormedField F] [NormedAlgebra ℝ F] (h : ∀ x : F, x ^ 2 ≠ -1) :
    NormedAlgebra ℂ (AdjoinRoot (.X ^ 2 + 1 : Polynomial F)) := _


end

end Complex

namespace Real

variable {F : Type*} [Field F] [Algebra ℝ F]
  {v : AbsoluteValue F ℝ} (hv : AbsoluteValue.restrict ℝ v = .abs)

noncomputable
def normedAlgebraOfAbsoluteValue : NormedAlgebra ℝ (WithAbs v) where
  __ := ‹Algebra ℝ (WithAbs v)›
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    refine le_of_eq ?_
    congr
    rw [WithAbs.norm_eq_abv, show ‖r‖ = AbsoluteValue.abs r from rfl, ← hv]
    rfl

noncomputable
def algEquivReal (hF : ∀ x : F, x ^ 2 ≠ -1) [CompleteSpace (WithAbs v)] : ℝ ≃ₐ[ℝ] WithAbs v := by
  letI algℂ := Complex.algebraAdjoinRootOfAlgebraReal hF

  sorry

end Real

namespace AbsoluteValue

namespace GelfandMazur

section preliminaries

section

variable {F : Type*} [Field F] [Algebra ℂ F]

lemma inv_one_sub_add_inv_one_add {x : F} (h : ∀ z : ℂ, x ≠ z • 1) :
    (1 - x)⁻¹ + (1 + x)⁻¹ = 2 * (1 - x ^ 2)⁻¹ := by
  have H₁ : 1 - x ≠ 0 := by
    specialize h 1
    simp only [one_smul] at h
    exact sub_ne_zero_of_ne h.symm
  have H₂ : 1 + x ≠ 0 := by
    specialize h (-1)
    simp only [neg_smul, one_smul] at h
    contrapose! h
    exact (neg_eq_of_add_eq_zero_right h).symm
  have H₃ : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact (mul_ne_zero_iff_right H₂).mpr H₁
  field_simp
  ring

lemma sum_rootsOfUnity_inv_one_sub {x : F} (h : ∀ z : ℂ, x ≠ z • 1) {n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) :
    ∑ k ∈ Finset.range (2 ^ n), (1 - ζ ^ k • x)⁻¹ = 2 ^ n * (1 - x ^ (2 ^ n))⁻¹ := by
  induction n generalizing x ζ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Finset.sum_range_two_mul]
    have hζ' : IsPrimitiveRoot (ζ ^ 2) (2 ^ n) :=
      IsPrimitiveRoot.pow (Nat.two_pow_pos _) hζ Nat.pow_succ'
    have H := ih h hζ'
    conv at H => enter [1, 2, k]; rw [← pow_mul]
    rw [H]; clear H
    have h' (z : ℂ) : ζ • x ≠ z • 1 := by
      apply_fun fun y ↦ ζ⁻¹ • y
      simpa [smul_smul, inv_mul_cancel₀ (hζ.ne_zero (Nat.two_pow_pos _).ne')] using h _
    have H := ih h' hζ'
    conv at H =>  enter [1, 2, k]; rw [← pow_mul, smul_smul, ← pow_succ]
    rw [H]; clear H
    have hζ'' : ζ ^ 2 ^ n = -1 :=
      IsPrimitiveRoot.eq_neg_one_of_two_right <|
        IsPrimitiveRoot.pow (Nat.two_pow_pos _) hζ <| Nat.pow_succ ..
    have h'' (z : ℂ) : x ^ 2 ^ n ≠ z • 1 := by
      contrapose! h
      let w := z ^ ((1 : ℂ) / 2 ^ n)
      have hw : z = w ^ 2 ^ n := by
        simp only [w]
        rw [← Complex.cpow_natCast, one_div]
        convert (Complex.cpow_inv_ofReal_mul_ofReal _ ?_).symm
        · norm_cast
        · exact_mod_cast Nat.one_le_two_pow
      let ζF := algebraMap ℂ F (ζ ^ 2)
      have hζF : IsPrimitiveRoot ζF (2 ^ n) :=
        hζ'.map_of_injective <| FaithfulSMul.algebraMap_injective ..
      rw [hw, ← one_pow (2 ^ n), ← smul_pow, ← sub_eq_zero,
        hζF.pow_sub_pow_eq_prod_sub_mul x (w • 1) n.two_pow_pos, Finset.prod_eq_zero_iff] at h
      obtain ⟨ξ, hξ, h⟩ := h
      rw [sub_eq_zero] at h
      obtain ⟨ξ', hξ'₁, hξ'₂⟩ := IsPrimitiveRoot.map_nthRootsFinset hζ' hξ
      refine ⟨ξ' * w, ?_⟩
      rw [h, ← hξ'₂, Algebra.mul_smul_comm, mul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
        mul_comm]
    rw [smul_pow, hζ'', neg_smul, one_smul, sub_neg_eq_add, ← mul_add,
      inv_one_sub_add_inv_one_add h'', ← pow_mul', ← mul_assoc, ← pow_succ]

end

section

open Topology Filter in
example (f g : ℕ → ℝ) (h : ∀ n, |f n| ≤ g n) (h' : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  exact squeeze_zero_norm h h'

variable {F : Type*} [NormedField F]

open Topology Filter in
lemma tendsto_mul_norm_inv_one_sub_pow_sub_one {y : F} (hy : ‖y‖ < 1) :
    Tendsto (fun n : ℕ ↦ 2 ^ n * (‖(1 - y ^ 2 ^ n)⁻¹‖ - 1)) atTop (𝓝 0) := by
  have H₀ (n : ℕ) : 0 < 1 - ‖y‖ ^ 2 ^ n := by
    rw [sub_pos]
    exact pow_lt_one₀ (norm_nonneg y) hy n.two_pow_pos.ne'
  have H (n : ℕ) : (1 - y ^ 2 ^ n)⁻¹ = 1 + y ^ 2 ^ n / (1 - y ^ 2 ^ n) := by
    have : 1 - y ^ 2 ^ n ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply_fun (‖·‖) at h
      rw [norm_one, norm_pow] at h
      specialize H₀ n
      rw [← h] at H₀
      norm_num at H₀
    field_simp
  conv => enter [1, n]; rw [H, ← norm_one (α := F)]
  have H' (n : ℕ) : ‖2 ^ n * (‖1 + y ^ 2 ^ n / (1 - y ^ 2 ^ n)‖ - ‖(1 : F)‖)‖ ≤
      2 ^ n * ‖y‖ ^ 2 ^ n / (1 - ‖y‖ ^ 2 ^ n) := by
    rw [norm_mul, mul_div_assoc]
    gcongr (?_ * ?_)
    · simp
    · rw [Real.norm_eq_abs]
      refine (abs_norm_sub_norm_le ..).trans ?_
      rw [add_sub_cancel_left, norm_div, norm_pow]
      gcongr (_ / ?_)
      · exact H₀ _
      · rw [← norm_pow, ← norm_one (α := F)]
        exact norm_sub_norm_le ..
  exact squeeze_zero_norm H' <|  Real.tendsto_two_pow_mul_pow_div_one_sub_pow (norm_nonneg _) hy

variable [Algebra ℂ F]

lemma locallyConstant_of_bounded {x : F} (h : ∀ z : ℂ, x ≠ z • 1)
    (hb : ∀ z : ℂ, ‖(1 - z • x)⁻¹‖ ≤ 1) {w : ℂ} (hw : ‖w • x‖ < 1) :
    ‖(1 - w • x)⁻¹‖ = 1 := by
  rcases eq_or_ne w 0 with rfl | hw₀
  · simp
  refine le_antisymm (hb w) <| le_of_forall_lt fun c hc ↦ ?_
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ n * ‖w • x‖ ^ 2 ^ n / (1 - ‖w • x‖ ^ 2 ^ n) < 1 - c := by
    have := Real.tendsto_two_pow_mul_pow_div_one_sub_pow (norm_nonneg _) hw
    rw [NormedAddCommGroup.tendsto_atTop] at this
    specialize this (1 - c) (by linarith)
    obtain ⟨n, hn⟩ := this
    specialize hn n le_rfl
    rw [Real.norm_eq_abs, sub_zero] at hn
    exact ⟨n, (le_abs_self _).trans_lt hn⟩
  rw [lt_sub_comm, mul_div_assoc] at hn
  have h' (z : ℂ) : w • x ≠ z • 1 := by sorry
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 ^ n) :=
    ⟨_, Complex.isPrimitiveRoot_exp (2 ^ n) n.two_pow_pos.ne'⟩
  have H₁ := sum_rootsOfUnity_inv_one_sub h' hζ
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot n.two_pow_pos, pow_zero, one_smul,
    zero_add, eq_comm] at H₁
  apply_fun (‖·‖) at H₁

  have H₂ : 1 + 2 ^ n * (‖1 - (w • x) ^ 2 ^ n‖⁻¹ - 1) ≤ ‖(1 - (w • x))⁻¹‖ := by

    sorry

  stop
  rw [H₁]
  refine LT.lt.trans_le ?_ H₂
  rw [show 2 ^ n * ‖1 - (w • x) ^ 2 ^ n‖⁻¹ - (2 ^ n - 1) =
             1 - 2 ^ n * (1 - ‖1 - (w • x) ^ 2 ^ n‖⁻¹) by ring]
  refine hn.trans_le ?_
  gcongr 1 - 2 ^ n * ?_
  have H₃ : 1 - ‖w • x‖ ^ 2 ^ n ≠ 0 := sorry
  rw [tsub_le_iff_tsub_le, one_sub_div H₃, ← norm_pow]
  -- a wrong turn somewhere
  stop
  have H : 1 - 2 ^ n * ‖w • x‖ ^ 2 ^ n / (1 - ‖w • x‖ ^ 2 ^ n) ≤
      1 - ‖w • x‖ ^ 2 ^ n * ‖2 ^ n * (1 - (w • x) ^ 2 ^ n)⁻¹‖ := by
    sorry
  refine hn.trans_le <| H.trans ?_
  rw [← sum_rootsOfUnity_inv_one_sub h' hζ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot,
    pow_zero, one_smul]
  stop
  calc
  c < _ := hn
  _ ≤ 1 - 2 ^ n * ‖w • x‖ ^ 2 ^ n / ‖1 - (w • x) ^ 2 ^ n‖ := sorry
  _ = 1 - ‖w • x‖ ^ 2 ^ n * ‖2 ^ n * (1 - (w • x) ^ 2 ^ n)⁻¹‖ := sorry
  _ = ‖(1 - w • x)⁻¹‖ := sorry



example (x y z : ℝ) (h : x - y ≤ z) : x - z ≤ y := tsub_le_iff_tsub_le.mp h

end

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ} [Algebra ℝ F] --(h : ¬ IsNonarchimedean v)
    (h' : v.restrict ℝ ≈ .abs)

section auxiliary

open WithAbs

include h'

lemma _root_.WithAbs.continuous_equiv_symm_comp_algebraMap :
    Continuous <| ⇑(equiv v).symm ∘ (algebraMap ℝ F) := by
  have H : Isometry (algebraMap (WithAbs (v.restrict ℝ)) (WithAbs v)) :=
    isometry_of_comp (congrFun rfl)
  rw [show ⇑(equiv v).symm ∘ (algebraMap ℝ F) =
        ⇑(algebraMap (WithAbs (restrict ℝ v)) (WithAbs v))
          ∘ ⇑(equiv₂ AbsoluteValue.abs (restrict ℝ v)) ∘ ⇑(equiv AbsoluteValue.abs).symm from rfl]
  exact H.continuous.comp <| (continuous_equiv₂ (Setoid.symm h')).comp <|
    continuous_of_continuousAt_zero _ fun ⦃_⦄ a ↦ a

-- Help `fun_prop` below.
-- Note that `fun_prop` on its own cannot fill in the argument `h'`,
-- so we use `fun_prop (disch := assumption)` below.
@[fun_prop]
lemma continuous_smul : Continuous fun p : ℝ × WithAbs v ↦ p.1 • p.2 :=
  (continuousSMul_of_algebraMap _ _ <| continuous_equiv_symm_comp_algebraMap h').continuous_smul

lemma continuous_expr {x : WithAbs v} (H : ∀ a b : ℝ, x ^ 2 + a • x + b • 1 ≠ 0) :
    Continuous fun z : ℂ ↦ 2 * (x - z.re • 1) / ((x - z.re • 1) ^ 2 + z.im ^ 2 • 1) := by
  refine Continuous.div₀ (by fun_prop (disch := assumption)) (by fun_prop (disch := assumption))
    fun z ↦ ?_
  convert H (-2 * z.re) (z.re ^ 2 + z.im ^ 2) using 1
  simp only [Algebra.smul_def, mul_one, map_pow, neg_mul, map_neg, map_mul, map_ofNat, map_add]
  ring

section

variable {E : Type*} [SeminormedCommRing E] [Algebra ℝ E]

-- lemma integral_eq

end

end auxiliary

-- We follow
--   Leonard Tornheim, *Normed fields over the real and complex fields*,
--   Michigan Math. J. 1 (1952), 61–68



/- Every element of `F` is algebraic (of degree at most `2`) over `ℝ`. -/
open Polynomial in
include h' in
lemma isIntegral (x : WithAbs v) : IsIntegral ℝ x := by
  suffices ∃ a b : ℝ, x ^ 2 + a • x + b • 1 = 0 by
    obtain ⟨a, b, H⟩ := this
    let p : ℝ[X] := X ^ 2 + C a * X + C b
    have hpm : p.Monic := by simp only [p]; monicity!
    have hpd : p.natDegree = 2 := by simp only [p]; compute_degree!
    have hx : IsIntegral ℝ (p.aeval x) := by
      simp only [Algebra.smul_def, mul_one] at H
      simpa [p, H] using isIntegral_zero
    exact IsIntegral.of_aeval_monic hpm (by omega) hx
  by_contra! H
  let f (z : ℂ) : ℝ := ‖2 * (x - z.re • 1) / ((x - z.re • 1) ^ 2 + z.im ^ 2 • 1)‖
  have hfc : Continuous f := continuous_norm.comp <| continuous_expr h' H
  sorry

-- #check NormedRing.algEquivComplexOfComplete

-- See #25332 by Junyan Xu
theorem nonempty_algEquiv_or_of_finrank_algClosure_eq_two
    {F F' : Type*} (E : Type*) [Field F] [Field F'] [Field E] [Algebra F F'] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed F'] (h : Module.finrank F F' = 2) :
    Nonempty (E ≃ₐ[F] F) ∨ Nonempty (E ≃ₐ[F] F') := by
  have emb : E →ₐ[F] F' := IsAlgClosed.lift
  have e := AlgEquiv.ofInjectiveField emb
  have := Subalgebra.isSimpleOrder_of_finrank h
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top emb.range <;> rw [h] at e
  exacts [.inl ⟨e.trans <| Algebra.botEquiv ..⟩, .inr ⟨e.trans Subalgebra.topEquiv⟩]

lemma nonempty_algEquiv_real_or_of_algebra_real {F : Type*} [Field F] [Algebra ℝ F]
    (h : (algebraMap ℝ F).IsIntegral) :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) :=
  have : Algebra.IsIntegral ℝ F := ⟨h⟩
  nonempty_algEquiv_or_of_finrank_algClosure_eq_two F Complex.finrank_real_complex
--

include h' in
theorem main_thm : Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) :=
  nonempty_algEquiv_real_or_of_algebra_real (isIntegral h')

end preliminaries

end GelfandMazur


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
  rw [← apply_algebraMap, absoluteValue_eq_norm, show (algebraMap F v.Completion) x = x from rfl,
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
  refine (isEquiv_iff_isHomeomorph .abs v).mpr ?_
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
  refine eq_of_isEquiv_of_restrict_eq (isEquiv_abs_of_restrict h') h ?_
  rw [h]
  exact ⟨2, two_ne_zero, by simp⟩

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ} [CompleteSpace (WithAbs v)]

omit [CompleteSpace (WithAbs v)] in
open WithAbs in
lemma comap_eq_of_isometry {F' : Type*} [Field F'] {v' : AbsoluteValue F' ℝ}
    {f : WithAbs v →+* WithAbs v'} (h : Isometry f) :
    v'.comap ((equiv v').toRingHom.comp (f.comp (equiv v).symm.toRingHom)) = v := by
  ext1 x
  rw [comap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← norm_eq_abv, (AddMonoidHomClass.isometry_iff_norm _).mp h, norm_eq_abv]
  simp

omit [CompleteSpace (WithAbs v)] in
open WithAbs in
lemma comap_completion_eq_of_isometry {F' : Type*} [Field F'] (v' : AbsoluteValue F' ℝ)
    {f : v.Completion →+* F'} (h : Isometry ((equiv v').symm.toRingHom.comp f)) :
    v'.comap f = Completion.absoluteValue v := by
  ext1 x
  rw [comap_apply]
  have := (AddMonoidHomClass.isometry_iff_norm _).mp h x
  simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    norm_eq_abv, RingEquiv.apply_symm_apply, ← Completion.absoluteValue_eq_norm] using this

omit [CompleteSpace (WithAbs v)] in
open WithAbs in
lemma isometry_equiv_comap {F' : Type*} [Field F'] (f : F' ≃+* v.Completion) :
    Isometry ((equiv ((Completion.absoluteValue v).comap f)).trans f) := by
  have H : Isometry (equiv (Completion.absoluteValue v)) :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr (congrFun rfl)
  replace H := H.comp <| isometry_comap (Completion.absoluteValue v) f.toRingHom
  simpa only [RingEquiv.coe_trans, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
    RingHom.coe_coe] using H

omit [CompleteSpace (WithAbs v)] in
open WithAbs in
lemma isHomeomorph_equiv_comap {F' : Type*} [Field F'] (f : F' ≃+* v.Completion) :
    IsHomeomorph ((equiv ((Completion.absoluteValue v).comap f)).trans f) :=
  (isometry_equiv_comap f).isHomeomorph_ofEquiv

open WithAbs RingEquiv Rat.AbsoluteValue in
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
    simp only [equiv₂, toRingHom_eq_coe, coe_trans]
    refine isHomeomorph_equiv_realAbs.ringEquiv_symm.comp ?_
    convert He₄.ringEquiv_symm.comp <|isHomeomorph_equiv_comap e₄
    rw [coe_trans, ← Function.comp_assoc, ← coe_trans, self_trans_symm, coe_refl,
      Function.id_comp]
  -- Finally, we take `e = e₁ ∘ e₄` and reduce to the statement `H₂` above.
  exact ⟨e₁.comp e₄, by rwa [comap_comp, H₁]⟩

/-- If an absolute value `v` on `ℝ` is equivalent to the standard absolute value `|·|`,
then `v = |·| ^ e` for some `0 < e ≤ 1`. -/
lemma _root_.Real.AbsoluteValue.eq_rpow_of_isEquiv_abs {v : AbsoluteValue ℝ ℝ} (hv : v ≈ .abs) :
    ∃ (e : ℝ) (h₀ : 0 < e) (h₁ : e ≤ 1), v = AbsoluteValue.rpow .abs h₀ h₁ := by
  have H₁ : v.restrict ℚ ≈ Rat.AbsoluteValue.real :=
    Setoid.trans (isEquiv_comap (algebraMap ℚ ℝ) hv) <| Setoid.refl _
  obtain ⟨e, he₀, he₁, he⟩ := Rat.AbsoluteValue.eq_rpow_of_isEquiv_real H₁
  refine ⟨e, he₀, he₁, ?_⟩
  refine eq_of_isEquiv_of_restrict_eq ?_ he ?_
  · exact Setoid.trans hv <| Setoid.symm (isEquiv_rpow AbsoluteValue.abs he₀ he₁)
  · rw [isNontrivial_iff_ne_trivial]
    intro h
    replace H₁ := Setoid.symm H₁
    rw [h, eq_trivial_of_isEquiv_trivial] at H₁
    revert H₁
    change _ ≠ _
    rw [← isNontrivial_iff_ne_trivial]
    exact ⟨2, two_ne_zero, by simp⟩

lemma _root_.Complex.AbsoluteValue.isEquiv_abv_of_restrict {v : AbsoluteValue ℂ ℝ}
    [CompleteSpace (WithAbs <| v.restrict ℝ)] (h : v.restrict ℝ ≈ .abs) :
    v ≈ NormedField.toAbsoluteValue ℂ := by
  have H₁ := AbsoluteValue.lemma_6_1_a (F' := ℂ) (v.restrict ℝ)
  obtain ⟨e, he₀, he₁, he⟩ := Real.AbsoluteValue.eq_rpow_of_isEquiv_abs h
  let v' := (NormedField.toAbsoluteValue ℂ).rpow he₀ he₁
  have hv' : v'.restrict ℝ = v.restrict ℝ := by
    simp only [v', he]
    ext1 x
    simp only [restrict, comap_apply, Complex.coe_algebraMap, rpow_apply, Pi.pow_apply, abs_apply]
    rw [show (NormedField.toAbsoluteValue ℂ) ↑x = ‖(x : ℂ)‖ from rfl, Complex.norm_real,
      Real.norm_eq_abs]
  rw [show v = v' from congrArg Subtype.val <| @Subsingleton.elim _ H₁ ⟨v, rfl⟩ ⟨v', hv'⟩]
  simp only [v']
  exact isEquiv_rpow (NormedField.toAbsoluteValue ℂ) he₀ he₁


theorem equiv_R_or_C_of_complete_archimedean (h : ¬ IsNonarchimedean v) :
    (∃ e : ℝ ≃+* F, v.comap e ≈ .abs)
      ∨ ∃ e : ℂ ≃+* F, v.comap e ≈ NormedField.toAbsoluteValue ℂ := by
  obtain ⟨e, he⟩ := algebra_of_archimedean h
  let inst := e.toAlgebra
  rcases GelfandMazur.main_thm he with H | H <;> let e' := Classical.choice H
  · -- `F` is isomorphic to `ℝ`.
    refine .inl ⟨e'.symm, ?_⟩
    convert he
    have : (e' : F →+* ℝ).comp e = RingHom.id ℝ := Subsingleton.elim ..
    rw [show ((e'.symm : ℝ ≃+* F) : ℝ →+* F) = e'.symm from rfl,
      ← RingHom.comp_id (e'.symm : ℝ →+* F), ← this]
    ext1
    simp
  · -- `F` is isomorphic to `ℂ` as an `ℝ`-algebra.
    refine .inr ⟨e'.symm, ?_⟩
    have H : (e' : F →+* ℂ).comp e = algebraMap ℝ ℂ := by
      suffices AlgHom.comp e' (Algebra.ofId ℝ F) = Algebra.ofId ℝ ℂ from
        congrArg AlgHom.toRingHom this
      exact Subsingleton.elim ..
    suffices v.comap ((e'.symm : ℂ →+* F).comp (algebraMap ℝ ℂ)) ≈ .abs by
      rw [comap_comp] at this
      have inst : CompleteSpace (WithAbs (restrict ℝ (R := ℂ) (v.comap e'.symm))) :=
        completeSpace_of_isEquiv <| Setoid.symm this
      convert Complex.AbsoluteValue.isEquiv_abv_of_restrict this
    convert he
    rw [← H]
    ext1
    simp

end AbsoluteValue

end GelfandMazur

end complete
