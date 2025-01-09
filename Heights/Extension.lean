import Mathlib

/-!
# Estensions of absolute values

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

section Mathlib.Analysis.SpecialFunctions.Pow.Real

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

section Mathlib.Analysis.Normed.Ring.WithAbs

variable {R : Type*} [Ring R]

lemma AbsoluteValue.norm_eq_abv (v : AbsoluteValue R ℝ) (x : WithAbs v) :
    ‖x‖ = v (WithAbs.equiv v x) := rfl

/- /-- The topology on `R` induced by an absolute value `v`. -/
noncomputable
def AbsoluteValue.topology (v : AbsoluteValue R ℝ) : TopologicalSpace R :=
  letI _ := v.toNormedRing
  inferInstance -/

/- lemma AbsoluteValue.topology_coinduced_eq (v : AbsoluteValue R ℝ) :
    letI t : TopologicalSpace (WithAbs v) := inferInstance
    v.topology.coinduced (WithAbs.equiv v).symm = t :=
  rfl -/

/- lemma AbsoluteValue.topology_eq_coinduced (v : AbsoluteValue R ℝ) :
    letI t : TopologicalSpace (WithAbs v) := inferInstance
    v.topology = t.coinduced (WithAbs.equiv v) :=
  rfl -/

/- lemma TopologicalSpace.isHomeomorph_iff_eq_coinduced {X Y : Type*} (t : TopologicalSpace Y)
    [TopologicalSpace X] (e : X ≃ Y) :
    IsHomeomorph e ↔ t = TopologicalSpace.coinduced e inferInstance := by
  rw [isHomeomorph_iff_exists_homeomorph]
  refine ⟨fun ⟨h, hh⟩ ↦ hh ▸ (Homeomorph.coinduced_eq h).symm, fun H ↦ ?_⟩
  exact ⟨e.toHomeomorph fun _ ↦ by convert isOpen_coinduced.symm, rfl⟩ -/

/- lemma TopologicalSpace.isHomeomorph_iff_induced_eq {X Y : Type*} (t : TopologicalSpace Y)
    [TopologicalSpace X] (e : X ≃ Y) :
    IsHomeomorph e ↔ t.induced e = (inferInstance : TopologicalSpace X) := by
  rw [t.isHomeomorph_iff_eq_coinduced]
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [H, ← e.induced_symm, induced_compose, e.symm_comp_self]
    exact induced_id
  · apply_fun TopologicalSpace.coinduced e at H
    rw [← H, ← e.induced_symm, induced_compose, e.self_comp_symm]
    exact induced_id.symm -/

/- /-- The homeomorphism between `WithAbs v` and the underlying ring with the induced topology. -/
def AbsoluteValue.homeomorph (v : AbsoluteValue R ℝ) :
    @Homeomorph (WithAbs v) R inferInstance v.topology :=
  letI inst := v.topology
  (WithAbs.equiv v).toHomeomorph fun _ ↦ isOpen_coinduced.symm -/

namespace WithAbs

/- lemma isHomeomorph_equiv_iff (t : TopologicalSpace R) (v : AbsoluteValue R ℝ) :
    IsHomeomorph (equiv v) ↔ t = v.topology :=
  t.isHomeomorph_iff_eq_coinduced _ -/

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

instance fd_left [AddCommGroup S] [Module F S] [FiniteDimensional F S] {v : AbsoluteValue F ℝ} :
    FiniteDimensional (WithAbs v) S :=
  inferInstanceAs <| FiniteDimensional F S

instance fd_right [Ring S] [Module F S] [FiniteDimensional F S] (v : AbsoluteValue S ℝ) :
    FiniteDimensional F (WithAbs v) :=
  inferInstanceAs <| FiniteDimensional F S

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

/-- An absolute value on a semiring `R` without zero divisors is *nontrivial* if it takes
a value `≠ 1` on a nonzero element.

This has the advantage over `v ≠ .trivial` that it does not require decidability
of `· = 0` in `R`. -/
def IsNontrivial (v : AbsoluteValue R S) : Prop :=
  ∃ x ≠ 0, v x ≠ 1

lemma isNontrivial_iff_not_eq_trivial [DecidableEq R] [NoZeroDivisors R] [Nontrivial S]
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

section restrict

variable [Nontrivial R] (F : Type*) [Field F] [Algebra F R]

/-- The restriction to a field `F` of an absolute value on an `F`-algebra `R`. -/
def restrict (v : AbsoluteValue R S) : AbsoluteValue F S :=
  v.comp (RingHom.injective (algebraMap F R))

variable {F}

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
  have hn₁ : 0 < n := Module.finrank_pos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n < v' (x ^ m) := by
    simpa only [v'.map_pow] using pow_unbounded_of_one_lt _ hx
  let p := (LinearMap.mulLeft F (x ^ m)).charpoly
  have hp₁ : p.Monic := LinearMap.charpoly_monic _
  have : p.aeval (x ^ m) = 0 := by
    have : p.aeval (LinearMap.mulLeft F (x ^ m)) = 0 := LinearMap.aeval_self_charpoly _
    apply_fun (· 1) at this
    simp only [Polynomial.aeval_endomorphism, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply,
      mul_one, LinearMap.zero_apply] at this
    rw [Polynomial.sum_eq_of_subset _ (p := p) (by simp) Polynomial.supp_subset_range_natDegree_succ] at this
    rwa [Polynomial.aeval_eq_sum_range]
  have hpn : p.natDegree = n := LinearMap.charpoly_natDegree _
  rw [← p.eraseLead_add_C_mul_X_pow, Polynomial.aeval_add, Polynomial.aeval_eq_sum_range,
    add_eq_zero_iff_eq_neg'] at this
  simp only [hp₁, Polynomial.Monic.leadingCoeff, map_one, one_mul, map_pow,
    Polynomial.aeval_X] at this
  have hxm : x ^ m ≠ 0 := pow_ne_zero m hx₀
  apply_fun (· * (x ^ m) ^ (-n + 1 : ℤ)) at this
  rw [hpn, ← zpow_natCast, ← zpow_add' (.inl hxm), add_neg_cancel_left, zpow_one, neg_mul] at this
  have pel : p.eraseLead.natDegree + 1 ≤ n := by
    rw [← hpn]
    by_cases hnc : p.nextCoeff = 0
    · have := Polynomial.natDegree_eraseLead_le_of_nextCoeff_eq_zero hnc
      omega
    · exact (Polynomial.natDegree_eraseLead_add_one hnc).le
  rw [Finset.sum_mul] at this
  conv at this =>
    enter [2, 1, 2, i]
    rw [smul_mul_assoc, ← zpow_natCast, ← zpow_add' (.inl hxm)]
  refine (hm.trans_le ?_).false
  rw [this, v'.map_neg]
  have pel' : (p.eraseLead.natDegree + 1 : ℝ) ≤ n := mod_cast pel
  have help (N : ℕ) : (N + 1 : ℝ) = ∑ i ∈ Finset.range (N + 1), 1 := by simp
  refine (v'.sum_le ..).trans (LE.le.trans ?_ pel')
  conv_rhs => rw [help]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  simp only [Algebra.smul_def]
  rw [v'.map_mul, apply_algebraMap, h]
  rcases eq_or_ne (p.eraseLead.coeff i) 0 with H | H
  · simp [H]
  · simp only [ne_eq, H, not_false_eq_true, hv, map_zpow₀, AbsoluteValue.map_pow, one_mul]
    refine zpow_le_one_of_nonpos₀ (one_le_pow₀ hx.le) ?_
    simp only [Finset.mem_range] at hi
    omega

variable {F' : Type*} [Ring F'] [Algebra F F'] {v : AbsoluteValue F ℝ}

lemma algebraMap_withAbs_apply (v' : AbsoluteValue F' ℝ) (x : WithAbs v) :
    algebraMap (WithAbs v) (WithAbs v') x =
      (WithAbs.equiv v').symm (algebraMap F F' (WithAbs.equiv v x)) := by
  rw [← WithAbs.equiv_apply_algebraMap v', Equiv.symm_apply_apply]

variable [Nontrivial F']

@[simp]
lemma apply_algebraMap_withAbs {v' : AbsoluteValue F' ℝ} (h : v'.restrict F = v) (x : WithAbs v) :
    v' (WithAbs.equiv v' (algebraMap (WithAbs v) (WithAbs v') x)) = v (WithAbs.equiv v x) := by
  rw [WithAbs.equiv_apply_algebraMap, apply_algebraMap, h]

@[fun_prop]
lemma continuous_algebraMap {v' : AbsoluteValue F' ℝ} (h : v'.restrict F = v) :
    Continuous <| algebraMap (WithAbs v) (WithAbs v') := by
  rw [continuous_iff_continuous_dist]
  conv => enter [1, x]; simp only [algebraMap_withAbs_apply v']
  simp_rw [dist_eq_norm_sub, norm_eq_abv, WithAbs.equiv_sub, Equiv.apply_symm_apply, ← map_sub,
    apply_algebraMap, h, ← WithAbs.equiv_sub, ← norm_eq_abv, ← dist_eq_norm_sub]
  exact continuous_dist

instance continuousSMul {v' : AbsoluteValue F' ℝ} [Fact <| v'.restrict F = v] :
    ContinuousSMul (WithAbs v) (WithAbs v') where
  continuous_smul := (continuous_algebraMap_iff_smul _ _).mp <| continuous_algebraMap Fact.out

end restrict

/-!
### Two absolute values are equivalent iff they induce the same topology

This is Theorem 1.1 in Conrad's notes. We split the interesting direction (same topology
implies equivalence) into two steps:

* `AbsoluteValue.abv_lt_one_iff_of_isHomeomorph`: if `v₁` and `v₂` induce the same
  topology, then `{x | v₁ x < 1} = {x | v₂ x < 1}`.

* `AbsoluteValue.equiv_of_abv_lt_one_iff`: if `{x | v₁ x < 1} = {x | v₂ x < 1}`,
  then `v₁ ≈ v₂`.

The main result is `AbsoluteValue.equiv_iff_isHomeomorph`.
-/

section withAbs

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

variable {F : Type*} [Field F]

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

section equiv

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

variable {F : Type*} [Field F]

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
    rw [of_not_not <| (isNontrivial_iff_not_eq_trivial v₁).not.mp H₁,
      of_not_not <| (isNontrivial_iff_not_eq_trivial v₂).not.mp H₂]

open Filter Topology in
/-- Two absolute values on a field are equivalent if and only if they induce the same topology. -/
-- (This is Theorem 1.1 in the reference.)
lemma equiv_iff_isHomeomorph (v₁ v₂ : AbsoluteValue F ℝ) :
    v₁ ≈ v₂ ↔ IsHomeomorph (WithAbs.equiv₂ v₁ v₂) := by
  refine ⟨fun H ↦ ?_, fun H ↦ equiv_of_abv_lt_one_iff <| abv_lt_one_iff_of_isHomeomorph H⟩
  exact isHomeomorph_iff_exists_homeomorph.mpr
    ⟨homeomorph_of_equiv H, by simp [homeomorph_of_equiv]⟩

/- /-- Two absolute values on a field are equivalent if and only if they induce the same topology. -/
lemma equiv_iff_same_topology (v₁ v₂ : AbsoluteValue F ℝ) :
    v₁ ≈ v₂ ↔ v₁.topology = v₂.topology := by
  rw [equiv_iff_isHomeomorph, v₁.topology_eq_coinduced, v₂.topology_eq_coinduced, WithAbs.equiv₂,
   TopologicalSpace.isHomeomorph_iff_eq_coinduced]
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply_fun TopologicalSpace.coinduced (WithAbs.equiv v₂) at H
    rw [coinduced_compose, Equiv.coe_trans, ← Function.comp_assoc] at H
    simpa only [Equiv.self_comp_symm, CompTriple.comp_eq, Equiv.induced_symm] using H.symm
  · apply_fun TopologicalSpace.coinduced (WithAbs.equiv v₂).symm at H
    rw [coinduced_compose, coinduced_compose] at H
    simpa only [Equiv.symm_comp_self, coinduced_id] using H.symm -/

end equiv

end API

section complete

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
    map_add' := by simp
    map_smul' := by simp
    invFun := WithAbs.equiv₂ v₂ v₁
    left_inv x := by simp
    right_inv x := by simp
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

end complete

end AbsoluteValue
