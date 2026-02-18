import Mathlib.NumberTheory.Height.NumberField
import Heights.Basic
/-!
# Instances of AdmissibleAbsValues

We provide instances of `Height.AdmissibleAbsValues` for

* algebraic number fields.

## TODO

* Fields of rational functions in `n` variables.

* Finite extensions of fields with `Height.AdmissibleAbsValues`.

-/

/-!
### Instance for number fields
-/

namespace NumberField

open Height Finset Multiset

variable {K : Type*} [Field K]

variable  [NumberField K]

open AdmissibleAbsValues

lemma sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val := by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (fun w hw ↦ ⟨w, mem_multisetInfinitePlace.mp <| mem_dedup.mp hw⟩)
    (fun v _ ↦ v.val) (fun _ _ ↦ mem_univ _) (fun v _ ↦ by simp [v.isInfinitePlace, archAbsVal])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun w hw ↦ by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace] at hw ⊢
      simp [count_multisetInfinitePlace_eq_mult ⟨w, hw⟩]

lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl

variable (K) in
lemma totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult := by
  simp only [totalWeight]
  convert sum_archAbsVal_eq (fun _ ↦ (1 : ℕ))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

variable (K) in
lemma totalWeight_eq_finrank : totalWeight K = Module.finrank ℚ K := by
  rw [totalWeight_eq_sum_mult, InfinitePlace.sum_mult_eq]

variable (K) in
lemma totalWeight_pos : 0 < totalWeight K := by
  simp [totalWeight, archAbsVal, multisetInfinitePlace]
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  exact Fintype.sum_pos <| NE.ne.pos <|
    Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩

open Real in
-- For the next PR
/-- This is the familiar definition of the logarithmic height on a number field. -/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v ↦ log⁺ (v x)]

-- Towards Northcott

section Northcott

variable {ι : Type*} [Finite ι]

open IsDedekindDomain RingOfIntegers.HeightOneSpectrum

/-
lemma FinitePlace.apply_eq_adicAbv_maximalIdeal_apply (v : FinitePlace K) (x : K) :
    v x = (adicAbv v.maximalIdeal) x := by
  rw [← FinitePlace.norm_def]
  exact (v.norm_embedding_eq x).symm

lemma abv_apply_eq_norm_inv_pow_multiplicity (v : FinitePlace K) (x : 𝓞 K) :
    v x = ((v.maximalIdeal.asIdeal.absNorm : ℝ)⁻¹) ^ multiplicity v.maximalIdeal.asIdeal (Ideal.span {x}) := by
  rw [v.apply_eq_adicAbv_maximalIdeal_apply, adicAbv, HeightOneSpectrum.adicAbv]
  simp only [AbsoluteValue.coe_mk, MulHom.coe_mk, inv_pow]
  generalize v.maximalIdeal = P
  simp only [HeightOneSpectrum.adicAbvDef, HeightOneSpectrum.valuation]
  -- ?
  sorry

lemma natCast_ciSup [Nonempty ι] (f : ι → ℕ) : ((⨆ i, f i :) : ℝ) = ⨆ i, (f i : ℝ) := by
  refine Monotone.map_ciSup_of_continuousAt ?_ Nat.mono_cast <| Finite.bddAbove_range f
  exact Continuous.continuousAt <| by fun_prop

-- set_option maxHeartbeats 0 in
lemma iSup_abv_eq_multiplicity (v : FinitePlace K) {x : ι → 𝓞 K} (hx : x ≠ 0) :
    ⨆ i, v (x i) = multiplicity v.maximalIdeal.asIdeal (Ideal.span <| Set.range x) := by
  have : Nonempty ι := .intro (Function.ne_iff.mp hx).choose
  simp only [abv_apply_eq_norm_inv_pow_multiplicity]

  sorry
-/

omit [NumberField K] in
lemma InfinitePlace.le_iSup_abv_nat (v : InfinitePlace K) (n : ℕ) (x : 𝓞 K) :
    n ≤ ⨆ i, v.val (![(x : K), n] i) := by
  refine Finite.le_ciSup_of_le 1 ?_
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← v.coe_apply, ← v.norm_embedding_eq, map_natCast, Complex.norm_natCast]

lemma absNorm_mul_finprod_nonarchAbsVal_eq_one {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (Ideal.span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v.val (x i) = 1 := by
  sorry

lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  -- Maybe state this right away for `n = absNorm D`, where `D` is the "denominator ideal"
  -- of `x` (which, however, is not yet defined in Mathlib).
  -- An alternative definition of `n` is as the index of `𝓞 K` in `𝓞 K + 𝓞 K • x`.
  sorry

lemma exists_nat_le_mulHeight₁ (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ n ≤ mulHeight₁ x ∧ IsIntegral ℤ (n * x) := by
  suffices ∃ n : ℕ, n ≠ 0 ∧
      ∃ a : 𝓞 K, n * x = a ∧ (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (totalWeight K - 1) by
    obtain ⟨n, hn, a, ha₁, ha₂⟩ := this
    refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
    have han : ![a, n] ≠ 0 := by simp [hn]
    have hv (v : FinitePlace K) (i : Fin 2) : v.val (![a, n] i : K) = v (![(a : K), n] i) := by
      fin_cases i <;> rfl
    have := absNorm_mul_finprod_nonarchAbsVal_eq_one han
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, ha₂, hv] at this
    push_cast at this
    have hx : mulHeight₁ x = mulHeight ![(a : K), n] := by
      rw [← mulHeight₁_div_eq_mulHeight (a : K) n, ← ha₁, mul_div_cancel_left₀ x (mod_cast hn)]
    rw [hx, mulHeight_eq (by simp [hn])]
    have hw : (0 : ℝ) < n ^ (totalWeight K - 1) := by positivity
    refine le_of_mul_le_mul_left ?_ hw
    rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind [totalWeight_pos],
      mul_left_comm, this, mul_one, totalWeight_eq_sum_mult]
    rw [← prod_pow_eq_pow_sum univ]
    refine prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ ?_
    gcongr
    exact InfinitePlace.le_iSup_abv_nat v n a
  rw [totalWeight_eq_finrank]
  exact exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x

lemma finite_setOf_prod_archAbsVal_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v.val (![(x : K), n] i)) ^ v.mult ≤ B}.Finite := by
  have H (x : 𝓞 K) (h : ∏ v : InfinitePlace K, (⨆ i, v.val (![(x : K), n] i)) ^ v.mult ≤ B)
      (v : InfinitePlace K) :
      v.val x ≤ B / n ^ (totalWeight K - 1) := by
    classical
    have hn₁ : 1 ≤ n := by lia
    have hvm := v.mult_pos
    rw [← Finset.prod_erase_mul _ _ (mem_univ v), show v.mult = v.mult - 1 + 1 by lia, pow_succ,
      ← mul_assoc] at h
    have : v.val x ≤ ⨆ i, v.val (![(x : K), n] i) := Finite.le_ciSup_of_le 0 le_rfl
    grw [this]
    nth_rw 1 [le_div_iff₀' (mod_cast Nat.pow_pos hn₁)]
    refine (mul_le_mul_of_nonneg_right ?_ v.val.iSup_abv_nonneg).trans h
    have := Finset.prod_le_prod (s := Finset.univ.erase v) (f := fun v ↦ (n : ℝ) ^v.mult)
        (g := fun v ↦ (⨆ i, v.val (![(x : K), n] i)) ^ v.mult) (by simp) (fun v _ ↦ ?hle)
    case hle => simp only [Nat.succ_eq_add_one, Nat.reduceAdd]; grw [v.le_iSup_abv_nat]
    grw [← this, ← v.le_iSup_abv_nat]
    · refine (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) by norm_cast)).mp ?_
      rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind [totalWeight_pos],
        mul_assoc, ← pow_succ, show v.mult - 1 + 1 = v.mult by lia,
        Finset.prod_erase_mul _ _ (mem_univ v), prod_pow_eq_pow_sum univ InfinitePlace.mult]
      exact (congrArg (fun a ↦ (n : ℝ) ^ a) <| totalWeight_eq_sum_mult K).le
    · exact pow_nonneg v.val.iSup_abv_nonneg _
  set B' := B / n ^ (totalWeight K - 1)
  refine Set.Finite.subset (s := {x : 𝓞 K | ∀ v : InfinitePlace K, v.val x ≤ B'}) ?_
    fun x hx ↦ by grind
  have H₁ := Embeddings.finite_of_norm_le K ℂ B'
  let f : 𝓞 K → K := (↑)
  have H₂ : Set.BijOn ((↑) : 𝓞 K → K) {x | ∀ (v : InfinitePlace K), v.val x ≤ B'}
      {x | IsIntegral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ B'} := by
    refine Set.BijOn.mk (fun x hx ↦ ?_) (fun x₁ _ x₂ _ ↦ RingOfIntegers.eq_iff.mp) ?_
    · simp only [Set.mem_setOf_eq] at hx ⊢
      exact ⟨x.isIntegral_coe, fun φ ↦ hx <| InfinitePlace.mk φ⟩
    · intro a ha
      simp only [Set.mem_setOf_eq] at ha ⊢
      simp only [Set.mem_image, Set.mem_setOf_eq]
      rw [← mem_integralClosure_iff ℤ K] at ha
      refine ⟨⟨a, ha.1⟩, fun v ↦ ?_, rfl⟩
      convert ha.2 v.embedding
      rw [InfinitePlace.norm_embedding_eq v a]
      rfl
  rwa [Set.BijOn.finite_iff_finite H₂]

lemma finite_setOf_mulHeight_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B}.Finite := by
  have H₀ (a : 𝓞 K) : ![(a : K), n] ≠ 0 := by simp [hn]
  have Hw : (0 : ℝ) < n ^ totalWeight K := pow_pos (by norm_cast; lia) _
  have H₁ (a : 𝓞 K) :
      (n ^ totalWeight K : ℝ)⁻¹ ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (![(a : K), n] i) := by
    let z : Fin 2 → 𝓞 K := ![a, n]
    have han : ![a, n] ≠ 0 := by simp [hn]
    have := absNorm_mul_finprod_nonarchAbsVal_eq_one han
    have Hnorm : (0 : ℝ) < (Ideal.absNorm (Ideal.span (Set.range ![a, n]))) := by
      norm_cast
      refine Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr ?_
      rw [mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot, Submodule.ne_bot_iff]
      exact ⟨n, by simpa using Ideal.mem_span_pair.mpr ⟨1, 0, by simp⟩, mod_cast hn⟩
    rw [mul_eq_one_iff_inv_eq₀ Hnorm.ne'] at this
    have HH (v : FinitePlace K) (i : Fin 2) : v.val (![a, ↑n] i).val = v (![(a : K), n] i) := by
      have (x : K) : v.val x = v x := rfl
      fin_cases i <;> simp [this]
    simp only [HH] at this
    rw [← this]
    nth_rw 1 [inv_le_inv₀ Hw Hnorm]
    norm_cast
    have := Ideal.absNorm_span_singleton (n : 𝓞 K)
    rw [Algebra.norm_apply ℤ (n : 𝓞 K)] at this
    have H₃ : (Algebra.lmul ℤ (𝓞 K)) n = (n : ℤ) • LinearMap.id := by ext1; simp
    rw [H₃, LinearMap.det_smul, LinearMap.det_id] at this
    simp only [mul_one, Int.natAbs_pow, Int.natAbs_natCast] at this
    rw [RingOfIntegers.rank, ← totalWeight_eq_finrank] at this
    rw [← this]
    exact Nat.le_of_dvd (this ▸ mod_cast Hw) <|
      Ideal.absNorm_dvd_absNorm_of_le <| Ideal.span_mono <| by simp +contextual
  have H₂ : {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B} ⊆
      {a : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v.val (![(a : K), n] i)) ^ v.mult ≤
        n ^ totalWeight K * B} := by
    intro a ha
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_setOf_eq] at ha ⊢
    rw [mulHeight_eq (H₀ a)] at ha
    grw [← H₁] at ha
    · exact (div_le_iff₀' Hw).mp ha
    · -- nonnegativity side goal from `grw`
      exact Finset.prod_nonneg fun v _ ↦ pow_nonneg v.val.iSup_abv_nonneg _
  exact (finite_setOf_prod_archAbsVal_nat_le hn _).subset H₂

variable (K) in
lemma finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : K | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B}.Finite := by
  let f (a : 𝓞 K) : K := a / n
  have H : Set.BijOn f {a | mulHeight ![(a : K), n] ≤ B}
      {x | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B} := by
    refine Set.BijOn.mk (fun a ha ↦ ?_) (fun a _ b _ h ↦ ?_) fun x ⟨hx₁, hx₂⟩ ↦ ?_
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_setOf_eq, f] at ha ⊢
      rw [mul_div_cancel₀ (a : K) (mod_cast hn), mulHeight₁_div_eq_mulHeight (a : K) n]
      exact ⟨a.isIntegral_coe, ha⟩
    · simp [f] at h
      rw [div_left_inj' (mod_cast hn)] at h
      exact_mod_cast h
    · simp only [Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_image]
      obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, n * x = a := ⟨⟨n * x, hx₁⟩, rfl⟩
      refine ⟨a, ?_, ?_⟩
      · rwa [← ha, ← mulHeight₁_div_eq_mulHeight (↑n * x) ↑n, mul_div_cancel_left₀ x (mod_cast hn)]
      · simpa only [f, ← ha] using mul_div_cancel_left₀ x (mod_cast hn)
  exact H.finite_iff_finite.mp <| finite_setOf_mulHeight_nat_le hn B

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded multiplicative height is finite. -/
theorem finite_setOf_mulHeight₁_le (B : ℝ) : {x : K | mulHeight₁ x ≤ B}.Finite := by
  rcases lt_or_ge B 0 with hB | hB
  · convert Set.finite_empty
    refine Set.eq_empty_of_forall_notMem fun x ↦ ?_
    simp only [Set.mem_setOf_eq, not_le]
    grw [hB]
    positivity
  have H₁ : {x : K | mulHeight₁ x ≤ B} =
      ⋃ n : Fin (⌊B⌋₊), {x : K | IsIntegral ℤ ((n + 1) * x) ∧ mulHeight₁ x ≤ B} := by
    ext1 x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    refine fun h ↦ ⟨⟨n - 1, by grind [Nat.le_floor <| hn₁.trans h]⟩, ?_⟩
    rw [← Nat.cast_add_one]
    convert hn
    grind
  rw [H₁]
  exact Set.finite_iUnion fun n ↦
    mod_cast finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le  K (Nat.zero_ne_add_one ↑n).symm B

open Real in
variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded logarithmic height is finite. -/
theorem finite_setOf_logHeight₁_le (B : ℝ) : {x : K | logHeight₁ x ≤ B}.Finite := by
  have := finite_setOf_mulHeight₁_le K (exp B)
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_exp B]
  convert this using 3 with x
  refine log_le_log_iff ?_ ?_ <;> positivity

end Northcott

end NumberField
