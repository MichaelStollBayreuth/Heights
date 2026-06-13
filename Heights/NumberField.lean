import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Heights.MvPolynomial

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and prove some properties.
-/

/-!
### The Northcott property for heights on number fields

We shoe that a number field `K` has the **Northcott property** with respect to the multiplicative
and with respect to the logarithmic height, i.e., for any `B : ℝ` the set of elements `x : K`
such that `mulHeight₁ x ≤ B` (resp., `logHeight₁ x ≤ B`) is finite.
See `NumberField.finite_setOf_mulHeight₁_le` and `NumberField.finite_setOf_logHeight₁_le`.

The main idea of the proof is as follows. We show that for every `x : K` there is `n : ℕ` such that
`n * x` is an algebraic integer and `n ≤ mulHeight₁ x`; see `NumberField.exists_nat_le_mulHeight₁`.
We also show that the set of `a : 𝓞 K` such that `mulHeight₁ (a / n)` is bounded is finite;
see `NumberField.finite_setOf_prod_infinitePlace_iSup_le`. The result for the multiplicative height
follows by combining these two ingredients, and the result for the logarithmic height follows
from that for any field with a family of admissible absolute values.
-/

section Northcott

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section withIdeal

open Ideal

private lemma relIndex_span_span_nat_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n * m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(n * m), n * a}).toAddSubgroup := by
  let f : 𝓞 K →ₗ[𝓞 K] 𝓞 K := .mulLeft _ n
  have hf : Function.Injective (f : 𝓞 K →+ 𝓞 K) :=
    (injective_iff_map_eq_zero f).mpr fun _ _ ↦ by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {↑m}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} = Submodule.map f (span {↑m, a}) := by
    simp [LinearMap.map_span, f, Set.image_pair]
  rw [H₁, H₂]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf |>.symm

private lemma relIndex_span_span_eq_relIndex_span_span {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {a b : 𝓞 K} (h : n * a = m * b) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, b}).toAddSubgroup := by
  refine (relIndex_span_span_nat_mul m hn a).trans ?_
  rw [mul_comm, mul_comm n, h]
  exact (relIndex_span_span_nat_mul n hm b).symm

open Module AddSubgroup LinearMap in
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ _ _ |>.mpr (.of_finite ℚ x)
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  rw [← RingOfIntegers.coe_eq_algebraMap r] at hmr
  have hI : (span {(m : 𝓞 K)}).toAddSubgroup ≤ (span {(m : 𝓞 K), r}).toAddSubgroup :=
    Submodule.toAddSubgroup_mono <| span_mono <| by grind
  set n := (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {(m : 𝓞 K), r}).toAddSubgroup with hndef
  have hn : n ≠ 0 := isFiniteRelIndex (by simp [hm]) _ |>.relIndex_ne_zero
  obtain ⟨a, ha'⟩ : ∃ a, m * a = n * r := by
    have : n • r ∈ span {(m : 𝓞 K)} :=
      (span {(m : 𝓞 K)}).toAddSubgroup.nsmul_relIndex_mem <| Submodule.mem_span_of_mem <| by grind
    simpa [mem_span_singleton', mul_comm] using this
  have ha : n * x = a := by
    refine mul_left_cancel₀ (mod_cast hm : (m : K) ≠ 0) ?_
    rw [mul_left_comm, ← nsmul_eq_mul m, hmr]
    exact_mod_cast ha'.symm
  refine ⟨n, hn, a, ha, mul_left_cancel₀ hn ?_⟩
  nth_rewrite 1 [hndef]
  rw [absNorm_eq_index, ← pow_succ',
    show finrank ℚ K - 1 + 1 = finrank ℚ K by grind [finrank_pos], ← RingOfIntegers.rank,
    ← absNorm_span_natCast, absNorm_eq_index, ← relIndex_span_span_eq_relIndex_span_span hn hm ha']
  exact relIndex_mul_index <| Submodule.toAddSubgroup_mono <| span_mono <| by grind

open Height in
private lemma one_le_pow_totalWeight_mul_finprod {n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    1 ≤ (n ^ totalWeight K : ℝ) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![↑a, ↑n] i) := by
  have Hw : (0 : ℝ) < n ^ totalWeight K := by positivity
  have := absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])
  have H (i : Fin 2) : (![a, ↑n] i : K) = ![(a : K), n] i := by fin_cases i <;> simp
  simp_rw [H] at this; clear H
  rw [← this, ← Nat.cast_pow]; clear this
  gcongr
  · -- nonnegativity side goal
    exact finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  rw_mod_cast [totalWeight_eq_finrank, ← RingOfIntegers.rank, ← absNorm_span_natCast] at Hw ⊢
  exact Nat.le_of_dvd Hw <| absNorm_dvd_absNorm_of_le <| span_mono <| by simp

end withIdeal

open Height

section withFinset

open Finset

/-- If `x : K` (for a number field `K`), then we can find a nonzero `n : ℕ` such that
`n ≤ mulHeight₁ x` and `n * x` is integral. I.e., the denominator of `x` can be bounded by
its multplicative height. -/
lemma exists_nat_le_mulHeight₁ (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ n ≤ mulHeight₁ x ∧ IsIntegral ℤ (n * x) := by
  obtain ⟨n, hn, a, ha₁, ha₂⟩ := exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
  rw [← totalWeight_eq_finrank] at ha₂
  have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
  rw [← mul_div_cancel_left₀ x (mod_cast hn : (n : K) ≠ 0), ha₁, mulHeight₁_div_eq_mulHeight,
    mulHeight_eq (by simp [hn])]
  refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < n ^ (totalWeight K - 1) by positivity)
  have : n ^ (totalWeight K - 1) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![(a : K), n] i) = 1 := by
    simpa [ha₂, hv] using absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])
  rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_left_comm, this,
    mul_one, totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum univ]
  refine prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ ?_
  gcongr
  exact Finite.le_ciSup_of_le 1 <| by simp

private lemma infinitePlace_apply_le_of_prod_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) {x : 𝓞 K}
    (h : ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B) (v : InfinitePlace K) :
    v x ≤ B / n ^ (totalWeight K - 1) := by
  classical
  have hvm : v.mult = v.mult - 1 + 1 := by have := v.mult_pos; lia
  have hv (v : InfinitePlace K) : n ≤ ⨆ i, v (![(x : K), n] i) := Finite.le_ciSup_of_le 1 <| by simp
  rw [← prod_erase_mul _ _ (mem_univ v), hvm, pow_succ, ← mul_assoc] at h
  have : v x ≤ ⨆ i, v (![(x : K), n] i) := Finite.le_ciSup_of_le 0 le_rfl
  grw [this, le_div_iff₀' (by positivity)]; clear this
  refine (mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg_of_nonnegHomClass ..)).trans h
  have := prod_le_prod (s := univ.erase v) (f := fun v ↦ (n : ℝ) ^ v.mult)
      (g := fun v ↦ _ ^ v.mult) (by simp) (fun v _ ↦ by grw [hv v])
  grw [← this, ← hv v]
  · refine (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) from mod_cast hn.pos)).mp ?_
    rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_assoc, ← pow_succ,
      ← hvm, prod_erase_mul _ _ (mem_univ v), prod_pow_eq_pow_sum, totalWeight_eq_sum_mult]
  · -- nonnegativity side goal
    exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _

end withFinset

lemma finite_setOf_prod_infinitePlace_iSup_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B}.Finite := by
  set B' := B / n ^ (totalWeight K - 1)
  have H' : Set.BijOn ((↑) : 𝓞 K → K) {x | ∀ (v : InfinitePlace K), v x ≤ B'}
      {x | IsIntegral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ B'} := by
    refine .mk (fun x hx ↦ ?_) (fun _ _ _ _ ↦ RingOfIntegers.ext) fun a ha ↦ ?_ <;>
      simp only [Set.mem_image, Set.mem_setOf_eq] at *
    · exact ⟨x.isIntegral_coe, fun φ ↦ hx <| .mk φ⟩
    · rw [← mem_integralClosure_iff ℤ K] at ha
      exact ⟨⟨a, ha.1⟩, fun v ↦ v.norm_embedding_eq a ▸ ha.2 v.embedding, rfl⟩
  exact H'.finite_iff_finite.mpr (Embeddings.finite_of_norm_le K ℂ B') |>.subset
    fun _ _ ↦ by grind [infinitePlace_apply_le_of_prod_le hn B]

/-- The set of `a : 𝓞 K` such that `mulHeight₁ (a / n) = mulHeight ![a, n]` is bounded
(for some given nonzero `n : ℕ`) is finite. -/
lemma finite_setOf_mulHeight_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B}.Finite := by
  have H : {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B} ⊆
      {a | ∏ v : InfinitePlace K, (⨆ i, v (![(a : K), n] i)) ^ v.mult ≤
        n ^ totalWeight K * B} := by
    refine Set.setOf_subset_setOf_of_imp fun a ha ↦ ?_
    rw [mulHeight_eq <| by simp [hn], mul_comm] at ha
    grw [← ha, ← mul_assoc, ← one_le_pow_totalWeight_mul_finprod hn, one_mul]
    -- nonnegativity side goal
    exact Finset.prod_nonneg fun _ _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _
  exact (finite_setOf_prod_infinitePlace_iSup_le hn _).subset H

variable (K) in
/-- The set of `x : K` such that `mulHeight₁ x` is bounded and `n * x` is integral
(for some given nonzero `n : ℕ`) is finite. -/
lemma finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : K | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B}.Finite := by
  have hn' : (n : K) ≠ 0 := mod_cast hn
  have H : Set.BijOn (fun a : 𝓞 K ↦ (a / n : K)) {a | mulHeight ![(a : K), n] ≤ B}
      {x | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B} := by
    refine .mk (fun a ha ↦ ?_) (fun a _ b _ h ↦ ?_) fun x ⟨hx₁, hx₂⟩ ↦ ?_
    · simp only [Set.mem_setOf_eq] at ha ⊢
      rw [mul_div_cancel₀ (a : K) hn', mulHeight₁_div_eq_mulHeight]
      exact ⟨a.isIntegral_coe, ha⟩
    · rwa [div_left_inj' hn', RingOfIntegers.eq_iff] at h
    · simp only [Set.mem_setOf_eq, Set.mem_image]
      obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, n * x = a := ⟨⟨_, hx₁⟩, rfl⟩
      refine ⟨a, ?_, (EuclideanDomain.eq_div_of_mul_eq_right hn' ha).symm⟩
      rwa [← ha, ← mulHeight₁_div_eq_mulHeight, mul_div_cancel_left₀ x hn']
  exact H.finite_iff_finite.mp <| finite_setOf_mulHeight_nat_le hn B

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded multiplicative height is finite. -/
theorem finite_setOf_mulHeight₁_le (B : ℝ) : {x : K | mulHeight₁ x ≤ B}.Finite := by
  rcases lt_or_ge B 0 with hB | hB
  · rw [show {x : K | mulHeight₁ x ≤ B} = ∅ by grind [mulHeight₁_pos]]
    exact Set.finite_empty
  have H : {x : K | mulHeight₁ x ≤ B} =
      ⋃ n : Fin ⌊B⌋₊, {x : K | IsIntegral ℤ ((n + 1) * x) ∧ mulHeight₁ x ≤ B} := by
    ext x : 1
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun h ↦ ⟨⟨n - 1, by grind [Nat.le_floor <| hn₁.trans h]⟩, ?_⟩
    rwa [← Nat.cast_add_one, Nat.sub_one_add_one hn₀]
  rw [H]
  exact Set.finite_iUnion fun n ↦
    mod_cast finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le K (Nat.zero_ne_add_one n).symm B

instance : Northcott (mulHeight₁ (K := K)) where
  finite_le := finite_setOf_mulHeight₁_le K

end NumberField

open Height Real Northcott

variable {K : Type*} [Field K]

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded logarithmic height is finite. -/
theorem NumberField.finite_setOf_logHeight₁_le [NumberField K] (B : ℝ) :
    {x : K | logHeight₁ x ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott
