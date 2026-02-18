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
lemma le_iSup_abv_nat (v : InfinitePlace K) (n : ℕ) (x : 𝓞 K) :
    n ≤ ⨆ i, v.val (![(n : K), x] i) := by
  refine Finite.le_ciSup_of_le 0 ?_
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero]
  rw [← v.coe_apply, ← v.norm_embedding_eq, map_natCast, Complex.norm_natCast]

lemma finite_setOf_prod_archAbsVal_nat_le {n : ℕ} (hn : n ≠ 0) {B : ℝ} :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v.val (![(n : K), x] i)) ^ v.mult ≤ B}.Finite := by
  have H (x : 𝓞 K) (h : ∏ v : InfinitePlace K, (⨆ i, v.val (![(n : K), x] i)) ^ v.mult ≤ B)
      (v : InfinitePlace K) : v.val x ≤ B / n ^ (totalWeight K - 1) := by
    classical
    have hn₁ : 1 ≤ n := by lia
    have hvm := v.mult_pos
    rw [← Finset.prod_erase_mul _ _ (mem_univ v), show v.mult = v.mult - 1 + 1 by lia, pow_succ,
      ← mul_assoc] at h
    have : v.val x ≤ ⨆ i, v.val (![(n : K), x] i) := Finite.le_ciSup_of_le 1 le_rfl
    grw [this]
    nth_rw 1 [le_div_iff₀' (mod_cast Nat.pow_pos hn₁)]
    refine (mul_le_mul_of_nonneg_right ?_ v.val.iSup_abv_nonneg).trans h
    have := Finset.prod_le_prod (s := Finset.univ.erase v) (f := fun v ↦ (n : ℝ) ^v.mult)
        (g := fun v ↦ (⨆ i, v.val (![(n : K), x] i)) ^ v.mult) (by simp) (fun v _ ↦ ?hle)
    case hle => simp only [Nat.succ_eq_add_one, Nat.reduceAdd]; grw [le_iSup_abv_nat v]
    grw [← this, ← le_iSup_abv_nat]
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

end Northcott

end NumberField
