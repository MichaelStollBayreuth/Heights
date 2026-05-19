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

section API

/-!
### API for Mathlib
-/

-- #39008

namespace IsAlgebraic

variable {Z : Type*} [CommRing Z] [IsDomain Z] (R : Type*) [CommRing R] {K : Type*} [Field K]
  [Algebra R K] [Algebra Z K] [IsIntegralClosure R Z K]

/-- If `x : K` is algebraic over some ring `Z`, then a nonzero `Z`-multiple of it is contained
in the integral closure of `Z` in `K`. -/
lemma exists_smul_eq {x : K} (hx : IsAlgebraic Z x) :
    ∃ (m : Z) (r : R), m ≠ 0 ∧ m • x = algebraMap R K r := by
  obtain ⟨m, hm, h⟩ := IsAlgebraic.iff_exists_smul_integral.mp hx
  obtain ⟨r, hr⟩ := IsIntegralClosure.isIntegral_iff (A := R) |>.mp h
  exact ⟨m, r, hm, hr.symm⟩

/-- If `x : K` is algebraic over `ℤ`, then a nonzero `ℕ`-multiple of it is contained in the
integral closure of `ℤ` in `K`. -/
lemma exists_nsmul_eq {x : K} [IsIntegralClosure R ℤ K] (hx : IsAlgebraic ℤ x) :
    ∃ (m : ℕ) (r : R), m ≠ 0 ∧ m • x = algebraMap R K r := by
  obtain ⟨a, r, ha, h⟩ := hx.exists_smul_eq R
  refine ⟨a.natAbs, a.sign * r, Int.natAbs_ne_zero.mpr ha, ?_⟩
  simp only [zsmul_eq_mul, nsmul_eq_mul, Nat.cast_natAbs, map_mul, map_intCast] at h ⊢
  rw [← h, ← mul_assoc]
  rw_mod_cast [Int.sign_mul_self_eq_abs a]

end IsAlgebraic

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R]

lemma asIdeal_injective : (fun v : HeightOneSpectrum R ↦ v.asIdeal).Injective :=
  fun ⦃_ _⦄ h ↦ HeightOneSpectrum.ext h

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField

open IsDedekindDomain HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

namespace FinitePlace

lemma finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ v : FinitePlace K, v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K))]
  simp only [show ∀ v : FinitePlace K, v.equivHeightOneSpectrum = v.maximalIdeal from fun _ ↦ rfl]
-- #find_home! finprod_finitePlace_pow_multiplicity -- [Mathlib.NumberTheory.NumberField.Completion.FinitePlace]

open Ideal in
lemma apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x ≠ 0) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (span {x}) = 1 := by
  have hnz : span {x} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x, ← Nat.cast_pow, ← map_pow,
    ← maxPowDividing_eq_pow_multiplicity hnz v.maximalIdeal]
  exact HeightOneSpectrum.embedding_mul_absNorm K v.maximalIdeal hx
-- #find_home! FinitePlace.apply_mul_absNorm_pow_eq_one -- [Mathlib.NumberTheory.NumberField.Completion.FinitePlace]

open UniqueFactorizationMonoid IsDedekindDomain.HeightOneSpectrum in
lemma hasFiniteMulSupport_fun_pow_multiplicity {M : Type*} [CommMonoid M] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (f : Ideal (𝓞 K) → M) :
    (fun v : FinitePlace K ↦
      (f v.maximalIdeal.asIdeal) ^ multiplicity v.maximalIdeal.asIdeal I).HasFiniteMulSupport := by
  simp only [← count_normalizedFactors_eq_multiplicity hI]
  exact Multiset.hasFiniteMulSupport_fun_pow_count (normalizedFactors I) f
    |>.fun_comp_of_injective  <| asIdeal_injective.comp maximalIdeal_injective

end NumberField.FinitePlace

-- end #39008

end API

-- #39127

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

-- set_option Elab.async false in
-- #count_heartbeats in -- 13486
open IsDedekindDomain.HeightOneSpectrum Ideal UniqueFactorizationMonoid FinitePlace Finite in
/-- This statement is equivalent to the fact that the "finite part" of the multiplicative
height of a (non-zero) tuple `x` is the inverse of the absolute norm of the ideal generated
by the values of `x`. We state it in a way that avoids taking an inverse. -/
lemma absNorm_mul_finprod_finitePlace_eq_one {ι : Type*} [Finite ι] {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_def] at hi₀
  let i' : { j // (x j : K) ≠ 0 } := ⟨i₀, mod_cast hi₀⟩
  have hI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) ≠ 0 } ↦ x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  have hx₀ : (fun i ↦ (x i : K)) ≠ 0 := Function.ne_iff.mpr ⟨i', i'.prop⟩
  simp_rw [coe_apply, iSup_eq_iSup_subtype hx₀, hI]
  have : Nonempty _ := .intro i'
  have Hj (j : { j // (x j : K) ≠ 0 }) : x j.val ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mp j.prop
  have H (j : { j // (x j : K) ≠ 0 }) : span {x ↑j} ≠ ⊥ := mt span_singleton_eq_bot.mp <| Hj j
  have hxι' : ⨆ i : { j // (x j : K) ≠ 0 }, span {x i.val} ≠ ⊥ := by
    rw [Ne, iSup_eq_bot, not_forall]
    exact ⟨i', H i'⟩
  rw [span_range_eq_iSup, ← finprod_finitePlace_pow_multiplicity hxι',
    map_finprod _ <| hasFiniteMulSupport_fun_pow_multiplicity hxι' (·), Nat.cast_finprod',
    ← finprod_mul_distrib ?hf ?hg]
  case hf =>
    simp only [map_pow, Nat.cast_pow]
    exact hasFiniteMulSupport_fun_pow_multiplicity hxι' fun v ↦ (v.absNorm : ℝ)
  case hg => exact .iSup fun j ↦ hasFiniteMulSupport j.prop
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  have hn := mt absNorm_eq_zero_iff.mp v.maximalIdeal.ne_bot
  have h {m : ℕ} : (0 : ℝ) < ↑(absNorm v.maximalIdeal.asIdeal ^ m) := mod_cast Nat.pow_pos <| by lia
  rw [multiplicity_iSup _ H, map_pow, mul_eq_one_iff_inv_eq₀ h.ne',
    map_iInf_of_monotone (fun _ ↦ multiplicity ..) (pow_right_monotone <| by lia),
    map_iInf_of_monotone _ Nat.mono_cast,
    map_iInf_of_antitoneOn antitoneOn_inv_pos fun _ ↦ Set.mem_setOf.mpr h]
  refine iSup_congr fun i ↦ ?_
  rw [← mul_eq_one_iff_inv_eq₀ h.ne', mul_comm, Nat.cast_pow]
  exact apply_mul_absNorm_pow_eq_one v <| Function.mem_support.mp <| Hj i

end NumberField

-- end #39127

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
      (g := fun v ↦ _ ^ v.mult) (by simp) (fun v _ ↦ by simp only; grw [hv v])
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
