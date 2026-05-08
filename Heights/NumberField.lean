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

-- #38654

section API

/-!
### API for Mathlib
-/

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R]

/-!
### Conversion between various multplicities
-/

variable [IsDedekindDomain R]

open UniqueFactorizationMonoid in
/-- Normalize multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
lemma count_normalizedFactors_eq_multiplicity [DecidableEq (Ideal R)] {I : Ideal R} (hI : I ≠ ⊥)
    (p : HeightOneSpectrum R) :
    Multiset.count p.asIdeal (normalizedFactors I) = multiplicity p.asIdeal I := by
  have := emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  rw [normalize_eq p.asIdeal] at this
  apply_fun ((↑) : ℕ → ℕ∞) using CharZero.cast_injective
  rw [← this]
  exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity

/-- Normalize multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
lemma maxPowDividing_eq_pow_multiplicity {I : Ideal R} (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    p.maxPowDividing I = p.asIdeal ^ multiplicity p.asIdeal I := by
  classical
  rw [maxPowDividing_eq_pow_multiset_count _ hI, count_normalizedFactors_eq_multiplicity hI]

/-- Normalize multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
lemma factorization_eq_multiplicity {I : Ideal R} (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    factorization I p.asIdeal = multiplicity p.asIdeal I := by
  rw [factorization_eq_count, count_normalizedFactors_eq_multiplicity hI]

/-!
---
-/

lemma _root_.Ideal.finprod_heightOneSpectrum_pow_multiplicity {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ᶠ p : HeightOneSpectrum R, p.asIdeal ^ multiplicity p.asIdeal I = I := by
  simpa only [maxPowDividing_eq_pow_multiplicity hI]
    using Ideal.finprod_heightOneSpectrum_factorization hI
-- #find_home! Ideal.finprod_heightOneSpectrum_pow_multiplicity -- [Mathlib.RingTheory.DedekindDomain.Factorization]

lemma multiplicity_le_of_ideal_ge (p : HeightOneSpectrum R) {I J : Ideal R} (h : J ≤ I)
    (hJ : J ≠ ⊥) :
    multiplicity p.asIdeal I ≤ multiplicity p.asIdeal J := by
  classical
  rw [← count_normalizedFactors_eq_multiplicity hJ,
    ← count_normalizedFactors_eq_multiplicity <| ne_bot_of_le_ne_bot hJ h]
  exact Ideal.count_le_of_ideal_ge h hJ _

open UniqueFactorizationMonoid Multiset in
lemma multiplicity_sup (p : HeightOneSpectrum R) {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    multiplicity p.asIdeal (I ⊔ J) = multiplicity p.asIdeal I ⊓ multiplicity p.asIdeal J := by
  classical
  rw [Ideal.sup_eq_prod_inf_factors hI hJ, ← count_normalizedFactors_eq_multiplicity ?h,
    ← count_normalizedFactors_eq_multiplicity hI, ← count_normalizedFactors_eq_multiplicity hJ]
  -- extracted from the proof of `sup_eq_prod_inf_factors`
  -- (which should really not be in the root namespace!)
  --   ==> refactor that (Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas)
  case h =>
    exact prod_ne_zero_of_prime _
      fun _ h ↦ prime_of_normalized_factor _ (mem_inter.mp h).1
  have H : normalizedFactors (normalizedFactors I ∩ normalizedFactors J).prod =
      normalizedFactors I ∩ normalizedFactors J := by
    refine normalizedFactors_prod_of_prime fun p hp ↦ ?_
    rw [mem_inter] at hp
    exact prime_of_normalized_factor p hp.left
  rw [H]
  exact count_inter ..

lemma emultiplicity_sup (p : HeightOneSpectrum R) (I J : Ideal R) :
    emultiplicity p.asIdeal (I ⊔ J) = emultiplicity p.asIdeal I ⊓ emultiplicity p.asIdeal J := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [bot_eq_zero, emultiplicity_zero]
    simp
  rcases eq_or_ne J ⊥ with rfl | hJ
  · rw [bot_eq_zero, emultiplicity_zero]
    simp
  have : I ⊔ J ≠ ⊥ := by grind
  have H {I' : Ideal R} (h : I' ≠ ⊥) : FiniteMultiplicity p.asIdeal I' :=
    FiniteMultiplicity.of_prime_left (prime p) h
  rw [(H this).emultiplicity_eq_multiplicity, (H hI).emultiplicity_eq_multiplicity,
    (H hJ).emultiplicity_eq_multiplicity, multiplicity_sup _ hI hJ]
  norm_cast

lemma emultiplicity_iSup {ι : Type*} [Finite ι] (p : HeightOneSpectrum R) (I : ι → Ideal R) :
    emultiplicity p.asIdeal (⨆ i, I i) = ⨅ i, emultiplicity p.asIdeal (I i) := by
  induction ι using Finite.induction_empty_option with
  | h_empty =>
    rw [iSup_of_empty, iInf_of_empty]
    exact emultiplicity_zero _
  | of_equiv e ih =>
    specialize @ih (I ∘ e)
    rw [← sSup_range, ← sInf_range] at ih ⊢
    rw [EquivLike.range_comp I e] at ih
    rw [ih, ← EquivLike.range_comp (fun i ↦ emultiplicity p.asIdeal (I i)) e]
    rfl
  | h_option ih =>
    rw [iSup_option, emultiplicity_sup p .., ih, iInf_option]

lemma multiplicity_iSup {ι : Type*} [Finite ι] [Nonempty ι] (p : HeightOneSpectrum R)
    {I : ι → Ideal R} (hI : ∀ i, I i ≠ ⊥) :
    multiplicity p.asIdeal (⨆ i, I i) = ⨅ i, multiplicity p.asIdeal (I i) := by
  have H i : FiniteMultiplicity p.asIdeal (I i) :=
    FiniteMultiplicity.of_prime_left (prime p) <| hI i
  have H' : FiniteMultiplicity p.asIdeal (⨆ i, I i) := by
    refine FiniteMultiplicity.of_prime_left (prime p) ?_
    contrapose! hI
    rw [← bot_eq_zero, iSup_eq_bot] at hI
    exact ⟨Classical.ofNonempty, hI _⟩
  have := emultiplicity_iSup p I
  simp only [H'.emultiplicity_eq_multiplicity, (H _).emultiplicity_eq_multiplicity] at this
  exact_mod_cast this

/-
I've been researching Mathlib for a bit today to figure out how to best set up a proof of the first
of the two lemmas in the initial post. I learned that there are at least seven ways of expressing
the multiplicity of a prime ideal `p` in the factorization of  another (nonzero) ideal `I` in a Dedkind domain:
* `factorization I p`
* `emultiplicity p I` (but this is an `ENat`)
* `multiplicity p I`
* `(UniqueFactorizationMonoid.normalizedFactors I).count p`
* `(UniqueFactorizationMonoid.normalizedFactors I).count (normalize p)`
* `(UniqueFactorizationMonoid.factors I).count p`
* `(UniqueFactorizationMonoid.factors I).count (normalize p)`

The APIs for these are a bit disparate. There are lemmas relating some of these: docs#factorization_eq_count
and docs#UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors (and, of course, one can relate
docs#emultiplicity with docs#multiplicity and docs#UniqueFactorizationMonoid.normalizedFactors with
docs#UniqueFactorizationMonoid.factors).
-/


end IsDedekindDomain.HeightOneSpectrum

-- end #38654

-- #39008

namespace NumberField

open IsDedekindDomain HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

lemma one_le_finrank_rat : 1 ≤ Module.finrank ℚ K := by
  rw [Nat.one_le_iff_ne_zero, Ne, Module.finrank_eq_zero_iff_of_free]
  exact not_subsingleton K
-- #find_home! one_le_finrank_rat -- Mathlib.NumberTheory.NumberField.Basic should work
-- [Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings, Mathlib.RingTheory.Valuation.Discrete.RankOne]

namespace FinitePlace

lemma asIdeal_maximalIdeal_injective :
    (fun v : FinitePlace K ↦ v.maximalIdeal.asIdeal).Injective :=
  fun ⦃_ _⦄ h ↦ (FinitePlace.maximalIdeal_inj ..).mp <| HeightOneSpectrum.ext h
-- #find_home! injective_asIdeal_maximalIdeal -- [Mathlib.NumberTheory.NumberField.Completion.FinitePlace]

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

end NumberField.FinitePlace

end API

-- end #39008

/-!
### The Northcott property for heights on number fields
-/

section API

variable {K ι : Type*} [Field K]

namespace NumberField

/- private lemma iSup_cast_ne_zero_eq_iSup_support (v : K → ℝ) (x : ι → 𝓞 K) :
    ⨆ i : { j // (x j : K) ≠ 0 }, v (x i.val) = ⨆ i : x.support, v (x i.val) :=
  let e : { j // (x j : K) ≠ 0 } ≃ ↑x.support := {
    toFun j := ⟨j.val, mod_cast j.prop⟩
    invFun i := ⟨i.val, mod_cast i.prop⟩
    left_inv j := by grind only
    right_inv i := by grind only
  }
  Equiv.iSup_congr e fun j ↦ by simp [e] -/

variable [NumberField K] {M : Type*} [CommMonoid M]

open UniqueFactorizationMonoid IsDedekindDomain.HeightOneSpectrum FinitePlace in
lemma hasFiniteMulSupport_fun_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (f : Ideal (𝓞 K) → M) :
    (fun v : FinitePlace K ↦
      (f v.maximalIdeal.asIdeal) ^ multiplicity v.maximalIdeal.asIdeal I).HasFiniteMulSupport := by
  classical
  have := Multiset.hasFiniteMulSupport_fun_pow_count (normalizedFactors I) f
  simp only [← count_normalizedFactors_eq_multiplicity hI]
  exact this.fun_comp_of_injective asIdeal_maximalIdeal_injective

end NumberField

end API

section Northcott

namespace NumberField

open Height Finset Multiset

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

open AdmissibleAbsValues IsDedekindDomain NumberField.HeightOneSpectrum

lemma InfinitePlace.le_iSup_abv_nat (v : InfinitePlace K) (n : ℕ) (x : 𝓞 K) :
    n ≤ ⨆ i, v (![(x : K), n] i) := by
  refine Finite.le_ciSup_of_le 1 ?_
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← v.norm_embedding_eq, map_natCast, Complex.norm_natCast]

lemma exists_integer_of_mem_span_one {x : K} (hx : x ∈ Submodule.span (𝓞 K) {(1 : K)}) :
    ∃ a : 𝓞 K, (a : K) = x := by
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by rw [← ha, ← Algebra.algebraMap_eq_smul_one a]⟩

variable [NumberField K]

open IsDedekindDomain.HeightOneSpectrum Ideal in
lemma FinitePlace.absNorm_pow_multiplicity_iSup_mul_iSup_eq_one [Nonempty ι] (x : ι → 𝓞 K)
    (hι : ∀ i, i ∈ x.support) (v : FinitePlace K) :
    (absNorm (v.maximalIdeal.asIdeal ^
      multiplicity v.maximalIdeal.asIdeal (⨆ i: ι, span {x i}))) *
      ⨆ i: ι, v (x i) = 1 := by
  have hnpos : 1 ≤ v.maximalIdeal.asIdeal.absNorm :=
    Nat.one_le_iff_ne_zero.mpr <| mt absNorm_eq_zero_iff.mp v.maximalIdeal.ne_bot
  rw [multiplicity_iSup _ fun j ↦ ?hj, mul_eq_one_iff_inv_eq₀ ?hn, map_pow,
    Finite.map_iInf_of_monotone (fun _ ↦ multiplicity ..) (pow_right_monotone <| hnpos),
    Finite.map_iInf_of_monotone _ Nat.mono_cast,
    Finite.map_iInf_of_antitoneOn antitoneOn_inv_pos fun j ↦ ?hs]
  case hj => simp [← Function.mem_support, hι]
  case hn => simp [Ideal.absNorm_eq_zero_iff, ne_bot]
  case hs => simpa only [Set.mem_setOf_eq] using mod_cast Nat.pow_pos hnpos
  refine iSup_congr fun i ↦ ?_
  rw [← mul_eq_one_iff_inv_eq₀ ?hne, mul_comm, Nat.cast_pow]
  case hne => simp [(show 0 < _ from hnpos).ne']
  exact FinitePlace.apply_mul_absNorm_pow_eq_one v <| Function.mem_support.mp <| hι i

open IsDedekindDomain.HeightOneSpectrum Ideal UniqueFactorizationMonoid FinitePlace in
lemma absNorm_mul_finprod_finitePlace_eq_one {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_def] at hi₀
  let i' : { j // (x j : K) ≠ 0 } := ⟨i₀, mod_cast hi₀⟩
  have HI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) ≠ 0 } ↦ x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  -- restrict to the subtype of `ι` where `x'` is non-zero
  have hx₀ : (fun i ↦ (x i : K)) ≠ 0 := Function.ne_iff.mpr ⟨i', i'.prop⟩
  simp_rw [coe_apply, iSup_abv_eq_iSup_subtype _ hx₀, HI]
  have hι' : Nonempty _ := .intro i'
  have hxι' : ⨆ i : { j // (x j : K) ≠ 0 }, Ideal.span {x i.val} ≠ ⊥ := by simpa using ⟨i', hi₀⟩
  rw [span_range_eq_iSup, ← finprod_finitePlace_pow_multiplicity hxι',
    map_finprod _ <| hasFiniteMulSupport_fun_pow_multiplicity hxι' (·), Nat.cast_finprod',
    ← finprod_mul_distrib ?hf ?hg]
  case hf =>
    simp only [map_pow, Nat.cast_pow]
    exact hasFiniteMulSupport_fun_pow_multiplicity hxι' fun v ↦ (v.absNorm : ℝ)
  case hg => exact .iSup fun j ↦ FinitePlace.hasFiniteMulSupport (mod_cast j.prop)
  have H (v : FinitePlace K) := v.absNorm_pow_multiplicity_iSup_mul_iSup_eq_one
    (fun j: { j // (x j : K) ≠ 0 } ↦ x j.val) fun j ↦ mod_cast j.prop
  exact finprod_eq_one_of_forall_eq_one H

lemma exists_zsmul_eq_integer (x : K) : ∃ (m : ℤ) (r : 𝓞 K), m ≠ 0 ∧  m • x = r := by
    obtain ⟨num, ⟨d, hd⟩, h⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid (𝓞 K) (nonZeroDivisors ℤ)) x
    rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map] at hd
    choose a hamem ha using hd
    refine ⟨a, num, mem_nonZeroDivisors_iff_ne_zero.mp hamem, ?_⟩
    rw [← h, zsmul_eq_mul, ← show (a : 𝓞 K) • _ = (a : K) * _ from smul_eq_mul ..,
      IsLocalization.smul_mk', Int.cast_comm a num, ← IsLocalization.smul_mk']
    simp [← ha, Algebra.smul_def]

lemma exists_nsmul_eq_integer (x : K) : ∃ (m : ℕ) (r : 𝓞 K), m ≠ 0 ∧  m • x = r := by
    obtain ⟨a, r, ha, h⟩ := exists_zsmul_eq_integer x
    refine ⟨a.natAbs, a.sign * r, Int.natAbs_ne_zero.mpr ha, ?_⟩
    simp only [zsmul_eq_mul, nsmul_eq_mul, Nat.cast_natAbs, map_mul, map_intCast] at h ⊢
    rw [← r.coe_eq_algebraMap, ← h, ← mul_assoc]
    rw_mod_cast [Int.sign_mul_self_eq_abs a]

section withIdeal

open Ideal

lemma isFiniteRelIndex_span_singleton_span_pair {m : ℕ} (hm : m ≠ 0) (r : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.IsFiniteRelIndex (span {(m : 𝓞 K), r}).toAddSubgroup := by
  refine Submodule.isFiniteRelIndex_of_map_linearMapMulLeft_le hm (Submodule.fg_span (by simp)) <|
    (LinearMap.map_span_le ..).mpr fun a ha ↦ ?_
  rw [LinearMap.mulLeft_apply, mem_span_singleton]
  exact dvd_mul_right ..

lemma relIndex_span_span_nat_mul {m n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n * m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(n * m), n * a}).toAddSubgroup := by
  let f : 𝓞 K →ₗ[𝓞 K] 𝓞 K := LinearMap.mulLeft _ n
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun a ha ↦ by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {(m : 𝓞 K)}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} = Submodule.map f (span {↑m, a}) := by
    simp [LinearMap.map_span, f, Set.image_pair]
  rw [H₁, H₂]
  simp_rw [Submodule.map_toAddSubgroup]
  convert AddSubgroup.relIndex_map_map_of_injective _ _ hf |>.symm

lemma relIndex_span_span_eq_relIndex_span_span {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {a b : 𝓞 K}
    (h : n * a = m * b) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, b}).toAddSubgroup := by
  trans (span {(n * m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(n * m), n * a}).toAddSubgroup
  · exact relIndex_span_span_nat_mul hn a
  · rw [mul_comm, mul_comm n, h]
    exact (relIndex_span_span_nat_mul hm b).symm

open Module in
lemma absNorm_span_pair_eq_pow {n : ℕ} (hn : n ≠ 0) {a : 𝓞 K}
    (h : (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, a}).toAddSubgroup = n) :
    (span {↑n, a}).absNorm = n ^ (finrank ℚ K - 1) := by
  rw [show Ideal.absNorm _ = (Submodule.toAddSubgroup _).index from rfl,
    ← AddSubgroup.relIndex_top_right]
  refine mul_left_cancel₀ hn ?_
  rw [← pow_succ', show finrank ℚ K - 1 + 1 = finrank ℚ K by grind [one_le_finrank_rat]]
  have : (span {(n : 𝓞 K)}).toAddSubgroup.relIndex ⊤ = n ^ (finrank ℚ K) := by
    have : (span {(n : 𝓞 K)}).toAddSubgroup = AddSubgroup.map (nsmulAddMonoidHom n) ⊤ := by
      ext : 1
      simp [mem_span_singleton', mul_comm]
    rw [this]
    have : finrank ℚ K = finrank ℤ ↥(⊤ : AddSubgroup (𝓞 K)) :=
      RingOfIntegers.rank K ▸ (AddSubgroup.finrank_eq_of_finiteIndex ⊤).symm
    rw [this]
    have hfr : Free ℤ (⊤ : AddSubgroup (𝓞 K)).toIntSubmodule :=
      free_of_finite_type_torsion_free'
    have hfin : Module.Finite ℤ (⊤ : AddSubgroup (𝓞 K)).toIntSubmodule := IsNoetherian.finite ..
    exact AddSubgroup.relIndex_map_nsmul n _
  rw [← this]
  nth_rewrite 1 [← h]
  refine AddSubgroup.relIndex_mul_relIndex _ _ _ ?_ le_top
  exact Submodule.toAddSubgroup_mono <| span_mono <| by grind

lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  obtain ⟨m, r, hm, hmr⟩ := exists_nsmul_eq_integer x
  let Im := span {(m : 𝓞 K)}
  let Imr := span {(m : 𝓞 K), r}
  have hI : Im.toAddSubgroup ≤ Imr.toAddSubgroup :=
    Submodule.toAddSubgroup_mono <| span_mono <| by grind
  let n := Im.toAddSubgroup.relIndex Imr.toAddSubgroup
  have hn : n ≠ 0 := isFiniteRelIndex_span_singleton_span_pair hm r |>.relIndex_ne_zero
  obtain ⟨a, ha'⟩ : ∃ a, m * a = n * r := by
    have : n • r ∈ span {(m : 𝓞 K)} :=
      Im.toAddSubgroup.nsmul_relIndex_mem <| Submodule.mem_span_of_mem <| by grind
    simpa [nsmul_eq_mul, mem_span_singleton', mul_comm] using this
  have ha : n * x = a := by
    apply_fun ((n : K) * ·) at hmr
    rw_mod_cast [← ha'] at hmr
    rw [nsmul_eq_mul, mul_left_comm] at hmr
    push_cast at hmr
    exact mul_left_cancel₀ (mod_cast hm) hmr
  refine ⟨n, hn, a, ha, absNorm_span_pair_eq_pow hn ?_⟩
  exact relIndex_span_span_eq_relIndex_span_span hn hm ha'

end withIdeal

lemma exists_nat_le_mulHeight₁ (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ n ≤ mulHeight₁ x ∧ IsIntegral ℤ (n * x) := by
  suffices ∃ n : ℕ, n ≠ 0 ∧
      ∃ a : 𝓞 K, n * x = a ∧ (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (totalWeight K - 1) by
    obtain ⟨n, hn, a, ha₁, ha₂⟩ := this
    refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
    have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
    have hx : mulHeight₁ x = mulHeight ![(a : K), n] := by
      rw [← mulHeight₁_div_eq_mulHeight (a : K) n, ← ha₁, mul_div_cancel_left₀ x (mod_cast hn)]
    rw [hx, mulHeight_eq (by simp [hn])]
    refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < n ^ (totalWeight K - 1) by positivity)
    have := absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, ha₂, hv, Nat.cast_pow] at this
    rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_left_comm, this,
      mul_one, totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum univ]
    refine prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ ?_
    gcongr
    exact v.le_iSup_abv_nat ..
  rw [totalWeight_eq_finrank]
  exact exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x

private lemma infinitePlace_apply_le_of_prod_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) {x : 𝓞 K}
    (h : ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B) (v : InfinitePlace K) :
    v x ≤ B / n ^ (totalWeight K - 1) := by
  classical
  have hvm : v.mult = v.mult - 1 + 1 := by have := v.mult_pos; lia
  rw [← Finset.prod_erase_mul _ _ (mem_univ v), hvm, pow_succ, ← mul_assoc] at h
  have : v x ≤ ⨆ i, v (![(x : K), n] i) := Finite.le_ciSup_of_le 0 le_rfl
  grw [this, le_div_iff₀' (by positivity)]; clear this
  refine (mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg_of_nonnegHomClass ..)).trans h
  have := Finset.prod_le_prod (s := Finset.univ.erase v) (f := fun v ↦ (n : ℝ) ^ v.mult)
      (g := fun v ↦ (⨆ i, v (![(x : K), n] i)) ^ v.mult) (by simp)
      (fun v _ ↦ by simp only; grw [v.le_iSup_abv_nat])
  grw [← this, ← v.le_iSup_abv_nat]
  · refine (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) from mod_cast hn.pos)).mp ?_
    rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_assoc, ← pow_succ,
      ← hvm, Finset.prod_erase_mul _ _ (mem_univ v), prod_pow_eq_pow_sum, totalWeight_eq_sum_mult]
  · -- nonnegativity side goal
    exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _

lemma finite_setOf_prod_infinitePlace_iSup_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B}.Finite := by
  set B' := B / n ^ (totalWeight K - 1)
  have H' : Set.BijOn ((↑) : 𝓞 K → K) {x | ∀ (v : InfinitePlace K), v x ≤ B'}
      {x | IsIntegral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ B'} := by
    refine Set.BijOn.mk (fun x hx ↦ ?_) (fun x₁ _ x₂ _ ↦ RingOfIntegers.eq_iff.mp) fun a ha ↦ ?_ <;>
      simp only [Set.mem_image, Set.mem_setOf_eq] at *
    · exact ⟨x.isIntegral_coe, fun φ ↦ hx <| InfinitePlace.mk φ⟩
    · rw [← mem_integralClosure_iff ℤ K] at ha
      exact ⟨⟨a, ha.1⟩, fun v ↦ v.norm_embedding_eq a ▸ ha.2 v.embedding, rfl⟩
  have := (Set.BijOn.finite_iff_finite H').mpr <| Embeddings.finite_of_norm_le K ℂ B'
  exact this.subset fun _ _ ↦ by grind [infinitePlace_apply_le_of_prod_le hn B]

open Ideal in
lemma absNorm_span_cast_eq_pow_totalWeight (n : ℕ) :
    absNorm (span {(n : 𝓞 K)}) = n ^ totalWeight K := by
  have H : Algebra.lmul ℤ (𝓞 K) n = (n : ℤ) • LinearMap.id := by ext : 1; simp
  rw [absNorm_span_singleton, Algebra.norm_apply, H, LinearMap.det_smul, totalWeight_eq_finrank,
    RingOfIntegers.rank]
  simp

open Ideal in
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
  rw_mod_cast [← absNorm_span_cast_eq_pow_totalWeight] at Hw ⊢
  exact Nat.le_of_dvd Hw <| absNorm_dvd_absNorm_of_le <| span_mono <| by simp +contextual

open Ideal in
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
lemma finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : K | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B}.Finite := by
  have hn' : (n : K) ≠ 0 := mod_cast hn
  have H : Set.BijOn (fun a : 𝓞 K ↦ (a / n : K)) {a | mulHeight ![(a : K), n] ≤ B}
      {x | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B} := by
    refine Set.BijOn.mk (fun a ha ↦ ?_) (fun a _ b _ h ↦ ?_) fun x ⟨hx₁, hx₂⟩ ↦ ?_
    · simp only [Set.mem_setOf_eq] at ha ⊢
      rw [mul_div_cancel₀ (a : K) hn', mulHeight₁_div_eq_mulHeight (a : K) n]
      exact ⟨a.isIntegral_coe, ha⟩
    · rw [div_left_inj' hn'] at h
      exact_mod_cast h
    · simp only [Set.mem_setOf_eq, Set.mem_image]
      obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, n * x = a := ⟨⟨n * x, hx₁⟩, rfl⟩
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

instance [AdmissibleAbsValues K] [Northcott (mulHeight₁ (K := K))] :
    Northcott (logHeight₁ (K := K)) :=
  comp_of_bddAbove mulHeight₁ log fun B ↦ bddAbove_def.mpr ⟨exp B, fun _ ↦ le_exp_of_log_le⟩

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded logarithmic height is finite. -/
theorem NumberField.finite_setOf_logHeight₁_le [NumberField K] (B : ℝ) :
    {x : K | logHeight₁ x ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott
