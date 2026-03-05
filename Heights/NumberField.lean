import Mathlib.GroupTheory.FiniteAbelian.Basic
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

variable {R : Type*} [GroupWithZero R] [PartialOrder R] [PosMulReflectLT R] [MulPosReflectLT R]

lemma antitoneOn_inv_pos : AntitoneOn (fun x : R ↦ x⁻¹) {r | 0 < r} :=
  antitoneOn_iff_forall_lt.mpr fun ⦃_⦄ ha ⦃_⦄ _ h ↦  inv_anti₀ (Set.mem_setOf.mp ha) h.le

namespace Function

variable {α M : Type*} [One M]

@[to_additive]
lemma HasFiniteMulSupport.subset {f g : α → M} (hg : g.HasFiniteMulSupport)
    (h : f.mulSupport ⊆ g.mulSupport) :
    f.HasFiniteMulSupport := by
  simp only [HasFiniteMulSupport] at hg ⊢
  exact hg.subset h

@[to_additive]
lemma HasFiniteMulSupport.comp_of_injective {β : Type*} {f : β → M} {g : α → β} (hg : Injective g)
    (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine Set.Finite.of_injOn (f := g) ?_ (Set.injOn_of_injective hg) hf
  exact Set.mapsTo_iff_subset_preimage.mpr fun ⦃_⦄ a ↦ a

@[to_additive]
lemma HasFiniteMulSupport.fun_comp_of_injective {β : Type*} {f : β → M} {g : α → β}
    (hg : Injective g) (hf : f.HasFiniteMulSupport) :
    (fun a ↦ f (g a)).HasFiniteMulSupport :=
  hf.comp_of_injective hg

@[to_additive]
lemma hasFiniteMulSupport_iff {f g : α → M} (h : f.mulSupport = g.mulSupport) :
    f.HasFiniteMulSupport ↔ g.HasFiniteMulSupport := by
  simp only [HasFiniteMulSupport]
  rw [h]

end Function

namespace Subgroup

@[to_additive]
lemma pow_relIndex_mem {G : Type*} [Group G] (H : Subgroup G) {K : Subgroup G} [H.Normal]
    {g : G} (hg : g ∈ K) : g ^ H.relIndex K ∈ H :=
  pow_index_mem (H.subgroupOf K) ⟨g, hg⟩

@[to_additive]
lemma index_ne_zero_of_range_powMonoidHom_le {A : Type*} [CommGroup A] [Group.FG A]
    (B : Subgroup A) {n : ℕ} (hn : n ≠ 0) (h : (powMonoidHom (α := A) n).range ≤ B) :
    B.index ≠ 0 := by
  refine index_ne_zero_iff_finite.mpr <| CommGroup.finite_of_fg_torsion _ ?_
  simp only [Monoid.IsTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g ↦ ⟨n, Nat.zero_lt_of_ne_zero hn, ?_⟩
  have H a : a ^ n ∈ B := by
    rw [SetLike.le_def] at h
    have ha : a ^ n ∈ (powMonoidHom n).range := by simp
    exact h ha
  suffices Quotient.out g ^ n ∈ B by
    obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ B, b = Quotient.out g ^ n := ⟨_, this, rfl⟩
    apply_fun QuotientGroup.mk (s := B) at hb₂
    rw [(QuotientGroup.eq_one_iff b).mpr hb₁] at hb₂
    rw [hb₂, QuotientGroup.mk_pow, QuotientGroup.out_eq']
  exact H _

@[to_additive]
lemma relIndex_ne_zero_of_range_powMonoidHom_le {A : Type*} [CommGroup A] (B C : Subgroup A)
    (hB : B.FG) {n : ℕ} (hn : n ≠ 0) (h : B.map (powMonoidHom (α := A) n) ≤ C) :
    C.relIndex B ≠ 0 := by
  simp only [relIndex]
  have : Group.FG B := (Group.fg_iff_subgroup_fg B).mpr hB
  refine index_ne_zero_of_range_powMonoidHom_le (A := B) (C.subgroupOf B) hn ?_
  rw [SetLike.le_def] at h ⊢
  rintro ⟨b, hbmem⟩ hb
  simp only [mem_map, powMonoidHom_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    MonoidHom.mem_range, Subtype.exists, SubmonoidClass.mk_pow, Subtype.mk.injEq,
    exists_prop] at h hb
  rw [mem_subgroupOf, show Subtype.val ⟨b, hbmem⟩ = b from rfl]
  obtain ⟨a, hamem, rfl⟩ := hb
  exact mem_carrier.mp (h a hamem)

end Subgroup

namespace Submodule

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [Module.Finite ℤ R]

lemma relIndex_ne_zero_of_map_linearMapMulLeft_le {A B : Submodule R K} {n : ℕ} (hn : n ≠ 0)
    (hfg : A.FG) (h : A.map (LinearMap.mulLeft R (n : K)) ≤ B) :
    B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 := by
  have hA : A.toAddSubgroup.FG := by
    suffices A.toAddSubgroup.toIntSubmodule.FG by
      rwa [fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at this
    rw [Submodule.toIntSubmodule_toAddSubgroup A]
    have : Module.Finite R ↥(restrictScalars ℤ A) := by
      rwa [← Module.Finite.iff_fg] at hfg
    nth_rw 1 [← Module.Finite.iff_fg]
    exact Module.Finite.trans R _
  refine A.toAddSubgroup.relIndex_ne_zero_of_range_nsmulAddMonoidHom_le B.toAddSubgroup hA hn ?_
  rw [SetLike.le_def] at h ⊢
  simpa using h

end Submodule

namespace Ideal

variable {R : Type*} [Semiring R]

lemma span_eq_iSup {ι : Type*} (x : ι → R) :
    Ideal.span (Set.range x) = ⨆ i, Ideal.span {x i} := by
  rw [← Ideal.span_iUnion, Set.iUnion_singleton_eq_range]

variable {ι : Type*}

lemma span_range_eq_span_range_support (x : ι → R) :
    span (Set.range x) = span (Set.range fun i : x.support ↦ x i.val) := by
  rw [← Ideal.span_sdiff_singleton_zero (s := Set.range x), Function.support]
  congr
  ext1 a
  simp only [Set.mem_diff, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨⟨i, hi⟩, ha⟩ ↦ ⟨⟨i, Set.mem_setOf.mpr (hi ▸ ha)⟩, hi⟩,
    fun ⟨j, hj⟩ ↦ ⟨⟨j.val, hj⟩, by grind⟩⟩
-- #find_home! span_range_eq_span_range_support -- [Mathlib.RingTheory.Ideal.Span]

end Ideal

/-
namespace Function

variable {α R : Type*} [Semiring R]

lemma mulSupport_pow_eq_support (f : α → ℕ) {b : R} (hb : orderOf b = 0) :
    (fun a ↦ b ^ f a).mulSupport = f.support := by
  ext1
  simp [← orderOf_dvd_iff_pow_eq_one, hb]

end Function
-/

namespace Nat

lemma cast_finprod' {ι R : Type*} [CommSemiring R] [CharZero R] (f : ι → ℕ) :
    ((∏ᶠ (x : ι), f x :) : R) = ∏ᶠ (x : ι), (f x : R) := by
  by_cases hf : f.HasFiniteMulSupport
  · exact map_finprod (Nat.castRingHom R) hf
  · have H : ¬ (fun i ↦ (f i : R)).HasFiniteMulSupport := by
      simp only [Function.HasFiniteMulSupport] at hf ⊢
      convert hf
      ext1; simp
    rw [finprod_of_not_hasFiniteMulSupport hf, finprod_of_not_hasFiniteMulSupport H, cast_one]

end Nat

namespace Multiset

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

open Function in
@[to_additive]
lemma mulSupport_subset (s : Multiset α) (f : α → M) :
    (fun a ↦ f a ^ count a s).mulSupport ⊆ s.toFinset := by
  refine Function.mulSupport_subset_iff'.mpr fun a h ↦ ?_
  simp only [SetLike.mem_coe, mem_toFinset] at h
  simp [count_eq_zero_of_notMem h]

@[to_additive]
lemma prod_map_eq_finprod (s : Multiset α) (f : α → M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  rw [Finset.prod_multiset_map_count, eq_comm]
  exact finprod_eq_prod_of_mulSupport_subset _ <| mulSupport_subset ..

open Function in
@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_fun_pow_multiplicity (s : Multiset α) (f : α → M) :
    (fun a ↦ (f a) ^ s.count a).HasFiniteMulSupport :=
  s.toFinset.finite_toSet.subset <| mulSupport_subset ..

end Multiset

namespace UniqueFactorizationMonoid

lemma multiplicity_eq_count_normalizedFactors {R : Type*} [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] [DecidableEq R] {a b : R}
    (ha : Irreducible a) (hb : b ≠ 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity ?h] at this
  case h => exact finiteMultiplicity_of_emultiplicity_eq_natCast this
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  exact_mod_cast this

lemma finprod_pow_count {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    [NormalizationMonoid α] [DecidableEq α] {x : α} (hx : x ≠ 0) :
    Associated (∏ᶠ p : α, p ^ (normalizedFactors x).count p) x := by
  rw [← Multiset.prod_map_eq_finprod, Multiset.map_id']
  exact prod_normalizedFactors hx

lemma finprod_pow_count_of_subsingleton_units {α : Type*} [CommMonoidWithZero α]
    [UniqueFactorizationMonoid α] [NormalizationMonoid α] [DecidableEq α] [Subsingleton αˣ]
    {x : α} (hx : x ≠ 0) :
    ∏ᶠ p : α, p ^ (normalizedFactors x).count p = x :=
  associated_iff_eq.mp <| finprod_pow_count hx

end UniqueFactorizationMonoid

namespace Finite

variable {α β : Type*} [ConditionallyCompleteLinearOrderBot α] [Finite β]

lemma ciSup_option (f : Option β → α) : ⨆ o, f o = f none ⊔ ⨆ b, f (some b) := by
  refine le_antisymm (ciSup_le fun o ↦ ?_) ?_
  · cases o with
    | none => exact le_sup_left
    | some val => exact le_sup_of_le_right <| le_ciSup_of_le val le_rfl
  · rcases isEmpty_or_nonempty β with hβ | hβ
    · rw [iSup_of_empty', csSup_empty, sup_bot_eq]
      exact le_ciSup ..
    exact sup_le (le_ciSup f none) <| ciSup_le fun b ↦ le_ciSup ..

-- There appears to be no `ConditionallyCompleteLinearOrderTop`, so we restrict
-- to our use case `β = ENat`.
lemma ciInf_option (f : Option β → ENat) : ⨅ o, f o = f none ⊓ ⨅ b, f (some b) := by
  -- exact ciSup_option (α := α ᵒᵈ) .. -- does not work
  refine le_antisymm (le_min (ciInf_le ..) ?_) <| le_ciInf fun o ↦ ?_
  · rcases isEmpty_or_nonempty β with hβ | hβ
    · simp
    exact le_ciInf fun b ↦ ciInf_le ..
  · cases o with
  | none => exact inf_le_left
  | some val => exact inf_le_of_right_le <| ciInf_le ..

end Finite

namespace AddSubgroup

noncomputable
def tupleModRangeNsmulAddMonoidHom {A : Type*} [AddCommGroup A] (n : ℕ) (ι : Type*) :
    (ι → A) ⧸ (nsmulAddMonoidHom n).range ≃+ (ι → A ⧸ (nsmulAddMonoidHom n).range) :=
  let φ : (ι → A) →+ (ι → A ⧸ (nsmulAddMonoidHom n).range) := {
    toFun x := (x ·)
    map_zero' := by simp [Pi.zero_def]
    map_add' x y := by simp [Pi.add_def]
  }
  QuotientAddGroup.liftEquiv (φ := φ) _ (fun y ↦ ⟨fun i ↦ Quotient.out (y i), by simp [φ]⟩) <| by
    ext1 x
    simpa [φ, funext_iff] using (Classical.skolem (p := fun i a ↦ n • a = x i)).symm

variable {M : Type*} [AddCommGroup M]

open Module

variable (M) in
lemma index_nsmul [Free ℤ M] [Module.Finite ℤ M] (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = n ^ finrank ℤ M := by
  let bas := Module.finBasis ℤ M
  let e := bas.equivFun
  suffices (nsmulAddMonoidHom (α := Fin (finrank ℤ M) → ℤ) n).range.index = n ^ finrank ℤ M by
    have H : (nsmulAddMonoidHom (α := Fin (finrank ℤ M) → ℤ) n).range =
        AddSubgroup.map e.toAddEquiv (nsmulAddMonoidHom (α := M) n).range := by
      ext x
      simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, nsmul_eq_mul, AddSubgroup.mem_map,
        AddMonoidHom.coe_coe, AddEquiv.coe_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk, exists_exists_eq_and,
        map_nsmul]
      refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
      · obtain ⟨x, rfl⟩ := H
        exact ⟨e.symm x, by simp⟩
      · obtain ⟨a, rfl⟩ := H
        exact ⟨e a, rfl⟩
    rwa [H, AddSubgroup.index_map_equiv] at this
  rw [AddSubgroup.index_eq_card, Nat.card_congr (tupleModRangeNsmulAddMonoidHom n _).toEquiv,
    Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  congr
  have : (nsmulAddMonoidHom (α := ℤ) n).range = AddSubgroup.zmultiples (n : ℤ) := by
    ext m
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, Int.nsmul_eq_mul,
      AddSubgroup.zmultiples, Int.zsmul_eq_mul, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_range]
    refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩ <;> obtain ⟨k, rfl⟩ := H <;> exact ⟨k, Int.mul_comm ..⟩
  rw [this, Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv, Nat.card_zmod]

lemma relIndex_nsmul (n : ℕ) (S : AddSubgroup M) [Free ℤ ↥S.toIntSubmodule]
    [Module.Finite ℤ ↥S.toIntSubmodule] :
    (AddSubgroup.map (nsmulAddMonoidHom (α := M) n) S).relIndex S = n ^ finrank ℤ S := by
  rw [AddSubgroup.relIndex]
  have H₁ : (AddSubgroup.map (nsmulAddMonoidHom n) S).addSubgroupOf S =
      (nsmulAddMonoidHom n).range := by
    ext1 x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range]
    simp only [nsmulAddMonoidHom_apply, Subtype.exists, AddSubmonoidClass.mk_nsmul]
    refine ⟨fun ⟨x, hx₁, hx₂⟩ ↦ ⟨x, hx₁, Subtype.ext hx₂⟩, fun ⟨a, ha₁, ha₂⟩ ↦ ⟨a, ha₁, ?_⟩⟩
    rw [← ha₂]
  rw [H₁]
  exact index_nsmul S.toIntSubmodule n

lemma finrank_eq_of_index_ne_zero [Module.Finite ℤ M] [IsTorsionFree ℤ M] {A : AddSubgroup M}
    (h : A.index ≠ 0) :
    finrank ℤ A = finrank ℤ M := by
  refine le_antisymm ?_ ?_
  · rw [← finrank_top ℤ M]
    exact Submodule.finrank_mono (s := A.toIntSubmodule) le_top
  · set n := A.index
    let F := DistribSMul.toLinearMap ℤ M n
    have : finrank ℤ M = finrank ℤ F.range.toAddSubgroup := by
      refine (LinearMap.finrank_range_of_inj <| LinearMap.ker_eq_bot.mp ?_).symm
      simp only [Submodule.eq_bot_iff, F]
      intro x hx
      simp only [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← natCast_zsmul] at hx
      exact (smul_eq_zero_iff_right <| mod_cast h).mp hx
    rw [this]
    refine Submodule.finrank_mono <| (OrderIso.symm_apply_le toIntSubmodule).mp fun m hm ↦ ?_
    suffices ∃ y, n • y = m by
      obtain ⟨x, rfl⟩ := this
      exact A.nsmul_index_mem x
    simpa [F] using hm

lemma finrank_eq_of_relIndex_ne_zero {A B : AddSubgroup M} [Module.Finite ℤ B] [IsTorsionFree ℤ B]
    (h : A ≤ B) (hi : A.relIndex B ≠ 0) :
    finrank ℤ A = finrank ℤ B := by
  simp only [relIndex] at hi
  rw [← finrank_eq_of_index_ne_zero hi]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

end AddSubgroup

namespace IsDedekindDomain.HeightOneSpectrum

/--
info: Ideal.finprod_count.{u_1} {R : Type u_1} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) (I : Ideal R)
  (hI : I ≠ 0) :
  (Associates.mk v.asIdeal).count (Associates.mk (∏ᶠ (v : HeightOneSpectrum R), v.maxPowDividing I)).factors =
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
-/
#guard_msgs in
#check Ideal.finprod_count

variable {R : Type*} [CommRing R]

lemma injective_asIdeal : (asIdeal (R := R)).Injective :=
  fun ⦃_ _⦄ h ↦ HeightOneSpectrum.ext h

/-!
### Conversion between various multplicities
-/
variable [IsDedekindDomain R]

open UniqueFactorizationMonoid in
@[simp]
lemma count_normalizedFactors_eq_multiplicity [DecidableEq (Ideal R)] {I : Ideal R} (hI : I ≠ ⊥)
    (p : HeightOneSpectrum R) :
    Multiset.count p.asIdeal (normalizedFactors I) = multiplicity p.asIdeal I := by
  have := emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  rw [normalize_eq p.asIdeal] at this
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  apply_fun ((↑) : ℕ → ℕ∞) using CharZero.cast_injective
  rw [← this]
  exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity

@[simp]
lemma maxPowDividing_eq_pow_multiplicity {I : Ideal R} (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    p.maxPowDividing I = p.asIdeal ^ multiplicity p.asIdeal I := by
  classical
  rw [maxPowDividing_eq_pow_multiset_count _ hI, count_normalizedFactors_eq_multiplicity hI]

@[simp]
lemma factorization_eq_multiplicity {I : Ideal R} (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    factorization I p.asIdeal = multiplicity p.asIdeal I := by
  rw [factorization_eq_count, count_normalizedFactors_eq_multiplicity hI]


/-!
---
-/

lemma _root_.Ideal.finprod_heightOneSpectrum_pow_multiplicity {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ᶠ p : HeightOneSpectrum R, p.asIdeal ^ multiplicity p.asIdeal I = I := by
  simpa only [← maxPowDividing_eq_pow_multiplicity hI]
    using Ideal.finprod_heightOneSpectrum_factorization hI

lemma multiplicity_le_of_ideal_ge (p : HeightOneSpectrum R) {I J : Ideal R} (h : J ≤ I)
    (hJ : J ≠ ⊥) :
    multiplicity p.asIdeal I ≤ multiplicity p.asIdeal J := by
  classical
  rw [← count_normalizedFactors_eq_multiplicity hJ,
    ← count_normalizedFactors_eq_multiplicity <| ne_bot_of_le_ne_bot hJ h]
  exact count_le_of_ideal_ge h hJ _

open UniqueFactorizationMonoid Multiset in
lemma multiplicity_sup (p : HeightOneSpectrum R) {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    multiplicity p.asIdeal (I ⊔ J) = multiplicity p.asIdeal I ⊓ multiplicity p.asIdeal J := by
  classical
  rw [sup_eq_prod_inf_factors hI hJ, ← count_normalizedFactors_eq_multiplicity ?h,
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

-- set_option backward.isDefEq.respectTransparency false in -- temporary measure
lemma emultiplicity_ciSup {ι : Type*} [Finite ι] (p : HeightOneSpectrum R) (I : ι → Ideal R) :
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
    rw [iSup_option, emultiplicity_sup p .., ih, Finite.ciInf_option]

lemma multiplicity_ciSup {ι : Type*} [Finite ι] [Nonempty ι] (p : HeightOneSpectrum R)
    {I : ι → Ideal R} (hI : ∀ i, I i ≠ ⊥) :
    multiplicity p.asIdeal (⨆ i, I i) = ⨅ i, multiplicity p.asIdeal (I i) := by
  have H i : FiniteMultiplicity p.asIdeal (I i) :=
    FiniteMultiplicity.of_prime_left (prime p) <| hI i
  have H' : FiniteMultiplicity p.asIdeal (⨆ i, I i) := by
    refine FiniteMultiplicity.of_prime_left (prime p) ?_
    contrapose! hI
    rw [← bot_eq_zero, iSup_eq_bot] at hI
    exact ⟨Classical.ofNonempty, hI _⟩
  have := emultiplicity_ciSup p I
  simp only [H'.emultiplicity_eq_multiplicity, (H _).emultiplicity_eq_multiplicity] at this
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  exact_mod_cast this

/--
info: multiplicity_mul.{u_1} {α : Type u_1} [CommMonoidWithZero α] [IsCancelMulZero α] {p a b : α} (hp : Prime p)
  (hfin : FiniteMultiplicity p (a * b)) : multiplicity p (a * b) = multiplicity p a + multiplicity p b
-/
#guard_msgs in
#check multiplicity_mul

/--
info: emultiplicity_mul.{u_1} {α : Type u_1} [CommMonoidWithZero α] [IsCancelMulZero α] {p a b : α} (hp : Prime p) :
  emultiplicity p (a * b) = emultiplicity p a + emultiplicity p b
-/
#guard_msgs in
#check emultiplicity_mul

/--
info: Finset.emultiplicity_prod.{u_1, u_3} {α : Type u_1} [CommMonoidWithZero α] [IsCancelMulZero α] {β : Type u_3} {p : α}
  (hp : Prime p) (s : Finset β) (f : β → α) : emultiplicity p (∏ x ∈ s, f x) = ∑ x ∈ s, emultiplicity p (f x)
-/
#guard_msgs in
#check Finset.emultiplicity_prod

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

namespace NumberField

open IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

lemma equivHeightOneSpectrum_apply (v : FinitePlace K) :
    v.equivHeightOneSpectrum = v.maximalIdeal :=
  rfl

lemma injective_asIdeal_maximalIdeal :
    (fun v : FinitePlace K ↦ v.maximalIdeal.asIdeal).Injective :=
  fun ⦃_ _⦄ h ↦ (FinitePlace.maximalIdeal_inj ..).mp <| injective_asIdeal h

lemma one_le_finrank_rat : 1 ≤ Module.finrank ℚ K := by
  refine Nat.one_le_iff_ne_zero.mpr ?_
  rw [Ne, Module.finrank_eq_zero_iff_of_free]
  exact not_subsingleton K

open FinitePlace in
lemma finite_setOf_multiplicity_ne_zero {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    {v : FinitePlace K | multiplicity v.maximalIdeal.asIdeal I ≠ 0}.Finite := by
  refine (Equiv.bijOn equivHeightOneSpectrum fun v ↦ ?_).finite_iff_finite.mpr <|
    I.finite_factors hI
  -- slow `simp` without `only`
  simp only [equivHeightOneSpectrum, Equiv.coe_fn_mk, Set.mem_setOf_eq, ne_eq,
    multiplicity_eq_zero, not_not]

lemma finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ v : FinitePlace K, v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I = I := by
  classical
  nth_rewrite 2 [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K))]
  simp only [equivHeightOneSpectrum_apply]

open Ideal in
lemma FinitePlace.apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x ≠ 0) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (span {x}) = 1 := by
  have hnz : span {x} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x, ← Nat.cast_pow, ← map_pow,
    ← maxPowDividing_eq_pow_multiplicity hnz v.maximalIdeal]
  exact v.maximalIdeal.embedding_mul_absNorm hx

end NumberField

end API

/-!
### The Northcott property for heights on number fields
-/

section API

variable {K ι : Type*} [Field K]

namespace NumberField

private lemma iSup_cast_ne_zero_eq_iSup_support (v : K → ℝ) (x : ι → 𝓞 K) :
    ⨆ i : { j // (x j : K) ≠ 0 }, v (x i.val) = ⨆ i : x.support, v (x i.val) :=
  let e : { j // (x j : K) ≠ 0 } ≃ ↑x.support := {
    toFun j := ⟨j.val, mod_cast j.prop⟩
    invFun i := ⟨i.val, mod_cast i.prop⟩
    left_inv j := by grind only
    right_inv i := by grind only
  }
  Equiv.iSup_congr e fun j ↦ by simp [e]

variable [NumberField K] {M : Type*} [CommMonoid M]

open UniqueFactorizationMonoid IsDedekindDomain.HeightOneSpectrum in
lemma hasFiniteMulSupport_fun_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (f : Ideal (𝓞 K) → M) :
    (fun v : FinitePlace K ↦
      (f v.maximalIdeal.asIdeal) ^ multiplicity v.maximalIdeal.asIdeal I).HasFiniteMulSupport := by
  classical
  have := Multiset.hasFiniteMulSupport_fun_pow_multiplicity (normalizedFactors I) f
  simp only [← count_normalizedFactors_eq_multiplicity hI]
  exact Function.HasFiniteMulSupport.fun_comp_of_injective injective_asIdeal_maximalIdeal this

end NumberField

end API

section Northcott

namespace NumberField

open Height Finset Multiset

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

open AdmissibleAbsValues IsDedekindDomain RingOfIntegers.HeightOneSpectrum

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

lemma InfinitePlace.le_iSup_abv_nat (v : InfinitePlace K) (n : ℕ) (x : 𝓞 K) :
    n ≤ ⨆ i, v.val (![(x : K), n] i) := by
  refine Finite.le_ciSup_of_le 1 ?_
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← v.coe_apply, ← v.norm_embedding_eq, map_natCast, Complex.norm_natCast]

lemma exists_integer_of_mem_span {x : K} (hx : x ∈ Submodule.span (𝓞 K) {(1 : K)}) :
    ∃ a : 𝓞 K, (a : K) = x := by
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, ?_⟩
  rw [← ha, ← Algebra.algebraMap_eq_smul_one a]

variable [NumberField K]

open IsDedekindDomain.HeightOneSpectrum Ideal UniqueFactorizationMonoid in
lemma absNorm_mul_finprod_nonarchAbsVal_eq_one {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v.val (x i) = 1 := by
  classical
  set ι' := Set.Elem x.support with hι'_eq
  have hnpos (v : FinitePlace K) : 1 ≤ v.maximalIdeal.asIdeal.absNorm :=
    Nat.one_le_iff_ne_zero.mpr <| mt absNorm_eq_zero_iff.mp v.maximalIdeal.ne_bot
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_def] at hi₀
  have Hi₀ : (x i₀ : K) ≠ 0 := by norm_cast
  have HI : span (Set.range x) = span (Set.range fun i : ι' ↦ x i.val) :=
    span_range_eq_span_range_support x
  -- restrict to the subtype of `ι` where `x` is non-zero
  have hx₀ : (fun i ↦ (x i : K)) ≠ 0 := Function.ne_iff.mpr ⟨i₀, Hi₀⟩
  simp only [Height.iSup_abv_eq_iSup_subtype _ hx₀, HI, iSup_cast_ne_zero_eq_iSup_support]
  let i' : ι' := ⟨i₀, hi₀⟩
  have hι' : Nonempty ι' := .intro i'
  have hx' : ⨆ i : ι', Ideal.span {x i.val} ≠ ⊥ := by simpa using ⟨i', hi₀⟩
  rw [span_eq_iSup, ← finprod_finitePlace_pow_multiplicity hx',
    map_finprod _ <| hasFiniteMulSupport_fun_pow_multiplicity hx' (·),
    Nat.cast_finprod', ← finprod_mul_distrib ?hf ?hg]
  case hf =>
    simp only [map_pow, Nat.cast_pow]
    exact hasFiniteMulSupport_fun_pow_multiplicity hx' fun v : Ideal (𝓞 K) ↦ (v.absNorm : ℝ)
  case hg =>
    exact Function.HasFiniteMulSupport.iSup
      fun j ↦ FinitePlace.hasFiniteMulSupport (mod_cast j.prop)
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  rw [multiplicity_ciSup _ fun j ↦ ?hj, mul_eq_one_iff_inv_eq₀ ?hn, map_pow,
    Finite.map_iInf_of_monotone (fun j : ι' ↦ multiplicity ..) (pow_right_monotone <| hnpos v),
    Finite.map_iInf_of_monotone _ Nat.mono_cast,
    Finite.map_iInf_of_antitoneOn antitoneOn_inv_pos fun j ↦ ?hs]
  case hj => simpa only [ne_eq, Ideal.span_singleton_eq_bot] using j.prop
  case hn => simp [Ideal.absNorm_eq_zero_iff, ne_bot]
  case hs => simpa only [Set.mem_setOf_eq] using mod_cast Nat.pow_pos (hnpos v)
  refine iSup_congr fun i ↦ ?_
  rw [← mul_eq_one_iff_inv_eq₀ ?hne, mul_comm, ← FinitePlace.coe_apply v ↑(x ↑i), Nat.cast_pow]
  case hne => simp [(show 0 < _ from hnpos v).ne']
  exact FinitePlace.apply_mul_absNorm_pow_eq_one v i.prop

/--
info: AddSubgroup.relIndex_pointwise_smul.{u_1, u_2} {G : Type u_1} {H : Type u_2} [Group H] (h : H) [AddGroup G]
  [DistribMulAction H G] (J K : AddSubgroup G) : (h • J).relIndex (h • K) = J.relIndex K
-/
#guard_msgs in
#check AddSubgroup.relIndex_pointwise_smul

lemma exists_zsmul_eq_integer (x : K) : ∃ (m : ℤ) (r : 𝓞 K), m ≠ 0 ∧  m • x = r := by
    obtain ⟨num, ⟨d, hd⟩, h⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid (𝓞 K) (nonZeroDivisors ℤ)) x
    rw [show
        (d ∈ Algebra.algebraMapSubmonoid ..) = ∃ a ∈ ↑(nonZeroDivisors ℤ), (algebraMap ..) a = d
        from rfl] at hd
    choose a hamem ha using hd
    rw [mem_nonZeroDivisors_iff_ne_zero] at hamem
    refine ⟨a, num, hamem, ?_⟩
    have Ha : (a : 𝓞 K) * num = num * (a : 𝓞 K) := Int.cast_comm a num
    rw [← h, zsmul_eq_mul, show (a : K) * _ = (a : 𝓞 K) • _ from (smul_eq_mul ..).symm]
    rw [IsLocalization.smul_mk', Int.cast_comm a num, ← IsLocalization.smul_mk']
    simp only [← ha, algebraMap_int_eq, eq_intCast, IsLocalization.mk'_self, Algebra.smul_def,
      mul_one]

lemma exists_nsmul_eq_integer (x : K) : ∃ (m : ℕ) (r : 𝓞 K), m ≠ 0 ∧  m • x = r := by
    obtain ⟨a, r, ha, h⟩ := exists_zsmul_eq_integer x
    refine ⟨a.natAbs, a.sign * r, Int.natAbs_ne_zero.mpr ha, ?_⟩
    simp only [zsmul_eq_mul, nsmul_eq_mul, Nat.cast_natAbs, map_mul, map_intCast] at h ⊢
    rw [← RingOfIntegers.coe_eq_algebraMap r, ← h, ← mul_assoc]
    congrm ?_ * x
    exact_mod_cast (Int.sign_mul_self_eq_abs a).symm

open Submodule in
lemma relIndex_ne_zero (x : K) :
    (span (𝓞 K) {(1 : K)}).toAddSubgroup.relIndex (span (𝓞 K) {1, x}).toAddSubgroup ≠ 0 := by
  obtain ⟨m, r, hm, h⟩ := exists_nsmul_eq_integer x
  refine relIndex_ne_zero_of_map_linearMapMulLeft_le hm (fg_span (by simp)) ?_
  rw [LinearMap.map_span_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rw [LinearMap.mulLeft_apply, mem_span_singleton]
  rcases ha with rfl | rfl
  · refine ⟨m, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one, mul_one]
    norm_cast
  · refine ⟨r, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one, ← RingOfIntegers.coe_eq_algebraMap, ← h, nsmul_eq_mul]

open Submodule in
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  let R : Submodule (𝓞 K) K := span (𝓞 K) {1}
  let I : Submodule (𝓞 K) K := span (𝓞 K) {1, x}
  have hRI : R.toAddSubgroup ≤ I.toAddSubgroup := by
    refine toAddSubgroup_mono <| span_le.mpr fun r hr ↦ ?_
    simpa only [Set.mem_singleton_iff.mp hr, SetLike.mem_coe, I] using mem_span_of_mem <| by simp
  let n := R.toAddSubgroup.relIndex I.toAddSubgroup
  have hn : n ≠ 0 := relIndex_ne_zero x
  have ha₁ : n * x ∈ R := by
    rw [← nsmul_eq_mul]
    have hx : x ∈ I := mem_span_of_mem <| Set.mem_insert_of_mem 1 rfl
    exact AddSubgroup.nsmul_relIndex_mem R.toAddSubgroup hx
  obtain ⟨a, ha₂⟩ := exists_integer_of_mem_span ha₁
  refine ⟨n, hn, a, ha₂.symm, ?_⟩
  let nI : Submodule (𝓞 K) K := span (𝓞 K) {(n : K), (a : K)}
  have hnIR : nI.toAddSubgroup ≤ R.toAddSubgroup := by
    refine toAddSubgroup_mono <| span_le.mpr fun r hr ↦ ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    simp only [SetLike.mem_coe, R, mem_span_singleton]
    rcases hr with rfl | rfl
    · exact ⟨n, by simp [Nat.cast_smul_eq_nsmul]⟩
    · exact ⟨a, by simp [Algebra.smul_def]⟩
  have hnI' : nI = I.map (DistribSMul.toLinearMap (𝓞 K) K n) := by
    have H (u v : 𝓞 K) : u • (n : K) + v • a = n * (u • 1 + v • x) := by
      simp [ha₂, ← nsmul_eq_mul, mul_add]
    ext1
    simp [I, nI, Submodule.mem_span_pair, H]
  have hnI : nI.toAddSubgroup = AddSubgroup.map (nsmulAddMonoidHom (α := K) n) I.toAddSubgroup := by
    rw [hnI', map_toAddSubgroup]
    rfl
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  let f : 𝓞 K →ₗ[𝓞 K] R := LinearMap.toSpanSingleton _ _ ⟨_, mem_span_singleton_self 1⟩
  have hf₀ : Function.Bijective f := by
    refine ⟨fun r r' h ↦ by simpa [f] using h, fun r ↦ ?_⟩
    have := r.prop
    simp only [R, mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by simp [f, ha]⟩
  have hf : Function.Bijective f.toAddMonoidHom := hf₀
  have H (u v : 𝓞 K) : u • (n : 𝓞 K) • (1 : K) + v • a • 1 = u • (n : K) + v • (a : K) := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_one, show a • (1 : K) = (a : K) • 1 from rfl,
      smul_eq_mul, mul_one]
  have H₁ : AddSubgroup.map f.toAddMonoidHom (toAddSubgroup (Ideal.span {↑n, a})) =
      nI.toAddSubgroup.addSubgroupOf R.toAddSubgroup := by
    have := congrArg toAddSubgroup (f.map_span {(n : 𝓞 K), a})
    rw [map_toAddSubgroup, show (f : 𝓞 K →+ ↥R) = f.toAddMonoidHom from rfl] at this
    simp only [nI, Ideal.span, this]
    ext1 r
    simp only [LinearMap.toSpanSingleton_apply, SetLike.mk_smul_mk, Set.image_pair, f, R,
      AddSubgroup.mem_mk, mem_toAddSubmonoid]
    rw [AddSubgroup.mem_addSubgroupOf, mem_toAddSubgroup]
    simp only [mem_span_pair, SetLike.mk_smul_mk, AddMemClass.mk_add_mk, Subtype.ext_iff, H]
  have H₂ : (Ideal.span {(n : 𝓞 K), a}).absNorm = nI.toAddSubgroup.relIndex R.toAddSubgroup := by
    rw [show Ideal.absNorm _ = (toAddSubgroup _).index from rfl, AddSubgroup.relIndex,
      ← AddSubgroup.index_map_of_bijective hf, H₁]
  have H₃ : Module.Finite ℤ ↥I.toAddSubgroup :=
    Module.Finite.of_fg <| FG.restrictScalars_iff.mpr <| fg_span <| Set.toFinite _
  have H₃' : Module.Finite ℤ ↥I.toAddSubgroup.toIntSubmodule := by
    simpa only [toIntSubmodule_toAddSubgroup] using H₃
  have H₄ : nI.toAddSubgroup.relIndex I.toAddSubgroup = n ^ Module.finrank ℚ K := by
    rw [hnI, I.toAddSubgroup.relIndex_nsmul n, ← RingOfIntegers.rank K,
      (AddEquiv.toIntLinearEquiv <| .ofBijective f hf).finrank_eq]
    exact congrArg (n ^ ·) <| (AddSubgroup.finrank_eq_of_relIndex_ne_zero hRI hn).symm
  rw [H₂, ← mul_left_inj' hn, AddSubgroup.relIndex_mul_relIndex _ _ _ hnIR hRI, H₄, ← pow_succ,
    Nat.sub_add_cancel one_le_finrank_rat]

lemma exists_nat_le_mulHeight₁ (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ n ≤ mulHeight₁ x ∧ IsIntegral ℤ (n * x) := by
  suffices ∃ n : ℕ, n ≠ 0 ∧
      ∃ a : 𝓞 K, n * x = a ∧ (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (totalWeight K - 1) by
    obtain ⟨n, hn, a, ha₁, ha₂⟩ := this
    refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
    have hv (v : FinitePlace K) (i : Fin 2) : v.val (![a, n] i : K) = v (![(a : K), n] i) := by
      fin_cases i <;> rfl
    have hx : mulHeight₁ x = mulHeight ![(a : K), n] := by
      rw [← mulHeight₁_div_eq_mulHeight (a : K) n, ← ha₁, mul_div_cancel_left₀ x (mod_cast hn)]
    rw [hx, mulHeight_eq (by simp [hn])]
    refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < n ^ (totalWeight K - 1) by positivity)
    have := absNorm_mul_finprod_nonarchAbsVal_eq_one (show ![a, n] ≠ 0 by simp [hn])
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, ha₂, hv, Nat.cast_pow] at this
    rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_left_comm, this,
      mul_one, totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum univ]
    refine prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ ?_
    gcongr
    exact InfinitePlace.le_iSup_abv_nat v n a
  rw [totalWeight_eq_finrank]
  exact exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x

lemma finite_setOf_prod_infinitePlace_iSup_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v.val (![(x : K), n] i)) ^ v.mult ≤ B}.Finite := by
  have H (x : 𝓞 K) (h : ∏ v : InfinitePlace K, (⨆ i, v.val (![(x : K), n] i)) ^ v.mult ≤ B)
      (v : InfinitePlace K) :
      v.val x ≤ B / n ^ (totalWeight K - 1) := by
    classical
    have hvm : v.mult = v.mult - 1 + 1 := by have := v.mult_pos; lia
    rw [← Finset.prod_erase_mul _ _ (mem_univ v), hvm, pow_succ, ← mul_assoc] at h
    have : v.val x ≤ ⨆ i, v.val (![(x : K), n] i) := Finite.le_ciSup_of_le 0 le_rfl
    grw [this]
    nth_rw 1 [le_div_iff₀' (mod_cast Nat.pow_pos hn.pos)]
    refine (mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg_of_nonnegHomClass ..)).trans h
    have := Finset.prod_le_prod (s := Finset.univ.erase v) (f := fun v ↦ (n : ℝ) ^ v.mult)
        (g := fun v ↦ (⨆ i, v.val (![(x : K), n] i)) ^ v.mult) (by simp) (fun v _ ↦ ?hle)
    case hle => simp only [Nat.succ_eq_add_one, Nat.reduceAdd]; grw [v.le_iSup_abv_nat]
    grw [← this, ← v.le_iSup_abv_nat]
    · refine (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) from mod_cast hn.pos)).mp ?_
      rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_assoc, ← pow_succ,
        ← hvm, Finset.prod_erase_mul _ _ (mem_univ v), prod_pow_eq_pow_sum univ InfinitePlace.mult]
      exact (congrArg (fun a ↦ (n : ℝ) ^ a) <| totalWeight_eq_sum_mult K).le
    · exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _
  set B' := B / n ^ (totalWeight K - 1)
  have H' : Set.BijOn ((↑) : 𝓞 K → K) {x | ∀ (v : InfinitePlace K), v.val x ≤ B'}
      {x | IsIntegral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ B'} := by
    refine Set.BijOn.mk (fun x hx ↦ ?_) (fun x₁ _ x₂ _ ↦ RingOfIntegers.eq_iff.mp) fun a ha ↦ ?_
    · simp only [Set.mem_setOf_eq] at hx ⊢
      exact ⟨x.isIntegral_coe, fun φ ↦ hx <| InfinitePlace.mk φ⟩
    · simp only [Set.mem_setOf_eq] at ha ⊢
      simp only [Set.mem_image, Set.mem_setOf_eq]
      rw [← mem_integralClosure_iff ℤ K] at ha
      refine ⟨⟨a, ha.1⟩, fun v ↦ ?_, rfl⟩
      have := ha.2 v.embedding
      rwa [InfinitePlace.norm_embedding_eq v a] at this
  have := (Set.BijOn.finite_iff_finite H').mpr <| Embeddings.finite_of_norm_le K ℂ B'
  exact Set.Finite.subset this fun x hx ↦ by grind

open Ideal in
lemma finite_setOf_mulHeight_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B}.Finite := by
  have H₀ (a : 𝓞 K) : ![(a : K), n] ≠ 0 := by simp [hn]
  have Hw : (0 : ℝ) < n ^ totalWeight K := by positivity
  have H₁ (a : 𝓞 K) :
      (n ^ totalWeight K : ℝ)⁻¹ ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (![(a : K), n] i) := by
    have Hnorm : (0 : ℝ) < (span (Set.range ![a, n])).absNorm := by
      norm_cast
      refine absNorm_pos_iff_mem_nonZeroDivisors.mpr ?_
      rw [mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot, Submodule.ne_bot_iff]
      exact ⟨n, by simpa using mem_span_pair.mpr ⟨1, 0, by simp⟩, mod_cast hn⟩
    have := absNorm_mul_finprod_nonarchAbsVal_eq_one (show ![a, n] ≠ 0 by simp [hn])
    rw [mul_eq_one_iff_inv_eq₀ Hnorm.ne'] at this
    have H (v : FinitePlace K) (i : Fin 2) : v.val (![a, ↑n] i).val = v (![(a : K), n] i) := by
      fin_cases i <;> simp [v.coe_apply]
    simp only [H] at this; clear H
    rw [← this, inv_le_inv₀ Hw Hnorm, ← Nat.cast_pow, Nat.cast_le]; clear this
    have H : (Algebra.lmul ℤ (𝓞 K)) n = (n : ℤ) • LinearMap.id := by ext1; simp
    have := absNorm_span_singleton (n : 𝓞 K)
    set_option backward.isDefEq.respectTransparency false in -- temporary measure
    rw [Algebra.norm_apply ℤ (n : 𝓞 K), H, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Int.natAbs_pow, Int.natAbs_natCast, RingOfIntegers.rank, ← totalWeight_eq_finrank] at this
    rw_mod_cast [← this] at Hw ⊢
    exact Nat.le_of_dvd Hw <| absNorm_dvd_absNorm_of_le <| span_mono <| by simp +contextual
  have H₂ : {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B} ⊆
      {a : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v.val (![(a : K), n] i)) ^ v.mult ≤
        n ^ totalWeight K * B} := by
    intro a ha
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_setOf_eq] at ha ⊢
    rw [mulHeight_eq (H₀ a)] at ha
    grw [← H₁] at ha
    · exact (div_le_iff₀' Hw).mp ha
    · -- nonnegativity side goal from `grw`
      exact Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _
  exact (finite_setOf_prod_infinitePlace_iSup_le hn _).subset H₂

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
    · simp only [f] at h
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
  · rw [show {x : K | mulHeight₁ x ≤ B} = ∅ by grind [mulHeight₁_pos]]
    exact Set.finite_empty
  have H₁ : {x : K | mulHeight₁ x ≤ B} =
      ⋃ n : Fin (⌊B⌋₊), {x : K | IsIntegral ℤ ((n + 1) * x) ∧ mulHeight₁ x ≤ B} := by
    ext1 x
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun h ↦ ⟨⟨n - 1, by grind [Nat.le_floor <| hn₁.trans h]⟩, ?_⟩
    rwa [← Nat.cast_add_one, Nat.sub_one_add_one hn₀]
  rw [H₁]
  exact Set.finite_iUnion fun n ↦
    mod_cast finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le K (Nat.zero_ne_add_one n).symm B

instance : Northcott (mulHeight₁ (K := K)) where
  finite_le := finite_setOf_mulHeight₁_le K

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

instance : Northcott (logHeight₁ (K := K)) where
  finite_le := finite_setOf_logHeight₁_le K

end NumberField

end Northcott
