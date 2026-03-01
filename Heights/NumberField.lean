import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Heights.Basic
/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and prove some properties.
-/

section API

/-!
### API for Mathlib
-/

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

lemma relIndex_ne_zero_of_map_linearMapMulLeft_le (A B : Submodule R K) {n : ℕ} (hn : n ≠ 0)
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

namespace Finite

variable {α β ι : Type*} [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLinearOrder β]
  [Finite ι] [Nonempty ι]

lemma map_iSup_of_monotoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : MonotoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨆ i, f i) = ⨆ i, g (f i) := by
  obtain ⟨j, hj⟩ : ∃ j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite
  rw [← hj]
  exact le_antisymm (le_ciSup_of_le j le_rfl) <|
    ciSup_le fun i ↦ hg (hs i) (hs j) (hj ▸ le_ciSup f i)

lemma map_iInf_of_monotoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : MonotoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (α := αᵒᵈ) (β := βᵒᵈ) (fun _ hi _ hj h ↦ hg hj hi h) hs

lemma map_iSup_of_antitoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : AntitoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (β := βᵒᵈ) hg hs

lemma map_iInf_of_antitoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : AntitoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotoneOn (β := βᵒᵈ) hg hs

lemma map_iSup_of_monotone (f : ι → α) {g : α → β} (hg : Monotone g) :
    g (⨆ i, f i) = ⨆ i, g (f i) :=
  map_iSup_of_monotoneOn (monotoneOn_univ.mpr hg) (fun i ↦ Set.mem_univ (f i))

lemma map_iInf_of_monotone (f : ι → α) {g : α → β} (hg : Monotone g) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (α := αᵒᵈ) (β := βᵒᵈ) f fun _ _ h ↦ hg h

lemma map_iSup_of_antitone (f : ι → α) {g : α → β} (hg : Antitone g) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (β := βᵒᵈ) f hg

lemma map_iInf_of_antitone (f : ι → α) {g : α → β} (hg : Antitone g) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotone (β := βᵒᵈ) f hg

end Finite

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
  rcases Set.finite_or_infinite (Function.mulSupport f) with hf | hf
  · have hf' : (fun i ↦ (f i : R)).mulSupport = f.mulSupport := by
      simp only [Function.mulSupport]
      ext1
      simp
    rw [finprod_eq_prod _ hf, finprod_eq_prod _ (hf' ▸ hf), cast_prod f hf.toFinset]
    congr
    exact hf'.symm
  · have hf' : (Function.mulSupport fun i ↦ (f i : R)).Infinite := by
      rw [Function.mulSupport] at hf ⊢
      convert hf with i
      rw [cast_eq_one]
    rw [finprod_of_infinite_mulSupport hf, finprod_of_infinite_mulSupport hf', cast_one]

end Nat

namespace Multiset

@[to_additive]
lemma prod_map_eq_finprod {α M : Type*} [DecidableEq α] [CommMonoid M] (s : Multiset α)
    (f : α → M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [map_cons, prod_cons, count_cons, ih]
    rw [show f a = f a ^ if a = a then 1 else 0 by simp,
      ← finprod_eq_single (fun b ↦ f b ^ if b = a then 1 else 0) a (by simp +contextual),
      ← finprod_mul_distrib ?hf ?hg]
    case hf =>
      simpa only [pow_ite, pow_one, pow_zero, Function.mulSupport]
        using Set.Finite.subset (Set.finite_singleton a) (by grind)
    case hg =>
      simp only [Function.mulSupport]
      have : {a | s.count a ≠ 0}.Finite := by simp
      refine Set.Finite.subset this fun b hb ↦ ?_
      simp only [ne_eq, Set.mem_setOf_eq, count_eq_zero, Decidable.not_not] at hb ⊢
      contrapose! hb
      rw [count_eq_zero_of_notMem hb, pow_zero]
    congr
    ext1 b
    split_ifs with rfl
    · simp [← pow_succ']
    · simp

end Multiset

namespace UniqueFactorizationMonoid

lemma multiplicity_eq_count_normalizedFactors {R : Type*} [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] [DecidableEq R] {a b : R}
    (ha : Irreducible a) (hb : b ≠ 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity ?h] at this
  case h => exact finiteMultiplicity_of_emultiplicity_eq_natCast this
  exact_mod_cast this

lemma finprod_pow_count {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    [NormalizationMonoid α] [DecidableEq α] {x : α} (hx : x ≠ 0) :
    Associated (∏ᶠ p : α, p ^ (normalizedFactors x).count p) x := by
  convert prod_normalizedFactors hx
  simp [← Multiset.prod_map_eq_finprod]

lemma finprod_pow_count_of_subsgingleton_units {α : Type*} [CommMonoidWithZero α]
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
def tupleModRangeNsmulAddMonoidHom (n : ℕ) (ι : Type*) :
    (ι → ℤ) ⧸ (nsmulAddMonoidHom n).range ≃+ (ι → ℤ ⧸ (nsmulAddMonoidHom n).range) := by
  let φ : (ι → ℤ) →+ (ι → ℤ ⧸ (nsmulAddMonoidHom n).range) := {
    toFun x := fun i ↦ x i
    map_zero' := by simp [Pi.zero_def]
    map_add' x y := by simp [Pi.add_def]
  }
  refine QuotientAddGroup.liftEquiv (φ := φ) _ (fun y ↦ ?_) ?_
  · exact ⟨fun i ↦ Quotient.out (y i), by simp [φ]⟩
  · ext x
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, nsmul_eq_mul, AddMonoidHom.mem_ker,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, φ]
    refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · obtain ⟨z, rfl⟩ := H
      ext i
      simp only [Pi.mul_apply, Pi.natCast_apply, QuotientAddGroup.mk_nat_mul, Pi.zero_apply,
        ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      simp
    · simp_rw [funext_iff, Pi.zero_apply, QuotientAddGroup.eq_zero_iff] at H
      simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, Int.nsmul_eq_mul] at H
      choose y hy using H
      refine ⟨y, ?_⟩
      ext i
      rw [← hy, Pi.mul_apply, Pi.natCast_apply]

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
    (AddSubgroup.map (nsmulAddMonoidHom (α := M) n) S).relIndex S =
      n ^ finrank ℤ S := by
  rw [AddSubgroup.relIndex]
  have H₁ : (AddSubgroup.map (nsmulAddMonoidHom n) S).addSubgroupOf S =
      (nsmulAddMonoidHom n).range := by
    ext1 x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range]
    simp only [nsmulAddMonoidHom_apply, Subtype.exists, AddSubmonoidClass.mk_nsmul]
    refine ⟨fun ⟨x, hx₁, hx₂⟩ ↦ ⟨x, hx₁, Subtype.ext hx₂⟩, fun ⟨a, ha₁, ha₂⟩ ↦ ⟨a, ha₁, ?_⟩⟩
    rw [← ha₂]
  rw [H₁]
  convert index_nsmul S.toIntSubmodule n <;> assumption

lemma finrank_eq_of_index_ne_zero [Module.Finite ℤ M] [IsTorsionFree ℤ M] {A : AddSubgroup M}
    (h : A.index ≠ 0) :
    finrank ℤ A = finrank ℤ M := by
  refine le_antisymm ?_ ?_
  · rw [← finrank_top ℤ M]
    exact Submodule.finrank_mono (s := A.toIntSubmodule) le_top
  · set n := A.index
    have H : (nsmulAddMonoidHom (α := M) n).range ≤ A := by
      intro m hm
      simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply] at hm
      obtain ⟨x, rfl⟩ := hm
      exact AddSubgroup.nsmul_index_mem ..
    have : finrank ℤ M = finrank ℤ (nsmulAddMonoidHom (α := M) n).range := by
      let f := (nsmulAddMonoidHom (α := M) n).toIntLinearMap
      have : (nsmulAddMonoidHom (α := M) n).range = f.range.toAddSubgroup := by
        ext x
        simp [f]
      rw [this]
      refine Eq.symm <| LinearMap.finrank_range_of_inj ?_
      refine LinearMap.ker_eq_bot.mp ?_
      simp only [AddMonoidHom.coe_toIntLinearMap_ker, f]
      rw [OrderIso.apply_eq_iff_eq_symm_apply toIntSubmodule]
      simp only [toIntSubmodule_symm, Submodule.bot_toAddSubgroup]
      ext x
      simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, mem_bot]
      rw [← natCast_zsmul]
      exact smul_eq_zero_iff_right (mod_cast h)
    rw [this]
    refine Submodule.finrank_mono (s := (nsmulAddMonoidHom (α := M) n).range.toIntSubmodule)
      (t := A.toIntSubmodule) ?_
    rwa [OrderIso.le_iff_le toIntSubmodule]

lemma finrank_eq_of_relIndex_ne_zero {A B : AddSubgroup M} [Module.Finite ℤ B] [IsTorsionFree ℤ B]
    (h : A ≤ B) (hi : A.relIndex B ≠ 0) :
    finrank ℤ A = finrank ℤ B := by
  simp only [relIndex] at hi
  rw [← finrank_eq_of_index_ne_zero hi]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

end AddSubgroup

namespace Ideal

variable {R : Type*} [Semiring R]

lemma span_eq_iSup {ι : Type*} (x : ι → R) :
    Ideal.span (Set.range x) = ⨆ i, Ideal.span {x i} := by
  rw [← Ideal.span_iUnion, Set.iUnion_singleton_eq_range]

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

/--
info: Ideal.finprod_count.{u_1} {R : Type u_1} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) (I : Ideal R)
  (hI : I ≠ 0) :
  (Associates.mk v.asIdeal).count (Associates.mk (∏ᶠ (v : HeightOneSpectrum R), v.maxPowDividing I)).factors =
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
-/
#guard_msgs in
#check Ideal.finprod_count

/--
info: IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm.{u_1} {K : Type u_1} [Field K] [NumberField K]
  (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) {x : NumberField.RingOfIntegers (WithVal (valuation K v))}
  (h_x_nezero : x ≠ 0) :
  ‖(NumberField.FinitePlace.embedding v) ↑x‖ * ↑(Ideal.absNorm (v.maxPowDividing (Ideal.span {x}))) = 1
-/
#guard_msgs in
#check IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm

/--
info: sup_eq_prod_inf_factors.{u_4} {T : Type u_4} [CommRing T] [IsDedekindDomain T] {I J : Ideal T} [DecidableEq (Ideal T)]
  (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  I ⊔ J = (UniqueFactorizationMonoid.normalizedFactors I ∩ UniqueFactorizationMonoid.normalizedFactors J).prod
-/
#guard_msgs in
#check sup_eq_prod_inf_factors -- should not be in the root name space?

/--
info: factorization_eq_count.{u_1} {α : Type u_1} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α]
  [DecidableEq α] {n p : α} : (factorization n) p = Multiset.count p (UniqueFactorizationMonoid.normalizedFactors n)
-/
#guard_msgs in
#check factorization_eq_count

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-!
### Conversion between various multplicities
-/

lemma count_normalizedFactors_eq_multiplicity [DecidableEq (Ideal R)] {I : Ideal R} (hI : I ≠ ⊥)
    (p : HeightOneSpectrum R) :
    Multiset.count p.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) =
      multiplicity p.asIdeal I := by
  have := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  apply_fun ((↑) : ℕ → ℕ∞) using CharZero.cast_injective
  convert this.symm
  · -- `p.asIdeal = normalize p.asIdeal`
    exact (normalize_eq p.asIdeal).symm
  · -- `↑(multiplicity p.asIdeal I) = emultiplicity p.asIdeal I`
    refine Eq.symm (FiniteMultiplicity.emultiplicity_eq_multiplicity ?_)
    exact finiteMultiplicity_of_emultiplicity_eq_natCast this

lemma maxPowDividing_eq_pow {I : Ideal R} (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    p.maxPowDividing I = p.asIdeal ^ multiplicity p.asIdeal I := by
  classical
  rw [maxPowDividing_eq_pow_multiset_count _ hI, count_normalizedFactors_eq_multiplicity hI]

/-!
---
-/

lemma _root_.Ideal.finprod_heightOneSpectrum_pow_multiplicity {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ᶠ p : HeightOneSpectrum R, p.asIdeal ^ multiplicity p.asIdeal I = I := by
  nth_rewrite 2 [← Ideal.finprod_heightOneSpectrum_factorization hI]
  simp only [maxPowDividing_eq_pow hI]

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
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity <| H this,
    FiniteMultiplicity.emultiplicity_eq_multiplicity <| H hI,
    FiniteMultiplicity.emultiplicity_eq_multiplicity <| H hJ, multiplicity_sup _ hI hJ]
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
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H'] at this
  conv_rhs at this => enter [1, i]; rw [FiniteMultiplicity.emultiplicity_eq_multiplicity (H i)]
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

lemma one_le_finrank_rat : 1 ≤ Module.finrank ℚ K := by
  refine Nat.one_le_iff_ne_zero.mpr ?_
  rw [Ne, Module.finrank_eq_zero_iff_of_free]
  exact not_subsingleton K

/--
info: IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count.{u_1} {R : Type u_1} [CommRing R]
  [IsDedekindDomain R] (v : IsDedekindDomain.HeightOneSpectrum R) [DecidableEq (Ideal R)] {I : Ideal R} (hI : I ≠ 0) :
  v.maxPowDividing I = v.asIdeal ^ Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)
-/
#guard_msgs in
#check IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count

/--
info: Ideal.finprod_heightOneSpectrum_factorization.{u_1} {R : Type u_1} [CommRing R] [IsDedekindDomain R] {I : Ideal R}
  (hI : I ≠ 0) : ∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum R), v.maxPowDividing I = I
-/
#guard_msgs in
#check Ideal.finprod_heightOneSpectrum_factorization


/- noncomputable
abbrev FinitePlace.asIdeal (v : FinitePlace K) : Ideal (𝓞 K) := v.maximalIdeal.asIdeal
 -/

lemma finite_setOf_multipicity_ne_zero {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    {v : FinitePlace K | multiplicity v.maximalIdeal.asIdeal I ≠ 0}.Finite := by
  simp only [ne_eq, multiplicity_eq_zero, not_not]
  let e := FinitePlace.equivHeightOneSpectrum (K := K)
  have he (v : FinitePlace K) : e v = v.maximalIdeal := rfl
  have he' (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : (e.symm v).maximalIdeal = v := by
    simp [e, ← he]
  let e' : ({v : FinitePlace K | v.maximalIdeal.asIdeal ∣ I}) ≃
      ({v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}) := {
    toFun v := ⟨e v.val, Set.mem_setOf.mpr v.prop⟩
    invFun v := ⟨e.symm v.val, Set.mem_setOf.mpr <| by simp only [he']; exact v.prop⟩
    left_inv v := by grind
    right_inv v := by grind
  }
  exact (Equiv.set_finite_iff e').mpr <| I.finite_factors hI

noncomputable
example : FinitePlace K ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 K) := by exact
  FinitePlace.equivHeightOneSpectrum

lemma finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ v : FinitePlace K, v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I = I := by
  classical
  nth_rewrite 2 [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K))]
  congr
  ext1 v
  rw [show FinitePlace.equivHeightOneSpectrum v = v.maximalIdeal from rfl,
    v.maximalIdeal.maxPowDividing_eq_pow_multiset_count]
  rwa [count_normalizedFactors_eq_multiplicity hI]

lemma FinitePlace.apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x ≠ 0) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (Ideal.span {x}) = 1 := by
  have hnz : Ideal.span {x} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  convert v.maximalIdeal.embedding_mul_absNorm hx using 2
  · exact (norm_embedding_eq v ↑x).symm
  · norm_cast
    rw [v.maximalIdeal.maxPowDividing_eq_pow (by exact hnz), map_pow]
    rfl

end NumberField

end API

/-!
### Properties of heights on number fields
-/

namespace NumberField

open Height Finset Multiset

variable {K : Type*} [Field K] [NumberField K]

open AdmissibleAbsValues

-- #35919
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

-- #35919
lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl

-- #35924
variable (K) in
lemma totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult := by
  simp only [totalWeight]
  convert sum_archAbsVal_eq (fun _ ↦ (1 : ℕ))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

-- #35924
variable (K) in
lemma totalWeight_eq_finrank : totalWeight K = Module.finrank ℚ K := by
  rw [totalWeight_eq_sum_mult, InfinitePlace.sum_mult_eq]

variable (K) in
@[grind! .]
lemma totalWeight_pos : 0 < totalWeight K := by
  simp [totalWeight, archAbsVal, multisetInfinitePlace]
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  exact Fintype.sum_pos
    (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

open Real in
-- #35919
/-- This is the familiar definition of the logarithmic height on a number field. -/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v ↦ log⁺ (v x)]

end NumberField

-- #35924

/-!
### Positivity extension for totalWeight on number fields
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Height.totalWeight` is positive for number fields. -/
@[positivity Height.totalWeight _]
meta def evalHeightTotalWeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Height.totalWeight $K $KF $KA) =>
    -- Check whether there is a `NumberField` instance for `$K` around.
    match ← trySynthInstanceQ q(NumberField $K) with
    | .some _instFinite =>
      assertInstancesCommute
      return .positive q(NumberField.totalWeight_pos $K)
    | _ => throwError "field in Height.totalWeight not known to be a number field"
  | _, _, _ => throwError "not Height.totalWeight"

end Mathlib.Meta.Positivity

-- end #35924

open Height in
example (K : Type*) [Field K] [NumberField K] (n : ℕ) : 0 < totalWeight K ^ n :=
  by positivity

-- Towards Northcott

section Northcott

namespace NumberField

open Height Finset Multiset

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

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

omit [NumberField K] in
lemma InfinitePlace.le_iSup_abv_nat (v : InfinitePlace K) (n : ℕ) (x : 𝓞 K) :
    n ≤ ⨆ i, v.val (![(x : K), n] i) := by
  refine Finite.le_ciSup_of_le 1 ?_
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← v.coe_apply, ← v.norm_embedding_eq, map_natCast, Complex.norm_natCast]

open IsDedekindDomain.HeightOneSpectrum in
lemma absNorm_mul_finprod_nonarchAbsVal_eq_one {ι : Type*} [Finite ι] {x : ι → 𝓞 K} (hx : x ≠ 0) :
    (Ideal.span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v.val (x i) = 1 := by
  classical
  set ι' := { j // (x j : K) ≠ 0 } with hι'_eq
  have hxnz {i} (h : x i ≠ 0) : (x i : K) ≠ 0 := by norm_cast
  have hnebot (v : FinitePlace K) : v.maximalIdeal.asIdeal ≠ ⊥ :=
    fun h ↦ RingOfIntegers.not_isField K <|
      Ring.isField_iff_maximal_bot.mpr (h ▸ isMaximal v.maximalIdeal)
  have hnpos (v : FinitePlace K) : 1 ≤ v.maximalIdeal.asIdeal.absNorm := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hnebot v
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_def] at hi₀
  have hx₀ : (fun i ↦ (x i : K)) ≠ 0 := Function.ne_iff.mpr ⟨i₀, hxnz hi₀⟩
  have Hv (v : AbsoluteValue K ℝ) := Height.iSup_abv_eq_iSup_subtype v hx₀
  have HI : Ideal.span (Set.range x) = Ideal.span (Set.range fun i : ι' ↦ x i.val) := by
    rw [← Ideal.span_sdiff_singleton_zero (s := Set.range x)]
    congr
    ext1 a
    simp only [Set.mem_diff, Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨⟨i, hi⟩, ha⟩ ↦ ⟨⟨i, hxnz (hi ▸ ha)⟩, hi⟩, fun ⟨j, hj⟩ ↦ ⟨⟨j.val, hj⟩, by grind⟩⟩
  -- restrict to the subtype of `ι` where `x` is non-zero
  simp only [Hv, HI]
  have hι' : Nonempty ι' := .intro ⟨i₀, hxnz hi₀⟩
  have hx' : ⨆ i : ι', Ideal.span {x i.val} ≠ ⊥ := by
    simpa only [ne_eq, iSup_eq_bot, Ideal.span_singleton_eq_bot, not_forall]
      using ⟨⟨i₀, hxnz hi₀⟩, hi₀⟩
  have H : (fun v : FinitePlace K ↦ v.maximalIdeal.asIdeal ^
      multiplicity v.maximalIdeal.asIdeal (⨆ i : ι', Ideal.span {x i.val})).mulSupport.Finite := by
    set I := ⨆ i : ι', Ideal.span {x i.val}
    have hs : (fun v : FinitePlace K ↦
                v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I).mulSupport =
        {v : FinitePlace K | multiplicity v.maximalIdeal.asIdeal I ≠ 0} := by
      ext1 v
      simp [Ideal.IsPrime.ne_top']
    simpa only [hs] using finite_setOf_multipicity_ne_zero hx'
  rw [Ideal.span_eq_iSup, ← finprod_finitePlace_pow_multiplicity hx', map_finprod _ H,
    Nat.cast_finprod', ← finprod_mul_distrib ?hf ?hg]
  case hf =>
    rwa [← Function.comp_def (fun v : Ideal (𝓞 K) ↦ (v.absNorm : ℝ)),
      Function.mulSupport_comp_eq _ fun {I} ↦ ?hnorm]
    case hnorm =>
      norm_cast
      rw [Ideal.absNorm_eq_one_iff, Ideal.one_eq_top]
  case hg =>
    exact Function.finite_mulSupport_iSup fun j ↦ FinitePlace.mulSupport_finite j.prop
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  rw [multiplicity_ciSup _ fun j ↦ ?hj, mul_eq_one_iff_inv_eq₀ ?hn, map_pow,
    Finite.map_iInf_of_monotone (fun j : ι' ↦ multiplicity ..) (pow_right_monotone <| hnpos v),
    Finite.map_iInf_of_monotone _ Nat.mono_cast,
    Finite.map_iInf_of_antitoneOn (s := {r : ℝ | 0 < r}) (g := (·⁻¹)) ?hinv fun j ↦ ?hs]
  case hj =>
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    apply_fun ((↑) : 𝓞 K → K)
    exact j.prop
  case hn => simp [Ideal.absNorm_eq_zero_iff, hnebot]
  case hinv =>
    refine antitoneOn_iff_forall_lt.mpr fun a ha b hb h ↦ ?_
    simp only [Set.mem_setOf_eq] at ha hb
    rw [inv_le_inv₀ hb ha]
    exact h.le
  case hs =>
    simp only [ne_eq, Set.mem_setOf_eq]
    norm_cast
    exact Nat.pow_pos (hnpos v)
  refine iSup_congr fun i ↦ ?_
  rw [← mul_eq_one_iff_inv_eq₀ ?hne, mul_comm, ← FinitePlace.coe_apply v ↑(x ↑i), Nat.cast_pow]
  case hne => simp [(show 0 < _ from hnpos v).ne']
  have hi₀ : x i.val ≠ 0 := by
    apply_fun ((↑) : 𝓞 K → K)
    exact i.prop
  exact FinitePlace.apply_mul_absNorm_pow_eq_one v hi₀

example : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {1}

/--
info: AddSubgroup.relIndex_pointwise_smul.{u_1, u_2} {G : Type u_1} {H : Type u_2} [Group H] (h : H) [AddGroup G]
  [DistribMulAction H G] (J K : AddSubgroup G) : (h • J).relIndex (h • K) = J.relIndex K
-/
#guard_msgs in
#check AddSubgroup.relIndex_pointwise_smul

lemma relIndex_ne_zero (x : K) :
    (Submodule.span (𝓞 K) {(1 : K)}).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) {1, x}).toAddSubgroup ≠ 0 := by
  obtain ⟨m, r, hm, h⟩ : ∃ (m : ℕ) (r : 𝓞 K), m ≠ 0 ∧  m • x = r := by
    obtain ⟨num, ⟨d, hd⟩, h⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid (𝓞 K) (nonZeroDivisors ℤ)) x
    rw [show
        (d ∈ Algebra.algebraMapSubmonoid ..) = ∃ a ∈ ↑(nonZeroDivisors ℤ), (algebraMap ..) a = d
        from rfl] at hd
    choose a hamem ha using hd
    rw [mem_nonZeroDivisors_iff_ne_zero] at hamem
    refine ⟨a.natAbs, a.sign * num, Int.natAbs_ne_zero.mpr hamem, ?_⟩
    have Ha : (a.natAbs : 𝓞 K) * num = (a.sign * num) * (a : 𝓞 K) := by
      rw [mul_right_comm]
      congr
      rw [← Int.cast_mul, Int.sign_mul_self]
      exact (Int.cast_natCast a.natAbs).symm
    rw [← h, nsmul_eq_mul,
      show (a.natAbs : K) * _ = (a.natAbs : 𝓞 K) • _ from (smul_eq_mul ..).symm,
      IsLocalization.smul_mk', Ha, ← IsLocalization.smul_mk']
    simp only [← ha, algebraMap_int_eq, eq_intCast, IsLocalization.mk'_self, map_mul, map_intCast]
    rw [← smul_eq_mul (↑a.sign) ((algebraMap (𝓞 K) K) num), Algebra.smul_def, mul_one]
    rfl
  refine Submodule.relIndex_ne_zero_of_map_linearMapMulLeft_le _ _ hm (Submodule.fg_span (by simp)) ?_
  rw [LinearMap.map_span_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rw [LinearMap.mulLeft_apply, Submodule.mem_span_singleton]
  rcases ha with rfl | rfl
  · refine ⟨m, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one, mul_one]
    norm_cast
  · refine ⟨r, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one, ← RingOfIntegers.coe_eq_algebraMap, ← h, nsmul_eq_mul]

lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  let R : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {1}
  let I : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {1, x}
  let n := R.toAddSubgroup.relIndex I.toAddSubgroup
  have hn : n ≠ 0 := relIndex_ne_zero x
  have ha₁ : n * x ∈ R := by
    rw [← nsmul_eq_mul]
    have hx : x ∈ I := Submodule.mem_span_of_mem <| Set.mem_insert_of_mem 1 rfl
    exact AddSubgroup.nsmul_relIndex_mem R.toAddSubgroup hx
  obtain ⟨a, ha₂⟩ : ∃ a : 𝓞 K, (a : K) = n * x := by
    simp only [R] at ha₁
    rw [Submodule.mem_span_singleton] at ha₁
    obtain ⟨a, ha⟩ := ha₁
    refine ⟨a, ?_⟩
    rw [← ha, ← Algebra.algebraMap_eq_smul_one a]
  refine ⟨n, hn, a, ha₂.symm, ?_⟩
  let nI : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(n : K), (a : K)}
  have hnI : nI.toAddSubgroup = AddSubgroup.map (nsmulAddMonoidHom (α := K) n) I.toAddSubgroup := by
    simp only [I, nI]
    ext z
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, nsmulAddMonoidHom_apply,
      nsmul_eq_mul, Submodule.mem_span_pair]
    refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · obtain ⟨u, v, rfl⟩ := H
      refine ⟨_, ⟨u, v, rfl⟩, ?_⟩
      rw [mul_add, mul_smul_comm v, ← ha₂, mul_smul_one u]
    · obtain ⟨_, ⟨u, v, rfl⟩, H⟩ := H
      refine ⟨u, v, ?_⟩
      rw [← H, mul_add, mul_smul_comm v, ← ha₂, mul_smul_one u]
  let f : 𝓞 K →+ R.toAddSubgroup := {
    toFun r := ⟨r • 1, by simpa [R] using Submodule.mem_span_singleton.mpr ⟨_, rfl⟩⟩
    map_zero' := by simp
    map_add' r r' := by simp [add_smul]
  }
  have hf : Function.Bijective f := by
    refine ⟨fun r r' h ↦ by simpa [f] using h, fun r ↦ ?_⟩
    have := r.prop
    simp only [R] at this
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton] at this
    obtain ⟨b, hb⟩ := this
    refine ⟨b, ?_⟩
    ext1
    rw [← hb]
    rfl
  have H₂ : (Ideal.span {(n : 𝓞 K), a}).absNorm = nI.toAddSubgroup.relIndex R.toAddSubgroup := by
    rw [show Ideal.absNorm _ = (Submodule.toAddSubgroup _).index from rfl]
    rw [show
        nI.toAddSubgroup.relIndex R.toAddSubgroup =
          (nI.toAddSubgroup.addSubgroupOf R.toAddSubgroup).index
        from rfl]
    erw [← AddSubgroup.index_map_of_bijective hf (Ideal.span {(n : 𝓞 K), a}).toAddSubgroup] -- `rw` does not work
    congr
    ext1 r
    simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, R, f, nI]
    refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · obtain ⟨y, hy, rfl⟩ := H
      rw [AddSubgroup.mem_addSubgroupOf]
      rw [show Subtype.val ⟨y • (1 : K), _⟩ = y • 1 from rfl]
      set_option backward.isDefEq.respectTransparency false in -- temporary measure
      -- have : Module (𝓞 K) (𝓞 K) := inferInstance
      rw [show Ideal.span _ = Submodule.span (𝓞 K) _ from rfl] at hy
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_pair] at hy ⊢
      obtain ⟨u, v, rfl⟩ := hy
      refine ⟨u, v, ?_⟩
      rw [add_smul]
      simp_rw [smul_assoc, ← Algebra.algebraMap_eq_smul_one, RingOfIntegers.coe_eq_algebraMap]
      rfl
    · rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
        Submodule.mem_span_pair] at H
      obtain ⟨u, v, huv⟩ := H
      conv =>
        enter [1, y, 1]
        erw [Submodule.mem_toAddSubgroup, Submodule.mem_span_pair] -- `rw` does not work
      obtain ⟨r', hr'⟩ := hf.surjective r
      refine ⟨r', ⟨u, v, ?_⟩, by rw [← hr']; simp [f]⟩
      apply_fun ((↑) : 𝓞 K → K) using RingOfIntegers.coe_injective
      push_cast
      rw [huv, ← hr']
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, f]
      rw [← Algebra.algebraMap_eq_smul_one r']
  have H' : Module.Finite ℤ ↥I.toAddSubgroup.toIntSubmodule := by
    simp only [Submodule.toIntSubmodule_toAddSubgroup]
    refine Module.Finite.of_fg ?_
    set_option backward.isDefEq.respectTransparency false in -- temporary measure
    exact Submodule.FG.restrictScalars_iff.mpr <| Submodule.fg_span <| Set.toFinite _
  have H₁ : nI.toAddSubgroup.relIndex I.toAddSubgroup = n ^ Module.finrank ℚ K := by
    rw [hnI]
    have H₃ : Module.Free ℤ ↥I.toAddSubgroup.toIntSubmodule := by
      convert Module.free_iff_isTorsionFree.mpr ?_
      · infer_instance
      · infer_instance
      · exact H'
      · exact I.toAddSubgroup.toIntSubmodule.instIsTorsionFree
    rw [AddSubgroup.relIndex_nsmul n I.toAddSubgroup]
    rw [← RingOfIntegers.rank K]
    refine congrArg (n ^ ·) ?_
    have : Module.finrank ℤ (𝓞 K) = Module.finrank ℤ R :=
      (AddEquiv.toIntLinearEquiv <| .ofBijective f hf).finrank_eq
    rw [this]
    convert (AddSubgroup.finrank_eq_of_relIndex_ne_zero ?_ hn).symm
    · convert H'
    · simp only [R, I]
      rw [Submodule.toAddSubgroup_le]
      simp only [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_span_of_mem (by simp)
  have H₃ : nI.toAddSubgroup.relIndex I.toAddSubgroup =
      nI.toAddSubgroup.relIndex R.toAddSubgroup * R.toAddSubgroup.relIndex I.toAddSubgroup := by
    refine (AddSubgroup.relIndex_mul_relIndex _ _ _ ?_ ?_).symm
    · refine Submodule.toAddSubgroup_mono <| Submodule.span_le.mpr fun r hr ↦ ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;>
        simp only [SetLike.mem_coe, R, Submodule.mem_span_singleton]
      · exact ⟨n, by simp [Nat.cast_smul_eq_nsmul]⟩
      · exact ⟨a, by simp [Algebra.smul_def]⟩
    · refine Submodule.toAddSubgroup_mono <| Submodule.span_le.mpr fun r hr ↦ ?_
      simp only [Set.mem_singleton_iff] at hr
      rw [hr]
      simp only [SetLike.mem_coe, I]
      exact Submodule.mem_span_of_mem <| by simp
  rw [H₂]
  apply_fun (· * n) using mul_left_injective₀ hn
  dsimp only
  rw [← H₃, H₁, ← pow_succ]
  exact congrArg (n ^ ·) (Nat.sub_add_cancel one_le_finrank_rat).symm

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
    rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_left_comm, this,
      mul_one, totalWeight_eq_sum_mult]
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
      rw [← pow_succ, show totalWeight K - 1 + 1 = totalWeight K by grind, mul_assoc, ← pow_succ,
        show v.mult - 1 + 1 = v.mult by lia, Finset.prod_erase_mul _ _ (mem_univ v),
        prod_pow_eq_pow_sum univ InfinitePlace.mult]
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

open Ideal in
lemma finite_setOf_mulHeight_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B}.Finite := by
  have H₀ (a : 𝓞 K) : ![(a : K), n] ≠ 0 := by simp [hn]
  have Hw : (0 : ℝ) < n ^ totalWeight K := by positivity
  have H₁ (a : 𝓞 K) :
      (n ^ totalWeight K : ℝ)⁻¹ ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (![(a : K), n] i) := by
    let z : Fin 2 → 𝓞 K := ![a, n]
    have han : ![a, n] ≠ 0 := by simp [hn]
    have := absNorm_mul_finprod_nonarchAbsVal_eq_one han
    have Hnorm : (0 : ℝ) < (span (Set.range ![a, n])).absNorm := by
      norm_cast
      refine absNorm_pos_iff_mem_nonZeroDivisors.mpr ?_
      rw [mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot, Submodule.ne_bot_iff]
      exact ⟨n, by simpa using mem_span_pair.mpr ⟨1, 0, by simp⟩, mod_cast hn⟩
    rw [mul_eq_one_iff_inv_eq₀ Hnorm.ne'] at this
    have HH (v : FinitePlace K) (i : Fin 2) : v.val (![a, ↑n] i).val = v (![(a : K), n] i) := by
      have (x : K) : v.val x = v x := rfl
      fin_cases i <;> simp [this]
    simp only [HH] at this
    rw [← this]
    nth_rw 1 [inv_le_inv₀ Hw Hnorm]
    norm_cast
    have := absNorm_span_singleton (n : 𝓞 K)
    rw [Algebra.norm_apply ℤ (n : 𝓞 K)] at this
    have H₃ : (Algebra.lmul ℤ (𝓞 K)) n = (n : ℤ) • LinearMap.id := by ext1; simp
    set_option backward.isDefEq.respectTransparency false in -- temporary measure
    rw [H₃, LinearMap.det_smul, LinearMap.det_id] at this
    simp only [mul_one, Int.natAbs_pow, Int.natAbs_natCast] at this
    rw [RingOfIntegers.rank, ← totalWeight_eq_finrank] at this
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

end NumberField

end Northcott
