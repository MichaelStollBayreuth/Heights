/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib

@[expose] public section

/-!
# Finite algebras over Henselian local rings (vendored from FLT)

This file is vendored (with light adaptation: single file, no module system) from the FLT
project, https://github.com/ImperialCollegeLondon/FLT, files
`FLT/HenselianLocalRing/{Stuff, EtaleDecomposition, Finite}.lean`, by Andrew Yang.

Main results (Stacks project, tag 04GH):

* `HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing`:
  a finite algebra over a Henselian local ring is a product of local rings.
* `HenselianLocalRing.of_finite`: a finite local algebra over a Henselian local ring is
  Henselian.
-/

/-! ### From `FLT/HenselianLocalRing/Stuff.lean` -/

/-! # Helper lemmas for finite extensions of henselian local is henselian -/


open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

attribute [ext high] Ideal.Quotient.algHom_ext

instance IsIdempotentElem.Corner.algebra
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {e : S} (he : IsIdempotentElem e) : Algebra R he.Corner where
  smul r x := ⟨r • x.1, by
    simp [he, Subsemigroup.mem_corner_iff, (Subsemigroup.mem_corner_iff he).mp x.2]⟩
  algebraMap :=
  { toFun r := ⟨r • e, by simp [he, Subsemigroup.mem_corner_iff, he.eq]⟩
    map_one' := by simp; rfl
    map_mul' a b := Subtype.ext <| show (a * b) • e = (a • e) * (b • e) by
      simp [he.eq, ← mul_smul, mul_comm]
    map_zero' := by simp; rfl
    map_add' a b := Subtype.ext (add_smul _ _ _) }
  commutes' r x := Subtype.ext (show r • e * x.1 = x.1 * r • e by
    simp [(Subsemigroup.mem_corner_iff he).mp x.2])
  smul_def' r x := Subtype.ext (show r • x.1 = (r • e) * x.1 by
    simp [(Subsemigroup.mem_corner_iff he).mp x.2])

instance {R R' S : Type*} [CommSemiring R] [CommSemiring R'] [Semiring S] [Algebra R S]
    [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]
    {e : S} (he : IsIdempotentElem e) : IsScalarTower R R' he.Corner :=
  .of_algebraMap_eq fun _ ↦ Subtype.ext (IsScalarTower.algebraMap_smul _ _ _).symm

lemma IsIdempotentElem.toCorner_surjective
    {R : Type*} [CommSemiring R] {e : R} (he : IsIdempotentElem e) :
    Function.Surjective (algebraMap R he.Corner) :=
  fun x ↦ ⟨x.1, Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.2).2⟩

lemma IsIdempotentElem.ker_toCorner
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    RingHom.ker (algebraMap R he.Corner) = Ideal.span {1 - e} := by
  apply le_antisymm
  · intro x hx
    refine Ideal.mem_span_singleton.mpr ⟨x, ?_⟩
    simp [show x * e = 0 from congr($(hx).1), sub_mul, mul_comm e]
  · simpa [Ideal.span_le, sub_eq_zero, -FaithfulSMul.ker_algebraMap_eq_bot] using!
      Subtype.ext he.eq.symm

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (I : Ideal T) (J : Ideal R) [I.LiesOver J] : (I.comap f).LiesOver J := by
  constructor; ext; simp [I.over_def J]

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] :
    Algebra.IsSeparable p.ResidueField q.ResidueField :=
  ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

lemma Ideal.isRadical_ker {R S : Type*} [CommRing R] [CommRing S] [IsReduced S] (f : R →+* S) :
    (RingHom.ker f).IsRadical := by
  simpa [IsRadical, SetLike.le_def, Ideal.mem_radical_iff] using fun _ _ ↦ eq_zero_of_pow_eq_zero

lemma Ideal.IsRadical.pow_mem_iff {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsRadical)
    {x : R} {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ I ↔ x ∈ I :=
  ⟨fun h ↦ hI ⟨_, h⟩, (Ideal.pow_mem_of_mem _ · _ hn.bot_lt)⟩

lemma Algebra.FormallyUnramified.isField_of_isLocalRing
    (R S : Type*) [Field R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] [IsLocalRing S] : IsField S :=
  have := finite_of_free R S
  have := IsArtinianRing.of_finite R S
  have := isReduced_of_field R S
  IsArtinianRing.isField_of_isReduced_of_isLocalRing _

/-! ### From `FLT/HenselianLocalRing/EtaleDecomposition.lean` -/

/-! # Etale local decompsition of finite extensions -/


open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

namespace Algebra

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- A key induction step of `exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`. -/
private theorem exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux.{v, u}
    {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R')
    [P.IsPrime] [P.LiesOver p] (e : R' ⊗[R] S) (P' : Ideal (R' ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (hP'q : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom P' = q)
    (heP' : e ∉ P') (hpP : Function.Bijective
      (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
    (H : ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P')
    (R'' : Type u) [CommRing R''] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    [Algebra.Etale R' R''] (Q : Ideal R'')
    [Q.IsPrime] [Q.LiesOver P] (n : ℕ)
    (e' : Fin ((n + 1) + 1) → R'' ⊗[R] S)
    (he' : CompleteOrthogonalIdempotents e')
    (he'0 : e' 0 = Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S) e)
    (Q' : Fin n → Ideal (R'' ⊗[R] S)) [∀ i, (Q' i).IsPrime] [∀ i, (Q' i).LiesOver Q]
    (hPQ : Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Q.over_def P)))
    (hQ' : ∀ (i : Fin n), e' i.succ.castSucc ∉ Q' i)
    (H' : ∀ (P'' : Ideal (R'' ⊗[R] S)), e' 0 ∈ P'' → P''.IsPrime → P''.LiesOver Q →
      e' (.last _) ∈ P'' ∧ ∀ (i : Fin n), e' i.succ.castSucc ∉ P'' → P'' = Q' i) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  let φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
  have : Q.LiesOver p := .trans _ P _
  have hpQ :
    Function.Bijective (Ideal.ResidueField.mapₐ p Q (Algebra.ofId _ _) (Q.over_def p)) := by
    convert hPQ.comp hpP
    rw [← @AlgHom.coe_restrictScalars' R R', ← AlgHom.coe_comp]; congr 1; ext
  let P'φ := (Ideal.fiberIsoOfBijectiveResidueField hpQ).symm
    (Ideal.fiberIsoOfBijectiveResidueField hpP ⟨P', ‹_›, ‹_›⟩)
  have : P'φ.1.LiesOver P := .trans _ Q _
  have : (P'φ.1.comap φ.toRingHom).LiesOver P := inferInstanceAs ((P'φ.1.comap φ).LiesOver P)
  have hP'φ : P'φ.1.comap φ.toRingHom = P' := by
    apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpP
    rw [Ideal.comap_comap]
    convert Ideal.comap_fiberIsoOfBijectiveResidueField_symm hpQ _
    · ext; simp [φ]
    · simp; rfl
  refine ⟨R'', inferInstance, _, .comp R R' R'', Q, ‹_›, .trans _ P _, _, _, he', Fin.cons P'φ
    Q', Fin.cases P'φ.2.1 ?_, Fin.cases P'φ.2.2 ?_, hpQ, Fin.cases ?_ ?_, ?_⟩
  · intro P'' _ _
    by_cases heP'' : e ∈ P''.comap φ
    · obtain ⟨h₁, h₂⟩ := H' P'' (by simpa [he'0]) inferInstance inferInstance
      exact ⟨h₁, Fin.cases (fun h ↦ (h (by simpa [he'0])).elim) (by simpa)⟩
    · have : P''.LiesOver P := .trans _ Q _
      obtain rfl := H _ inferInstance inferInstance heP''
      have : ∀ i ≠ 0, e' i ∈ P'' := by
        intro j hj
        rw [← Ideal.IsPrime.mul_mem_left_iff (I := P'') heP'']
        simp [φ, ← he'0, he'.ortho hj.symm]
      refine ⟨by simp [this], Fin.cases (fun _ ↦ ?_) (by simp [this])⟩
      simp only [Fin.cons_zero]
      apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpQ
      have : (φ.restrictScalars _).comp Algebra.TensorProduct.includeRight =
          Algebra.TensorProduct.includeRight := by ext; simp [φ]
      rw [← this]
      exact congr(($hP'φ).comap Algebra.TensorProduct.includeRight).symm
  · simp only [Fin.cons_succ]; infer_instance
  · simp only [Fin.cons_succ]; infer_instance
  · rw [← hP'φ] at heP'; simpa [he'0]
  · simpa

lemma ncard_primesOver_quotient_singleton_lt_of_notMem
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) (e : S) (P' : Ideal S) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') (H : (P.primesOver S).Finite) :
    (P.primesOver (S ⧸ Ideal.span {e})).ncard < (P.primesOver S).ncard := by
  rw [← Set.ncard_image_of_injective _
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective)]
  refine Set.ncard_lt_ncard (Set.ssubset_iff_exists.mpr ⟨?_, P', ⟨‹_›, ‹_›⟩, ?_⟩) H
  · rintro _ ⟨q, ⟨_, _⟩, rfl⟩
    exact ⟨inferInstance, inferInstanceAs ((q.comap (Ideal.Quotient.mkₐ R _)).LiesOver _)⟩
  · rintro ⟨q, ⟨_, _⟩, rfl⟩; simp at heP'

set_option backward.isDefEq.respectTransparency false in
/-- A less universe polymorphic version of
`exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`. Use that instead. -/
private lemma exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'.{u, v}
    {R : Type u} {S : Type max u v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  induction h : (p.primesOver S).ncard using Nat.strong_induction_on generalizing R S with
  | h n IH =>
    have : IsArtinianRing (p.ResidueField ⊗[R] S) := IsArtinianRing.of_finite p.ResidueField _
    have hpSfin : (p.primesOver S).Finite :=
      (PrimeSpectrum.primesOverOrderIsoFiber R S p).finite_iff.mpr inferInstance
    cases n with
    | zero =>
      have := (Set.ncard_eq_zero hpSfin).mp h
      refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, ⟨rfl⟩, 0, 1,
        ⟨⟨by simp [IsIdempotentElem],
          by simp only [Nat.reduceAdd, Pi.one_apply, mul_one, Subsingleton.pairwise]⟩,
          by simp⟩, nofun, nofun, nofun, ?_, nofun, ?_⟩
      · convert show Function.Bijective (AlgHom.id R _) from Function.bijective_id; ext
      · exact fun P h₁ h₂ ↦ (this.le
          ⟨show (P.comap Algebra.TensorProduct.includeRight.toRingHom).IsPrime from inferInstance,
          ⟨by simp [P.over_def p, Ideal.under, Ideal.comap_comap]⟩⟩).elim
    | succ n =>
    obtain ⟨q, hq, hq'⟩ := Set.nonempty_of_ncard_ne_zero (h.trans_ne (by simp))
    obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hpP, _, H⟩ :=
      Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
    have : (P.primesOver (R' ⊗[R] S ⧸ Ideal.span {e})).ncard < n + 1 := by
      let F := Ideal.fiberIsoOfBijectiveResidueField hpP (S := S)
      refine (ncard_primesOver_quotient_singleton_lt_of_notMem _ _
        P' heP' (F.finite_iff.mpr hpSfin)).trans_le ?_
      rw [← h, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr F.toEquiv]
    obtain ⟨R'', _, _, _, Q, _, _, n, e' : _ → R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}),
      he', Q' : _ → Ideal (R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e})), _, _, hPQ, hQ', H'⟩ :=
      IH _ this (R := R') (S := R' ⊗[R] S ⧸ Ideal.span {e}) P rfl
    change ∀ (P'' : Ideal (R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}))), P''.IsPrime → P''.LiesOver Q →
      e' (Fin.last n) ∈ P'' ∧ ∀ (i : Fin n), e' i.castSucc ∉ P'' → P'' = Q' i at H'
    letI : Algebra R R'' := .compHom _ (algebraMap R R')
    haveI : IsScalarTower R R' R'' := .of_algebraMap_eq' rfl
    let φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
    let e₁ : R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[R''] (R'' ⊗[R] S ⧸ Ideal.span {φ e}) :=
      tensorQuotientTensorEquiv (R'' := R'') e
    obtain ⟨e'', he'', he''e'⟩ := CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
      (Ideal.Quotient.mk (Ideal.span {φ e})) (I := Fin (n + 1)) (φ e) (he.map φ) (by simp)
      (e₁ ∘ e') (he'.map e₁.toRingHom) (fun _ ↦ Ideal.Quotient.mk_surjective _)
    have he''e'' (i : _) : e₁ (e' i) = e'' i := congr_fun he''e' i
    have hψe'' (i : _) : (e' i) = e₁.symm (e'' i) := e₁.eq_symm_apply.mpr (he''e'' i)
    refine exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux p q R' P e P'
      hP'q heP' hpP (fun P'' h₁ h₂ heP'' ↦ H P'' h₁ h₂ heP'') R'' Q n _
      ((CompleteOrthogonalIdempotents.equiv (finSuccEquiv _)).mpr he'') rfl
      (Q' · |>.comap (e₁.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _))) hPQ
      (fun i ↦ by rw [Function.comp_def]; simpa [← hψe''] using hQ' i) ?_
    simp only [Function.comp_apply, finSuccEquiv_zero,
      show finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n from rfl, Fin.castSucc_succ,
      finSuccEquiv_succ]
    intro P'' heP'' _ _
    have : (P''.map (Ideal.Quotient.mk (.span {φ e}))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa [Ideal.span_le])
    have : (P''.map (Ideal.Quotient.mk (.span {φ e}))).LiesOver Q := ⟨by
      have : P'' ⊔ Ideal.span {φ e} = P'' := by simpa [Ideal.span_le]
      rw [← Ideal.under_under (B := R'' ⊗[R] S)]
      simpa [Ideal.under, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, this] using P''.over_def Q⟩
    have := H' ((P''.map (Ideal.Quotient.mk (.span {φ e}))).comap e₁) inferInstance
      (inferInstanceAs <| ((P''.map (Ideal.Quotient.mk (.span {φ e}))).comap
        e₁.toAlgHom).LiesOver Q)
    have hP'' : (1 - φ e) ∉ P'' :=
      fun h ↦ ‹P''.IsPrime›.one_notMem (by convert add_mem heP'' h; ring)
    simp only [Ideal.mem_comap, he''e'',
      Ideal.mem_map_span_singleton_iff_of_isIdempotentElem (he.map φ),
      Ideal.IsPrime.mul_mem_left_iff hP''] at this
    refine ⟨this.1, fun i hi ↦ (this.2 i hi).symm ▸ ?_⟩
    change _ = Ideal.comap (Ideal.Quotient.mk _) (Ideal.comap (e₁.symm.trans e₁).toRingHom _)
    simp only [AlgEquiv.symm_trans_self, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.refl_toRingHom, Ideal.comap_id]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    simpa [left_eq_sup, ← RingHom.ker_eq_comap_bot, Ideal.span_le] using heP''

end Algebra

/-! ### From `FLT/HenselianLocalRing/Finite.lean` -/

/-! # Finite extensions of henselian local rings are products of henselian local rings -/


open Polynomial TensorProduct

open IsLocalRing

universe u

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

open Polynomial TensorProduct KaehlerDifferential

open nonZeroDivisors

attribute [ext high] Ideal.Quotient.algHom_ext

lemma Ideal.isMaximal_of_isMaximal_under_of_formallyUnramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (I : Ideal S) [I.IsPrime] (hI : (I.under R).IsMaximal) : I.IsMaximal := by
  let Q := I.under R
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (Ideal.IsPrime.ne_top inferInstance)
  have : J.LiesOver Q := ⟨Ideal.IsMaximal.eq_of_le hI (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.comap_mono hIJ)⟩
  suffices J ≤ I from this.antisymm hIJ ▸ hJ
  refine ((PrimeSpectrum.primesOverOrderIsoFiber R S Q).le_iff_le
    (x := ⟨J, inferInstance, inferInstance⟩)
    (y := ⟨I, inferInstance, inferInstance⟩)).mp ?_
  let : Module.Free Q.ResidueField (Q.ResidueField ⊗[R] S) := .of_divisionRing ..
  have := Algebra.FormallyUnramified.finite_of_free Q.ResidueField (Q.ResidueField ⊗[R] S)
  have : IsArtinianRing (Q.ResidueField ⊗[R] S) := .of_finite Q.ResidueField _
  rw [← PrimeSpectrum.asIdeal_le_asIdeal]
  refine (Ideal.IsMaximal.eq_of_le (Ideal.IsPrime.isMaximal' (R := Q.ResidueField ⊗[R] S)
    inferInstance) (Ideal.IsPrime.ne_top inferInstance) ?_).ge
  rwa [PrimeSpectrum.asIdeal_le_asIdeal, OrderIso.le_iff_le]

instance {A : Type*} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    {P : Ideal A} [P.IsPrime] : Algebra.IsEtaleAt R P :=
  have : Algebra.IsEtaleAt A P :=
    .of_isLocalization P.primeCompl
  Algebra.FormallyEtale.comp _ A _

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
lemma HenselianLocalRing.exists_lift_of_to_ResidueField
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
    [HenselianLocalRing R] (f : A →ₐ[R] ResidueField R) :
    ∃ (g : A →ₐ[R] R), f = (IsScalarTower.toAlgHom _ _ _).comp g := by
  let P := RingHom.ker f.toRingHom
  have : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨r, hrP, ⟨⟨𝓟⟩⟩⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) P
  let φ : Localization.Away r →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := .powers r) (f := f) <| Subtype.forall.mpr <|
      show Submonoid.powers r ≤ (IsUnit.submonoid _).comap _ from Submonoid.powers_le.mpr
      (by simpa [IsUnit.mem_submonoid_iff])
  obtain ⟨x, hx⟩ := residue_surjective (φ 𝓟.x)
  obtain ⟨y, hy, hxy⟩ := HenselianLocalRing.is_henselian 𝓟.f 𝓟.monic_f x (by
    rw [← residue_eq_zero_iff, ← ResidueField.algebraMap_eq, eval, hom_eval₂, RingHom.comp_id,
      ← aeval_def, ResidueField.algebraMap_eq, hx, aeval_algHom_apply, 𝓟.hasMap.1, map_zero]) (by
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, eval, hom_eval₂,
      RingHom.comp_id, ← aeval_def, ResidueField.algebraMap_eq, hx, aeval_algHom_apply]
    exact (𝓟.hasMap.isUnit_derivative_f.map φ).ne_zero)
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hxy
  have Hy : 𝓟.HasMap y := by
    refine ⟨hy, ?_⟩
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← aeval_algebraMap_apply,
      ResidueField.algebraMap_eq, hxy, hx, aeval_algHom_apply]
    exact (𝓟.hasMap.2.map φ).ne_zero
  refine ⟨((𝓟.lift _ Hy).comp 𝓟.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom _ _ _), ?_⟩
  trans ((φ.comp 𝓟.equivRing.symm.toAlgHom).comp 𝓟.equivRing.toAlgHom).comp
      (IsScalarTower.toAlgHom _ _ _)
  · ext; simp [φ]
  · simp_rw [← AlgHom.comp_assoc]
    congr 2
    ext
    simp [hxy, hx]

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
set_option backward.isDefEq.respectTransparency false in
lemma HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
    {R A : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (n : ℕ) (e : Fin n → A) (he : CompleteOrthogonalIdempotents e),
      ∀ i, IsLocalRing (he.idem i).Corner := by
  obtain ⟨R', _, _, _, P, _, _, n, e, he, P', _, _, hP, hP', H⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (R := R) (S := A) 𝓂[R]
  let φ : 𝓀[R] ≃ₐ[R] 𝓂[R].ResidueField := .ofBijective
    (IsScalarTower.toAlgHom R (R ⧸ 𝓂[R]) 𝓂[R].ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField _)
  let φ' := φ.trans (AlgEquiv.ofBijective _ hP)
  obtain ⟨ψ, hψ⟩ := HenselianLocalRing.exists_lift_of_to_ResidueField
    (φ'.symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' _))
  have hPeq : P = 𝓂[R].comap ψ.toRingHom := by
    trans RingHom.ker (IsScalarTower.toAlgHom R R' P.ResidueField).toRingHom
    · exact P.ker_algebraMap_residueField.symm
    · rw [← RingHom.ker_comp_of_injective _ (f := RingHomClass.toRingHom φ'.symm) φ'.symm.injective,
        ← AlgEquiv.toAlgHom_toRingHom, AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, hψ,
        AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← 𝓂[R].mk_ker]; rfl
  have hψ : Function.Surjective ψ.toRingHom := fun x ↦ ⟨algebraMap _ _ x, by simp⟩
  have : P.IsMaximal := by rw [hPeq]; exact Ideal.comap_isMaximal_of_surjective _ hψ
  let ψ' : R' ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId _ _).comp ψ) (.id R A) fun _ _ ↦ .all _ _
  have hψ' : Function.Surjective ψ'.toRingHom := fun x ↦ ⟨1 ⊗ₜ x, by simp [ψ']⟩
  have h₁ : ψ' (e (.last _)) = 0 := by
    suffices IsUnit (1 - ψ' (e (Fin.last n))) by
      simpa using this.mul_left_cancel
        (((he.idem (.last n)).map ψ').one_sub.eq.trans (mul_one _).symm)
    by_contra he'
    obtain ⟨M, hM, heM⟩ := Ideal.exists_le_maximal (Ideal.span {1 - ψ' (e (Fin.last n))}) (by simpa)
    have := (H (M.comap ψ'.toRingHom) inferInstance ⟨by
      rw [Ideal.under, Ideal.comap_comap]
      trans M.comap ((algebraMap R A).comp ψ.toRingHom); swap
      · congr 1; ext; simp [ψ']
      · rw [hPeq, ← Ideal.comap_comap,
          eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) M)]⟩).1
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_comap, RingHom.coe_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe] at this heM
    exact Ideal.one_notMem M (by convert add_mem this heM; ring)
  refine ⟨n, ψ' ∘ e ∘ Fin.castSucc, ⟨(he.map ψ'.toRingHom).1.embedding Fin.castSuccEmb, ?_⟩, ?_⟩
  · simpa [Fin.sum_univ_castSucc, h₁] using (he.map ψ'.toRingHom).2
  · intro i
    have he₀ := (he.idem i.castSucc).map ψ'
    let Q := (P' i).comap Algebra.TensorProduct.includeRight.toRingHom
    have _ : (P' i).LiesOver 𝓂[R] := .trans _ P _
    have _ : Q.LiesOver 𝓂[R] :=
      inferInstanceAs (((P' i).comap Algebra.TensorProduct.includeRight).LiesOver _)
    have _ : (P' i).LiesOver 𝓂[R] := .trans _ P _
    have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) _
      (by rw [← Ideal.under, ← Q.over_def 𝓂[R]]; infer_instance)
    have hψ' : Function.Surjective ψ'.toRingHom := fun x ↦ ⟨1 ⊗ₜ x, by simp [ψ']⟩
    have hQP' : Q.comap ψ'.toRingHom = P' i := by
      have : (Ideal.comap ψ'.toRingHom Q).LiesOver P := by
        rw [hPeq]
        simp only [Ideal.liesOver_iff, Ideal.under, Ideal.comap_comap, Q, (P' i).over_def 𝓂[R]]
        congr 1
        ext a; simp [ψ']
      apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
      simp only [Ideal.comap_comap, Q]
      congr 1; ext; simp [ψ']
    have hQP'' : (P' i).comap Algebra.TensorProduct.includeRight.toRingHom = Q := by
      rw [← hQP', Ideal.comap_comap]; convert Ideal.comap_id _; ext; simp [ψ']
    have heQ : RingHom.ker (algebraMap A he₀.Corner) ≤ Q := by
      rw [he₀.ker_toCorner, Ideal.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      rw [← Ideal.IsPrime.mul_mem_left_iff (I := Q) fun h ↦ hP' i (hQP'.le h)]
      simp [mul_sub, ← map_mul, (he.idem _).eq]
    have := Ideal.IsMaximal.map_of_surjective_of_ker_le he₀.toCorner_surjective heQ
    refine IsLocalRing.of_unique_max_ideal ⟨Q.map (algebraMap A he₀.Corner), ‹_›, fun Q' hQ' ↦ ?_⟩
    have inst := Ideal.comap_isMaximal_of_surjective _ he₀.toCorner_surjective (K := Q')
    refine (hQ'.eq_of_le this.ne_top ?_)
    refine Ideal.le_map_of_comap_le_of_surjective _ he₀.toCorner_surjective ?_
    suffices (Q'.comap (algebraMap A _)).comap ψ'.toRingHom = P' i by
      rw [← hQP'', ← this, Ideal.comap_comap,]
      simp only [AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, ψ', Function.comp_apply, le_refl,
        Algebra.TensorProduct.lift_comp_includeRight', AlgHom.id_toRingHom, Ideal.comap_id]
    refine (H _ inferInstance ⟨?_⟩).2 _ ?_
    · rw [hPeq, ← eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
        (Q'.comap (algebraMap A he₀.Corner)))]
      simp only [Ideal.under, Ideal.comap_comap, RingHom.comp_assoc]
      congr 2; ext; simp [ψ']
    · have : algebraMap _ he₀.Corner (ψ' (e i.castSucc)) = 1 := Subtype.ext ((he.idem _).map ψ')
      simpa [this] using Ideal.one_notMem Q'

lemma Ideal.quotientKerAlgEquivOfSurjective_symm_apply' {R₁ A B : Type*} [CommSemiring R₁]
    [Ring A] [Algebra R₁ A] [Semiring B] [Algebra R₁ B] {f : A →ₐ[R₁] B}
    (hf : Function.Surjective ⇑f) (x : A) :
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f x) = x :=
  (Ideal.quotientKerAlgEquivOfSurjective hf).symm_apply_eq.mpr rfl

lemma Module.finrank_pos_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [Nontrivial M] : 0 < Module.finrank R M := by
  nontriviality R
  simpa [Module.finrank_eq_card_chooseBasisIndex] using Fintype.card_pos

lemma Module.finrank_eq_one_iff_algebraMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Nontrivial R] :
    Module.finrank R S = 1 ↔ Function.Bijective (algebraMap R S) := by
  constructor
  · intro H
    let := (Module.basisUnique Unit H).repr ≪≫ₗ Finsupp.uniqueLinearEquiv _ _ .unit
    exact (LinearEquiv.algEquivOfRing this.symm).bijective
  · intro H
    rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) H).toLinearEquiv.finrank_eq, finrank_self]

attribute [local instance] RingHom.ker_isPrime in
theorem HenselianLocalRing.of_finite_aux
    {A : Type*} [CommRing A] [IsLocalRing A]
    (f : A[X]) (a₀ : A) (ha₀ : eval a₀ f ∈ 𝓂[A])
    (ha₀' : IsUnit (eval a₀ (derivative f))) (e : AdjoinRoot f)
    (he : IsIdempotentElem e) [IsLocalRing he.Corner]
    (ha₀'' : AdjoinRoot.liftAlgHom _ (Algebra.ofId _ 𝓀[A]) (algebraMap _ _ a₀)
      (by simpa using ha₀) e ≠ 0) :
    1 ⊗ₜ[A] (algebraMap (AdjoinRoot f) he.Corner) (AdjoinRoot.root f) = residue A a₀ ⊗ₜ[A] 1 := by
  let φ : AdjoinRoot f →ₐ[A] 𝓀[A] := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (algebraMap _ _ a₀) (by simpa using ha₀)
  have hφ : Function.Surjective φ := residue_surjective.forall.mpr fun x ↦ ⟨.of f x, by simp [φ]⟩
  set root := (1 : 𝓀[A]) ⊗ₜ[A] algebraMap _ he.Corner (AdjoinRoot.root f)
  obtain ⟨g, hg⟩ : X - C (residue A a₀) ∣ f.map (residue A) := by
    simpa [dvd_iff_isRoot, eval_map] using ha₀
  obtain ⟨g, rfl⟩ := Polynomial.map_surjective _ residue_surjective g
  have hga₀ : IsUnit (eval a₀ g) := by
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq,
      eval, hom_eval₂, RingHom.comp_id, ← eval_map, ResidueField.algebraMap_eq] at ha₀' ⊢
    rw [← derivative_map, hg] at ha₀'
    simpa using ha₀'
  let φ' : he.Corner →ₐ[A] 𝓀[A] := by
    refine AlgHom.liftOfSurjective (IsScalarTower.toAlgHom _ _ _)
      he.toCorner_surjective φ ?_
    refine he.ker_toCorner.trans_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [← Ideal.IsPrime.mul_mem_left_iff (by exact ha₀''), mul_sub, mul_one, he.eq, sub_self]
    exact zero_mem _
  have hφ' (x : AdjoinRoot f) : φ' (algebraMap _ _ x) = φ x :=
    AlgHom.liftOfSurjective_apply ..
  have hφ'' : IsLocalHom φ'.toRingHom :=
    .of_surjective _ (AlgHom.liftOfSurjective_surjective _ _ _ _ hφ)
  have hrootf : aeval root f = 0 := by
    refine (aeval_algHom_apply Algebra.TensorProduct.includeRight _ _).trans ?_
    simp [aeval_algebraMap_apply]
  have hrootg : IsUnit (aeval root g) := by
    have := hφ''.1 (algebraMap _ _ (AdjoinRoot.mk f g)) (by simpa [hφ', φ])
    convert this.map (Algebra.TensorProduct.includeRight : _ →ₐ[A] 𝓀[A] ⊗[A] he.Corner)
    rw [← AdjoinRoot.aeval_eq, ← aeval_algebraMap_apply, ← aeval_algHom_apply]
    rfl
  rw [← sub_eq_zero, ← hrootg.mul_left_inj]
  simpa [← ResidueField.algebraMap_eq, hrootf, -mul_eq_zero, -mul_eq_left₀, -mul_eq_right₀] using
    congr(aeval root $hg).symm

lemma HenselianLocalRing.of_finite
    {R A : Type*} [CommRing R] [HenselianLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [IsLocalRing A] : HenselianLocalRing A := by
  refine ⟨fun f hf a₀ ha₀ ha₀' ↦ ?_⟩
  have := hf.finite_adjoinRoot
  have := hf.free_adjoinRoot
  have : Module.Finite R (AdjoinRoot f) := .trans A _
  obtain ⟨n, e, he, h⟩ := HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
    (R := R) (A := AdjoinRoot f)
  let φ : AdjoinRoot f →ₐ[A] 𝓀[A] := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (algebraMap _ _ a₀) (by simpa using ha₀)
  have hφ : Function.Surjective φ := residue_surjective.forall.mpr fun x ↦ ⟨.of f x, by simp [φ]⟩
  have : (RingHom.ker φ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hφ
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ RingHom.ker φ := by
    by_contra! H
    exact Ideal.one_notMem (RingHom.ker φ.toRingHom) (he.complete ▸ sum_mem fun i _ ↦ H i)
  have : Module.Finite A (he.idem i).Corner := .of_surjective
    (IsScalarTower.toAlgHom _ (AdjoinRoot f) _).toLinearMap (he.idem i).toCorner_surjective
  have : Module.Free A (he.idem i).Corner :=
    have : Module.Projective A (he.idem i).Corner :=
      .of_split ⟨⟨Subtype.val, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
        (IsScalarTower.toAlgHom _ (AdjoinRoot f) _).toLinearMap
        (LinearMap.ext fun a ↦ Subtype.ext ((Subsemigroup.mem_corner_iff (he.idem i)).mp a.2).2)
    have : Module.Flat A (he.idem i).Corner := Module.Flat.of_projective
    Module.free_of_flat_of_isLocalRing
  have hroot :
      1 ⊗ₜ algebraMap _ (he.idem i).Corner (AdjoinRoot.root f) = residue A a₀ ⊗ₜ[A] 1 :=
    HenselianLocalRing.of_finite_aux f a₀ ha₀ ha₀' _ (he.idem i) hi
  have H : Function.Surjective (algebraMap 𝓀[A] (𝓀[A] ⊗[A] (he.idem i).Corner)) := by
    intro x
    obtain ⟨x, rfl⟩ := Algebra.TensorProduct.includeRight_surjective _
      (by exact residue_surjective) x
    obtain ⟨x, rfl⟩ := (he.idem i).toCorner_surjective x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have h₁ : residue _ (eval a₀ g) = φ (.mk f g) := by simp [φ]
    have h₂ : (IsScalarTower.toAlgHom _ _ (𝓀[A] ⊗[A] (he.idem i).Corner)).comp φ =
        Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom _ _ _) := by
      ext; simp [φ, ← hroot]
    use algebraMap _ _ (aeval a₀ g)
    trans algebraMap _ _ (eval a₀ g)
    · simp
    · simpa [φ] using congr($h₂ (.mk f g))
  have : Module.finrank A (he.idem i).Corner = 1 := by
    apply le_antisymm ?_ (Nat.one_le_iff_ne_zero.mpr Module.finrank_pos_of_free.ne')
    · rw [← Module.finrank_baseChange (R := 𝓀[A]), finrank_le_one_iff]
      refine ⟨1, H.forall.mpr fun x ↦
        ⟨x, by simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']⟩⟩
  rw [Module.finrank_eq_one_iff_algebraMap_bijective] at this
  obtain ⟨a, ha⟩ := this.2 (algebraMap _ _ (AdjoinRoot.root f))
  refine ⟨a, this.1 ?_, ?_⟩
  · rw [eval, hom_eval₂, RingHom.comp_id, ← aeval_def, ha, aeval_algebraMap_apply]
    simp
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    apply (algebraMap 𝓀[A] (𝓀[A] ⊗[A] (he.idem i).Corner)).injective
    trans Algebra.TensorProduct.includeRight (algebraMap _ _ a)
    · simp
    · rw [ha]; simp [← hroot]

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [Algebra.IsIntegral R S] [Nontrivial S] : IsLocalHom (algebraMap R S) := by
  have : (algebraMap R S).kerLift.IsIntegral :=
    .tower_top (Ideal.Quotient.mk _) _
      (by have := algebraMap_isIntegral_iff.mpr ‹Algebra.IsIntegral R S›; exact this)
  have := this.isLocalHom (algebraMap R S).kerLift_injective
  have : Nontrivial (R ⧸ RingHom.ker (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker (algebraMap R S))) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  exact RingHom.isLocalHom_comp (algebraMap R S).kerLift (Ideal.Quotient.mk _)

lemma HenselianLocalRing.exist_residueFieldMap_eq_of_etale {A B : Type*}
    [CommRing A] [IsLocalRing A] [Algebra R A]
      [IsLocalHom (algebraMap R A)] [Algebra.Etale R A]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]
    (f : 𝓀[A] →ₐ[𝓀[R]] 𝓀[B]) :
    ∃ (g : A →ₐ[R] B) (_ : IsLocalHom g.toRingHom), ResidueField.map g.toRingHom = f.toRingHom := by
  have : HenselianLocalRing B := .of_finite (R := R)
  let f' : B ⊗[R] A →ₐ[B] 𝓀[B] :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((f.restrictScalars R).comp <| IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  obtain ⟨g, hg⟩ := HenselianLocalRing.exists_lift_of_to_ResidueField f'
  let g' := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have H (x : _) : residue B (g' x) = f (residue _ x) := by
    trans f' (1 ⊗ₜ x)
    · exact congr($hg (1 ⊗ₜ x)).symm
    · simp [f']
  have : IsLocalHom g'.toRingHom := by
    refine ⟨fun x hx ↦ ?_⟩
    rw [← residue_ne_zero_iff_isUnit] at hx
    simpa [H, f'] using hx
  refine ⟨g', this, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp [ResidueField.map_residue, H]

lemma IsLocalRing.eq_of_eval_derivative_notMem
    (p : R[X]) (a b : R) (ha : p.eval a = 0) (hb : p.eval b = 0) (hab : a - b ∈ 𝓂[R])
    (ha' : p.derivative.eval a ∉ 𝓂[R]) : a = b := by
  obtain ⟨c, hc⟩ : ∃ c, c * (b - a) * (b - a) + eval a (derivative p) * (b - a) = 0 := by
    have : (taylor a p).eval (b - a) = 0 := by
      rw [taylor_eval]; simp [hb]
    rw [eval_eq_sum_range' (n := (taylor (b - a) p).natDegree + 2),
      Finset.sum_range_succ',  Finset.sum_range_succ'] at this
    · simp only [natDegree_taylor, pow_add, pow_one, ← mul_assoc, ← Finset.sum_mul, zero_add,
        taylor_coeff_one, taylor_coeff_zero, ha, pow_zero, mul_one, add_zero] at this
      exact ⟨_, this⟩
    · simp
  have hc' : IsUnit (c * (b - a) + eval a (derivative p)) := by
    rwa [← @not_not (IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal,
      Ideal.add_mem_iff_right]
    exact Ideal.mul_mem_left _ _ (sub_mem_comm_iff.mpr hab)
  rwa [← add_mul, hc'.mul_right_eq_zero, sub_eq_zero, eq_comm] at hc

lemma HenselianLocalRing.eq_of_toAlgHom_residueField_comp_eq_of_isStandardEtale
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.IsStandardEtale R A] (f₁ f₂ : A →ₐ[R] R)
    (H : (IsScalarTower.toAlgHom _ _ (ResidueField R)).comp f₁ =
      (IsScalarTower.toAlgHom _ _ _).comp f₂) : f₁ = f₂ := by
  obtain ⟨𝓟⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := A)
  apply 𝓟.hom_ext
  apply IsLocalRing.eq_of_eval_derivative_notMem 𝓟.f
  · rw [← coe_aeval_eq_eval, aeval_algHom_apply, 𝓟.hasMap.1, map_zero]
  · rw [← coe_aeval_eq_eval, aeval_algHom_apply, 𝓟.hasMap.1, map_zero]
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact congr($H _)
  · rw [← coe_aeval_eq_eval, aeval_algHom_apply]
    simpa using 𝓟.hasMap.isUnit_derivative_f.map f₁

lemma HenselianLocalRing.eq_of_toAlgHom_residueField_comp_eq
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.Etale R A] (f₁ f₂ : A →ₐ[R] R)
    (H : (IsScalarTower.toAlgHom _ _ (ResidueField R)).comp f₁ =
      (IsScalarTower.toAlgHom _ _ _).comp f₂) : f₁ = f₂ := by
  let P := RingHom.ker ((IsScalarTower.toAlgHom R R 𝓀[R]).comp f₁).toRingHom
  have : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨r, hrP, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) P
  have hf₁ : IsUnit (f₁ r) := by
    rw [← residue_ne_zero_iff_isUnit]
    exact hrP
  have hf₂ : IsUnit (f₂ r) := by
    rw [← residue_ne_zero_iff_isUnit]
    refine congr($H r).symm.trans_ne hrP
  have : IsLocalization.liftAlgHom (S := Localization.Away r) (f := f₁) (M := .powers r)
        (by simp [Submonoid.mem_powers_iff, hf₁.pow _]) =
      IsLocalization.liftAlgHom (f := f₂) (M := .powers r)
        (by simp [Submonoid.mem_powers_iff, hf₂.pow _]) := by
    apply HenselianLocalRing.eq_of_toAlgHom_residueField_comp_eq_of_isStandardEtale
    apply IsLocalization.algHom_ext (.powers r)
    ext x
    simpa [Algebra.algHom] using congr($H x)
  ext x
  simpa using congr($this (algebraMap _ _ x))

lemma HenselianLocalRing.eq_of_residueFieldMap_eq {A B : Type*}
    [CommRing A] [IsLocalRing A] [Algebra R A]
    [Algebra.Etale R A]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]
    (f₁ f₂ : A →ₐ[R] B) [IsLocalHom f₁.toRingHom] [IsLocalHom f₂.toRingHom]
    (H : ResidueField.map f₁.toRingHom = ResidueField.map f₂.toRingHom) : f₁ = f₂ := by
  have : HenselianLocalRing B := .of_finite (R := R)
  have := HenselianLocalRing.eq_of_toAlgHom_residueField_comp_eq
    (R := B) (A := B ⊗[R] A)
    (Algebra.TensorProduct.lift (Algebra.ofId _ _) f₁ fun _ _ ↦ .all _ _)
    (Algebra.TensorProduct.lift (Algebra.ofId _ _) f₂ fun _ _ ↦ .all _ _)
    (by ext a; simpa using congr($H (algebraMap _ _ a)))
  ext x
  simpa using congr($this (1 ⊗ₜ x))

lemma HenselianLocalRing.exist_algEquiv_residueFieldMap_eq_of_etale
    {R A B : Type*} [CommRing R] [HenselianLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    (f : 𝓀[A] ≃ₐ[𝓀[R]] 𝓀[B]) :
    ∃ (g : A ≃ₐ[R] B) (_ : IsLocalHom g.toRingHom), ResidueField.map g.toRingHom = f.toRingHom := by
  obtain ⟨φ, hφ, hφ'⟩ := exist_residueFieldMap_eq_of_etale f.toAlgHom
  obtain ⟨ψ, hψ, hψ'⟩ := exist_residueFieldMap_eq_of_etale f.symm.toAlgHom
  have : φ.comp ψ = .id _ _ := by
    have : IsLocalHom (AlgHom.id R B).toRingHom := by dsimp; infer_instance
    have : IsLocalHom (φ.comp ψ).toRingHom := by
      dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢; exact RingHom.isLocalHom_comp _ _
    apply HenselianLocalRing.eq_of_residueFieldMap_eq
    dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢ hφ' hψ'
    simp only [ResidueField.map_comp, ResidueField.map_id, *]
    ext; simp
  have : ψ.comp φ = .id _ _ := by
    have : IsLocalHom (AlgHom.id R A).toRingHom := by dsimp; infer_instance
    have : IsLocalHom (ψ.comp φ).toRingHom := by
      dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢; exact RingHom.isLocalHom_comp _ _
    apply HenselianLocalRing.eq_of_residueFieldMap_eq
    dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢ hφ' hψ'
    simp only [ResidueField.map_comp, ResidueField.map_id, *]
    ext; simp
  exact ⟨.ofAlgHom φ ψ ‹_› ‹_›, _, hφ'⟩

end
