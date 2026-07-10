import Heights.ForMathlib
import Mathlib

/-!
# Finiteness of Selmer groups

Let `R` be a Dedekind domain with fraction field `K`, let `S` be a set of primes of `R` and let
`n` be a positive integer. `Mathlib.RingTheory.DedekindDomain.SelmerGroup` defines the Selmer
group `K(S,n) ≤ Kˣ/(Kˣ)ⁿ` as the classes whose `v`-adic valuation is divisible by `n` for all
`v ∉ S`, and records as a `TODO` both the maps in the fundamental exact sequence and the
finiteness of `K(S,n)`. This file supplies them, and deduces the finiteness of the Selmer group
of a finite étale `K`-algebra, which is what the proof of the Weak Mordell-Weil theorem
(`Heights.WeakMordellWeil`, Step 7) needs.

## The hypotheses

The finiteness of `K(S,n)` is *not* automatic for a general Dedekind domain: it fails already for
`R = K` a field with `Kˣ` not `n`-divisible-of-finite-index. The fundamental exact sequence
```
1 → 𝒪_S(K)ˣ / (𝒪_S(K)ˣ)ⁿ → K(S,n) → Cl_S(R)[n] → 1
```
shows that the two things one needs are

* the `S`-unit group `Set.unit S K` is finitely generated, and
* the `S`-class group `Cl_S(R)` is finite.

Each of these follows from the corresponding statement for `S = ∅` together with `S` being finite:
`Cl_S(R)` is by construction a quotient of `Cl(R)`, and `𝒪_S(K)ˣ` is an extension of a subgroup
of the free abelian group `ℤ^S` by `Rˣ`. So the weakest reasonable hypotheses, and the ones used
below, are

* `[Finite (ClassGroup R)]`,
* `[Group.FG Rˣ]`,
* `S.Finite`, and
* `[NeZero n]`.

For `R` the ring of integers of a number field, the first is the class number theorem
(`Fintype (ClassGroup (𝓞 K))`) and the second is Dirichlet's unit theorem
(`Monoid.FG (𝓞 K)ˣ`), both in Mathlib; see the section `NumberField` at the end. Nothing here
needs `R` to be of *arithmetic* type beyond these two properties, and in particular the results
apply verbatim to the ring of integers of a function field.

Note that `[NeZero n]` cannot be dropped: `K(S,0) = Kˣ`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.classGroupMk`: the class of a height one prime.
* `IsDedekindDomain.sClassGroup`: the `S`-class group `Cl(R)` modulo the classes of primes in `S`.
* `IsDedekindDomain.sUnitValuation`: the tuple of `v`-adic valuations of an `S`-unit,
  for `v ∈ S`.
* `IsDedekindDomain.sUnitToSelmer` and `IsDedekindDomain.sUnitModPowToSelmer`: the left-hand map
  of the fundamental exact sequence.
* `IsDedekindDomain.toSClassGroup`: the right-hand map of the fundamental exact sequence.
* `IsDedekindDomain.selmerGroupPi` and `IsDedekindDomain.selmerGroupOfEquiv`: the Selmer group of
  a finite étale algebra, presented through a decomposition into fields.

## Main statements

* `IsDedekindDomain.fg_sUnit`: finite generation of the `S`-unit group.
* `IsDedekindDomain.ker_toSClassGroup`: exactness of the fundamental sequence in the middle.
* `IsDedekindDomain.finite_selmerGroup`: **the main result**, `K(S,n)` is finite.
* `IsDedekindDomain.finite_selmerGroupOfEquiv`: the Selmer group of a finite étale algebra is
  finite.

## TODO

Everything except the three `sorry`s below is proved; in particular, `finite_selmerGroup` is a
complete reduction of the main result to them, and the étale part needs nothing further.

* `toSClassGroup` and `ker_toSClassGroup`: this needs to write the fractional ideal `(x)` of an
  `x ∈ K(S,n)` as `𝔞 ^ n` times an ideal supported on `S`, and to check that the class of `𝔞` in
  `Cl_S(R)` depends only on the Selmer class.
* `surjective_toSClassGroup`, exactness on the right. It is not needed for finiteness, but it is
  the remaining half of the fundamental exact sequence.

The plan for the first two is to go through the ring `𝒪_S(K) = Set.integer S K` of `S`-integers,
proving that it is a Dedekind domain with fraction field `K` whose class group is `Cl_S(R)` and
whose height one spectrum is `{v | v ∉ S}`. That reduces the fundamental exact sequence to the
case `S = ∅`, where the map to the class group is the class of the ideal `𝔞` with `𝔞 ^ n = (x)`.
Mathlib has none of these facts about `Set.integer S K` yet, but they are of independent
interest, which is why this route is preferred to an ad hoc construction of `toSClassGroup`.

-/

open IsDedekindDomain

/-!
### Quotients of finitely generated commutative groups
-/

/-- A commutative group is finitely generated iff it is finitely generated as a `ℤ`-module. -/
theorem Module.finite_int_additive (G : Type*) [CommGroup G] [Group.FG G] :
    Module.Finite ℤ (Additive G) :=
  Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr ‹_›)

theorem Group.fg_of_module_finite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : Group.FG G :=
  AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp h)

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring. -/
theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    Group.FG H :=
  have : Module.Finite ℤ (Additive G) := Module.finite_int_additive G
  Group.fg_of_module_finite_int <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)

/-- An extension of finitely generated commutative groups is finitely generated. -/
theorem CommGroup.fg_of_fg_ker_of_fg_range {G H : Type*} [CommGroup G] [CommGroup H] (φ : G →* H)
    (hker : Group.FG φ.ker) (hrange : Group.FG φ.range) : Group.FG G := by
  have h₁ : Module.Finite ℤ (Additive φ.ker) := Module.finite_int_additive _
  have h₂ : Module.Finite ℤ (Additive φ.range) := Module.finite_int_additive _
  refine Group.fg_of_module_finite_int (Module.Finite.of_exact
    (f := (MonoidHom.toAdditive φ.ker.subtype).toIntLinearMap)
    (g := (MonoidHom.toAdditive φ.rangeRestrict).toIntLinearMap) (fun x ↦ ?_)
    φ.rangeRestrict_surjective)
  simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive]
  refine ⟨fun hx ↦ ⟨⟨Additive.toMul x, ?_⟩, rfl⟩, ?_⟩
  · simpa [Subtype.ext_iff] using hx
  · rintro ⟨y, rfl⟩
    exact Subtype.ext y.2

/-- A finitely generated commutative group of finite exponent is finite. -/
theorem CommGroup.finite_of_fg_of_pow_eq_one {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ)
    [NeZero n] (hn : ∀ x : G, x ^ n = 1) : Finite G := by
  let _ : Module (ZMod n) (Additive G) := AddCommGroup.zmodModule (n := n) hn
  have h₁ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (by rwa [AddGroup.fg_iff_mul_fg])
  have h₂ : Module.Finite (ZMod n) (Additive G) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod n) (Additive G)
  have := Module.finite_of_finite (ZMod n) (M := Additive G)
  exact Finite.of_equiv _ (Additive.toMul (α := G))

/-- The group of `n`-th power classes of a finitely generated commutative group is finite. -/
theorem CommGroup.finite_modPow {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ) [NeZero n] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  have : Group.FG (G ⧸ (powMonoidHom n : G →* G).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  refine finite_of_fg_of_pow_eq_one n fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-!
### The `S`-class group

`Cl_S(R)` is the class group of `R` modulo the subgroup generated by the classes of the primes
in `S`; equivalently, the class group of the ring `𝒪_S(K)` of `S`-integers. Only the first
description is used here, as Mathlib does not yet know that `Set.integer S K` is a Dedekind
domain with class group the quotient.
-/

namespace HeightOneSpectrum

/-- The class of a height one prime in the class group. -/
noncomputable def classGroupMk (v : HeightOneSpectrum R) : ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

end HeightOneSpectrum

variable (R) in
/-- The `S`-class group: the class group of `R` modulo the classes of the primes in `S`. -/
noncomputable def sClassGroup (S : Set (HeightOneSpectrum R)) : Type _ :=
  ClassGroup R ⧸ Subgroup.closure (HeightOneSpectrum.classGroupMk '' S)

namespace sClassGroup

variable (R) in
noncomputable instance (S : Set (HeightOneSpectrum R)) : CommGroup (sClassGroup R S) :=
  inferInstanceAs <| CommGroup (ClassGroup R ⧸ _)

variable (R) in
/-- The `S`-class group is a quotient of the class group, so it is finite as soon as the latter
is. -/
instance instFinite (S : Set (HeightOneSpectrum R)) [Finite (ClassGroup R)] :
    Finite (sClassGroup R S) :=
  inferInstanceAs <| Finite (ClassGroup R ⧸ _)

end sClassGroup

/-!
### `S`-units

`Set.unit S K` is the subgroup of `x : Kˣ` with `v x = 1` for all `v ∉ S`. Sending `x` to its
tuple of valuations at the primes *in* `S` gives a homomorphism to `ℤ^S` whose kernel is the
group of `∅`-units, i.e. `Rˣ`. When `S` is finite this exhibits `Set.unit S K` as an extension
of a subgroup of a free abelian group of finite rank by `Rˣ`.
-/

variable (S : Set (HeightOneSpectrum R))

/-- The tuple of `v`-adic valuations of an `S`-unit at the primes `v ∈ S`. -/
noncomputable def sUnitValuation : S.unit K →* (S → Multiplicative ℤ) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ)
  map_one' := funext fun _ ↦ map_one _
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul]; rfl

@[simp]
lemma sUnitValuation_apply (x : S.unit K) (v : S) :
    sUnitValuation K S x v = (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ) :=
  rfl

/-- The kernel of `sUnitValuation` consists of the `∅`-units, i.e. of the units of `R`. -/
theorem ker_sUnitValuation :
    (sUnitValuation K S).ker =
      ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext x
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, sUnitValuation_apply,
    Subgroup.mem_subgroupOf]
  refine ⟨fun hx v _ ↦ ?_, fun hx v ↦ ?_⟩
  · by_cases hv : v ∈ S
    · simpa using (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mp (hx ⟨v, hv⟩)
    · exact x.property v hv
  · exact (v.1.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by
      simpa using hx v.1 (Set.notMem_empty _))

variable (R) in
/-- The `∅`-units of `K` are the units of `R`. -/
noncomputable def unitsEquivEmptyUnit : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).unit K :=
  let e₁ : R ≃ₐ[R] (⊥ : Subalgebra R K) :=
    (Algebra.botEquivOfInjective (IsFractionRing.injective R K)).symm
  let e₂ : (⊥ : Subalgebra R K) ≃ₐ[R] (∅ : Set (HeightOneSpectrum R)).integer K :=
    Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K).symm
  (Units.mapEquiv (e₁.trans e₂).toRingEquiv.toMulEquiv).trans (Set.unitEquivUnitsInteger _ K).symm

/-- The `∅`-units are contained in the `S`-units. -/
theorem emptyUnit_le_unit : (∅ : Set (HeightOneSpectrum R)).unit K ≤ S.unit K :=
  fun _ hx v _ ↦ hx v (Set.notMem_empty v)

/-- **Dirichlet's `S`-unit theorem**, weak form: if `Rˣ` is finitely generated and `S` is finite,
then the group of `S`-units is finitely generated.

The map `sUnitValuation` has finitely generated image (a subgroup of the free abelian group
`ℤ^S` of finite rank) and kernel isomorphic to `Rˣ` (`ker_sUnitValuation`,
`unitsEquivEmptyUnit`), and an extension of a finitely generated group by a finitely generated
group is finitely generated. -/
theorem fg_sUnit [Group.FG Rˣ] (hS : S.Finite) : Group.FG (S.unit K) := by
  have : Finite S := hS.to_subtype
  refine CommGroup.fg_of_fg_ker_of_fg_range (sUnitValuation K S) ?_ (Subgroup.fg_of_commGroup_fg _)
  rw [ker_sUnitValuation]
  have : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K) :=
    Group.fg_of_surjective (f := (unitsEquivEmptyUnit R K).toMonoidHom)
      (unitsEquivEmptyUnit R K).surjective
  exact Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (emptyUnit_le_unit K S)).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (emptyUnit_le_unit K S)).symm.surjective

/-!
### The fundamental exact sequence
-/

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-- The class of an `S`-unit lies in the Selmer group `K(S,n)`. -/
noncomputable def sUnitToSelmer : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
    have : v.valuationOfNeZero (x : Kˣ) = 1 :=
      (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by rw [x.property v hv, WithZero.coe_one])
    simp [this]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The left-hand map of the fundamental exact sequence: an `S`-unit modulo `n`-th powers of
`S`-units maps to the Selmer group `K(S,n)`. -/
noncomputable def sUnitModPowToSelmer :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (sUnitToSelmer K S n) <| by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

@[simp]
lemma range_sUnitModPowToSelmer :
    (sUnitModPowToSelmer K S n).range = (sUnitToSelmer K S n).range := by
  ext x
  exact ⟨by rintro ⟨y, rfl⟩; induction y using QuotientGroup.induction_on with
    | H y => exact ⟨y, rfl⟩, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, hy⟩⟩

variable (R) in
/-- The right-hand map of the fundamental exact sequence.

If `x ∈ Kˣ` represents a class in `K(S,n)`, then `n ∣ ord_v x` for every `v ∉ S`, so the
fractional ideal `(x)` is the `n`-th power of a fractional ideal `𝔞` times an ideal supported on
`S`. The class of `𝔞` in `Cl_S(R)` is independent of both choices, and is `n`-torsion. -/
noncomputable def toSClassGroup :
    selmerGroup (K := K) (S := S) (n := n) →* sClassGroup R S :=
  sorry

variable (R) in
/-- Exactness of the fundamental exact sequence in the middle: a Selmer class is represented by an
`S`-unit exactly when the associated ideal class is trivial. -/
theorem ker_toSClassGroup :
    (toSClassGroup R K S n).ker = (sUnitToSelmer K S n).range :=
  sorry

variable (R) in
/-- Exactness of the fundamental exact sequence on the right. Not needed for finiteness. -/
theorem surjective_toSClassGroup [NeZero n] :
    Function.Surjective (toSClassGroup R K S n) :=
  sorry

/-!
### Finiteness
-/

variable (R) in
/-- **The Selmer group `K(S,n)` is finite**, provided that the class group of `R` is finite, that
`Rˣ` is finitely generated, that `S` is finite and that `n ≠ 0`.

The image of `sUnitModPowToSelmer` is finite, since its source is the quotient of a finitely
generated commutative group (`fg_sUnit`) by its `n`-th powers (`CommGroup.finite_modPow`).
By `ker_toSClassGroup` that image is the kernel of `toSClassGroup`, whose target is finite. -/
theorem finite_selmerGroup [Finite (ClassGroup R)] [Group.FG Rˣ] (hS : S.Finite) [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have := fg_sUnit K S hS
  have hker : Finite (toSClassGroup R K S n).ker := by
    rw [ker_toSClassGroup, ← range_sUnitModPowToSelmer]
    have := CommGroup.finite_modPow (G := S.unit K) n
    exact Finite.Set.finite_range _
  have hquot : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (toSClassGroup R K S n).ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective (toSClassGroup R K S n))
  exact Finite.of_subgroup_quotient (toSClassGroup R K S n).ker

/-!
### Selmer groups of finite étale algebras

A finite étale algebra `A` over `K` is a finite product of finite separable field extensions of
`K`. Choosing a Dedekind order `B i` in each factor `L i` and a finite set `S i` of primes of
`B i`, the Selmer group of `A` is the preimage in `Aˣ/(Aˣ)ⁿ` of the product of the Selmer groups
`L i (S i, n)` under the induced isomorphism. It is finite as soon as each factor's Selmer group
is.

The decomposition `e` is an input rather than something derived from an `Algebra.IsEtale`
hypothesis: Mathlib does not currently provide the splitting of an étale algebra into fields, and
in the application (`Heights.WeakMordellWeil`) the decomposition is explicitly available as
`AdjoinRoot.modPowEquivPiFactors`.
-/

section Etale

variable {ι : Type*} (L : ι → Type*) [(i : ι) → Field (L i)]
  (B : (i : ι) → Type*) [(i : ι) → CommRing (B i)] [(i : ι) → IsDedekindDomain (B i)]
  [(i : ι) → Algebra (B i) (L i)] [(i : ι) → IsFractionRing (B i) (L i)]
  (S : (i : ι) → Set (HeightOneSpectrum (B i))) (n : ℕ)

/-- The product of the Selmer groups of the field factors. -/
noncomputable def selmerGroupPi : Subgroup ((i : ι) → Units.modPow (L i) n) :=
  Subgroup.pi Set.univ fun i ↦ selmerGroup (R := B i) (K := L i) (S := S i) (n := n)

lemma mem_selmerGroupPi_iff (x : (i : ι) → Units.modPow (L i) n) :
    x ∈ selmerGroupPi L B S n ↔
      ∀ i, x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupPi, Subgroup.mem_pi]

theorem finite_selmerGroupPi [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → Group.FG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n] :
    Finite (selmerGroupPi L B S n) := by
  have (i : ι) : Finite (selmerGroup (R := B i) (K := L i) (S := S i) (n := n)) :=
    finite_selmerGroup (B i) (L i) (S i) n (hS i)
  exact Finite.of_injective (fun x i ↦ (⟨x.1 i, (mem_selmerGroupPi_iff L B S n x.1).mp x.2 i⟩ :
    selmerGroup (R := B i) (K := L i) (S := S i) (n := n)))
    fun x y hxy ↦ Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun hxy i)

variable {A : Type*} [CommRing A]

/-- The Selmer group of the étale algebra `A`, transported along a decomposition of `A` into a
product of fields. -/
noncomputable def selmerGroupOfEquiv
    (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n)) :
    Subgroup (Units.modPow A n) :=
  (selmerGroupPi L B S n).comap e.toMonoidHom

/-- The Selmer group of a finite étale algebra is finite. -/
theorem finite_selmerGroupOfEquiv [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → Group.FG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n]
    (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n)) :
    Finite (selmerGroupOfEquiv L B S n e) := by
  have := finite_selmerGroupPi L B S n hS
  exact Finite.of_injective (fun x ↦ (⟨e x.1, x.2⟩ : selmerGroupPi L B S n))
    fun x y hxy ↦ Subtype.ext <| e.injective <| congrArg Subtype.val hxy

end Etale

/-!
### Number fields

For the ring of integers of a number field both hypotheses are theorems of Mathlib, so the
finiteness of `K(S,n)` holds for every finite `S` and every `n ≠ 0`.
-/

section NumberField

open NumberField

variable (F : Type*) [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ)

instance : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance

example [NeZero n] (hS : S.Finite) : Finite (selmerGroup (K := F) (S := S) (n := n)) :=
  finite_selmerGroup (𝓞 F) F S n hS

end NumberField

end IsDedekindDomain
