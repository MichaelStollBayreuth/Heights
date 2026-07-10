import Heights.ForMathlib
import Heights.FractionalIdeal
import Heights.SIntegers
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

## Implementation

The `S`-class group is realized as `ClassGroup (S.integer K)`, the class group of the ring
`𝒪_S = Set.integer S K` of `S`-integers, which `Heights.SIntegers` shows to be a Dedekind domain
with fraction field `K`, height one spectrum `{v | v ∉ S}` (valuation-compatibly) and finite
class group whenever `Cl(R)` is finite. Via this dictionary the Selmer condition on a class
`u(Kˣ)ⁿ ∈ K(S,n)` says exactly that the principal fractional ideal `(u)` of `𝒪_S` has all its
valuations divisible by `n` (`mem_selmerGroup_iff_unitsNDivisible`), so the `n`-th-root class
map of `Heights.FractionalIdeal` (`FractionalIdeal.nthRootClass`, built from the isomorphism of
the group of fractional ideals with the free abelian group on the primes) descends to the
right-hand map `toSClassGroup : K(S,n) →* Cl(𝒪_S)` of the fundamental exact sequence.

Note that `toSClassGroup` is *not* surjective onto `Cl(𝒪_S)` in general: its image is the
`n`-torsion subgroup (`range_toSClassGroup`), as the sequence above says.

## Main definitions

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
* `IsDedekindDomain.range_toSClassGroup`: exactness on the right; the image is the `n`-torsion
  of the class group.
* `IsDedekindDomain.finite_selmerGroup`: **the main result**, `K(S,n)` is finite.
* `IsDedekindDomain.finite_selmerGroupOfEquiv`: the Selmer group of a finite étale algebra is
  finite.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

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

/-- Transport of the integer-valued valuation along the spectrum correspondence between the
primes of `R` off `S` and the primes of `𝒪_S`. -/
lemma SInteger.valuationOfNeZero_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S})
    (u : Kˣ) : (SInteger.heightOneSpectrumEquiv K S v).valuationOfNeZero u
      = (v : HeightOneSpectrum R).valuationOfNeZero u := by
  rw [← WithZero.coe_inj,
    show ((_ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ from
      HeightOneSpectrum.valuationOfNeZero_eq _ u, HeightOneSpectrum.valuationOfNeZero_eq,
    SInteger.valuation_heightOneSpectrumEquiv K S v (u : K)]

/-- **The membership bridge**: the class of `u` lies in the Selmer group `K(S,n)` exactly when
the principal fractional ideal `(u)` of the `S`-integers is `n`-divisible. -/
lemma mem_selmerGroup_iff_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Units.modPow K n) ∈ selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  have lhs : (QuotientGroup.mk u : Units.modPow K n) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd
        ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
    forall₂_congr fun v _ => HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v n u
  have rhs : u ∈ unitsNDivisible (S.integer K) K n ↔
      ∀ w : HeightOneSpectrum (S.integer K),
        (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    refine forall_congr' fun w => ?_
    rw [toAdd_valuationOfNeZero, Int.dvd_neg]
    show (n : ℤ) ∣ count K w ((toPrincipalIdeal (S.integer K) K u :
      (FractionalIdeal (S.integer K)⁰ K)ˣ) : FractionalIdeal (S.integer K)⁰ K) ↔ _
    rw [coe_toPrincipalIdeal]
  rw [lhs, rhs]
  constructor
  · intro h w
    rw [show w = SInteger.heightOneSpectrumEquiv K S
        ((SInteger.heightOneSpectrumEquiv K S).symm w) from
        ((SInteger.heightOneSpectrumEquiv K S).apply_symm_apply w).symm,
      SInteger.valuationOfNeZero_heightOneSpectrumEquiv]
    exact h _ ((SInteger.heightOneSpectrumEquiv K S).symm w).property
  · intro h v hv
    have := h (SInteger.heightOneSpectrumEquiv K S ⟨v, hv⟩)
    rwa [SInteger.valuationOfNeZero_heightOneSpectrumEquiv] at this

/-- The surjection from the `n`-divisible units onto the Selmer group. -/
noncomputable def selmerGroupFromUnits :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).comp
    (unitsNDivisible (S.integer K) K n).subtype).codRestrict _
      (fun u => (mem_selmerGroup_iff_unitsNDivisible K S n (u : Kˣ)).mpr u.2)

@[simp] lemma coe_selmerGroupFromUnits (u : unitsNDivisible (S.integer K) K n) :
    (selmerGroupFromUnits K S n u : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) := rfl

lemma selmerGroupFromUnits_surjective :
    Function.Surjective (selmerGroupFromUnits K S n) := by
  rintro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u =>
    exact ⟨⟨u, (mem_selmerGroup_iff_unitsNDivisible K S n u).mp hc⟩, rfl⟩

/-- The kernel of `selmerGroupFromUnits` is contained in that of the `n`-th-root class map:
an `n`-th power has principal `n`-th root. -/
lemma ker_selmerGroupFromUnits_le [NeZero n] :
    (selmerGroupFromUnits K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have : (QuotientGroup.mk (u : Kˣ) : Units.modPow K n) = 1 := congrArg Subtype.val hu
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp this
  exact (nthRootClass_eq_one_iff _ _ (NeZero.ne n) u).mpr ⟨1, w, by
    rw [map_one, one_mul]; exact hw⟩

/-- The right-hand map of the fundamental exact sequence: a Selmer class is sent to the ideal
class of the `n`-th root of the principal ideal `(u)` of any representative `u`, in the class
group of the ring of `S`-integers. Obtained by descending `FractionalIdeal.nthRootClass` along
`selmerGroupFromUnits`. -/
noncomputable def toSClassGroup [NeZero n] :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (QuotientGroup.lift _ (nthRootClass (S.integer K) K n)
      (ker_selmerGroupFromUnits_le K S n)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm.toMonoidHom

/-- Evaluation of `toSClassGroup` on the class of an `n`-divisible unit. -/
lemma toSClassGroup_selmerGroupFromUnits [NeZero n] (u : unitsNDivisible (S.integer K) K n) :
    toSClassGroup K S n (selmerGroupFromUnits K S n u) =
      nthRootClass (S.integer K) K n u := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm (selmerGroupFromUnits K S n u) =
        QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [toSClassGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk']

/-- The image of a unit of the `S`-integers in `Kˣ`, via the `S`-unit equivalence. -/
lemma coe_unitEquivUnitsInteger_symm (a : (S.integer K)ˣ) :
    ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
      Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := by
  apply Units.ext
  rw [Set.unitEquivUnitsInteger_symm_apply_coe]
  rfl

/-- Exactness of the fundamental exact sequence in the middle: a Selmer class has trivial
`n`-th-root ideal class exactly when it is represented by an `S`-unit. -/
theorem ker_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).ker = (sUnitToSelmer K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
  rw [MonoidHom.mem_ker, toSClassGroup_selmerGroupFromUnits,
    nthRootClass_eq_one_iff _ _ (NeZero.ne n)]
  constructor
  · rintro ⟨a, w, hw⟩
    refine ⟨(S.unitEquivUnitsInteger K).symm a, Subtype.ext ?_⟩
    show (QuotientGroup.mk _ : Units.modPow K n) = QuotientGroup.mk (u : Kˣ)
    rw [coe_unitEquivUnitsInteger_symm, ← hw, QuotientGroup.mk_mul,
      show (QuotientGroup.mk (w ^ n) : Units.modPow K n) = 1 from
        (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩]
    exact (mul_one _).symm
  · rintro ⟨s, hs⟩
    have hcoe : (QuotientGroup.mk (s : Kˣ) : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) :=
      congrArg Subtype.val hs
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hcoe
    refine ⟨S.unitEquivUnitsInteger K s, w, ?_⟩
    have hmap : Units.map (algebraMap (S.integer K) K : S.integer K →* K)
        (S.unitEquivUnitsInteger K s) = (s : Kˣ) := by
      rw [← coe_unitEquivUnitsInteger_symm, MulEquiv.symm_apply_apply]
    rw [powMonoidHom_apply] at hw
    rw [hmap, hw]
    group

/-- Exactness of the fundamental exact sequence on the right: the image of `toSClassGroup` is
the `n`-torsion of the class group of the `S`-integers. (Surjectivity onto the full class group
fails in general.) -/
theorem range_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).range =
      (powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker := by
  ext c
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
    rw [toSClassGroup_selmerGroupFromUnits, nthRootClass, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ← map_pow, nthRootHom_pow]
    exact ClassGroup.mk_eq_one_iff_exists.mpr ⟨(u : Kˣ), rfl⟩
  · intro hc
    obtain ⟨I, rfl⟩ : ∃ I, ClassGroup.mk K I = c :=
      ClassGroup.induction (K := K) (fun I => ⟨I, rfl⟩) c
    rw [← map_pow, ClassGroup.mk_eq_one_iff_exists] at hc
    obtain ⟨x, hx⟩ := hc
    have hcount (v : HeightOneSpectrum (S.integer K)) :
        count K v ((toPrincipalIdeal (S.integer K) K x : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) =
          n * count K v ((I : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) := by
      rw [hx, Units.val_pow_eq_pow_val, count_pow]
    have hmem : x ∈ unitsNDivisible (S.integer K) K n := fun v => by
      rw [hcount v]; exact Dvd.intro _ rfl
    refine ⟨selmerGroupFromUnits K S n ⟨x, hmem⟩, ?_⟩
    rw [toSClassGroup_selmerGroupFromUnits]
    show ClassGroup.mk K (nthRootHom (S.integer K) K n
      (unitsNDivisibleToNDivisible (S.integer K) K n ⟨x, hmem⟩)) = _
    congr 1
    refine count_injective fun v => ?_
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcount v,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne n))]

/-!
### Finiteness
-/

variable (R) in
/-- **The Selmer group `K(S,n)` is finite**, provided that the class group of `R` is finite, that
`Rˣ` is finitely generated, that `S` is finite and that `n ≠ 0`.

The image of `sUnitModPowToSelmer` is finite, since its source is the quotient of a finitely
generated commutative group (`fg_sUnit`) by its `n`-th powers (`CommGroup.finite_modPow`).
By `ker_toSClassGroup` that image is the kernel of `toSClassGroup`, whose target
`ClassGroup (S.integer K)` is finite by `SInteger.finite_classGroup`. -/
theorem finite_selmerGroup [Finite (ClassGroup R)] [Group.FG Rˣ] (hS : S.Finite) [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have := fg_sUnit K S hS
  have hker : Finite (toSClassGroup K S n).ker := by
    rw [ker_toSClassGroup, ← range_sUnitModPowToSelmer]
    have := CommGroup.finite_modPow (G := S.unit K) n
    exact Finite.Set.finite_range _
  have hquot : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (toSClassGroup K S n).ker) :=
    Finite.of_injective _ (QuotientGroup.kerLift_injective (toSClassGroup K S n))
  exact Finite.of_subgroup_quotient (toSClassGroup K S n).ker

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
