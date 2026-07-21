module

public import Mathlib
public import Heights.ForMathlib.Basic

@[expose] public section

/-!
# Extension of adic completions along an extension of Dedekind domains

Let `A` be a Dedekind domain with fraction field `K`, let `L/K` be a finite extension and
`B` a Dedekind domain with fraction field `L` extending `A` (e.g. the integral closure of
`A` in `L`), and let `w` be a height-one prime of `B` lying over the height-one prime `v`
of `A`. This file provides

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`: the induced continuous ring
  homomorphism `K_v →+* L_w` of adic completions, with
  `valued_adicCompletionExtension`: the valuation of `L_w` restricted along it is the
  valuation of `K_v` raised to the ramification index of `w` over `v`, and
  `adicCompletionIntegersExtension`, its restriction `𝒪_v →+* 𝒪_w` to the rings of
  integers, under which the maximal ideal contracts to the maximal ideal
  (`comap_maximalIdeal_adicCompletionIntegersExtension`);
* `IsDedekindDomain.HeightOneSpectrum.valuation_maximalIdeal_adicCompletionIntegers`:
  the valuation associated to the height-one prime of the ring of integers `𝒪_v` (a discrete
  valuation ring) of a completion `K_v` is the valuation of the completion;
* `IsDedekindDomain.HeightOneSpectrum.henselianLocalRing_adicCompletionIntegers` (and the
  instances leading up to it): the subspace topology on `𝒪_v` is the `𝔪`-adic topology
  (`isAdic_maximalIdeal_adicCompletionIntegers`, via `mem_maximalIdeal_pow_iff`), `𝒪_v` is
  complete, hence `𝔪`-adically complete, hence a Henselian local ring.

The completion-extension material is adapted from the FLT project
(https://github.com/ImperialCollegeLondon/FLT), file
`FLT/DedekindDomain/Completion/BaseChange.lean` by Kevin Buzzard, Andrew Yang and
Matthew Jasper, ported to build on Mathlib's `valuation_liesOver` and
`uniformContinuous_algebraMap_liesOver`.
-/

open Polynomial IsDedekindDomain WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- An irreducible element of the ring of integers of a completion has valuation `exp (-1)`. -/
theorem valued_irreducible_adicCompletionIntegers {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni

/-- The valuation associated to the maximal ideal of the ring of integers of an adic
completion is the valuation of the completion. -/
theorem valuation_maximalIdeal_adicCompletionIntegers (x : v.adicCompletion K) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
      (v.adicCompletion K) x = Valued.v x := by
  -- reduce to elements of the ring of integers
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := v.adicCompletionIntegers K) x
  rw [map_div₀, map_div₀]
  suffices h : ∀ y : v.adicCompletionIntegers K,
      (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
        (v.adicCompletion K) (algebraMap _ _ y) = Valued.v (algebraMap _ _ y) by
    rw [h, h]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  -- decompose `y` as a unit times a power of a uniformizer
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  rw [valuation_of_algebraMap]
  -- the unit has valuation `1` on both sides
  have hu1 : (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers K)).intValuation (u : v.adicCompletionIntegers K) = 1 := by
    simp [IsDiscreteValuationRing.maximalIdeal]
  have hu2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (u : v.adicCompletionIntegers K)) = 1 :=
    (Valuation.valuationSubring.integers (v := Valued.v)).valuation_unit u
  -- the uniformizer has valuation `exp (-1)` on both sides
  have hπ1 : (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers K)).intValuation π = exp (-1) :=
    (IsDiscreteValuationRing.maximalIdeal _).intValuation_singleton hπ.ne_zero
      hπ.maximalIdeal_eq
  have hπ2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      exp (-1) := v.valued_irreducible_adicCompletionIntegers hπ
  simp only [map_mul, map_pow]
  rw [hu1, hu2, hπ1, hπ2]

/-- An element of the ring of integers of a completion of valuation `exp (-e)` generates the
`e`-th power of the maximal ideal. -/
theorem span_singleton_eq_maximalIdeal_pow {x : v.adicCompletionIntegers K} {e : ℕ}
    (hx : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x) =
      exp (-(e : ℤ))) :
    Ideal.span {x} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ e := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hx
    exact absurd hx.symm exp_ne_zero
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hu2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (u : v.adicCompletionIntegers K)) = 1 :=
    (Valuation.valuationSubring.integers (v := Valued.v)).valuation_unit u
  have hval : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (↑u * π ^ n)) = exp (-(n : ℤ)) := by
    rw [map_mul, map_mul, hu2, one_mul, map_pow, map_pow,
      v.valued_irreducible_adicCompletionIntegers hπ, ← exp_nsmul]
    simp
  rw [hval, exp_inj, neg_inj, Int.natCast_inj] at hx
  subst hx
  rw [Ideal.span_singleton_eq_span_singleton.mpr (associated_unit_mul_left _ _ u.isUnit),
    ← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]

/-- Any element of the ring of integers of the completion is congruent to an element of `R`
modulo the maximal ideal. -/
theorem exists_valued_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) < 1 := by
  -- approximate by an element of `K` first
  have hball : {y | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy ↦ by simpa using hy⟩
  obtain ⟨w, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (denseRange_algebraMap (K := K) v _) _ hball
  rw [Set.mem_setOf_eq] at hwball
  -- the approximating element is integral at `v`
  have hz1 : v.valuation K z ≤ 1 := by
    rw [show v.valuation K z = Valued.v (algebraMap K (v.adicCompletion K) z) from
      (v.valuedAdicCompletion_eq_valuation' z).symm]
    calc Valued.v (algebraMap K (v.adicCompletion K) z)
        = Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)
            + (x : v.adicCompletion K)) := by ring_nf
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)))
            (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hwball.le x.2
  -- approximate the element of `K` by an element of `R`
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) z -
      algebraMap R (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      show Valued.v (algebraMap K (v.adicCompletion K) (z - algebraMap R K a)) =
        v.valuation K (z - algebraMap R K a) from v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    simpa using ha
  calc Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a)
      = Valued.v (((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) z)
          + (algebraMap K (v.adicCompletion K) z - algebraMap R (v.adicCompletion K) a)) := by
        ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'

/-- The residue field of `v` maps isomorphically onto the residue field of the ring of
integers of the completion at `v`. -/
noncomputable def residueFieldEquivAdicCompletionIntegers :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valued_sub_lt_one (K := K) x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine (Ideal.Quotient.eq).mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰))).mpr ?_
    rw [show ((algebraMap R (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap R (v.adicCompletion K) a - (x : v.adicCompletion K)
      from rfl, Valuation.map_sub_swap]
    exact ha

/-- At a place of odd residue characteristic, the ring of integers of the completion has a
unit that is not a square in the completion: any lift of a non-square of the residue
field. -/
theorem exists_unit_not_isSquare [Finite (R ⧸ v.asIdeal)] (hv2 : (2 : R) ∉ v.asIdeal) :
    ∃ c : (v.adicCompletionIntegers K)ˣ,
      ¬ IsSquare (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (c : v.adicCompletionIntegers K)) := by
  have hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  -- the residue characteristic is odd
  have h2 : IsLocalRing.residue (v.adicCompletionIntegers K) 2 ≠ 0 := by
    intro h0
    have hmem : (2 : v.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
      Ideal.Quotient.eq_zero_iff_mem.mp h0
    rw [show (2 : v.adicCompletionIntegers K) = algebraMap R (v.adicCompletionIntegers K) 2
        from (map_ofNat _ 2).symm, ← Ideal.mem_comap,
      v.comap_maximalIdeal_adicCompletionIntegers] at hmem
    exact hv2 hmem
  have hchar : ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) ≠ 2 := by
    intro h
    apply h2
    have h0 : ((2 : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    rw [Nat.cast_ofNat] at h0
    rw [show IsLocalRing.residue (v.adicCompletionIntegers K) 2 =
      (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers K)) from map_ofNat _ 2]
    exact h0
  -- a non-square in the residue field
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := fun h ↦ ha (h ▸ IsSquare.zero)
  -- lift it to a unit of the ring of integers
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K) a
  have hxu : IsUnit x := by
    by_contra h
    exact ha0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  refine ⟨hxu.unit, fun ⟨d, hd⟩ ↦ ?_⟩
  rw [IsUnit.unit_spec] at hd
  -- a square root would have valuation `1`
  have hx1 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x) = 1 := by
    rw [show x = (hxu.unit : v.adicCompletionIntegers K) from hxu.unit_spec.symm]
    exact (Valuation.valuationSubring.integers (v := Valued.v)).valuation_unit hxu.unit
  rw [hd, map_mul] at hx1
  have hd0 : Valued.v d ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hx1
    exact zero_ne_one hx1
  have hlog := congrArg WithZero.log hx1
  rw [WithZero.log_mul hd0 hd0, WithZero.log_one] at hlog
  have hd1 : Valued.v d = 1 := by
    have hz : WithZero.log (Valued.v d) = 0 := by omega
    rw [← WithZero.exp_log hd0, hz, WithZero.exp_zero]
  -- hence it lies in the ring of integers, and reduces to a square root of the non-square
  have hdmem : d ∈ v.adicCompletionIntegers K := (mem_adicCompletionIntegers R K v).mpr hd1.le
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
    fun a b h ↦ Subtype.ext h
  have hx_eq : x = (⟨d, hdmem⟩ : v.adicCompletionIntegers K) * ⟨d, hdmem⟩ :=
    hinj (by rw [map_mul]; exact hd)
  exact ha ⟨IsLocalRing.residue _ ⟨d, hdmem⟩, by rw [hx_eq, map_mul]⟩

/-- An element of `𝒪_v` lies in the `n`-th power of the maximal ideal exactly when its
valuation is at most `exp (-n)`. -/
theorem mem_maximalIdeal_pow_iff {x : v.adicCompletionIntegers K} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπn : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (π ^ n)) =
      exp (-(n : ℤ)) := by
    rw [map_pow, map_pow, v.valued_irreducible_adicCompletionIntegers hπ, ← exp_nsmul]
    simp
  rw [← span_singleton_eq_maximalIdeal_pow v hπn, Ideal.mem_span_singleton]
  have hint := Valuation.valuationSubring.integers (v := (Valued.v : Valuation
    (v.adicCompletion K) ℤᵐ⁰))
  exact ⟨fun h ↦ (hint.le_of_dvd h).trans hπn.le, fun h ↦ hint.dvd_of_le (h.trans_eq hπn.symm)⟩

instance isTopologicalRing_adicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing
    (Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring)

/-- The subspace topology on the ring of integers `𝒪_v` of an adic completion is the
`𝔪`-adic topology of its maximal ideal. -/
theorem isAdic_maximalIdeal_adicCompletionIntegers :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  rw [isAdic_iff]
  constructor
  · -- each `𝔪 ^ n` is open: it is the preimage of a closed ball
    intro n
    obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp (-(n : ℤ)))
    have hr0 : Valued.v.restrict z ≠ 0 := by
      intro h
      have h0 : Valued.v z = 0 := by rw [← Valuation.embedding_restrict, h, map_zero]
      rw [hz] at h0
      exact exp_ne_zero h0
    have : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
          Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
        (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) ⁻¹'
          {y | Valued.v.restrict y ≤ Valued.v.restrict z} := by
      ext x
      rw [Set.mem_preimage, Set.mem_setOf, Valuation.restrict_le_iff_le_embedding,
        Valuation.embedding_restrict, hz]
      exact v.mem_maximalIdeal_pow_iff (K := K)
    rw [this]
    exact (Valued.isOpen_closedBall _ hr0).preimage continuous_subtype_val
  · -- each neighbourhood of `0` contains some `𝔪 ^ n`
    intro s hs
    obtain ⟨t, ht, hts⟩ := mem_nhds_subtype _ _ _ |>.mp hs
    rw [ZeroMemClass.coe_zero] at ht
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
    obtain ⟨m, hm⟩ : ∃ m : ℤ, exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
      obtain ⟨a, ha⟩ :=
        WithZero.ne_zero_iff_exists.mp (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
      refine ⟨Multiplicative.toAdd a - 1, ?_⟩
      rw [← ha, show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl]
      exact exp_lt_exp.mpr (by lia)
    refine ⟨(-m).toNat, fun x hx ↦ hts ?_⟩
    refine Set.mem_preimage.mpr (hγ ?_)
    have h1 := v.mem_maximalIdeal_pow_iff (K := K) |>.mp hx
    refine Set.mem_setOf.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
      (h1.trans_lt ?_))
    calc exp (-(((-m).toNat : ℤ))) ≤ exp m := exp_le_exp.mpr (by lia)
      _ < _ := hm

instance completeSpace_adicCompletionIntegers : CompleteSpace (v.adicCompletionIntegers K) :=
  (Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe

instance isUniformAddGroup_adicCompletionIntegers :
    IsUniformAddGroup (v.adicCompletionIntegers K) :=
  ((Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring.toAddSubgroup).isUniformAddGroup

instance isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

instance henselianLocalRing_adicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) where
  is_henselian f hf a₀ h₁ h₂ :=
    (IsAdicComplete.henselianRing _
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).is_henselian f hf a₀ h₁ (h₂.map _)

/-- `Units.modPow`-friendly form: the valuation of the height-one prime of `𝒪_v` at the
image of a unit of `K` is the `v`-adic valuation of the unit. -/
theorem valuationOfNeZero_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R)
    (u : Kˣ) :
    (IsDiscreteValuationRing.maximalIdeal
        (v.adicCompletionIntegers K)).valuationOfNeZero
      (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u) =
      v.valuationOfNeZero u := by
  rw [valuationOfNeZero_eq_iff, valuationOfNeZero_eq,
    valuation_maximalIdeal_adicCompletionIntegers]
  exact v.valuedAdicCompletion_eq_valuation' _

/-- Any height-one prime `P` of the valuation ring `𝒪_v` (necessarily its maximal ideal)
induces on `K` the valuation `v` itself. -/
theorem valuation_adicCompletion_algebraMap (v : HeightOneSpectrum R)
    (P : HeightOneSpectrum (v.adicCompletionIntegers K)) (z : K) :
    P.valuation (v.adicCompletion K) (algebraMap K (v.adicCompletion K) z) =
      v.valuation K z := by
  rw [P.eq_maximalIdeal, valuation_maximalIdeal_adicCompletionIntegers]
  exact v.valuedAdicCompletion_eq_valuation' z

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.IsTorsionFree R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L)

/-- The extension of adic completions along `w ∣ v`: the ring homomorphism `K_v →+* L_w`
extending `K → L` continuously. Adapted from the FLT project
(`FLT.DedekindDomain.Completion.BaseChange`, by Kevin Buzzard, Andrew Yang, Matthew Jasper). -/
noncomputable def adicCompletionExtension : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom

/-- The completion of `x : K_v` under `adicCompletionExtension` is the base change of its
underlying element of the completion of `WithVal (v.valuation K)`. -/
lemma toCompletion_adicCompletionExtension (x : v.adicCompletion K) :
    (adicCompletionExtension K L v w x).toCompletion =
      UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous x.toCompletion :=
  rfl

/-- The square with sides `K → K_v → L_w` and `K → L → L_w` commutes. -/
lemma adicCompletionExtension_coe (x : K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) := by
  apply adicCompletion.ext
  rw [toCompletion_adicCompletionExtension, show (↑x : v.adicCompletion K).toCompletion
      = ((WithVal.equiv (v.valuation K)).symm x : (v.valuation K).Completion) from rfl,
    UniformSpace.Completion.mapRingHom_coe]
  rfl

lemma adicCompletionExtension_coe' (a : WithVal (v.valuation K)) :
    adicCompletionExtension K L v w ↑a =
      ↑(algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)) a) := by
  apply adicCompletion.ext
  rw [toCompletion_adicCompletionExtension, show (↑a : v.adicCompletion K).toCompletion
      = (a : (v.valuation K).Completion) from rfl, UniformSpace.Completion.mapRingHom_coe]

open WithZeroTopology in
/-- The valuation on `L_w` restricted along `K_v → L_w` is the valuation on `K_v` raised to
the ramification index of `w` over `v`. Adapted from FLT's
`valued_adicCompletionSemialgHom` (Buzzard, Yang, Jasper). -/
lemma valued_adicCompletionExtension (x : v.adicCompletion K) :
    Valued.v (adicCompletionExtension K L v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  rw [← adicCompletion.valued_toCompletion L w (adicCompletionExtension K L v w x),
    toCompletion_adicCompletionExtension, ← adicCompletion.valued_toCompletion K v x]
  have hsurjK : Function.Surjective (⇑(Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  have hsurjL : Function.Surjective (⇑(Valued.v : Valuation (w.valuation L).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (w.valuation_surjective L)
  generalize x.toCompletion = y
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact (Valued.continuous_valuation_of_surjective hsurjK).pow _
  · exact (Valued.continuous_valuation_of_surjective hsurjL).comp
      UniformSpace.Completion.continuous_map
  intro a
  rw [UniformSpace.Completion.mapRingHom_coe, Valued.valuedCompletion_apply,
    Valued.valuedCompletion_apply]
  exact valuation_liesOver (K := K) L v w (WithVal.equiv (v.valuation K) a)

lemma adicCompletionExtension_mem_adicCompletionIntegers (x : v.adicCompletionIntegers K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) ∈ w.adicCompletionIntegers L := by
  rw [mem_adicCompletionIntegers, valued_adicCompletionExtension]
  exact pow_le_one' x.2 _

/-- The restriction of `adicCompletionExtension` to the rings of integers. -/
noncomputable def adicCompletionIntegersExtension :
    v.adicCompletionIntegers K →+* w.adicCompletionIntegers L :=
  ((adicCompletionExtension K L v w).comp
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).codRestrict
      (w.adicCompletionIntegers L).toSubring
      fun x ↦ adicCompletionExtension_mem_adicCompletionIntegers K L v w x

lemma algebraMap_adicCompletionIntegersExtension (x : v.adicCompletionIntegers K) :
    (adicCompletionIntegersExtension K L v w x : w.adicCompletion L) =
      adicCompletionExtension K L v w (x : v.adicCompletion K) :=
  rfl

/-- The maximal ideal of the ring of integers of `L_w` contracts to the maximal ideal
of the ring of integers of `K_v`. -/
lemma comap_maximalIdeal_adicCompletionIntegersExtension :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).comap
        (adicCompletionIntegersExtension K L v w) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  ext x
  rw [Ideal.mem_comap]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion L)
    (WithZero (Multiplicative ℤ))))).trans <| Iff.trans ?_
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))))).symm
  rw [algebraMap_adicCompletionIntegersExtension K L v w, valued_adicCompletionExtension]
  exact pow_lt_one_iff
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

end Extension

end IsDedekindDomain.HeightOneSpectrum

end
