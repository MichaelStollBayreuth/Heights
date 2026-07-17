import Mathlib
import Heights.ForMathlib.Basic

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
  valuation ring) of a completion `K_v` is the valuation of the completion.

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
  UniformSpace.Completion.mapRingHom
    (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
    (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous

/-- The square with sides `K → K_v → L_w` and `K → L → L_w` commutes. -/
lemma adicCompletionExtension_coe (x : K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) :=
  UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous
    ((WithVal.equiv (v.valuation K)).symm x)

lemma adicCompletionExtension_coe' (a : WithVal (v.valuation K)) :
    adicCompletionExtension K L v w ↑a =
      ↑(algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)) a) :=
  UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous a

open WithZeroTopology in
/-- The valuation on `L_w` restricted along `K_v → L_w` is the valuation on `K_v` raised to
the ramification index of `w` over `v`. Adapted from FLT's
`valued_adicCompletionSemialgHom` (Buzzard, Yang, Jasper). -/
lemma valued_adicCompletionExtension (x : v.adicCompletion K) :
    Valued.v (adicCompletionExtension K L v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  revert x
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact (Valued.continuous_valuation_of_surjective
      (v.valuedAdicCompletion_surjective K)).pow _
  · exact (Valued.continuous_valuation_of_surjective
      (w.valuedAdicCompletion_surjective L)).comp UniformSpace.Completion.continuous_map
  intro a
  rw [adicCompletionExtension_coe' K L v w a, Valued.valuedCompletion_apply,
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

