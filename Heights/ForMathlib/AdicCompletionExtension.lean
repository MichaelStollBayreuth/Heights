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
      exp (-1) := by
    have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
        ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
    have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
    rwa [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective K)] at huni
  simp only [map_mul, map_pow]
  rw [hu1, hu2, hπ1, hπ2]

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
  rw [show ((adicCompletionIntegersExtension K L v w x : w.adicCompletionIntegers L) :
      w.adicCompletion L) = adicCompletionExtension K L v w (x : v.adicCompletion K) from rfl,
    valued_adicCompletionExtension]
  exact pow_lt_one_iff
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

end Extension

end IsDedekindDomain.HeightOneSpectrum

