import Mathlib
import Heights.ForMathlib.SelmerGroup

/-!
# Interface to formal-group theory over a local field

Let `K` be the fraction field of a Dedekind domain, `v` a height-one prime with finite
residue field, and `K_v` the completion (of characteristic `0`). This file states the
structural consequences of the theory of formal groups over `𝒪_v` that the 2-descent
machinery needs. Both statements are `sorry`ed for now.

* `WeierstrassCurve.Affine.exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers`:
  for an elliptic curve `E` over `K_v`, the group `E(K_v)` has a subgroup of finite index
  isomorphic to the additive group `(𝒪_v, +)`.

  The proof is a separate project: the points reducing to the identity form a subgroup
  `E₁(K_v)` isomorphic to the group `Ê(𝔪)` of points of the formal group `Ê` of `E`
  (Silverman, *Arithmetic of Elliptic Curves*, VII.2.2); the formal logarithm gives an
  isomorphism `Ê(𝔪^k) ≅ (𝔪^k, +) ≅ (𝒪_v, +)` for `k` large compared to the ramification
  of `p` (Silverman IV.6.4); and `Ê(𝔪^k)` is open in the compact group `E(K_v)`, hence of
  finite index. Mathlib's `FormalGroup` (one-dimensional formal group laws) is a starting
  point, but the formal group of an elliptic curve, the formal logarithm, and the topology
  on the points of an elliptic curve over a local field are all still missing.

* `IsDedekindDomain.HeightOneSpectrum.card_selmerGroup_integralClosure`: for odd residue
  characteristic and a finite extension `L` of `K_v` with `B` the integral closure of `𝒪_v`
  in `L`, the Selmer group `L(∅, 2)` (classes of units of `L` with even valuation at every
  prime of `B`) has exactly two elements.

  This is the multiplicative (`𝔾ₘ`) analogue: `B` is a discrete valuation ring (integral
  closures in finite extensions of complete fields are local), `L(∅, 2) ≅ Bˣ/(Bˣ)²`, and
  the filtration of `Bˣ` by principal units has graded pieces `kˣ` (with `#(kˣ/(kˣ)²) = 2`
  for the finite residue field `k` of odd characteristic) and `(k, +)`; the principal units
  are uniquely `2`-divisible by the formal-group/Hensel argument for `𝔾̂ₘ`.
-/

open IsDedekindDomain Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
  (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
  (W : Affine (v.adicCompletion K)) [W.IsElliptic]

open scoped Classical in
/-- The group of points of an elliptic curve over the completion `K_v` (a characteristic-`0`
local field with finite residue field) has a subgroup of finite index that is isomorphic to
the additive group of the valuation ring `𝒪_v`.

This is the structure theorem coming from the formal group of the curve; see the module
docstring for the proof sketch. -/
theorem exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers :
    ∃ U : AddSubgroup W.Point, U.FiniteIndex ∧ Nonempty (U ≃+ (v.adicCompletionIntegers K)) :=
  sorry

end WeierstrassCurve.Affine

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
  (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
  [FiniteDimensional (v.adicCompletion K) L]
  [Algebra (v.adicCompletionIntegers K) L]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) L]
  [IsDedekindDomain (integralClosure (v.adicCompletionIntegers K) L)]
  [IsFractionRing (integralClosure (v.adicCompletionIntegers K) L) L]

/-- For a finite extension `L` of the completion `K_v` at a place of odd residue
characteristic, the group of square classes of `L` that have even valuation at every prime
of the integral closure `B` of `𝒪_v` has exactly two elements.

This is the multiplicative analogue of
`exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers`; see the module docstring for
the proof sketch. -/
theorem card_selmerGroup_integralClosure (hv2 : (2 : R) ∉ v.asIdeal) :
    Nat.card (selmerGroup (R := integralClosure (v.adicCompletionIntegers K) L) (K := L)
      (S := (∅ : Set (HeightOneSpectrum (integralClosure (v.adicCompletionIntegers K) L))))
      (n := 2)) = 2 :=
  sorry

end IsDedekindDomain.HeightOneSpectrum
