import Mathlib
import Heights.ForMathlib.WeierstrassFormalGroup.Reduction
import Heights.EllipticCurve.SelmerGroup

/-!
# An infinite-order certificate via reduction at two primes

Let `E` be an elliptic curve over the fraction field `K` of a Dedekind domain `R` (e.g. a number
field). Reduction at a prime `v` of good reduction is injective on the torsion of `E(K_v)`
provided the residue characteristic `p` is not too ramified (`(p) ∈ 𝔪_v` but `(p) ∉ 𝔪_v ^ (p-1)`,
which holds for instance when `p` is odd and `v` is unramified). Base change `E(K) → E(K_v)` is
injective, so the composite reduction `E(K) → Ẽ(k_v)` is injective on torsion.

This yields a certificate for a point of `E(K)` to have **infinite order**: if the reductions of a
nonzero point at two good primes are torsion of coprime orders, the point cannot be torsion.

## Main statements

* `WeierstrassCurve.Affine.pointMap_injective`: base change of points along `K → L` is injective.
* `WeierstrassCurve.Affine.nsmul_eq_zero_of_red_pointMap_nsmul_eq_zero`: the single-prime bridge —
  if the reduction of a torsion point is `m`-torsion, so is the point.
* `WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red`: the two-prime infinite-order
  certificate.

## Implementation notes

The reduction map `WeierstrassCurve.Affine.red` and the base change `pointMap` both take a
`DecidableEq` instance on a field with no computable equality, so this file works under
`open scoped Classical` rather than threading those instances through every signature.
-/

open Function IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

open scoped Classical

/-- An element of an additive monoid annihilated by two coprime multiples is zero. -/
private theorem eq_zero_of_nsmul_eq_zero_of_coprime {A : Type*} [AddMonoid A] {P : A} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : m • P = 0) (hn : n • P = 0) : P = 0 :=
  AddMonoid.addOrderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes hmn
    (addOrderOf_dvd_of_nsmul_eq_zero hm) (addOrderOf_dvd_of_nsmul_eq_zero hn)

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (E : Affine K)

/-- The base change of points along a field extension `K → L` is injective. -/
lemma pointMap_injective (L : Type*) [Field L] [Algebra K L] : Injective (E.pointMap L) := by
  rw [pointMap]
  exact (Point.map_injective _).comp (Point.congr _).injective

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  [CharZero K] [E.IsElliptic]

section OnePrime

variable {v : HeightOneSpectrum R}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)} [W₀.IsElliptic]
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    = (E ⁄ (v.adicCompletion K)).toAffine)

include hW in
/-- **Single-prime bridge.** If the reduction at `v` of a torsion point of `E(K)` is `m`-torsion,
then the point itself is `m`-torsion. Here `W₀` is a good integral model of `E` at `v`. -/
lemma nsmul_eq_zero_of_red_pointMap_nsmul_eq_zero {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {P : E.Point} (hP : IsOfFinAddOrder P) {m : ℕ}
    (h : m • red hW (E.pointMap (v.adicCompletion K) P) = 0) : m • P = 0 := by
  apply pointMap_injective E (v.adicCompletion K)
  rw [map_nsmul, nsmul_eq_zero_of_red_nsmul_eq_zero hW hp hpmem hpram
    (AddMonoidHom.isOfFinAddOrder _ hP) h, map_zero]

end OnePrime

/-- **Two-prime infinite-order certificate.** A nonzero point of `E(K)` whose reductions at two
good primes `v`, `w` are torsion of coprime orders (`m • red_v P = 0`, `n • red_w P = 0` with
`m`, `n` coprime) has infinite order. `W₀ᵥ`, `W₀w` are good integral models of `E` at `v`, `w`,
and `p`, `q` are the (lightly ramified) residue characteristics. -/
theorem not_isOfFinAddOrder_of_coprime_red {v w : HeightOneSpectrum R}
    {W₀ᵥ : WeierstrassCurve (v.adicCompletionIntegers K)} [W₀ᵥ.IsElliptic]
    (hWᵥ : W₀ᵥ.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      = (E ⁄ (v.adicCompletion K)).toAffine)
    {W₀w : WeierstrassCurve (w.adicCompletionIntegers K)} [W₀w.IsElliptic]
    (hWw : W₀w.map (algebraMap (w.adicCompletionIntegers K) (w.adicCompletion K))
      = (E ⁄ (w.adicCompletion K)).toAffine)
    {P : E.Point} (hP : P ≠ 0)
    {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {q : ℕ} (hq : q.Prime)
    (hqmem : (q : w.adicCompletionIntegers K) ∈ maximalIdeal (w.adicCompletionIntegers K))
    (hqram : (q : w.adicCompletionIntegers K) ∉
      maximalIdeal (w.adicCompletionIntegers K) ^ (q - 1))
    {m n : ℕ} (hmn : Nat.Coprime m n)
    (hv : m • red hWᵥ (E.pointMap (v.adicCompletion K) P) = 0)
    (hw : n • red hWw (E.pointMap (w.adicCompletion K) P) = 0) :
    ¬ IsOfFinAddOrder P := fun hfin ↦ hP <|
  eq_zero_of_nsmul_eq_zero_of_coprime hmn
    (nsmul_eq_zero_of_red_pointMap_nsmul_eq_zero E hWᵥ hp hpmem hpram hfin hv)
    (nsmul_eq_zero_of_red_pointMap_nsmul_eq_zero E hWw hq hqmem hqram hfin hw)

end WeierstrassCurve.Affine
