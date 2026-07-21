import Mathlib

/-!
# Example: `(1, 1)` on `y² = x³ - x + 1` has infinite order

The point `P = (1, 1)` on the elliptic curve `E : y² = x³ - x + 1` over `ℚ` has infinite order.
A certificate is that its reductions at two primes have coprime orders: modulo `3` the reduced
point is killed by `7` (indeed `#E(𝔽₃) = 7`) and modulo `5` it is killed by `8` (`#E(𝔽₅) = 8`),
and `gcd(7, 8) = 1`. This is exactly the input to
`WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red`.

This file records the two finite-field torsion facts, `nsmul_seven_eq_zero_mod_three` and
`nsmul_eight_eq_zero_mod_five`, over `ZMod 3` and `ZMod 5`.

## Implementation notes

Mathlib's `WeierstrassCurve.Affine.Point` addition is noncomputable (its `AddCommGroup` instance
goes through `Classical.choice`, and `slope`/`addX`/`addY` do not reduce in the kernel), so the
torsion facts cannot be closed `by decide`. Instead each multiple `k • P` is computed by hand from
the group laws `two_nsmul`/`succ_nsmul`/`add_nsmul` and the explicit `add_of_X_ne`/`add_of_Y_eq`/
`add_self_of_Y_ne` formulas, with each slope value first cleared of its denominator (`div_eq_iff`)
so the remaining coordinate identities are division-free and `decide`-able.

Turning these into a formal proof that `P ∈ E(ℚ)` has infinite order via the certificate is left as
future work: it additionally needs the reduction over the abstract residue field
`IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)` to be identified with the computable
`ZMod p` (Mathlib has `PadicInt.residueField` for `ℤ_[p]`), and the `p`-adic integral model with
its good-reduction and ramification data.
-/

open WeierstrassCurve

namespace InfiniteOrderExample

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ### Reduction modulo `3`: `7 • (1, 1) = 0` -/

/-- `y² = x³ - x + 1` over `𝔽₃`. -/
def E3 : WeierstrassCurve (ZMod 3) := ⟨0, 0, 0, -1, 1⟩

instance : E3.IsElliptic := by rw [WeierstrassCurve.isElliptic_iff]; decide

private theorem ns3 {x y : ZMod 3} (h : y ^ 2 + x = x ^ 3 + 1) : E3.toAffine.Nonsingular x y := by
  rw [← E3.toAffine.equation_iff_nonsingular, Affine.equation_iff]
  simp only [E3]; ring_nf; ring_nf at h; linear_combination h

/-- The point `(1, 1)` on `E : y² = x³ - x + 1` over `𝔽₃`. -/
def P3 : E3.toAffine.Point := .some 1 1 (ns3 (by decide))

/-- `P = (1, 1)` reduces modulo `3` to a point of order `7` (so `7 • P₃ = 0`); computed as
`P₃ → 2P₃ = (2,1) → 3P₃ = (0,2) → 4P₃ = (0,1)` and `7 • P₃ = 4P₃ + 3P₃ = 0`. -/
theorem nsmul_seven_eq_zero_mod_three : (7 : ℕ) • P3 = 0 := by
  have h2 : (2 : ℕ) • P3 = .some 2 1 (ns3 (by decide)) := by
    have hs : E3.toAffine.slope 1 1 1 1 = 1 := by
      rw [Affine.slope_of_Y_ne rfl (by decide), div_eq_iff (by decide)]; decide
    rw [two_nsmul, P3, Affine.Point.add_self_of_Y_ne (by decide), Affine.Point.some.injEq, hs]
    exact ⟨by decide, by decide⟩
  have h3 : (3 : ℕ) • P3 = .some 0 2 (ns3 (by decide)) := by
    have hs : E3.toAffine.slope 2 1 1 1 = 0 := by
      rw [Affine.slope_of_X_ne (by decide), div_eq_iff (by decide)]; decide
    rw [(succ_nsmul P3 2 : (3 : ℕ) • P3 = _), h2, P3, Affine.Point.add_of_X_ne (by decide),
      Affine.Point.some.injEq, hs]
    exact ⟨by decide, by decide⟩
  have h4 : (4 : ℕ) • P3 = .some 0 1 (ns3 (by decide)) := by
    have hs : E3.toAffine.slope 0 1 2 1 = 2 := by
      rw [Affine.slope_of_X_ne (by decide), div_eq_iff (by decide)]; decide
    rw [(succ_nsmul P3 3 : (4 : ℕ) • P3 = _), h3, P3, Affine.Point.add_of_X_ne (by decide),
      Affine.Point.some.injEq, hs]
    exact ⟨by decide, by decide⟩
  rw [(add_nsmul P3 4 3 : (7 : ℕ) • P3 = _), h4, h3, Affine.Point.add_of_Y_eq rfl (by decide)]

/-! ### Reduction modulo `5`: `8 • (1, 1) = 0` -/

/-- `y² = x³ - x + 1` over `𝔽₅`. -/
def E5 : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, -1, 1⟩

instance : E5.IsElliptic := by rw [WeierstrassCurve.isElliptic_iff]; decide

private theorem ns5 {x y : ZMod 5} (h : y ^ 2 + x = x ^ 3 + 1) : E5.toAffine.Nonsingular x y := by
  rw [← E5.toAffine.equation_iff_nonsingular, Affine.equation_iff]
  simp only [E5]; ring_nf; ring_nf at h; linear_combination h

/-- The point `(1, 1)` on `E : y² = x³ - x + 1` over `𝔽₅`. -/
def P5 : E5.toAffine.Point := .some 1 1 (ns5 (by decide))

/-- `P = (1, 1)` reduces modulo `5` to a point of order `8` (so `8 • P₅ = 0`); computed as
`P₅ → 2P₅ = (4,1) → 3P₅ = (0,4) → 4P₅ = (3,0)`, where `4P₅` is `2`-torsion, so
`8 • P₅ = 4P₅ + 4P₅ = 0`. -/
theorem nsmul_eight_eq_zero_mod_five : (8 : ℕ) • P5 = 0 := by
  have h2 : (2 : ℕ) • P5 = .some 4 1 (ns5 (by decide)) := by
    have hs : E5.toAffine.slope 1 1 1 1 = 1 := by
      rw [Affine.slope_of_Y_ne rfl (by decide), div_eq_iff (by decide)]; decide
    rw [two_nsmul, P5, Affine.Point.add_self_of_Y_ne (by decide), Affine.Point.some.injEq, hs]
    exact ⟨by decide, by decide⟩
  have h3 : (3 : ℕ) • P5 = .some 0 4 (ns5 (by decide)) := by
    have hs : E5.toAffine.slope 4 1 1 1 = 0 := by
      rw [Affine.slope_of_X_ne (by decide), div_eq_iff (by decide)]; decide
    rw [(succ_nsmul P5 2 : (3 : ℕ) • P5 = _), h2, P5, Affine.Point.add_of_X_ne (by decide),
      Affine.Point.some.injEq, hs]
    exact ⟨by decide, by decide⟩
  have h4 : (4 : ℕ) • P5 = .some 3 0 (ns5 (by decide)) := by
    have hs : E5.toAffine.slope 0 1 4 1 = 2 := by
      rw [Affine.slope_of_X_ne (by decide), div_eq_iff (by decide)]; decide
    rw [(succ_nsmul P5 3 : (4 : ℕ) • P5 = _), h3, P5, Affine.Point.add_of_X_ne (by decide),
      Affine.Point.some.injEq, hs]
    exact ⟨by decide, by decide⟩
  rw [(add_nsmul P5 4 4 : (8 : ℕ) • P5 = _), h4, Affine.Point.add_of_Y_eq rfl (by decide)]

/-- The two reduced orders are coprime, so the certificate
`WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red` would conclude infinite order. -/
theorem coprime_seven_eight : Nat.Coprime 7 8 := by decide

end InfiniteOrderExample
