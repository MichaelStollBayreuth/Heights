import Mathlib

/-!
# The group of fractional ideals is free abelian on the primes

Let `R` be a Dedekind domain with fraction field `K`. The nonzero fractional ideals of `R` form a
group `(FractionalIdeal R⁰ K)ˣ` (every nonzero fractional ideal is invertible), and unique
factorization says this group is free abelian on the height one primes. Mathlib has all the
valuation bookkeeping (`IsDedekindDomain.HeightOneSpectrum.count` and the factorization lemmas in
`Mathlib.RingTheory.DedekindDomain.Factorization`) but does not package the isomorphism itself;
this file does.

## Main definitions and results

* `FractionalIdeal.factorization`: the isomorphism
  `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`, sending a fractional
  ideal to its tuple of valuations.
* `FractionalIdeal.exists_pow_eq`: **`n`-th roots** — a fractional ideal all of whose valuations
  are divisible by `n` is an `n`-th power. This is the key input to the fundamental exact sequence
  of the Selmer group.
* `FractionalIdeal.prod_count`, `count_injective`: a nonzero fractional ideal is the product of
  `v ^ (count v)` over the primes, and is determined by its valuations.

This is general material, candidate for upstreaming to Mathlib.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace FractionalIdeal

/-- A nonzero fractional ideal is the product `∏ v ^ (count v)` over the height one primes. -/
theorem prod_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v I = I := by
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  simp_rw [fun v => count_well_defined K v hI haJ]
  exact finprod_heightOneSpectrum_factorization hI haJ

/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := rfl

/-- The finitely-supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) := rfl

/-- The unit fractional ideal `∏ v ^ (g v)`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod (fun v e => unitOfPrime v ^ e)

lemma coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = g.prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

lemma count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- A unit fractional ideal is determined by its valuations. -/
lemma count_injective {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  apply Units.ext
  rw [← prod_count (Units.ne_zero I), ← prod_count (Units.ne_zero J)]
  exact finprod_congr fun v => by rw [h v]

/-- **The group of nonzero fractional ideals of a Dedekind domain is free abelian on the height
one primes.** -/
noncomputable def factorization :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (toFinsupp I)
  invFun g := ofFinsupp (Multiplicative.toAdd g)
  left_inv I := count_injective fun v => by rw [count_ofFinsupp]; rfl
  right_inv g := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, toFinsupp_apply, count_ofFinsupp]
  map_mul' I J := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, Finsupp.coe_add, Pi.add_apply, toFinsupp_apply, Units.val_mul,
      toAdd_mul]
    exact count_mul K v (Units.ne_zero I) (Units.ne_zero J)

@[simp] lemma factorization_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (factorization I) v = count K v (I : FractionalIdeal R⁰ K) := rfl

/-- **`n`-th roots of fractional ideals**: if every valuation of `I` is divisible by `n`, then
`I` is an `n`-th power. (The `n`-th root is unique, as the group is torsion-free, but only
existence is recorded here.) -/
lemma exists_pow_eq (n : ℕ) {I : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)) :
    ∃ J : (FractionalIdeal R⁰ K)ˣ, J ^ n = I := by
  refine ⟨factorization.symm (Multiplicative.ofAdd
    (Finsupp.mapRange (· / n) (by simp) (Multiplicative.toAdd (factorization I)))), ?_⟩
  apply factorization.injective
  rw [map_pow, MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  ext v
  simp only [toAdd_pow, toAdd_ofAdd, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul,
    factorization_apply]
  rw [mul_comm]
  exact Int.ediv_mul_cancel (h v)

end FractionalIdeal
