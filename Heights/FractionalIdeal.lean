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

/-- The `v`-adic valuation of `x : K` is `exp (- count v (x))`: the `count` of the principal
fractional ideal generated by `x` recovers the adic valuation. -/
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (- count K v (spanSingleton R⁰ x)) := by
  have key (r : R) (hr : r ≠ 0) : v.valuation K (algebraMap R K r) =
      WithZero.exp (- count K v (spanSingleton R⁰ (algebraMap R K r))) := by
    rw [valuation_of_algebraMap, intValuation_apply, v.intValuationDef_if_neg hr,
      ← coeIdeal_span_singleton, count_coe K v (by simpa using hr)]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hsa : spanSingleton R⁰ (algebraMap R K a) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hsb : spanSingleton R⁰ (algebraMap R K (b:R)) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hcount : count K v (spanSingleton R⁰ (algebraMap R K a / algebraMap R K (b:R))) =
      count K v (spanSingleton R⁰ (algebraMap R K a)) -
        count K v (spanSingleton R⁰ (algebraMap R K (b:R))) := by
    rw [← spanSingleton_div_spanSingleton, div_eq_mul_inv, count_mul K v hsa (inv_ne_zero hsb),
      count_inv, sub_eq_add_neg]
  rw [map_div₀, key a ha0, key (b:R) hb0, hcount, div_eq_mul_inv, ← WithZero.exp_neg,
    ← WithZero.exp_add]
  congr 1
  ring

/-- The Selmer/divisibility bridge: the `v`-adic order of a unit `x : Kˣ` is `- count v (x)`. -/
theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      - count K v (spanSingleton R⁰ (x : K)) := by
  have h : (v.valuationOfNeZero x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (- count K v (spanSingleton R⁰ (x : K))) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, valuation_eq_exp_neg_count v x.ne_zero]
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at h
  rw [h, toAdd_ofAdd]

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

/-!
### The kernel of the principal-ideal map

The principal fractional ideal `(x)` is trivial exactly when `x` comes from a unit of `R`. This
identifies `ker toPrincipalIdeal` with the units of `R`, the left end of the ideal class exact
sequence.
-/

/-- A principal fractional ideal `(x)` (with `x ≠ 0`) equals `1` exactly when `x` is (the image
of) a unit of `R`. -/
lemma spanSingleton_eq_one_iff {x : K} (hx : x ≠ 0) :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
  constructor
  · intro h
    have hinv : spanSingleton R⁰ x⁻¹ = 1 := by rw [← spanSingleton_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (mem_one_iff R⁰).mp (h ▸ mem_spanSingleton_self R⁰ x)
    obtain ⟨b, hb⟩ := (mem_one_iff R⁰).mp (hinv ▸ mem_spanSingleton_self R⁰ x⁻¹)
    have hab : a * b = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ha, hb, mul_inv_cancel₀ hx, map_one])
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr a.isUnit, coeIdeal_top]

/-- `toPrincipalIdeal x = 1` exactly when `x` is a unit of `R`: the kernel of the principal-ideal
map is the image of `Rˣ`. -/
lemma toPrincipalIdeal_eq_one_iff (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff u.ne_zero]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ => ⟨a, by rw [← ha]; rfl⟩⟩

/-!
### The `n`-th root as a homomorphism

On the subgroup of fractional ideals all of whose valuations are divisible by `n`, the `n`-th
root is a genuine group homomorphism (not merely an existence statement): dividing every
valuation by `n` is additive there.
-/

section NthRoot

variable (R K)

/-- The subgroup of fractional ideals whose valuations are all divisible by `n`. -/
def nDivisible (n : ℕ) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)}
  one_mem' v := by rw [Units.val_one, count_one]; exact dvd_zero _
  mul_mem' {I J} hI hJ v := by
    rw [Units.val_mul, count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    exact dvd_add (hI v) (hJ v)
  inv_mem' {I} hI v := by
    rw [Units.val_inv_eq_inv_val, count_inv]; exact (hI v).neg_right

/-- The `n`-th root ideal of `I`: its valuations divided by `n`. -/
noncomputable def nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) : (FractionalIdeal R⁰ K)ˣ :=
  ofFinsupp (Finsupp.mapRange (· / (n:ℤ)) (by simp) (toFinsupp I))

lemma count_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    count K v (nthRootFun R K n I : FractionalIdeal R⁰ K) =
      count K v (I : FractionalIdeal R⁰ K) / n := by
  rw [nthRootFun, count_ofFinsupp, Finsupp.mapRange_apply, toFinsupp_apply]

/-- The `n`-th root as a group homomorphism on the `n`-divisible subgroup. -/
noncomputable def nthRootHom (n : ℕ) : nDivisible R K n →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ)
  map_one' := count_injective fun v => by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := count_injective fun v => by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _), Int.add_ediv_of_dvd_left (I.2 v)]

/-- The `n`-th root homomorphism is a genuine `n`-th root. -/
lemma nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    (nthRootHom R K n I) ^ n = (I : (FractionalIdeal R⁰ K)ˣ) := by
  apply count_injective
  intro v
  rw [Units.val_pow_eq_pow_val, count_pow, nthRootHom, MonoidHom.coe_mk, OneHom.coe_mk,
    count_nthRootFun, Int.mul_ediv_cancel' (I.2 v)]

end NthRoot

end FractionalIdeal
