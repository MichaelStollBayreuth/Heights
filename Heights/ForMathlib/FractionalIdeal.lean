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

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

/-!
### The kernel of the principal-ideal map

The principal fractional ideal `(x)` is trivial exactly when `x` comes from a unit of `R`. This
identifies `ker toPrincipalIdeal` with the units of `R`, the left end of the ideal class exact
sequence. This part needs `R` to be a domain only.
-/

section PrincipalIdeal

variable [IsDomain R]

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
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- `ClassGroup.mk I = 1` exactly when the unit fractional ideal `I` is principal, with the
generator provided as a unit of `K`. Variant of `ClassGroup.mk_eq_one_iff` avoiding
`Submodule.IsPrincipal`. -/
lemma _root_.ClassGroup.mk_eq_one_iff_exists {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := hI.principal
    have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
      apply Subtype.coe_injective
      simp only [val_eq_coe, hx, coe_spanSingleton]
    have hx0 : x ≠ 0 := fun h ↦ Units.ne_zero I (by rw [hx', h, spanSingleton_zero])
    exact ⟨Units.mk0 x hx0, by rw [← Units.val_inj, coe_toPrincipalIdeal, hx']; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

@[simp]
lemma _root_.ClassGroup.mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff_exists.mpr ⟨x, rfl⟩

end PrincipalIdeal

variable [IsDedekindDomain R]

/-- A nonzero fractional ideal is the product `∏ v ^ (count v)` over the height one primes. -/
theorem prod_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v I = I := by
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  simp_rw [fun v ↦ count_well_defined K v hI haJ]
  exact finprod_heightOneSpectrum_factorization hI haJ

/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := rfl

/-- The finitely-supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) := rfl

/-- The unit fractional ideal `∏ v ^ (g v)`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod (fun v e ↦ unitOfPrime v ^ e)

lemma coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = g.prod (fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
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
  exact finprod_congr fun v ↦ by rw [h v]

/-- **The group of nonzero fractional ideals of a Dedekind domain is free abelian on the height
one primes.** -/
noncomputable def factorization :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (toFinsupp I)
  invFun g := ofFinsupp (Multiplicative.toAdd g)
  left_inv I := count_injective fun v ↦ by rw [count_ofFinsupp]; rfl
  right_inv g := by
    apply Multiplicative.toAdd.injective
    ext
    simp only [toAdd_ofAdd, toFinsupp_apply, count_ofFinsupp]
  map_mul' I J := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, Finsupp.coe_add, Pi.add_apply, toFinsupp_apply, Units.val_mul,
      toAdd_mul]
    exact count_mul K v (Units.ne_zero I) (Units.ne_zero J)

@[simp] lemma factorization_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (factorization I) v = count K v (I : FractionalIdeal R⁰ K) := rfl

lemma ofFinsupp_single (v : HeightOneSpectrum R) (m : ℤ) :
    (ofFinsupp (Finsupp.single v m) : (FractionalIdeal R⁰ K)ˣ) = unitOfPrime v ^ m := by
  rw [ofFinsupp, Finsupp.prod_single_index (zpow_zero _)]

/-- Under `factorization`, a prime corresponds to a basis vector of the free abelian group. -/
@[simp]
lemma factorization_unitOfPrime (v : HeightOneSpectrum R) :
    factorization (unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) =
      Multiplicative.ofAdd (Finsupp.single v 1) := by
  apply Multiplicative.toAdd.injective
  ext w
  rw [toAdd_ofAdd, factorization_apply, coe_unitOfPrime, Finsupp.single_apply,
    count_maximal K w v]

/-- The group of nonzero fractional ideals is torsion-free: taking `n`-th powers is injective
for `n ≠ 0`. In particular the `n`-th root in `exists_pow_eq` is unique. -/
lemma pow_left_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective fun I : (FractionalIdeal R⁰ K)ˣ ↦ I ^ n := by
  intro I J h
  have h2 := congrArg (Multiplicative.toAdd <| factorization ·) h
  simp only [map_pow, toAdd_pow] at h2
  refine factorization.injective (Multiplicative.toAdd.injective (Finsupp.ext fun v ↦ ?_))
  have := congrArg (· v) h2
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) this

/-- The class of a height one prime in the class group. -/
noncomputable def _root_.IsDedekindDomain.HeightOneSpectrum.classGroupMk
    (v : HeightOneSpectrum R) : ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

lemma _root_.IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_one_iff
    (v : HeightOneSpectrum R) : v.classGroupMk = 1 ↔ v.asIdeal.IsPrincipal :=
  ClassGroup.mk0_eq_one_iff _

lemma _root_.IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk_unitOfPrime (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk K (unitOfPrime v) := by
  rw [HeightOneSpectrum.classGroupMk, ← ClassGroup.mk_mk0 K]
  exact congrArg _ (Units.ext rfl)

/-- If the class group is finite, then some positive power of every height one prime is
principal, with a nonzero generator. -/
lemma _root_.IsDedekindDomain.HeightOneSpectrum.exists_pow_eq_span [Finite (ClassGroup R)]
    (v : HeightOneSpectrum R) :
    ∃ (n : ℕ) (π : R), 0 < n ∧ π ≠ 0 ∧ v.asIdeal ^ n = Ideal.span {π} := by
  set m := orderOf v.classGroupMk with hm
  refine ⟨m, ?_⟩
  have h1 : v.classGroupMk ^ m = 1 := pow_orderOf_eq_one _
  have hpow : (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : (Ideal R)⁰) ^ m =
      ⟨v.asIdeal ^ m, pow_mem (mem_nonZeroDivisors_of_ne_zero v.ne_bot) m⟩ :=
    Subtype.ext (SubmonoidClass.coe_pow _ m)
  rw [HeightOneSpectrum.classGroupMk, ← map_pow, hpow] at h1
  obtain ⟨π, hπ⟩ := (ClassGroup.mk0_eq_one_iff _).mp h1
  rw [Ideal.submodule_span_eq] at hπ
  refine ⟨π, by rw [hm]; exact orderOf_pos _, ?_, hπ⟩
  rintro rfl
  exact pow_ne_zero _ v.ne_bot (hπ.trans (by simp))

/-- If all valuations of `I` outside a set `T` of primes vanish, then the ideal class of `I`
lies in the subgroup generated by the classes of the primes in `T`. -/
lemma mk_mem_closure_of_count_eq_zero {T : Set (HeightOneSpectrum R)}
    {I : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v ∉ T, count K v (I : FractionalIdeal R⁰ K) = 0) :
    ClassGroup.mk K I ∈ Subgroup.closure (HeightOneSpectrum.classGroupMk '' T) := by
  have hI : I = ofFinsupp (toFinsupp I) := (factorization.left_inv I).symm
  rw [hI, ofFinsupp, map_finsuppProd]
  refine Subgroup.prod_mem _ fun v hv ↦ ?_
  have hvT : v ∈ T := by
    by_contra hvn
    exact Finsupp.mem_support_iff.mp hv (by rw [toFinsupp_apply, h v hvn])
  show ClassGroup.mk K (unitOfPrime v ^ toFinsupp I v) ∈
    Subgroup.closure (HeightOneSpectrum.classGroupMk '' T)
  rw [map_zpow, ← v.classGroupMk_eq_mk_unitOfPrime K]
  exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem _ hvT)) _

/-- If the valuations of an ideal `J` agree with those of `x : Kˣ` outside a set `T` of primes,
then the class of `J` lies in the subgroup generated by the classes of the primes in `T`. -/
lemma mk0_mem_closure_of_count_eq {T : Set (HeightOneSpectrum R)} {J : (Ideal R)⁰} {x : Kˣ}
    (h : ∀ v ∉ T, count K v ((J : Ideal R) : FractionalIdeal R⁰ K) =
      count K v (spanSingleton R⁰ (x : K))) :
    ClassGroup.mk0 J ∈ Subgroup.closure (HeightOneSpectrum.classGroupMk '' T) := by
  have hmk : ClassGroup.mk0 J =
      ClassGroup.mk K (FractionalIdeal.mk0 K J * (toPrincipalIdeal R K x)⁻¹) := by
    rw [map_mul, map_inv, ClassGroup.mk_toPrincipalIdeal, inv_one, mul_one, ClassGroup.mk_mk0]
  rw [hmk]
  refine mk_mem_closure_of_count_eq_zero fun v hv ↦ ?_
  rw [Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
    Units.val_inv_eq_inv_val, count_inv, FractionalIdeal.coe_mk0, coe_toPrincipalIdeal, h v hv]
  exact add_neg_cancel _

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

/-- The `v`-adic order of a unit `x : Kˣ` is `- count v (x)`: the additive form of
`valuation_eq_exp_neg_count`. -/
theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      - count K v (spanSingleton R⁰ (x : K)) := by
  have h : (v.valuationOfNeZero x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (- count K v (spanSingleton R⁰ (x : K))) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, valuation_eq_exp_neg_count v x.ne_zero]
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at h
  rw [h, toAdd_ofAdd]

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

variable {R K} in
lemma mem_nDivisible {n : ℕ} {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ nDivisible R K n ↔ ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K) :=
  Iff.rfl

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
  map_one' := count_injective fun v ↦ by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := count_injective fun v ↦ by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _), Int.add_ediv_of_dvd_left (I.2 v)]

variable {R K} in
@[simp] lemma nthRootHom_apply (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I = nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ) := rfl

/-- The `n`-th root homomorphism is a genuine `n`-th root. -/
lemma nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    (nthRootHom R K n I) ^ n = (I : (FractionalIdeal R⁰ K)ˣ) := by
  apply count_injective
  intro v
  rw [Units.val_pow_eq_pow_val, count_pow, nthRootHom_apply,
    count_nthRootFun, Int.mul_ediv_cancel' (I.2 v)]

/-- **`n`-th roots of fractional ideals**: if every valuation of `I` is divisible by `n`, then
`I` is an `n`-th power; the root is unique for `n ≠ 0` by `pow_left_injective`. -/
lemma exists_pow_eq (n : ℕ) {I : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)) :
    ∃ J : (FractionalIdeal R⁰ K)ˣ, J ^ n = I :=
  ⟨nthRootHom R K n ⟨I, h⟩, nthRootHom_pow R K n ⟨I, h⟩⟩

end NthRoot

/-!
### The `n`-th-root class map and its kernel

For a unit `u : Kˣ` whose principal ideal has all valuations divisible by `n`, the `n`-th root
`𝔞` of `(u)` has a well-defined class in `ClassGroup R`. The class vanishes exactly when `u` is
a unit of `R` times an `n`-th power in `Kˣ` — the exactness of the fundamental sequence
`1 → Rˣ/(Rˣ)ⁿ → K(∅,n) → Cl(R)[n]` at the middle spot, stated here before any quotients are
taken.
-/

section NthRootClass


variable (R K)

/-- The units of `K` whose principal fractional ideal has all valuations divisible by `n`. -/
def unitsNDivisible (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal R K) (nDivisible R K n)

variable {R K} in
lemma mem_unitsNDivisible {n : ℕ} {u : Kˣ} :
    u ∈ unitsNDivisible R K n ↔ ∀ v, (n : ℤ) ∣ count K v (spanSingleton R⁰ (u : K)) := by
  rw [unitsNDivisible, Subgroup.mem_comap, mem_nDivisible]
  simp only [coe_toPrincipalIdeal]

/-- The restriction of `toPrincipalIdeal` to `unitsNDivisible`, into the `n`-divisible
subgroup. -/
noncomputable def unitsNDivisibleToNDivisible (n : ℕ) :
    unitsNDivisible R K n →* nDivisible R K n :=
  ((toPrincipalIdeal R K).comp (unitsNDivisible R K n).subtype).codRestrict _ (fun x ↦ x.2)

@[simp] lemma coe_unitsNDivisibleToNDivisible (n : ℕ) (u : unitsNDivisible R K n) :
    (unitsNDivisibleToNDivisible R K n u : (FractionalIdeal R⁰ K)ˣ) =
      toPrincipalIdeal R K (u : Kˣ) := rfl

/-- The `n`-th-root class map: the class of the `n`-th root of the principal ideal `(u)`. -/
noncomputable def nthRootClass (n : ℕ) : unitsNDivisible R K n →* ClassGroup R :=
  (ClassGroup.mk K).comp ((nthRootHom R K n).comp (unitsNDivisibleToNDivisible R K n))

@[simp]
lemma nthRootClass_apply (n : ℕ) (u : unitsNDivisible R K n) :
    nthRootClass R K n u =
      ClassGroup.mk K (nthRootHom R K n (unitsNDivisibleToNDivisible R K n u)) :=
  rfl

/-- **Exactness of the fundamental sequence at the middle spot**: the `n`-th-root class of `u`
vanishes exactly when `u` is a unit of `R` times an `n`-th power. -/
lemma nthRootClass_eq_one_iff {n : ℕ} (hn : n ≠ 0) (u : unitsNDivisible R K n) :
    nthRootClass R K n u = 1 ↔
      ∃ (a : Rˣ) (w : Kˣ), Units.map (algebraMap R K : R →* K) a * w ^ n = (u : Kˣ) := by
  rw [nthRootClass_apply, ClassGroup.mk_eq_one_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    -- the `n`-th power of the found generator `w` generates `(u)`, so `u / wⁿ` is a unit of `R`
    have hpow : toPrincipalIdeal R K (w ^ n) = toPrincipalIdeal R K (u : Kˣ) := by
      rw [map_pow, hw, nthRootHom_pow, coe_unitsNDivisibleToNDivisible]
    have h1 : toPrincipalIdeal R K ((u : Kˣ) * (w ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpow, mul_inv_cancel]
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp h1
    exact ⟨a, w, by rw [ha]; group⟩
  · rintro ⟨a, w, hw⟩
    -- `w` generates the `n`-th root: its valuations are `count (u) / n`
    refine ⟨w, count_injective fun v ↦ ?_⟩
    have hcu : count K v ((toPrincipalIdeal R K (u : Kˣ) : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) = n * count K v
          ((toPrincipalIdeal R K w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) := by
      rw [← hw, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        count_mul K v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)), count_pow,
        (toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, Units.val_one, count_one, zero_add]
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcu,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hn)]

end NthRootClass

end FractionalIdeal
