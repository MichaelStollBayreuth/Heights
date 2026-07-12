import Mathlib

/-!
# Material for Mathlib

This file collects the general-purpose results developed for `Heights.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots
  (with the special cases `map_cubic_of_one_lt`, `le_one_of_root_cubic` for depressed cubics).
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`.
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
-/

section Group

variable {G H : Type*} [Group G] [Group H]

/-- A map `f` between groups with `f 1 = 1` that sends triples with product `1` to triples
with product `1` is a homomorphism. Useful when a map is naturally defined via a symmetric
ternary relation, like collinearity on a cubic curve. -/
@[to_additive /-- A map `f` between additive groups with `f 0 = 0` that sends triples with
sum `0` to triples with sum `0` is a homomorphism. Useful when a map is naturally defined via
a symmetric ternary relation, like collinearity on a cubic curve. -/]
def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group

@[to_additive (attr := simp)]
lemma MonoidHom.coe_ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    ⇑(ofMapMulMulEqOne hf₁ hf) = f :=
  rfl

/-- The preimage of a finite subgroup under an injective group homomorphism is finite. -/
@[to_additive]
lemma Subgroup.finite_comap_of_injective {f : G →* H} (hf : Function.Injective f)
    (S : Subgroup H) [Finite S] : Finite (S.comap f) :=
  .of_injective (fun x ↦ (⟨f x, x.2⟩ : S)) fun _ _ h ↦
    Subtype.ext <| hf <| congrArg Subtype.val h

/-- A product of finitely many finite subgroups is finite. -/
@[to_additive]
instance Subgroup.instFinitePi {ι : Type*} [Finite ι] {G : ι → Type*} [(i : ι) → Group (G i)]
    {S : (i : ι) → Subgroup (G i)} [(i : ι) → Finite (S i)] :
    Finite (Subgroup.pi Set.univ S) :=
  .of_injective (fun x i ↦ (⟨x.1 i, x.2 i (Set.mem_univ i)⟩ : S i)) fun _ _ h ↦
    Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun h i)

end Group

section Units

variable {α : Type*} [Monoid α]

@[to_additive]
lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · simpa using congrArg Units.val hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩

end Units

section modPow

/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def QuotientGroup.congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e <| by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u ^ n, ⟨_, rfl⟩, by simp⟩

namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  simp [IsUnit.exists_pow_eq_unit_iff]

lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  simp only [← mk_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp

lemma mk_eq_mk_iff {u v : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = QuotientGroup.mk v ↔ ∃ w : αˣ, v = u * w ^ n := by
  simp only [QuotientGroup.eq, MonoidHom.mem_range, powMonoidHom_apply]
  exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [hw]; group⟩, fun ⟨w, hw⟩ ↦ ⟨w, by rw [hw]; group⟩⟩

@[simp]
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩

/-- A monoid homomorphism `α →* β` induces a homomorphism on `n`-th power classes of units. -/
def map (φ : α →* β) (n : ℕ) : Units.modPow α n →* Units.modPow β n :=
  QuotientGroup.map _ _ (Units.map φ) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map φ u, by simp [powMonoidHom]⟩

@[simp]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) :
    map φ n (QuotientGroup.mk u) = QuotientGroup.mk (Units.map φ u) :=
  rfl

@[simp]
lemma map_id (n : ℕ) : map (MonoidHom.id α) n = MonoidHom.id (Units.modPow α n) := by
  ext
  simp

lemma map_comp {γ : Type*} [CommMonoid γ] (ψ : β →* γ) (φ : α →* β) (n : ℕ) :
    (map ψ n).comp (map φ n) = map (ψ.comp φ) n := by
  ext
  simp

@[simp]
lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : Units.modPow α n) = ((ha.map φ).unit : Units.modPow β n) := by
  rw [map, ← mk'_apply, map_mk']
  exact congrArg _ (Units.ext rfl)

/-- A multiplicative equivalence `α ≃* β` induces one on `n`-th power classes of units. -/
def congr (e : α ≃* β) (n : ℕ) : Units.modPow α n ≃* Units.modPow β n :=
  congrRangePowMonoidHom (Units.mapEquiv e) n

/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def piEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ) :
    Units.modPow ((i : ι) → α i) n ≃* ((i : ι) → Units.modPow (α i) n) :=
  (congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

@[simp]
lemma piEquiv_mk {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ)
    (u : ((i : ι) → α i)ˣ) (i : ι) :
    piEquiv α n (QuotientGroup.mk u) i = QuotientGroup.mk (MulEquiv.piUnits u i) := by
  simp [piEquiv, congrRangePowMonoidHom, mulEquivPiModRangePowMonoidHom_apply]

end Units.modPow

end modPow

section LinearAlgebra

/-- A "diagonal" family of vectors — supported at the family index with nonzero value there —
is linearly independent. -/
lemma linearIndependent_of_diagonal {ι A : Type*} [CommRing A] [NoZeroDivisors A]
    {u : ι → ι → A} (hd : ∀ i, u i i ≠ 0) (ho : ∀ i j, j ≠ i → u i j = 0) :
    LinearIndependent A u := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrFun hg i
  rw [Finset.sum_apply, Pi.zero_apply,
    Finset.sum_eq_single i
      (fun j _ hji ↦ by rw [Pi.smul_apply, ho j i (fun hc ↦ hji (hc ▸ rfl)), smul_zero])
      (fun hni ↦ absurd hi hni),
    Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (hd i)

end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

lemma Valuation.map_natCast_le_one {R : Type*} [Ring R] (ν : Valuation R Γ) (n : ℕ) :
    ν (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (ν.map_add _ _).trans (max_le ih ν.map_one.le)

/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma Valuation.eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
  _ ≤ ν a * 1 := by gcongr
  _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma Valuation.map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial of positive degree with coefficients that are integral for the
valuation `ν` is itself integral. (This is a concrete form of the fact that valuation rings are
integrally closed.) -/
lemma Valuation.le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  by_contra! hlt
  have h := ν.map_eval_eq_of_one_lt hp hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

section Cubic

variable [Nontrivial L]

-- The following three lemmas are very specific and should be moved
-- as private lemma to their use site.
-- Or maybe better: inline the proofs if it doesn't blow up proof length too much.
private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) :
    ∀ i < (X ^ 3 + C a * X + C b).natDegree, ν ((X ^ 3 + C a * X + C b).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X + C b).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb]

/-- If `1 < ν t` and `a`, `b` are integral, the leading term of the cubic dominates. -/
lemma Valuation.map_cubic_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (ht : 1 < ν t) :
    ν (t ^ 3 + a * t + b) = ν t ^ 3 := by
  have hp : (X ^ 3 + C a * X + C b).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X + C b).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb) ht
  rw [hdeg] at h
  simpa using h

/-- A root of a monic cubic with integral coefficients is integral. -/
lemma Valuation.le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1)
    (heq : t ^ 3 + a * t + b = 0) : ν t ≤ 1 := by
  have hp : (X ^ 3 + C a * X + C b).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X + C b).natDegree = 3 := by compute_degree!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb) (by rw [hdeg]; norm_num) ?_
  simpa using heq

end Cubic

end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  -- maybe this can be streamlined using 'Ideal.hasFiniteMulSupport`?
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_setOf_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

lemma Set.integer_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    S.integer K ≤ T.integer K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

lemma Set.unit_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) : S.unit K ≤ T.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

/-- Ideal-level divisibility characterization of `Associates.count`: the multiplicity of `v` in
`J` is at least `k` iff `v ^ k` divides `J`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff_le {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/-- Divisibility characterization of `Associates.count` for a height one prime: the `v`-adic
valuation of `x` is at least `k` iff `x ∈ v ^ k`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- If the valuation of a unit `u` is the `n`-th power of the valuation of a unit `z`, then the
`v`-adic order of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero (v : HeightOneSpectrum R)
    {n : ℕ} {u z : Kˣ} (h : v.valuation K (u : K) = v.valuation K (z : K) ^ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  have hu : v.valuationOfNeZero u = v.valuationOfNeZero z ^ n := by
    rw [valuationOfNeZero_eq_iff]
    push_cast
    rw [valuationOfNeZero_eq, h]
  exact ⟨Multiplicative.toAdd (v.valuationOfNeZero z), by rw [hu]; simp [toAdd_pow]⟩

/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [valuationOfNeZeroMod, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, EmbeddingLike.map_eq_one_iff]
  -- This is not necessary:
  -- show (QuotientGroup.mk (v.valuationOfNeZero u) : Multiplicative ℤ ⧸ _) = 1 ↔ _
  -- If helpful for following the proof, replace `show` by `change`.
  refine (QuotientGroup.eq_one_iff _).trans ?_
  rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [← hk]; ring⟩, fun ⟨k, hk⟩ ↦ ⟨k, by rw [hk]; ring⟩⟩

/-- If a power of the prime `v` is generated by `π`, then `π` is a `w`-adic unit at every prime
`w ≠ v`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_eq_span
    {v w : HeightOneSpectrum R} (hne : w ≠ v) {n : ℕ} {π : R}
    (h : v.asIdeal ^ n = Ideal.span {π}) :
    w.valuation K (algebraMap R K π) = 1 := by
  refine w.valuation_eq_one_iff_notMem.mpr fun hmem ↦ hne (HeightOneSpectrum.ext ?_).symm
  refine v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le (n := n) ?_)
  rwa [h, Ideal.span_le, Set.singleton_subset_iff]

variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]

/-- The primes of `B` lying above a set `S` of primes of `R`. -/
def IsDedekindDomain.HeightOneSpectrum.primesAbove (S : Set (HeightOneSpectrum R)) :
    Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.
set_option linter.unusedSectionVars false in
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_mono {S T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) : primesAbove R B S ⊆ primesAbove R B T :=
  fun _ ⟨v, hv, hva⟩ ↦ ⟨v, hST hv, hva⟩

/-- The prime of `R` lying below a prime `w` of an integral extension `B`. -/
def IsDedekindDomain.HeightOneSpectrum.below [Algebra.IsIntegral R B] (w : HeightOneSpectrum B) :
    HeightOneSpectrum R where
  asIdeal := w.asIdeal.under R
  isPrime := Ideal.IsPrime.under R w.asIdeal
  ne_bot := Ideal.IsIntegral.comap_ne_bot R w.ne_bot

@[simp]
lemma IsDedekindDomain.HeightOneSpectrum.below_asIdeal [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    (w.below R).asIdeal = w.asIdeal.under R :=
  rfl

instance IsDedekindDomain.HeightOneSpectrum.instLiesOverBelow [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.below R).asIdeal :=
  Ideal.over_under ..

lemma IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff [Algebra.IsIntegral R B]
    (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.below R ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨w.below R, hw, rfl⟩⟩
  rwa [show w.below R = v from HeightOneSpectrum.ext hva.symm]

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`: each fiber
injects into `Ideal.primesOver`, which is finite for a Dedekind extension. -/
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_finite [Algebra.IsIntegral R B]
    [Module.IsTorsionFree R B] {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w ⟨v, hv, hva⟩ ↦ Set.mem_biUnion hv ⟨w.isPrime, ⟨hva⟩⟩
  refine (hS.biUnion fun v _ ↦ ?_).subset hsub
  have := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)

/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def IsDedekindDomain.selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Units.modPow L n) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

set_option linter.unusedSectionVars false in
lemma IsDedekindDomain.mem_selmerGroupAbove_iff (L : Type*) [Field L] [Algebra B L]
    [IsFractionRing B L] (S : Set (HeightOneSpectrum R)) (n : ℕ) (x : Units.modPow L n) :
    x ∈ selmerGroupAbove R B L S n ↔
      ∀ w ∉ HeightOneSpectrum.primesAbove R B S, w.valuationOfNeZeroMod n x = 1 :=
  Iff.rfl

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

/-- The resultant of `f` with the linear polynomial `C x - X` is `f.eval x`.
Note the absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
lemma resultant_C_sub_X (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  have h : f.resultant (X - C x) m 1 = (-1) ^ m * f.eval x := by
    have := resultant_X_sub_C_pow_right f x m 1 hm
    rwa [pow_one, mul_one, pow_one] at this
  rw [show C x - X = C (-1 : R) * (X - C x) by simp, resultant_C_mul_right, h,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

lemma Monic.resultant_one_right (hg : g.Monic) (n : ℕ) :
    g.resultant 1 g.natDegree n = 1 := by
  convert resultant_add_right_deg g 1 g.natDegree 0 n (by simp)
  · simp
  rw [← C_1, resultant_C_zero_right, one_pow, mul_one, hg.coeff_natDegree, one_pow]

lemma mem_degreeLT_natDegree_iff {q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]

section

variable [Nontrivial R] {q : R[X]} {n : ℕ}

lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]

lemma modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

lemma divByMonic_mem_degreeLT (hg : g.Monic)
    (hq : q ∈ degreeLT R (g.natDegree + n)) : q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd

private lemma Monic.divMod_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g ∧ (g * v + u) %ₘ g = u %ₘ g := by
  refine div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

lemma Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g :=
  (hg.divMod_mul_add v u).1

lemma Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g :=
  (hg.divMod_mul_add v u).2

end

section Sylvester
-- Reviewed up to here.

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`. This is the
map that `mk g : R[X]_(g.natDegree) ≃ₗ AdjoinRoot g` turns into multiplication by `mk g p`. -/
noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
lemma mulModByMonic_apply_coe (hg : g.Monic) (p : R[X])
    (q : degreeLT R g.natDegree) : (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl

/-- For monic `g`, the Sylvester map of `g` and `1`, namely `(u, v) ↦ g * v + u`, is a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`. Its inverse is
`q ↦ (q %ₘ g, q /ₘ g)`. -/
noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · rintro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
lemma coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl

/-- The inverse of `Ψ` is division with remainder by `g`. -/
lemma coe_sylvesterEquivOne_symm (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g) ∧
      ((((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g) := by
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have hq : ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X]) =
      g * (w.2 : R[X]) + (w.1 : R[X]) := by
    simp [sylvesterEquivOne]
  have h₁ : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, hq]
  refine ⟨?_, ?_⟩
  · rw [hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr h₁]
  · rw [hg.divByMonic_mul_add, (divByMonic_eq_zero_iff hg).mpr h₁, add_zero]

/-- The block-triangular endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`. -/
noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

/-- The first coordinate of `B (u, v)` is `(p * u) %ₘ g`. -/
lemma coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).1, sylvesterMap_apply_coe, hg.modByMonic_mul_add]

/-- The second coordinate of `B (u, v)` is `v + (p * u) /ₘ g`. -/
lemma coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).2, sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in
/-- The determinant of the block-triangular map `B` is the determinant of its upper-left block. -/
lemma det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  -- the upper-left block is `mulModByMonic hg p`, and `B` fixes `{0} × R[X]_n` pointwise
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
      (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester

end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)

lemma exists_degree_lt_mk_eq [Nontrivial R] (hg : g.Monic) (a : AdjoinRoot g) :
    ∃ p, p.degree < g.degree ∧ a = mk g p := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  exact ⟨q %ₘ g, degree_modByMonic_lt q hg, (mk_modByMonic hg q).symm⟩

lemma mk_eq_mk_iff_of_degree_lt [Nontrivial R] (hg : g.Monic) {p q : R[X]}
    (hp : p.degree < g.degree) (hq : q.degree < g.degree) :
    mk g p = mk g q ↔ p = q :=
  ⟨fun h ↦ sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg (mk_eq_mk.mp h) <|
    (degree_sub_le p q).trans_lt (max_lt hp hq), fun h ↦ h ▸ rfl⟩

/-- `mk g` is a linear equivalence from the polynomials of degree `< g.natDegree` onto
`AdjoinRoot g`, for `g` monic. -/
noncomputable def degreeLTEquiv [Nontrivial R] (hg : g.Monic) :
    degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  ofBijective ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype) <| by
    constructor
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      replace h : mk g q = mk g q' := h
      rw [mk_eq_mk] at h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hq hq'
      refine Subtype.ext (sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg h ?_)
      exact (degree_sub_le q q').trans_lt (max_lt hq hq')
    · intro a
      obtain ⟨q, rfl⟩ := mk_surjective a
      exact ⟨⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, mk_modByMonic hg q⟩

@[simp]
lemma degreeLTEquiv_apply [Nontrivial R] (hg : g.Monic)
    (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl

/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
lemma norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic hg, map_mul]

/-- The norm of `AdjoinRoot.mk g p` over the base ring, for `g` monic, is the resultant of `g`
and `p`. Equivalently, it is the product of the values of `p` at the roots of `g`. -/
lemma norm_mk_eq_resultant [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k, comp_coe,
      symm_trans_self, refl_toLinearMap, id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]

end AdjoinRoot

section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

Note that this is *not* defined via `normalizedFactors` (which would require `DecidableEq K`);
membership in `normalizedFactors f` is characterized by `Factors.mem_normalizedFactors_iff`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

lemma ne_zero (p : f.Factors) : (p : K[X]) ≠ 0 := p.irreducible.ne_zero

lemma prime (p : f.Factors) : Prime (p : K[X]) := p.irreducible.prime

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd

/-- Membership in `normalizedFactors` (with its normalization from `DecidableEq K`) is
equivalent to being a monic irreducible factor. -/
lemma mem_normalizedFactors_iff [DecidableEq K] (hf : f ≠ 0) {p : K[X]} :
    p ∈ normalizedFactors f ↔ p.Monic ∧ Irreducible p ∧ p ∣ f := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hf]
  refine ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂ ▸ monic_normalize h₁.ne_zero, h₁, h₃⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁.normalize_eq_self, h₃⟩⟩

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact Finite.of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (mem_normalizedFactors_iff hf).mpr hp).injective

lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
        Ideal.span_singleton_eq_span_singleton.mp h

lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

lemma associated_prod [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  -- identify `f.Factors` with the subtype of the `Finset` of normalized factors
  have hprod : ∏ p : f.Factors, (p : K[X]) =
      ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ by
        rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hf]) _ _
      fun x ↦ by rw [Equiv.subtypeEquivRight_apply]
  have hcoe : ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) =
      ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hprod, hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']
  exact prod_normalizedFactors hf

lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hf hsq)).symm

end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite

lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]

open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X]/(f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h

/-- **Chinese Remainder Theorem** for `AdjoinRoot`: for `f` nonzero and squarefree,
`K[X]/(f)` is the product of the fields `K[X]/(p)` over the monic irreducible factors `p`
of `f`. -/
noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hf
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

@[simp]
lemma equivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    equivPiFactors hf hsq (mk f q) p = mk (p : K[X]) q :=
  rfl

/-- The projection of `K[X]/(f)` onto the field factor `K[X]/(p)`. -/
noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hf hsq).toRingEquiv.toRingHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  rfl

/-- The `n`-th power classes of units of `K[X]/(f)` are the product of those of its
field factors. -/
noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    Units.modPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) n) :=
  (Units.modPow.congr (equivPiFactors hf hsq).toMulEquiv n).trans <|
    Units.modPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors. -/
@[simp]
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (ha.unit : Units.modPow (AdjoinRoot f) n) p =
      ((ha.map (projFactor hf hsq p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) n) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, Units.modPow.congr,
    QuotientGroup.congrRangePowMonoidHom, QuotientGroup.congr_mk, Units.modPow.piEquiv,
    QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]
  exact congrArg _ (Units.ext rfl)

end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The integral closure of `𝓞 K` in an extension `L` of `K` is the integral closure of `ℤ`
in `L`. -/
theorem isIntegralClosure_int_integralClosure :
    IsIntegralClosure (integralClosure (𝓞 K) L) ℤ L := by
  refine ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ?_, fun ⟨y, hy⟩ => ?_⟩⟩
  · exact ⟨⟨x, IsIntegral.tower_top (A := 𝓞 K) hx⟩, rfl⟩
  · have hyint : IsIntegral (𝓞 K) (y : L) := y.2
    have := isIntegral_trans (R := ℤ) (y : L) hyint
    rwa [show ((y : L)) = x from hy] at this

variable [NumberField K] [FiniteDimensional K L]

/-- The **class number theorem** for the integral closure of `𝓞 K` in a finite extension `L`
of the number field `K`: its class group is finite. -/
theorem NumberField.finite_classGroup_integralClosure :
    Finite (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have := isIntegralClosure_int_integralClosure K L
  have := ClassGroup.fintypeOfAdmissibleOfFinite ℚ L
    (S := integralClosure (𝓞 K) L) AbsoluteValue.absIsAdmissible
  exact Finite.of_fintype _

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `𝓞 K` in a
finite extension `L` of the number field `K`: its unit group is finitely generated. -/
theorem NumberField.fg_units_integralClosure :
    Group.FG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Group.fg_of_surjective
    (f := (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).toMonoidHom)
    (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).surjective

end NumberField
