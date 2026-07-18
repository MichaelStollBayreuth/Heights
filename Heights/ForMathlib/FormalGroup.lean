import Mathlib
import Heights.ForMathlib.Henselian
import Heights.ForMathlib.AdicCompletionExtension
import Heights.ForMathlib.SelmerGroup
import Heights.ForMathlib.VariableChange

/-!
# Interface to formal-group theory over a local field

Let `K` be the fraction field of a Dedekind domain, `v` a height-one prime with finite
residue field, and `K_v` the completion (of characteristic `0`). This file states the
structural consequences of the theory of formal groups over `𝒪_v` that the 2-descent
machinery needs.

* `WeierstrassCurve.Affine.exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers`:
  for an elliptic curve `E` over `K_v`, the group `E(K_v)` has a subgroup of finite index
  isomorphic to the additive group `(𝒪_v, +)`.

  This is proved from a skeleton of `sorry`ed pieces (Silverman, *Arithmetic of Elliptic
  Curves*, VII.2 and IV.6): after passing to an integral model
  (`exists_variableChange_map_eq`), the valuation filtration `E_{n+1}(K_v)` is a subgroup
  (`filtration`; closure under addition is the group-law part of the formal-group theory),
  each of its steps is of finite index (`filtration_finiteIndex`; the steps are open in the
  compact group `E(K_v)`), and a suitable step is identified with `(𝒪_v, +)` by the formal
  logarithm (`exists_filtration_equiv`, using `k > e/(p-1)`, Silverman IV.6.4). Mathlib's
  `FormalGroup` (one-dimensional formal group laws) is a starting point for the remaining
  pieces, but the formal group of an elliptic curve, the formal logarithm, and the topology
  on the points of an elliptic curve over a local field are all still missing.

* `IsDedekindDomain.HeightOneSpectrum.card_selmerGroup_integralClosure`: for odd residue
  characteristic and a finite separable extension `L` of `K_v` with `B` the integral
  closure of `𝒪_v` in `L`, the Selmer group `L(∅, 2)` (classes of units of `L` with even
  valuation at every prime of `B`) has exactly two elements.

  This is the multiplicative (`𝔾ₘ`) analogue of the first statement, and is proved here:
  `𝒪_v` is a complete discrete valuation ring, hence Henselian
  (`henselianLocalRing_adicCompletionIntegers`), so by the theory of finite algebras over
  Henselian local rings (see `Heights.ForMathlib.Henselian`, vendored from the FLT
  project) its integral closure `B` in `L` is a Henselian discrete valuation ring with
  finite residue field `k`. Then `L(∅, 2) ≅ Bˣ/(Bˣ)²` (`selmerGroup.fromUnitLift` is
  bijective over a DVR), the principal units of `B` are squares by Hensel's lemma applied
  to `X² - u` (`IsSquare.of_sub_one_mem_maximalIdeal`), so `Bˣ/(Bˣ)² ≅ kˣ/(kˣ)²`, which
  has order `2` for a finite field of odd characteristic.
-/

open IsDedekindDomain Polynomial

namespace WeierstrassCurve.Affine

open WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

section IntegralModel

variable (W : Affine (v.adicCompletion K))

private lemma pow_mul_mem_adicCompletionIntegers {z : v.adicCompletion K}
    (hz : Valued.v z = exp (-1)) {N i : ℕ} (hi : 1 ≤ i) {a : v.adicCompletion K}
    (ha : log (Valued.v a) ≤ (N : ℤ)) :
    (z ^ N) ^ i * a ∈ v.adicCompletionIntegers K := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  refine (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mpr ?_
  have hva : Valued.v a = exp (log (Valued.v a)) :=
    (exp_log ((Valuation.ne_zero_iff _).mpr ha0)).symm
  rw [map_mul, map_pow, map_pow, hz, ← exp_nsmul, ← exp_nsmul, hva, ← exp_add, ← exp_zero]
  refine exp_le_exp.mpr ?_
  have h2 : (N : ℤ) ≤ ((i * N : ℕ) : ℤ) := by exact_mod_cast Nat.le_mul_of_pos_left N hi
  push_cast at h2 ⊢
  lia

/-- Every Weierstrass curve over `K_v` has an integral model: after an admissible change of
variables, the coefficients lie in `𝒪_v`. -/
theorem exists_variableChange_map_eq :
    ∃ (C : VariableChange (v.adicCompletion K))
      (W₀ : WeierstrassCurve (v.adicCompletionIntegers K)),
      W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = C • W := by
  -- an element of valuation `exp (-1)`
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp (-1))
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact exp_ne_zero hz.symm
  set w : (v.adicCompletion K)ˣ := Units.mk0 z hz0 with hw
  -- a bound for the valuations of the coefficients
  set M : ℤ := log (Valued.v W.a₁) ⊔ log (Valued.v W.a₂) ⊔ log (Valued.v W.a₃) ⊔
    log (Valued.v W.a₄) ⊔ log (Valued.v W.a₆) ⊔ 0
  set N : ℕ := M.toNat
  -- scaling a coefficient by `z ^ (N * i)` lands in the ring of integers
  have key (a : v.adicCompletion K) (ha : log (Valued.v a) ≤ M) {i : ℕ} (hi : 1 ≤ i) :
      (z ^ N) ^ i * a ∈ v.adicCompletionIntegers K :=
    pow_mul_mem_adicCompletionIntegers v hz hi (ha.trans (Int.self_le_toNat M))
  -- the change of variables by `u = w⁻¹ ^ N`
  set C : VariableChange (v.adicCompletion K) := ⟨w⁻¹ ^ N, 0, 0, 0⟩ with hC
  have hu (i : ℕ) : ((C.u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ i =
      (z ^ N) ^ i := by
    simp [hC, hw]
  have hb₁ : log (Valued.v W.a₁) ≤ M :=
    le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans le_sup_left
  have hb₂ : log (Valued.v W.a₂) ≤ M :=
    le_sup_right.trans <| le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans le_sup_left
  have hb₃ : log (Valued.v W.a₃) ≤ M :=
    le_sup_right.trans <| le_sup_left.trans <| le_sup_left.trans le_sup_left
  have hb₄ : log (Valued.v W.a₄) ≤ M := le_sup_right.trans <| le_sup_left.trans le_sup_left
  have hb₆ : log (Valued.v W.a₆) ≤ M := le_sup_right.trans le_sup_left
  refine ⟨C, ⟨⟨_, key W.a₁ hb₁ le_rfl⟩, ⟨_, key W.a₂ hb₂ one_le_two⟩,
    ⟨_, key W.a₃ hb₃ (i := 3) (by lia)⟩, ⟨_, key W.a₄ hb₄ (i := 4) (by lia)⟩,
    ⟨_, key W.a₆ hb₆ (i := 6) (by lia)⟩⟩, ?_⟩
  ext
  · show (z ^ N) ^ 1 * W.a₁ = (C • W).a₁
    rw [variableChange_a₁, ← hu 1]
    ring
  · show (z ^ N) ^ 2 * W.a₂ = (C • W).a₂
    rw [variableChange_a₂, ← hu 2]
    ring
  · show (z ^ N) ^ 3 * W.a₃ = (C • W).a₃
    rw [variableChange_a₃, ← hu 3]
    ring
  · show (z ^ N) ^ 4 * W.a₄ = (C • W).a₄
    rw [variableChange_a₄, ← hu 4]
    ring
  · show (z ^ N) ^ 6 * W.a₆ = (C • W).a₆
    rw [variableChange_a₆, ← hu 6]
    ring

end IntegralModel

section Filtration

variable {v} [DecidableEq (v.adicCompletion K)] {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}

/-- For an elliptic curve `W` over `K_v` with an integral model `W₀` and `n : ℕ`, the
subgroup `E_{n+1}(K_v)` of points `(x, y)` with `exp (2 * (n + 1)) ≤ v(x)` (a pole of order
at least `2(n + 1)` at `x`, together with `0`); this is the kernel of reduction modulo
`𝔪^(n+1)`, isomorphic to the group `Ê(𝔪^(n+1))` of points of the formal group of `W₀`
(Silverman, VII.2.2). The proof that it is closed under addition is formal-group material
and is `sorry`ed for now. -/
def filtration (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) (n : ℕ) : AddSubgroup W.Point where
  carrier := {P | match P with
    | .zero => True
    | @Point.some _ _ _ x _ _ => exp (2 * (n + 1) : ℤ) ≤ Valued.v x}
  zero_mem' := trivial
  neg_mem' {P} hP := by
    match P with
    | .zero => exact hP
    | @Point.some _ _ _ x y h => rw [Set.mem_setOf_eq, Point.neg_some]; exact hP
  add_mem' := sorry

variable {hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W}
  {n : ℕ}

@[simp]
lemma zero_mem_filtration : (0 : W.Point) ∈ filtration hW n := trivial

@[simp]
lemma some_mem_filtration {x y : v.adicCompletion K} {h : W.Nonsingular x y} :
    (.some x y h : W.Point) ∈ filtration hW n ↔ exp (2 * (n + 1) : ℤ) ≤ Valued.v x := Iff.rfl

variable [CharZero K] [Finite (R ⧸ v.asIdeal)] [W.IsElliptic]

/-- Each step of the valuation filtration on the points of an elliptic curve over `K_v` has
finite index: the filtration steps are open subgroups of the compact group `E(K_v)`. -/
theorem filtration_finiteIndex (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) (n : ℕ) : (filtration hW n).FiniteIndex :=
  sorry

/-- Some step of the valuation filtration on the points of an elliptic curve over `K_v` is
isomorphic to the additive group of `𝒪_v`: for `𝔪^k` past the ramification of the residue
characteristic, the formal logarithm identifies `Ê(𝔪^k)` with `(𝔪^k, +) ≅ (𝒪_v, +)`
(Silverman, IV.6.4). -/
theorem exists_filtration_equiv (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) :
    ∃ n, Nonempty (filtration hW n ≃+ v.adicCompletionIntegers K) :=
  sorry

end Filtration

variable [CharZero K] [Finite (R ⧸ v.asIdeal)] (W : Affine (v.adicCompletion K))
  [W.IsElliptic]

open scoped Classical in
/-- The group of points of an elliptic curve over the completion `K_v` (a characteristic-`0`
local field with finite residue field) has a subgroup of finite index that is isomorphic to
the additive group of the valuation ring `𝒪_v`.

This is the structure theorem coming from the formal group of the curve: pass to an
integral model and take a suitable step of the valuation filtration. -/
theorem exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers :
    ∃ U : AddSubgroup W.Point, U.FiniteIndex ∧ Nonempty (U ≃+ (v.adicCompletionIntegers K)) := by
  obtain ⟨C, W₀, hW⟩ := exists_variableChange_map_eq v W
  obtain ⟨n, ⟨e⟩⟩ := exists_filtration_equiv hW
  refine ⟨(filtration hW n).map (Point.equivVariableChange W C : _ →+ _), ⟨?_⟩, ?_⟩
  · rw [AddSubgroup.index_map_equiv]
    exact (filtration_finiteIndex hW n).index_ne_zero
  · exact ⟨((AddEquiv.addSubgroupMap (Point.equivVariableChange W C) _).symm.trans e)⟩

end WeierstrassCurve.Affine

/-!
### Square classes of units of a Henselian local ring

The lemmas in this section are stated in their natural generality: any Henselian local ring
in which `2` is a unit, resp. any discrete valuation ring. They are Mathlib-upstreaming
candidates.
-/

section Henselian

open IsLocalRing

/-- In a Henselian local ring in which `2` is a unit, every element congruent to `1` modulo
the maximal ideal is a square (Hensel's lemma for `X ^ 2 - u`). -/
theorem IsSquare.of_sub_one_mem_maximalIdeal {A : Type*} [CommRing A] [HenselianLocalRing A]
    (h2 : IsUnit (2 : A)) {u : A} (hu : u - 1 ∈ maximalIdeal A) : IsSquare u := by
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) 1 (by simpa using neg_mem hu)
    (by simpa [one_add_one_eq_two] using h2)
  have h : a ^ 2 = u := by simpa [IsRoot, sub_eq_zero] using ha
  exact ⟨a, by rw [← h, pow_two]⟩

/-- The group of square classes of a finite field of odd characteristic has order `2`. -/
theorem Nat.card_units_quotient_squares {k : Type*} [Field k] [Finite k]
    (h2 : ringChar k ≠ 2) :
    Nat.card (kˣ ⧸ (powMonoidHom 2 : kˣ →* kˣ).range) = 2 := by
  have : Fintype k := Fintype.ofFinite k
  have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
  rw [← Subgroup.index, IsCyclic.index_powMonoidHom_range, Nat.card_units,
    Nat.card_eq_fintype_card,
    Nat.gcd_eq_right (by have := Fintype.card_pos (α := k); lia)]

/-- The group of square classes of the units of a Henselian local ring with finite residue
field in which `2` is a unit has order `2`: reduction to the residue field is a bijection on
square classes, since the principal units are squares by Hensel's lemma. -/
theorem Nat.card_units_quotient_squares_of_henselian {A : Type*} [CommRing A]
    [HenselianLocalRing A] [Finite (ResidueField A)] (h2 : IsUnit (2 : A)) :
    Nat.card (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) = 2 := by
  have h2' : ringChar (ResidueField A) ≠ 2 := by
    intro h
    have : (2 : ResidueField A) = 0 := by
      rw [show (2 : ResidueField A) = ((2 : ℕ) : ResidueField A) by push_cast; rfl, ← h,
        ringChar.Nat.cast_ringChar]
    exact (h2.map (residue A)).ne_zero (by rwa [map_ofNat])
  -- the composite `Aˣ → kˣ → kˣ/squares` is surjective with kernel the squares of `Aˣ`
  let φ : Aˣ →* (ResidueField A)ˣ := Units.map (residue A)
  let ρ : Aˣ →* (ResidueField A)ˣ ⧸ (powMonoidHom 2 : _ →* (ResidueField A)ˣ).range :=
    (QuotientGroup.mk' _).comp φ
  have hlift (w : (ResidueField A)ˣ) : ∃ u : Aˣ, φ u = w := by
    obtain ⟨x, hx⟩ := residue_surjective (w : ResidueField A)
    have hxu : IsUnit x := isUnit_of_map_unit (residue A) x (hx ▸ w.isUnit)
    exact ⟨hxu.unit, Units.ext (by simpa [φ] using hx)⟩
  have hρ : Function.Surjective ρ := by
    intro c
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ c
    obtain ⟨u, hu⟩ := hlift w
    exact ⟨u, congrArg _ hu⟩
  have hker : ρ.ker = (powMonoidHom 2 : Aˣ →* Aˣ).range := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, MonoidHom.mem_range, ρ]
    refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun ⟨c, hc⟩ ↦ ⟨φ c, by rw [← hc]; simp [φ, powMonoidHom_apply]⟩⟩
    -- lift the square root of the residue and correct by it
    obtain ⟨c, hc⟩ := hlift w
    have h1 : φ (u * (c ^ 2)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hc, ← hw]
      simp [powMonoidHom_apply]
    have hval : residue A ((u * (c ^ 2)⁻¹ : Aˣ) : A) = 1 := by
      have := congrArg Units.val h1
      rwa [show (φ (u * (c ^ 2)⁻¹) : ResidueField A) = residue A ((u * (c ^ 2)⁻¹ : Aˣ) : A)
        from rfl, Units.val_one] at this
    have hmem : ((u * (c ^ 2)⁻¹ : Aˣ) : A) - 1 ∈ maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
      exact hval
    obtain ⟨a, ha⟩ := IsSquare.of_sub_one_mem_maximalIdeal h2 hmem
    have hau : IsUnit a := isUnit_of_mul_isUnit_left (ha ▸ (u * (c ^ 2)⁻¹).isUnit)
    have hsq : hau.unit ^ 2 = u * (c ^ 2)⁻¹ :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, pow_two, IsUnit.unit_spec]; exact ha.symm)
    exact ⟨hau.unit * c, by rw [powMonoidHom_apply, mul_pow, hsq, inv_mul_cancel_right]⟩
  calc Nat.card (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range)
      = Nat.card ((ResidueField A)ˣ ⧸ (powMonoidHom 2 : _ →* (ResidueField A)ˣ).range) :=
        Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)).toEquiv
    _ = 2 := Nat.card_units_quotient_squares h2'

open IsDiscreteValuationRing in
/-- Over a discrete valuation ring, every Selmer class comes from a unit: strip the even
power of a uniformizer off a representative. -/
theorem IsDedekindDomain.selmerGroup.fromUnitLift_surjective {B : Type*} [CommRing B]
    [IsDedekindDomain B] [IsDiscreteValuationRing B] {L : Type*} [Field L]
    [Algebra B L] [IsFractionRing B L] {n : ℕ} [Fact (0 < n)] :
    Function.Surjective (@fromUnitLift B _ _ L _ _ _ n _) := by
  intro x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective x.1
  -- the valuation of `u` at the unique prime of `B` is divisible by `n`
  obtain ⟨k, hk⟩ : (n : ℤ) ∣ Multiplicative.toAdd
      ((IsDiscreteValuationRing.maximalIdeal B).valuationOfNeZero u) := by
    rw [← HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff, hu]
    exact x.2 (IsDiscreteValuationRing.maximalIdeal B) (Set.notMem_empty _)
  -- a uniformizer, as a unit of `L`
  obtain ⟨π, hπ⟩ :=
    (IsDiscreteValuationRing.maximalIdeal B).valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  set πu : Lˣ := Units.mk0 π hπ0 with hπu
  have hπval : (IsDiscreteValuationRing.maximalIdeal B).valuationOfNeZero πu =
      Multiplicative.ofAdd (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq_iff]
    exact hπ
  -- correct `u` by the appropriate power of the uniformizer to get valuation `1`
  set y : Lˣ := u * πu ^ ((n : ℤ) * k) with hy
  have hyval : (IsDiscreteValuationRing.maximalIdeal B).valuationOfNeZero y = 1 := by
    have : Multiplicative.toAdd
        ((IsDiscreteValuationRing.maximalIdeal B).valuationOfNeZero y) = 0 := by
      rw [hy, map_mul, map_zpow, hπval, toAdd_mul, toAdd_zpow, hk]
      simp
    rwa [← toAdd_eq_zero]
  -- so `y` is (the image of) a unit of `B`
  have hymem : (y : L) ∈ MonoidHom.mker
      ((IsDiscreteValuationRing.maximalIdeal B).valuation L) := by
    rw [MonoidHom.mem_mker]
    rw [HeightOneSpectrum.valuationOfNeZero_eq_iff] at hyval
    simpa using hyval
  rw [mker_valuation_eq_isUnitSubmonoid] at hymem
  obtain ⟨b, hb, hby⟩ := hymem
  refine ⟨QuotientGroup.mk hb.unit, ?_⟩
  -- the class of that unit is the given Selmer class
  have h1 : @fromUnitLift B _ _ L _ _ _ n _ (QuotientGroup.mk hb.unit) =
      fromUnit (K := L) (n := n) hb.unit := rfl
  refine Subtype.ext ?_
  rw [h1]
  show QuotientGroup.mk (Units.map (algebraMap B L : B →* L) hb.unit) = x.1
  have hunits : Units.map (algebraMap B L : B →* L) hb.unit = y :=
    Units.ext (by simpa using hby)
  have hone : (QuotientGroup.mk (πu ^ ((n : ℤ) * k)) :
      Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr
      ⟨πu ^ k, by rw [powMonoidHom_apply, ← zpow_natCast, ← zpow_mul, mul_comm (k : ℤ)]⟩
  rw [hunits, ← hu, hy, QuotientGroup.mk_mul, hone]
  exact mul_one (QuotientGroup.mk u : Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range)

end Henselian

/-!
### The integral closure of `𝒪_v` in a finite separable extension of `K_v`

Since `𝒪_v` is Henselian, its integral closure `B` in a finite separable extension `L` of
`K_v` is a Henselian discrete valuation ring with finite residue field. The lemmas below
record this; the section culminates in the count `#L(∅, 2) = 2`.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (L : Type*) [Field L] [Algebra (v.adicCompletionIntegers K) L]

/-- If the residue characteristic of `v` is odd, then `2` is a unit in the integral closure
of `𝒪_v` in `L`. -/
theorem isUnit_two_integralClosure (hv2 : (2 : R) ∉ v.asIdeal) :
    IsUnit (2 : integralClosure (v.adicCompletionIntegers K) L) := by
  have h : IsUnit (2 : v.adicCompletionIntegers K) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    rw [show (2 : v.adicCompletionIntegers K) = algebraMap R (v.adicCompletionIntegers K) 2
        from (map_ofNat _ 2).symm, ← Ideal.mem_comap,
      v.comap_maximalIdeal_adicCompletionIntegers] at hmem
    exact hv2 hmem
  have := h.map (algebraMap (v.adicCompletionIntegers K)
    (integralClosure (v.adicCompletionIntegers K) L))
  rwa [map_ofNat] at this

variable [Algebra (v.adicCompletion K) L]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) L]
  [FiniteDimensional (v.adicCompletion K) L]
  [Algebra.IsSeparable (v.adicCompletion K) L]

/-- The integral closure of `𝒪_v` in a finite separable extension of `K_v` is a finite
`𝒪_v`-module. -/
instance module_finite_integralClosure :
    Module.Finite (v.adicCompletionIntegers K)
      (integralClosure (v.adicCompletionIntegers K) L) :=
  IsIntegralClosure.finite (v.adicCompletionIntegers K) (v.adicCompletion K) L _

/-- The integral closure of `𝒪_v` in a finite separable extension of `K_v` is a local ring:
a finite algebra over the Henselian local ring `𝒪_v` is a product of local rings, and a
domain admits no nontrivial such decomposition. -/
instance isLocalRing_integralClosure :
    IsLocalRing (integralClosure (v.adicCompletionIntegers K) L) := by
  obtain ⟨n, e, he, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
      (R := v.adicCompletionIntegers K) (A := integralClosure (v.adicCompletionIntegers K) L)
  -- in a domain, one of the idempotents is `1`
  obtain ⟨i, hi⟩ : ∃ i, e i = 1 := by
    by_contra! h
    have h0 i : e i = 0 :=
      (IsIdempotentElem.iff_eq_zero_or_one.mp (he.idem i)).resolve_right (h i)
    have := he.complete
    rw [Finset.sum_eq_zero fun i _ ↦ h0 i] at this
    exact zero_ne_one this
  -- so the corresponding corner is the whole ring
  have hbij : Function.Bijective
      (algebraMap (integralClosure (v.adicCompletionIntegers K) L) (he.idem i).Corner) := by
    refine ⟨?_, (he.idem i).toCorner_surjective⟩
    rw [RingHom.injective_iff_ker_eq_bot, (he.idem i).ker_toCorner, hi, sub_self,
      Ideal.span_singleton_eq_bot]
  exact @RingEquiv.isLocalRing _ _ _ (hloc i) _ (RingEquiv.ofBijective _ hbij).symm

/-- The integral closure of `𝒪_v` in a finite separable extension of `K_v` is Henselian. -/
instance henselianLocalRing_integralClosure :
    HenselianLocalRing (integralClosure (v.adicCompletionIntegers K) L) :=
  .of_finite (R := v.adicCompletionIntegers K)

section

variable [Finite (R ⧸ v.asIdeal)]

/-- The integral closure of `𝒪_v` in a finite separable extension of `K_v` has finite
residue field when the residue field of `v` is finite. -/
instance finite_residueField_integralClosure :
    Finite (ResidueField (integralClosure (v.adicCompletionIntegers K) L)) :=
  IsLocalRing.ResidueField.finite_of_finite
    (Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv)

end

variable [IsDedekindDomain (integralClosure (v.adicCompletionIntegers K) L)]

/-- The integral closure of `𝒪_v` in a finite separable extension of `K_v` is a discrete
valuation ring. -/
instance isDiscreteValuationRing_integralClosure :
    IsDiscreteValuationRing (integralClosure (v.adicCompletionIntegers K) L) := by
  -- not a field: the image of a uniformizer of `𝒪_v` is a nonzero nonunit
  have hnf : ¬ IsField (integralClosure (v.adicCompletionIntegers K) L) := by
    intro hf
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    set z := algebraMap (v.adicCompletionIntegers K)
      (integralClosure (v.adicCompletionIntegers K) L) π with hz
    have hinj : Function.Injective (algebraMap (v.adicCompletionIntegers K) L) := by
      rw [IsScalarTower.algebraMap_eq (v.adicCompletionIntegers K) (v.adicCompletion K) L]
      exact (algebraMap (v.adicCompletion K) L).injective.comp
        (FaithfulSMul.algebraMap_injective _ _)
    have hz0 : z ≠ 0 := by
      intro h
      apply hπ.ne_zero
      apply hinj
      rw [map_zero, IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
        (integralClosure (v.adicCompletionIntegers K) L) L, ← hz, h, map_zero]
    have : IsUnit z := by
      obtain ⟨w, hw⟩ := hf.mul_inv_cancel hz0
      exact IsUnit.of_mul_eq_one w hw
    exact hπ.not_isUnit (isUnit_of_map_unit _ π this)
  exact ((IsDiscreteValuationRing.TFAE
    (R := integralClosure (v.adicCompletionIntegers K) L) hnf).out 2 0).mp
    (inferInstance : IsDedekindDomain (integralClosure (v.adicCompletionIntegers K) L))

variable [Finite (R ⧸ v.asIdeal)]
  [IsFractionRing (integralClosure (v.adicCompletionIntegers K) L) L]

/-- For a finite separable extension `L` of the completion `K_v` at a place of odd residue
characteristic, the group of square classes of `L` that have even valuation at every prime
of the integral closure `B` of `𝒪_v` has exactly two elements.

This is the multiplicative analogue of
`exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers`; see the module docstring for
an outline of the proof. -/
theorem card_selmerGroup_integralClosure (hv2 : (2 : R) ∉ v.asIdeal) :
    Nat.card (selmerGroup (R := integralClosure (v.adicCompletionIntegers K) L) (K := L)
      (S := (∅ : Set (HeightOneSpectrum (integralClosure (v.adicCompletionIntegers K) L))))
      (n := 2)) = 2 := by
  have : Fact (0 < 2) := ⟨two_pos⟩
  have hbij : Function.Bijective
      (@_root_.IsDedekindDomain.selmerGroup.fromUnitLift
        (integralClosure (v.adicCompletionIntegers K) L) _ _ L _ _ _ 2 _) :=
    ⟨_root_.IsDedekindDomain.selmerGroup.fromUnitLift_injective,
      _root_.IsDedekindDomain.selmerGroup.fromUnitLift_surjective⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  exact Nat.card_units_quotient_squares_of_henselian (v.isUnit_two_integralClosure L hv2)

end IsDedekindDomain.HeightOneSpectrum
