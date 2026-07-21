module

public import Heights.ForMathlib.WeierstrassFormalGroup.Filtration
import all Heights.ForMathlib.WeierstrassFormalGroup.Filtration
import all Heights.ForMathlib.WeierstrassFormalGroup.Foundations

@[expose] public section

/-!
# The point-level reduction map

For a good integral model `W₀` of `W` over `𝒪_v` (good reduction: `[W₀.IsElliptic]`), the
reduction map `E(K_v) → Ẽ(k_v)` sends a point with integral coordinates to their residues and a
point of the kernel of reduction (a pole at `x`) to the point at infinity.  This file builds the
map, identifies its kernel with the filtration step `E₁(K_v)`, and upgrades it to the reduction
homomorphism `redHom`; it closes with the injectivity of `red` on torsion and the resulting
preservation of the additive order of a torsion point.
-/

open ChabautyColeman IsLocalRing MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)

local notation:max "res" x:max => IsLocalRing.residue (v.adicCompletionIntegers K) x

/-- The reduction `Ẽ` of the good integral model `W₀` modulo the maximal ideal, an elliptic
curve over the residue field `k_v` (good reduction is the hypothesis `[W₀.IsElliptic]`). -/
noncomputable abbrev redCurve (W₀ : WeierstrassCurve (v.adicCompletionIntegers K)) :
    Affine (ResidueField (v.adicCompletionIntegers K)) :=
  (W₀.map (IsLocalRing.residue (v.adicCompletionIntegers K))).toAffine

include hW in
/-- An integral solution of the Weierstrass equation over `K_v` is a solution over `𝒪_v`. -/
lemma equation_integral {x y : v.adicCompletion K} (h : W.Equation x y)
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    (W₀.toAffine).Equation (⟨x, hx⟩ : v.adicCompletionIntegers K) ⟨y, hy⟩ := by
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
    IsFractionRing.injective (v.adicCompletionIntegers K) (v.adicCompletion K)
  rw [← hW] at h
  exact ((W₀.toAffine).map_equation hinj (⟨x, hx⟩ : v.adicCompletionIntegers K) ⟨y, hy⟩).mp h

include hW in
/-- `W.negY` of integral coordinates is the coercion of `W₀.negY`. -/
lemma coe_negY {x y : v.adicCompletion K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    W.negY x y = ((W₀.toAffine).negY (⟨x, hx⟩ : v.adicCompletionIntegers K) ⟨y, hy⟩ :
      v.adicCompletion K) := by
  conv_lhs => rw [← hW]
  exact (W₀.toAffine).map_negY (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    ⟨x, hx⟩ ⟨y, hy⟩

include hW in
/-- `W.negY` of integral coordinates is integral. -/
lemma valued_negY_le {x y : v.adicCompletion K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    Valued.v (W.negY x y) ≤ 1 := by
  rw [coe_negY hW hx hy]; exact valued_coe_le_one _

include hW in
/-- Reduction commutes with `negY` on integral coordinates. -/
lemma redCoord_negY {x y : v.adicCompletion K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hn : Valued.v (W.negY x y) ≤ 1) :
    IsLocalRing.residue _ ⟨W.negY x y, hn⟩
      = (redCurve W₀).negY (IsLocalRing.residue _ ⟨x, hx⟩) (IsLocalRing.residue _ ⟨y, hy⟩) := by
  have hsub : (⟨W.negY x y, hn⟩ : v.adicCompletionIntegers K)
      = (W₀.toAffine).negY ⟨x, hx⟩ ⟨y, hy⟩ := Subtype.ext (coe_negY hW hx hy)
  rw [hsub]
  exact ((W₀.toAffine).map_negY (IsLocalRing.residue (v.adicCompletionIntegers K))
    ⟨x, hx⟩ ⟨y, hy⟩).symm

include hW in
/-- `W.addX` of integral coordinates is the coercion of `W₀.addX`. -/
lemma coe_addX {x₁ x₂ ℓ : v.adicCompletion K} (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hℓ : Valued.v ℓ ≤ 1) :
    W.addX x₁ x₂ ℓ = ((W₀.toAffine).addX (⟨x₁, h₁⟩ : v.adicCompletionIntegers K) ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩ :
      v.adicCompletion K) := by
  conv_lhs => rw [← hW]
  exact (W₀.toAffine).map_addX (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩

include hW in
/-- `W.addY` of integral coordinates is the coercion of `W₀.addY`. -/
lemma coe_addY {x₁ x₂ y₁ ℓ : v.adicCompletion K} (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hy₁ : Valued.v y₁ ≤ 1) (hℓ : Valued.v ℓ ≤ 1) :
    W.addY x₁ x₂ y₁ ℓ = ((W₀.toAffine).addY (⟨x₁, h₁⟩ : v.adicCompletionIntegers K) ⟨x₂, h₂⟩
      ⟨y₁, hy₁⟩ ⟨ℓ, hℓ⟩ : v.adicCompletion K) := by
  conv_lhs => rw [← hW]
  exact (W₀.toAffine).map_addY (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    ⟨x₁, h₁⟩ ⟨y₁, hy₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩

include hW in
/-- Reduction commutes with `addX` on integral coordinates. -/
lemma redCoord_addX {x₁ x₂ ℓ : v.adicCompletion K} (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hℓ : Valued.v ℓ ≤ 1) (hs : Valued.v (W.addX x₁ x₂ ℓ) ≤ 1) :
    IsLocalRing.residue _ ⟨W.addX x₁ x₂ ℓ, hs⟩ = (redCurve W₀).addX
      (IsLocalRing.residue _ ⟨x₁, h₁⟩) (IsLocalRing.residue _ ⟨x₂, h₂⟩)
      (IsLocalRing.residue _ ⟨ℓ, hℓ⟩) := by
  have hsub : (⟨W.addX x₁ x₂ ℓ, hs⟩ : v.adicCompletionIntegers K)
      = (W₀.toAffine).addX ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩ := Subtype.ext (coe_addX hW h₁ h₂ hℓ)
  rw [hsub]
  exact ((W₀.toAffine).map_addX (IsLocalRing.residue (v.adicCompletionIntegers K))
    ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩).symm

include hW in
/-- Reduction commutes with `addY` on integral coordinates. -/
lemma redCoord_addY {x₁ x₂ y₁ ℓ : v.adicCompletion K} (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hy₁ : Valued.v y₁ ≤ 1) (hℓ : Valued.v ℓ ≤ 1) (hs : Valued.v (W.addY x₁ x₂ y₁ ℓ) ≤ 1) :
    IsLocalRing.residue _ ⟨W.addY x₁ x₂ y₁ ℓ, hs⟩ = (redCurve W₀).addY
      (IsLocalRing.residue _ ⟨x₁, h₁⟩) (IsLocalRing.residue _ ⟨x₂, h₂⟩)
      (IsLocalRing.residue _ ⟨y₁, hy₁⟩) (IsLocalRing.residue _ ⟨ℓ, hℓ⟩) := by
  have hsub : (⟨W.addY x₁ x₂ y₁ ℓ, hs⟩ : v.adicCompletionIntegers K)
      = (W₀.toAffine).addY ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨y₁, hy₁⟩ ⟨ℓ, hℓ⟩ :=
    Subtype.ext (coe_addY hW h₁ h₂ hy₁ hℓ)
  rw [hsub]
  exact ((W₀.toAffine).map_addY (IsLocalRing.residue (v.adicCompletionIntegers K))
    ⟨x₁, h₁⟩ ⟨y₁, hy₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩).symm

include hW in
lemma res_a₁ : IsLocalRing.residue _ ⟨W.a₁, valued_a₁ hW⟩ = (redCurve W₀).a₁ := by
  rw [show (⟨W.a₁, valued_a₁ hW⟩ : v.adicCompletionIntegers K) = W₀.a₁ from
    Subtype.ext (coe_a₁ hW).symm]
  exact (W₀.map_a₁ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm

include hW in
lemma res_a₂ : IsLocalRing.residue _ ⟨W.a₂, valued_a₂ hW⟩ = (redCurve W₀).a₂ := by
  rw [show (⟨W.a₂, valued_a₂ hW⟩ : v.adicCompletionIntegers K) = W₀.a₂ from
    Subtype.ext (coe_a₂ hW).symm]
  exact (W₀.map_a₂ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm

include hW in
lemma res_a₃ : IsLocalRing.residue _ ⟨W.a₃, valued_a₃ hW⟩ = (redCurve W₀).a₃ := by
  rw [show (⟨W.a₃, valued_a₃ hW⟩ : v.adicCompletionIntegers K) = W₀.a₃ from
    Subtype.ext (coe_a₃ hW).symm]
  exact (W₀.map_a₃ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm

include hW in
lemma res_a₄ : IsLocalRing.residue _ ⟨W.a₄, valued_a₄ hW⟩ = (redCurve W₀).a₄ := by
  rw [show (⟨W.a₄, valued_a₄ hW⟩ : v.adicCompletionIntegers K) = W₀.a₄ from
    Subtype.ext (coe_a₄ hW).symm]
  exact (W₀.map_a₄ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm


/-- Residue of a difference of integral elements. -/
lemma res_sub {a b : v.adicCompletion K} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1)
    (hab : Valued.v (a - b) ≤ 1) :
    res (⟨a - b, hab⟩ : v.adicCompletionIntegers K) = res ⟨a, ha⟩ - res ⟨b, hb⟩ := by
  rw [show (⟨a - b, hab⟩ : v.adicCompletionIntegers K) = ⟨a, ha⟩ - ⟨b, hb⟩ from
    Subtype.ext (by push_cast; ring), map_sub]

/-- Reduction commutes with division by a residue-unit denominator (field-element form). -/
lemma residue_div' {p q : v.adicCompletion K} (hp : Valued.v p ≤ 1) (hq : Valued.v q ≤ 1)
    (hqu : res (⟨q, hq⟩ : v.adicCompletionIntegers K) ≠ 0) (hpq : Valued.v (p / q) ≤ 1) :
    res (⟨p / q, hpq⟩ : v.adicCompletionIntegers K) = res ⟨p, hp⟩ / res ⟨q, hq⟩ := by
  have hq0 : (q : v.adicCompletion K) ≠ 0 := fun h ↦ hqu <| by
    rw [show (⟨q, hq⟩ : v.adicCompletionIntegers K) = 0 from Subtype.ext (by push_cast; exact h),
      map_zero]
  rw [eq_div_iff hqu, ← map_mul]
  congr 1
  apply Subtype.ext
  push_cast
  field_simp

include hW in
/-- Residue of the finite-difference numerator. -/
lemma res_ficoNum {x₁ x₂ y₁ : v.adicCompletion K} (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hy₁ : Valued.v y₁ ≤ 1)
    (hN : Valued.v (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) ≤ 1) :
    res (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁, hN⟩ :
        v.adicCompletionIntegers K)
      = res ⟨x₁, h₁⟩ ^ 2 + res ⟨x₁, h₁⟩ * res ⟨x₂, h₂⟩ + res ⟨x₂, h₂⟩ ^ 2
        + (redCurve W₀).a₂ * (res ⟨x₁, h₁⟩ + res ⟨x₂, h₂⟩) + (redCurve W₀).a₄
        - (redCurve W₀).a₁ * res ⟨y₁, hy₁⟩ := by
  rw [← res_a₁ hW, ← res_a₂ hW, ← res_a₄ hW,
    show (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁, hN⟩ :
        v.adicCompletionIntegers K)
      = ⟨x₁, h₁⟩ ^ 2 + ⟨x₁, h₁⟩ * ⟨x₂, h₂⟩ + ⟨x₂, h₂⟩ ^ 2
        + ⟨W.a₂, valued_a₂ hW⟩ * (⟨x₁, h₁⟩ + ⟨x₂, h₂⟩) + ⟨W.a₄, valued_a₄ hW⟩
        - ⟨W.a₁, valued_a₁ hW⟩ * ⟨y₁, hy₁⟩ from Subtype.ext (by push_cast; ring)]
  simp only [map_add, map_sub, map_mul, map_pow]

/-- Valuation of a difference of integral elements is `≤ 1`. -/
private lemma valued_sub_le {a b : v.adicCompletion K} (ha : Valued.v a ≤ 1)
    (hb : Valued.v b ≤ 1) : Valued.v (a - b) ≤ 1 :=
  (Valued.v.map_sub _ _).trans (max_le ha hb)

include hW in
/-- The finite-difference numerator of integral coordinates is integral. -/
lemma valued_ficoNum_le {x₁ x₂ y₁ : v.adicCompletion K} (h₁ : Valued.v x₁ ≤ 1)
    (h₂ : Valued.v x₂ ≤ 1) (hy₁ : Valued.v y₁ ≤ 1) :
    Valued.v (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) ≤ 1 := by
  rw [show x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁
      = ((⟨x₁, h₁⟩ ^ 2 + ⟨x₁, h₁⟩ * ⟨x₂, h₂⟩ + ⟨x₂, h₂⟩ ^ 2
          + ⟨W.a₂, valued_a₂ hW⟩ * (⟨x₁, h₁⟩ + ⟨x₂, h₂⟩) + ⟨W.a₄, valued_a₄ hW⟩
          - ⟨W.a₁, valued_a₁ hW⟩ * ⟨y₁, hy₁⟩ : v.adicCompletionIntegers K) :
        v.adicCompletion K) from by push_cast; ring]
  exact valued_coe_le_one _

/-- At a nonsingular point of a Weierstrass curve, one of the two partial derivatives of the
Weierstrass polynomial is nonzero. -/
lemma nonsingular_deriv_disj {F : Type*} [Field F] {E' : Affine F} {a b : F}
    (h : E'.Nonsingular a b) :
    E'.a₁ * b - (3 * a ^ 2 + 2 * E'.a₂ * a + E'.a₄) ≠ 0 ∨ b - E'.negY a b ≠ 0 := by
  rcases ((E'.nonsingular_iff' a b).mp h).2 with h1 | h2
  · exact Or.inl h1
  · refine Or.inr fun hc ↦ h2 ?_
    rw [Affine.negY] at hc
    linear_combination hc


/-- `v x = 1` for an `x ≤ 1` whose reduction is a unit (avoids the subtype-coe unification). -/
lemma valued_eq_one_of_residue_ne {a : v.adicCompletion K} (ha : Valued.v a ≤ 1)
    (h : res (⟨a, ha⟩ : v.adicCompletionIntegers K) ≠ 0) : Valued.v a = 1 :=
  valued_coe_isUnit (a := (⟨a, ha⟩ : v.adicCompletionIntegers K))
    ((residue_ne_zero_iff_isUnit (⟨a, ha⟩ : v.adicCompletionIntegers K)).mp h)

/-- An integral element with nonzero reduction is nonzero. -/
lemma ne_zero_of_residue_ne {a : v.adicCompletion K} (ha : Valued.v a ≤ 1)
    (h : res (⟨a, ha⟩ : v.adicCompletionIntegers K) ≠ 0) : a ≠ 0 := by
  rintro rfl; exact h (map_zero _)

section

variable [DecidableEq (v.adicCompletion K)]

/-- On the curve, the chord/tangent slope is the finite-difference quotient
`N / (y₁ - negY x₂ y₂)`; valid in the honest-tangent case too, where `y₁ = y₂`. -/
lemma slope_eq_div {x₁ x₂ y₁ y₂ : v.adicCompletion K} (hc₁ : W.Equation x₁ y₁)
    (hc₂ : W.Equation x₂ y₂) (hD0 : y₁ - W.negY x₂ y₂ ≠ 0) :
    W.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
        / (y₁ - W.negY x₂ y₂) := by
  by_cases hxx : x₁ = x₂
  · have hyne : y₁ ≠ W.negY x₂ y₂ := sub_ne_zero.mp hD0
    rw [W.slope_of_Y_ne hxx hyne, ← hxx,
      ← (W.Y_eq_of_X_eq hc₁ hc₂ hxx).resolve_right hyne]
    ring
  · rw [W.slope_of_X_ne hxx, div_eq_div_iff (sub_ne_zero.mpr hxx) hD0, Affine.negY]
    linear_combination (W.equation_iff x₁ y₁).mp hc₁ - (W.equation_iff x₂ y₂).mp hc₂

variable [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))]

include hW in
/-- **Reduction commutes with the chord/tangent slope**, off the reduced anti-diagonal.
Mathlib's `map_slope` cannot apply (the residue map is not an injective field hom), so the
secant/tangent branch is chosen by the *reduced* points: the finite-difference identity turns a
`K_v`-secant that reduces to a tangent into a genuine tangent downstairs. -/
lemma red_slope {x₁ x₂ y₁ y₂ : v.adicCompletion K} (hx₁ : Valued.v x₁ ≤ 1)
    (hx₂ : Valued.v x₂ ≤ 1) (hy₁ : Valued.v y₁ ≤ 1) (hy₂ : Valued.v y₂ ≤ 1)
    (hc₁ : W.Equation x₁ y₁) (hc₂ : W.Equation x₂ y₂) (hℓ : Valued.v (W.slope x₁ x₂ y₁ y₂) ≤ 1)
    (hne : ¬ (res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩ ∧
      res ⟨y₁, hy₁⟩ = (redCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩))) :
    res (⟨W.slope x₁ x₂ y₁ y₂, hℓ⟩ : v.adicCompletionIntegers K) = (redCurve W₀).slope
      (res ⟨x₁, hx₁⟩) (res ⟨x₂, hx₂⟩) (res ⟨y₁, hy₁⟩) (res ⟨y₂, hy₂⟩) := by
  by_cases hXeq : res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩
  · -- tangent: `x₁, x₂` reduce equal; the reduced slope is the tangent form
    have hYne : res (⟨y₁, hy₁⟩ : v.adicCompletionIntegers K)
        ≠ (redCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩) := fun h ↦ hne ⟨hXeq, h⟩
    have hnegYint : Valued.v (W.negY x₂ y₂) ≤ 1 := valued_negY_le hW hx₂ hy₂
    have hDint : Valued.v (y₁ - W.negY x₂ y₂) ≤ 1 := valued_sub_le hy₁ hnegYint
    have hDu : res (⟨y₁ - W.negY x₂ y₂, hDint⟩ : v.adicCompletionIntegers K) ≠ 0 := by
      rw [res_sub hy₁ hnegYint hDint, redCoord_negY hW hx₂ hy₂ hnegYint]
      exact sub_ne_zero.mpr hYne
    have hD0 : y₁ - W.negY x₂ y₂ ≠ 0 := ne_zero_of_residue_ne hDint hDu
    have hNint : Valued.v
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) ≤ 1 :=
      valued_ficoNum_le hW hx₁ hx₂ hy₁
    have hYeq : res (⟨y₁, hy₁⟩ : v.adicCompletionIntegers K) = res ⟨y₂, hy₂⟩ :=
      ((redCurve W₀).Y_eq_of_X_eq (Equation.map _ (equation_integral hW hc₁ hx₁ hy₁))
        (Equation.map _ (equation_integral hW hc₂ hx₂ hy₂)) hXeq).resolve_right hYne
    rw [show (⟨W.slope x₁ x₂ y₁ y₂, hℓ⟩ : v.adicCompletionIntegers K)
        = ⟨_, W.slope_eq_div hc₁ hc₂ hD0 ▸ hℓ⟩ from Subtype.ext (W.slope_eq_div hc₁ hc₂ hD0),
      residue_div' hNint hDint hDu, res_ficoNum hW hx₁ hx₂ hy₁,
      res_sub hy₁ hnegYint hDint, redCoord_negY hW hx₂ hy₂ hnegYint,
      (redCurve W₀).slope_of_Y_ne hXeq hYne, ← hXeq, ← hYeq]
    ring
  · -- secant: `x₁, x₂` reduce distinct, so `x₁ - x₂` is a unit
    have hxx : x₁ ≠ x₂ := fun h ↦ hXeq (congrArg (IsLocalRing.residue _) (Subtype.ext h))
    have hden : Valued.v (x₁ - x₂) ≤ 1 := valued_sub_le hx₁ hx₂
    have hnum : Valued.v (y₁ - y₂) ≤ 1 := valued_sub_le hy₁ hy₂
    have hdenu : res (⟨x₁ - x₂, hden⟩ : v.adicCompletionIntegers K) ≠ 0 := by
      rw [res_sub hx₁ hx₂ hden]; exact sub_ne_zero.mpr hXeq
    rw [show (⟨W.slope x₁ x₂ y₁ y₂, hℓ⟩ : v.adicCompletionIntegers K)
        = ⟨(y₁ - y₂) / (x₁ - x₂), W.slope_of_X_ne hxx ▸ hℓ⟩ from
        Subtype.ext (W.slope_of_X_ne hxx),
      residue_div' hnum hden hdenu, res_sub hx₁ hx₂ hden, res_sub hy₁ hy₂ hnum,
      (redCurve W₀).slope_of_X_ne hXeq]

include hW in
/-- Off the reduced anti-diagonal, the chord/tangent slope of two integral points is integral. -/
lemma valued_slope_le {x₁ x₂ y₁ y₂ : v.adicCompletion K} (hx₁ : Valued.v x₁ ≤ 1)
    (hx₂ : Valued.v x₂ ≤ 1) (hy₁ : Valued.v y₁ ≤ 1) (hy₂ : Valued.v y₂ ≤ 1)
    (hc₁ : W.Equation x₁ y₁) (hc₂ : W.Equation x₂ y₂)
    (hne : ¬ (res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩ ∧
      res ⟨y₁, hy₁⟩ = (redCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩))) :
    Valued.v (W.slope x₁ x₂ y₁ y₂) ≤ 1 := by
  by_cases hXeq : res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩
  · have hYne : res (⟨y₁, hy₁⟩ : v.adicCompletionIntegers K)
        ≠ (redCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩) := fun h ↦ hne ⟨hXeq, h⟩
    have hnegYint : Valued.v (W.negY x₂ y₂) ≤ 1 := valued_negY_le hW hx₂ hy₂
    have hDint : Valued.v (y₁ - W.negY x₂ y₂) ≤ 1 := valued_sub_le hy₁ hnegYint
    have hDu : res (⟨y₁ - W.negY x₂ y₂, hDint⟩ : v.adicCompletionIntegers K) ≠ 0 := by
      rw [res_sub hy₁ hnegYint hDint, redCoord_negY hW hx₂ hy₂ hnegYint]
      exact sub_ne_zero.mpr hYne
    have hD0 : y₁ - W.negY x₂ y₂ ≠ 0 := ne_zero_of_residue_ne hDint hDu
    have hNint : Valued.v
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) ≤ 1 :=
      valued_ficoNum_le hW hx₁ hx₂ hy₁
    rw [slope_eq_div hc₁ hc₂ hD0, map_div₀,
      valued_coe_isUnit ((residue_ne_zero_iff_isUnit _).mp hDu), div_one]
    exact hNint
  · have hxx : x₁ ≠ x₂ := fun h ↦ hXeq (congrArg (IsLocalRing.residue _) (Subtype.ext h))
    have hden : Valued.v (x₁ - x₂) ≤ 1 := valued_sub_le hx₁ hx₂
    have hdenu : res (⟨x₁ - x₂, hden⟩ : v.adicCompletionIntegers K) ≠ 0 := by
      rw [res_sub hx₁ hx₂ hden]; exact sub_ne_zero.mpr hXeq
    rw [W.slope_of_X_ne hxx, map_div₀,
      valued_coe_isUnit ((residue_ne_zero_iff_isUnit _).mp hdenu), div_one]
    exact valued_sub_le hy₁ hy₂

end

variable [W₀.IsElliptic]

include hW in
/-- The reduced coordinates of an integral point are nonsingular on the smooth curve `Ẽ`. -/
lemma red_nonsingular {x y : v.adicCompletion K} (h : W.Equation x y)
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    (redCurve W₀).Nonsingular (IsLocalRing.residue _ ⟨x, hx⟩)
      (IsLocalRing.residue _ ⟨y, hy⟩) := by
  rw [← equation_iff_nonsingular]
  exact Equation.map (IsLocalRing.residue (v.adicCompletionIntegers K))
    (equation_integral hW h hx hy)

include hW in
/-- The point-level reduction map. `0 ↦ 0`; an affine point with a pole of order `≥ 2` at `x`
(the kernel of reduction) ↦ `0`; otherwise the coordinatewise reduction. -/
noncomputable def red : W.Point → (redCurve W₀).Point
  | .zero => 0
  | .some x y h =>
      if hx : exp (2 : ℤ) ≤ Valued.v x then 0
      else
        .some (IsLocalRing.residue _ ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
              (IsLocalRing.residue _ ⟨y, (integral_of_not_mem hW h.left hx).2⟩)
              (red_nonsingular hW h.left (integral_of_not_mem hW h.left hx).1
                (integral_of_not_mem hW h.left hx).2)

@[simp] lemma red_zero : red hW (0 : W.Point) = 0 := rfl

include hW in
/-- Unfolding lemma for `red` on a kernel point. -/
lemma red_some_of_mem {x y : v.adicCompletion K} {h : W.Nonsingular x y}
    (hx : exp (2 : ℤ) ≤ Valued.v x) : red hW (.some x y h) = 0 :=
  dif_pos hx

include hW in
/-- Unfolding lemma for `red` on an integral (non-kernel) point. -/
lemma red_some_of_not_mem {x y : v.adicCompletion K} {h : W.Nonsingular x y}
    (hx : ¬ exp (2 : ℤ) ≤ Valued.v x) :
    red hW (.some x y h)
      = .some (IsLocalRing.residue _ ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
          (IsLocalRing.residue _ ⟨y, (integral_of_not_mem hW h.left hx).2⟩)
          (red_nonsingular hW h.left (integral_of_not_mem hW h.left hx).1
            (integral_of_not_mem hW h.left hx).2) :=
  dif_neg hx

include hW in
/-- `red` commutes with negation. -/
lemma red_neg (P : W.Point) : red hW (-P) = - red hW P := by
  match P with
  | .zero => rfl
  | .some x y h =>
      by_cases hx : exp (2 : ℤ) ≤ Valued.v x
      · rw [Point.neg_some, red_some_of_mem hW hx, red_some_of_mem hW hx]; simp
      · rw [Point.neg_some, red_some_of_not_mem hW hx, red_some_of_not_mem hW hx,
          Point.neg_some, Point.some.injEq]
        exact ⟨rfl, redCoord_negY hW _ _ _⟩

variable [W.IsElliptic] [DecidableEq (v.adicCompletion K)] [CharZero K]

include hW in
/-- The kernel of `red` is exactly the kernel of reduction `E₁(K_v) = filtration hW 0`. -/
lemma red_eq_zero_iff {P : W.Point} : red hW P = 0 ↔ P ∈ filtration hW 0 := by
  match P with
  | .zero => exact iff_of_true rfl zero_mem_filtration
  | .some x y h =>
      rw [some_mem_filtration]
      by_cases hx : exp (2 : ℤ) ≤ Valued.v x
      · exact iff_of_true (red_some_of_mem hW hx) (le_trans (exp_le_exp.mpr (by lia)) hx)
      · refine iff_of_false ?_ (fun hc ↦ hx (le_trans (exp_le_exp.mpr (by lia)) hc))
        rw [red_some_of_not_mem hW hx]; exact Point.some_ne_zero _

variable [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))]

include hW in
/-- **Additivity of `red` on the good, reduced-non-opposite locus.** Two integral points whose
reductions are not opposite have an integral sum, and `red` respects that sum. -/
lemma red_add_of_reduced_ne_neg {x₁ x₂ y₁ y₂ : v.adicCompletion K}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hP : ¬ exp (2 : ℤ) ≤ Valued.v x₁) (hQ : ¬ exp (2 : ℤ) ≤ Valued.v x₂)
    (hne : red hW (.some x₁ y₁ h₁) ≠ - red hW (.some x₂ y₂ h₂)) :
    ((.some x₁ y₁ h₁ : W.Point) + .some x₂ y₂ h₂ ∉ filtration hW 0) ∧
      red hW (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
        = red hW (.some x₁ y₁ h₁) + red hW (.some x₂ y₂ h₂) := by
  obtain ⟨hx₁, hy₁⟩ := integral_of_not_mem hW h₁.left hP
  obtain ⟨hx₂, hy₂⟩ := integral_of_not_mem hW h₂.left hQ
  have hne_res : ¬ (res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩ ∧
      res ⟨y₁, hy₁⟩ = (redCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩)) := fun ⟨e1, e2⟩ ↦
    hne (by rw [red_some_of_not_mem hW hP, red_some_of_not_mem hW hQ, Point.neg_some,
      Point.some.injEq]; exact ⟨e1, e2⟩)
  have hnegYint : Valued.v (W.negY x₂ y₂) ≤ 1 := valued_negY_le hW hx₂ hy₂
  have hxy : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨ex, ey⟩
    refine hne_res ⟨congrArg (IsLocalRing.residue _) (Subtype.ext ex), ?_⟩
    rw [show (⟨y₁, hy₁⟩ : v.adicCompletionIntegers K) = ⟨W.negY x₂ y₂, hnegYint⟩ from
      Subtype.ext ey, redCoord_negY hW hx₂ hy₂ hnegYint]
  have hℓ : Valued.v (W.slope x₁ x₂ y₁ y₂) ≤ 1 :=
    valued_slope_le hW hx₁ hx₂ hy₁ hy₂ h₁.left h₂.left hne_res
  have haXint : Valued.v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) ≤ 1 := by
    rw [coe_addX hW hx₁ hx₂ hℓ]; exact valued_coe_le_one _
  have haYint : Valued.v (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) ≤ 1 := by
    rw [coe_addY hW hx₁ hx₂ hy₁ hℓ]; exact valued_coe_le_one _
  have hgate : ¬ exp (2 : ℤ) ≤ Valued.v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) := fun hc ↦
    absurd (le_trans hc haXint) (by rw [not_le, ← exp_zero]; exact exp_lt_exp.mpr (by lia))
  have hsum : (.some x₁ y₁ h₁ : W.Point) + .some x₂ y₂ h₂
      = .some (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂))
        (nonsingular_add h₁ h₂ hxy) := Point.add_some hxy
  have hslope := red_slope hW hx₁ hx₂ hy₁ hy₂ h₁.left h₂.left hℓ hne_res
  refine ⟨by rw [hsum, some_mem_filtration]; exact hgate, ?_⟩
  rw [hsum, red_some_of_not_mem hW hgate, red_some_of_not_mem hW hP, red_some_of_not_mem hW hQ,
    Point.add_some hne_res, Point.some.injEq]
  exact ⟨(redCoord_addX hW hx₁ hx₂ hℓ haXint).trans (by rw [hslope]),
    (redCoord_addY hW hx₁ hx₂ hy₁ hℓ haYint).trans (by rw [hslope])⟩

omit [W.IsElliptic] [DecidableEq (v.adicCompletion K)] [CharZero K]
  [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] in
include hW in
/-- At an integral nonsingular point, one of the two partial derivatives of the Weierstrass
polynomial reduces to a unit (has valuation `1`). -/
lemma unit_deriv {x₀ y₀ : v.adicCompletion K} (h₀ : W.Nonsingular x₀ y₀)
    (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1) :
    Valued.v (y₀ - W.negY x₀ y₀) = 1 ∨
      Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 1 := by
  have hnegYint : Valued.v (W.negY x₀ y₀) ≤ 1 := valued_negY_le hW hx₀ hy₀
  have hψint : Valued.v (y₀ - W.negY x₀ y₀) ≤ 1 := valued_sub_le hy₀ hnegYint
  have hφint : Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) ≤ 1 := by
    rw [show W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
        = ((⟨W.a₁, valued_a₁ hW⟩ * ⟨y₀, hy₀⟩ - (⟨x₀, hx₀⟩ ^ 2 + ⟨x₀, hx₀⟩ ^ 2 + ⟨x₀, hx₀⟩ ^ 2
            + (⟨W.a₂, valued_a₂ hW⟩ * ⟨x₀, hx₀⟩ + ⟨W.a₂, valued_a₂ hW⟩ * ⟨x₀, hx₀⟩)
            + ⟨W.a₄, valued_a₄ hW⟩) : v.adicCompletionIntegers K) : v.adicCompletion K)
        from by push_cast; ring]
    exact valued_coe_le_one _
  have hresψ : res (⟨y₀ - W.negY x₀ y₀, hψint⟩ : v.adicCompletionIntegers K)
      = res ⟨y₀, hy₀⟩ - (redCurve W₀).negY (res ⟨x₀, hx₀⟩) (res ⟨y₀, hy₀⟩) := by
    rw [res_sub hy₀ hnegYint hψint, redCoord_negY hW hx₀ hy₀ hnegYint]
  have hresφ : res (⟨W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄), hφint⟩ :
        v.adicCompletionIntegers K)
      = (redCurve W₀).a₁ * res ⟨y₀, hy₀⟩
        - (3 * res ⟨x₀, hx₀⟩ ^ 2 + 2 * (redCurve W₀).a₂ * res ⟨x₀, hx₀⟩ + (redCurve W₀).a₄) := by
    rw [← res_a₁ hW, ← res_a₂ hW, ← res_a₄ hW,
      show (⟨W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄), hφint⟩ : v.adicCompletionIntegers K)
        = ⟨W.a₁, valued_a₁ hW⟩ * ⟨y₀, hy₀⟩ - (⟨x₀, hx₀⟩ ^ 2 + ⟨x₀, hx₀⟩ ^ 2 + ⟨x₀, hx₀⟩ ^ 2
            + (⟨W.a₂, valued_a₂ hW⟩ * ⟨x₀, hx₀⟩ + ⟨W.a₂, valued_a₂ hW⟩ * ⟨x₀, hx₀⟩)
            + ⟨W.a₄, valued_a₄ hW⟩) from Subtype.ext (by push_cast; ring)]
    simp only [map_sub, map_add, map_mul, map_pow]
    ring
  rcases nonsingular_deriv_disj (red_nonsingular hW h₀.left hx₀ hy₀) with hφ | hψ
  · exact Or.inr (valued_eq_one_of_residue_ne hφint (fun h ↦ hφ (hresφ.symm.trans h)))
  · exact Or.inl (valued_eq_one_of_residue_ne hψint (fun h ↦ hψ (hresψ.symm.trans h)))

omit [W₀.IsElliptic] [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] in
include hW in
/-- If the tangent slope at an integral point whose reduction is `2`-torsion is large
(`≥ exp 1`), the point's double lies in the kernel of reduction. -/
lemma add_self_mem_filtration_of_slope {x₀ y₀ : v.adicCompletion K} (h₀ : W.Nonsingular x₀ y₀)
    (hx₀ : Valued.v x₀ ≤ 1) (hψ : y₀ ≠ W.negY x₀ y₀)
    (hs : exp (1 : ℤ) ≤ Valued.v (W.slope x₀ x₀ y₀ y₀)) :
    (.some x₀ y₀ h₀ : W.Point) + .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := valued_a₁ hW
  have ha₂ : Valued.v W.a₂ ≤ 1 := valued_a₂ hW
  rw [Point.add_some (fun hc ↦ hψ hc.2), some_mem_filtration, Affine.addX]
  set L : v.adicCompletion K := W.slope x₀ x₀ y₀ y₀ with hL
  have hL1 : (1 : ℤᵐ⁰) < Valued.v L := lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; lia) hs
  have hbig : ∀ c : ℤᵐ⁰, c ≤ 1 → c < Valued.v L ^ 2 := fun c hc ↦
    lt_of_le_of_lt hc (by
      calc (1 : ℤᵐ⁰) < Valued.v L := hL1
        _ = Valued.v L ^ 1 := (pow_one _).symm
        _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL1 (by lia))
  have hrest : Valued.v (W.a₁ * L - W.a₂ - x₀ - x₀) < Valued.v L ^ 2 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt
      (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _)
        (max_lt ?_ (hbig _ ha₂))) (hbig _ hx₀))) (hbig _ hx₀))
    rw [map_mul]
    calc Valued.v W.a₁ * Valued.v L ≤ 1 * Valued.v L := mul_le_mul' ha₁ le_rfl
      _ = Valued.v L ^ 1 := by rw [one_mul, pow_one]
      _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL1 (by lia)
  rw [show L ^ 2 + W.a₁ * L - W.a₂ - x₀ - x₀ = L ^ 2 + (W.a₁ * L - W.a₂ - x₀ - x₀) by ring,
    Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hrest), map_pow]
  refine le_trans (le_of_eq ?_) (pow_le_pow_left' hs 2)
  rw [← exp_nsmul, nsmul_eq_mul]
  norm_num

omit [W₀.IsElliptic] [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] in
include hW in
/-- Two integral points with equal coordinates differ by `0`, hence lie in every filtration
step. -/
lemma sub_mem_filtration_of_eq {x y x₀ y₀ : v.adicCompletion K} (h : W.Nonsingular x y)
    (h₀ : W.Nonsingular x₀ y₀) (hx : x = x₀) (hy : y = y₀) :
    (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  rw [show (.some x y h : W.Point) = .some x₀ y₀ h₀ by subst hx hy; rfl, sub_self]
  exact zero_mem _

omit [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] in
include hW in
/-- Two integral points whose coordinates are congruent modulo `𝔪` (differ by elements of
valuation `≤ exp (-1)`) differ by a kernel-of-reduction element. -/
lemma exists_level_one_sub_mem {x₀ y₀ : v.adicCompletion K} (h₀ : W.Nonsingular x₀ y₀)
    (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1) {x y : v.adicCompletion K}
    (h : W.Nonsingular x y) (hx : Valued.v (x - x₀) ≤ exp (-1 : ℤ))
    (hy : Valued.v (y - y₀) ≤ exp (-1 : ℤ)) :
    (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have hxI : Valued.v x ≤ 1 := valued_le_one_of_sub hx hx₀
  rcases eq_or_ne x x₀ with heq | hxx
  · -- `x = x₀`: the coordinates agree, so compare the `y`-coordinates
    subst x
    rcases W.Y_eq_of_X_eq h.left h₀.left rfl with hy' | hy'
    · exact sub_mem_filtration_of_eq hW h h₀ rfl hy'
    · have hψsmall : Valued.v (y₀ - W.negY x₀ y₀) ≤ exp (-1 : ℤ) := by
        rw [show y₀ - W.negY x₀ y₀ = -(y - y₀) by rw [hy']; ring, Valuation.map_neg]; exact hy
      rcases eq_or_ne (y₀ - W.negY x₀ y₀) 0 with hψ0 | hψ0
      · refine sub_mem_filtration_of_eq hW h h₀ rfl ?_
        rw [hy', ← sub_eq_zero, show W.negY x₀ y₀ - y₀ = -(y₀ - W.negY x₀ y₀) by ring,
          hψ0, neg_zero]
      · -- `Q` reduces to a `2`-torsion point (`φ` a unit) without being `2`-torsion, and
        -- `P = -Q`, so `P - Q = -(Q + Q)` lies in the kernel of reduction
        have hφ1 : Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 1 := by
          rcases unit_deriv hW h₀ hx₀ hy₀ with hψ1 | hφ1
          · exact absurd hψsmall (by rw [hψ1, ← exp_zero, exp_le_exp]; lia)
          · exact hφ1
        have hψne : y₀ ≠ W.negY x₀ y₀ := fun hc ↦ hψ0 (sub_eq_zero.mpr hc)
        have hP : (.some x₀ y h : W.Point) = -.some x₀ y₀ h₀ := by
          rw [Point.neg_some]; subst hy'; rfl
        rw [hP, show -(.some x₀ y₀ h₀ : W.Point) - .some x₀ y₀ h₀
            = -(.some x₀ y₀ h₀ + .some x₀ y₀ h₀) by abel]
        refine neg_mem (add_self_mem_filtration_of_slope hW h₀ hx₀ hψne ?_)
        rw [W.slope_of_Y_ne rfl hψne, map_div₀]
        obtain ⟨dψ, hdψ⟩ : ∃ dψ : ℤ, Valued.v (y₀ - W.negY x₀ y₀) = exp dψ :=
          ⟨_, (exp_log (by simpa using hψ0)).symm⟩
        have hnumφ : Valued.v (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) = 1 := by
          rw [show 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀
              = -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) by ring,
            Valuation.map_neg, hφ1]
        rw [hnumφ, hdψ, ← exp_zero, ← exp_sub, exp_le_exp]
        have hdψ' : dψ ≤ -1 := by rwa [hdψ, exp_le_exp] at hψsmall
        lia
  · -- `x ≠ x₀`: the secant slope through the two points is large
    refine sub_mem_filtration_of_slope h₀ h hxx hx₀ hxI ?_
    rcases unit_deriv hW h₀ hx₀ hy₀ with hψ1 | hφ1
    · -- `ψ` a unit: the numerator `y - negY x₀ y₀` is a unit
      have hnum : Valued.v (y - W.negY x₀ y₀) = 1 := by
        rw [show y - W.negY x₀ y₀ = (y₀ - W.negY x₀ y₀) + (y - y₀) by ring,
          Valuation.map_add_eq_of_lt_left, hψ1]
        refine lt_of_le_of_lt hy ?_
        rw [hψ1, ← exp_zero, exp_lt_exp]; lia
      obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
        ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
      rw [map_div₀, hnum, hdx, ← exp_zero, ← exp_sub, exp_le_exp]
      have hdx' : dx ≤ -1 := by rwa [hdx, exp_le_exp] at hx
      lia
    · -- `φ` a unit: use the finite-difference identity for the numerator
      have hid : (y - W.negY x₀ y₀) * (y - y₀) = (x - x₀) *
          (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) := by
        rw [Affine.negY]
        linear_combination (W.equation_iff x y).mp h.left - (W.equation_iff x₀ y₀).mp h₀.left
      have hval := congrArg Valued.v hid
      rw [map_mul, map_mul, valued_num_of_two_torsion hW hx₀ (hφ1.trans exp_zero.symm)
        (by norm_num) hx hy] at hval
      exact exp_one_le_valued_slope hxx (by norm_num) hy hval

omit [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] in
include hW in
/-- **Congruence criterion**: equal reductions of two points differ by a kernel-of-reduction
element. -/
lemma sub_mem_filtration_of_red_eq {P Q : W.Point} (hPQ : red hW P = red hW Q) :
    P - Q ∈ filtration hW 0 := by
  by_cases hQ0 : Q ∈ filtration hW 0
  · exact AddSubgroup.sub_mem _
      ((red_eq_zero_iff hW).mp (hPQ.trans ((red_eq_zero_iff hW).mpr hQ0))) hQ0
  · have hP0 : P ∉ filtration hW 0 := fun h ↦ hQ0
      ((red_eq_zero_iff hW).mp (hPQ.symm.trans ((red_eq_zero_iff hW).mpr h)))
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd zero_mem_filtration hP0
    rcases Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd zero_mem_filtration hQ0
    have hPm : ¬ exp (2 : ℤ) ≤ Valued.v x := fun hc ↦ hP0 (some_mem_filtration.mpr hc)
    have hQm : ¬ exp (2 : ℤ) ≤ Valued.v x₀ := fun hc ↦ hQ0 (some_mem_filtration.mpr hc)
    obtain ⟨hxi, hyi⟩ := integral_of_not_mem hW hxy.left hPm
    obtain ⟨hxi₀, hyi₀⟩ := integral_of_not_mem hW h₀.left hQm
    rw [red_some_of_not_mem hW hPm, red_some_of_not_mem hW hQm, Point.some.injEq] at hPQ
    refine exists_level_one_sub_mem hW h₀ hxi₀ hyi₀ hxy ?_ ?_
    · refine mem_maximalIdeal_iff (x := ⟨x - x₀, valued_sub_le hxi hxi₀⟩) |>.mp
        (residue_eq_zero_iff _ |>.mp ?_)
      rw [res_sub hxi hxi₀ (valued_sub_le hxi hxi₀), hPQ.1, sub_self]
    · refine mem_maximalIdeal_iff (x := ⟨y - y₀, valued_sub_le hyi hyi₀⟩) |>.mp
        (residue_eq_zero_iff _ |>.mp ?_)
      rw [res_sub hyi hyi₀ (valued_sub_le hyi hyi₀), hPQ.2, sub_self]

include hW in
/-- **Additivity of `red` off the kernel of reduction.** Two points not in `E₁(K_v)`
have `red (P + Q) = red P + red Q`. -/
lemma red_add_of_not_mem {P Q : W.Point} (hP : P ∉ filtration hW 0)
    (hQ : Q ∉ filtration hW 0) : red hW (P + Q) = red hW P + red hW Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd zero_mem_filtration hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd zero_mem_filtration hQ
  have hPm : ¬ exp (2 : ℤ) ≤ Valued.v x₁ := fun hc ↦ hP (some_mem_filtration.mpr hc)
  have hQm : ¬ exp (2 : ℤ) ≤ Valued.v x₂ := fun hc ↦ hQ (some_mem_filtration.mpr hc)
  by_cases hop : red hW (.some x₁ y₁ h₁) = - red hW (.some x₂ y₂ h₂)
  · rw [hop, neg_add_cancel, red_eq_zero_iff hW, ← sub_neg_eq_add]
    exact sub_mem_filtration_of_red_eq hW (hop.trans (red_neg hW _).symm)
  · exact (red_add_of_reduced_ne_neg hW h₁ h₂ hPm hQm hop).2

include hW in
/-- Adding a kernel-of-reduction point does not change the reduction. -/
lemma red_add_of_mem_left {P : W.Point} (hP : P ∈ filtration hW 0) (Q : W.Point) :
    red hW (P + Q) = red hW Q := by
  by_cases hQ : Q ∈ filtration hW 0
  · rw [(red_eq_zero_iff hW).mpr (add_mem hP hQ), (red_eq_zero_iff hW).mpr hQ]
  · have hPQ : P + Q ∉ filtration hW 0 := fun h ↦ hQ (by simpa using AddSubgroup.sub_mem _ h hP)
    have hnQ : -Q ∉ filtration hW 0 := fun h ↦ hQ (by simpa using neg_mem h)
    have key := red_add_of_not_mem hW hPQ hnQ
    rwa [show P + Q + -Q = P from by abel, red_neg, (red_eq_zero_iff hW).mpr hP, eq_comm,
      add_neg_eq_zero] at key

include hW in
/-- **The reduction map is additive.** -/
lemma red_add (P Q : W.Point) : red hW (P + Q) = red hW P + red hW Q := by
  by_cases hP : P ∈ filtration hW 0
  · rw [red_add_of_mem_left hW hP, (red_eq_zero_iff hW).mpr hP, zero_add]
  · by_cases hQ : Q ∈ filtration hW 0
    · rw [add_comm P Q, red_add_of_mem_left hW hQ, (red_eq_zero_iff hW).mpr hQ, add_zero]
    · exact red_add_of_not_mem hW hP hQ

include hW in
/-- **The reduction homomorphism** `E(K_v) →+ Ẽ(k_v)`. -/
noncomputable def redHom : W.Point →+ (redCurve W₀).Point :=
  AddMonoidHom.mk' (red hW) (red_add hW)

@[simp] lemma coe_redHom : ⇑(redHom hW) = red hW := rfl

omit [DecidableEq (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] in
include hW in
/-- `red` is injective on torsion: a torsion point in the kernel of reduction is zero. -/
lemma eq_zero_of_isOfFinAddOrder_of_red_eq_zero {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {P : W.Point} (hP : IsOfFinAddOrder P) (h0 : red hW P = 0) : P = 0 :=
  eq_zero_of_isOfFinAddOrder_of_mem_filtration hp hpmem hpram ((red_eq_zero_iff hW).mp h0) hP

include hW in
/-- If a torsion point's reduction is annihilated by `m`, then so is the point itself. -/
lemma nsmul_eq_zero_of_red_nsmul_eq_zero {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {P : W.Point} (hP : IsOfFinAddOrder P) {m : ℕ} (h : m • red hW P = 0) :
    m • P = 0 :=
  eq_zero_of_isOfFinAddOrder_of_red_eq_zero hW hp hpmem hpram hP.nsmul
    (by simpa only [← coe_redHom hW, map_nsmul] using h)

include hW in
/-- **`red` preserves the additive order of a torsion point** (it is injective on torsion, so no
collapse of order can occur). -/
lemma addOrderOf_red {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {P : W.Point} (hP : IsOfFinAddOrder P) : addOrderOf (red hW P) = addOrderOf P :=
  Nat.dvd_antisymm
    (addOrderOf_dvd_of_nsmul_eq_zero
      (by rw [← coe_redHom hW, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]))
    (addOrderOf_dvd_of_nsmul_eq_zero
      (nsmul_eq_zero_of_red_nsmul_eq_zero hW hp hpmem hpram hP (addOrderOf_nsmul_eq_zero _)))

end WeierstrassCurve.Affine

end
