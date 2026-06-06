import Mathlib
import Heights.Basic
import Heights.MvPolynomial
import Heights.NumberField

/-!
# The approximate parallelogram law on elliptic curves

If `K` is a field with `AdmissibleAbsoluteValues` and `E` is an elliptic curve over `K`,
let `h : E(K) → ℝ` be the naïve height of the x-coordinate.

The goal of this file is to show the approximate parallelogram law:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`,
where `h` denotes the (logarithmic) naïve height on `E(K)`,
and to show that there are only finitely many points in `E(K)` of bounded height
when `K` has the Northcott property.
-/

namespace WeierstrassCurve

-- #36989
/-!
### The addition-and-subtraction map on x-coordinates
-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (a b : R)

open MvPolynomial

name_poly_vars s, t, u over R

/-- The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the elliptic curve `W`. -/
noncomputable def addSubMap : Fin 3 → MvPolynomial (Fin 3) R :=
  ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]

/-- The coefficient polynomials in linear combinations of the polynomials in `addSubMap`
that result in the fourth powers of the variables, multiplied by `W.Δ`. -/
noncomputable def addSubMapCoeff : Fin 3 × Fin 3 → MvPolynomial (Fin 3) R :=
  ![![C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * s ^ 2 +
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ - 10 * W.b₆ * W.b₈) * s * t +
        C (-W.b₂ * W.b₆ * W.b₈ + W.b₄ * W.b₆ ^ 2) * s * u +
        C (3 * W.b₄ ^ 2 * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t * u,
      C (-W.b₂ * W.b₄ * W.b₈ + W.b₄ ^ 2 * W.b₆ + 5 * W.b₆ * W.b₈) * s ^ 2 +
        C (2 * W.b₂ * W.b₆ * W.b₈ - 2 * W.b₄ * W.b₆^2 - 10 * W.b₈ ^ 2) * s * t  +
        C (-W.b₂ * W.b₈ ^ 2 + W.b₄ * W.b₆ * W.b₈) * s * u +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t ^ 2 +
        C (3 * W.b₄ * W.b₈ ^ 2 -3 * W.b₆ ^ 2 * W.b₈) * t * u,
      C (W.b₂ * W.b₆ * W.b₈ - 8 * W.b₄ ^ 2 * W.b₈ + 7 * W.b₄ * W.b₆ ^ 2) * s ^ 2 +
        C (-6 * W.b₄ * W.b₆ * W.b₈ + 6 * W.b₆ ^ 3) * s * t +
        C (-8 * W.b₄ * W.b₈ ^ 2 + 8 * W.b₆ ^ 2 * W.b₈) * s * u],
    ![C (96 * W.b₆) * s * t + C (12 * W.b₂ * W.b₆ - 64 * W.b₈) * t ^ 2 +
        C (16 * W.b₄ * W.b₆) * t * u,
      C (-48 * W.b₆) * s ^ 2 + C (32 * W.b₈) * s * t +
        C (-4 * W.b₂ * W.b₈ + 16 * W.b₄ * W.b₆) * t ^ 2 + C (16 * W.b₄ * W.b₈) * t * u,
      C (-12 * W.b₂ * W.b₆) * s ^ 2 + C (8 * W.b₂ * W.b₈ - 32 * W.b₄ * W.b₆) * s * t +
        C (-12 * W.b₆ ^ 2) * s * u +
        C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * t ^ 2 +
        C (4 * W.b₂ * W.b₄ * W.b₈ - 4 * W.b₂ * W.b₆ ^ 2 ) * t * u],
    ![C (-12) * t ^ 2 + C (-4 * W.b₂) * t * u +  C (W.b₂ ^ 2 - 32 * W.b₄) * u ^ 2,
      C 6 * s * t + C (-W.b₂) * s * u + C (-5 * W.b₄) * t * u + C (W.b₂ * W.b₄ - 27 * W.b₆) * u ^ 2,
      C (-8 * W.b₄) * s * u + C (-12 * W.b₆) * t * u + C (W.b₄ ^ 2 - 28 * W.b₈) * u ^ 2]].uncurry

/-- The multiples of the relation `W.b_relation`, which is equivalent to
`4*W.b₈ - W.b₂*W.b₆ + W.b₄^2 = 0`, that we have to add to show the equality in
`addSubMapCoeff_condition` below. -/
noncomputable def bRelationCoeffs : Fin 3 → MvPolynomial (Fin 3) R :=
  ![C (-8 * W.b₄ ^ 2) * s ^ 3 * u + C (5 * W.b₈) * s ^ 2 * t ^ 2 +
      C (3 * W.b₂ * W.b₈ - 11 * W.b₄ * W.b₆) * s ^ 2 * t * u +
      C (-8 * W.b₄ * W.b₈) * s ^ 2 * u ^ 2 + C (3 * W.b₄ * W.b₈ - 3 * W.b₆ ^ 2) * s * t ^ 2 * u,
    C (-32 * W.b₄) * s * t ^ 2 * u + C (16 * W.b₆) * s * t * u ^ 2 + C (-16 * W.b₆) * t ^ 3 * u +
      C (-16 * W.b₈) * t ^ 2 * u ^ 2,
    C (-28) * s * u ^ 3 + C 4 * t ^ 2 * u ^ 2 + C (-W.b₂) * t * u ^ 3 +  C (-8 * W.b₄) * u ^ 4]

private lemma CXX {i : Fin 3} {a : R} : (C a * X (R := R) i ^ 2).IsHomogeneous 2 :=
    isHomogeneous_C_mul_X_pow ..

private lemma CXY {i j : Fin 3} {a : R} : (C a * X (R := R) i * X j).IsHomogeneous 2 :=
    .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · exact .sub (.sub (.sub (isHomogeneous_X_pow ..) CXY) CXY) CXX
  · exact .add (.add (.add CXY CXY) CXY) CXX
  · exact .sub (isHomogeneous_X_pow ..) CXY

lemma isHomogenous_addSubMapCoeff (ij : Fin 3 × Fin 3) : (addSubMapCoeff W ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
    -- The following works, but is slow (44883 vs. 11592 heartbeats):
    -- <;> repeat first | refine .add ?_ CXY | refine .add ?_ CXX | exact CXX | exact CXY
  · exact .add (.add (.add (.add CXX CXY) CXY) CXX) CXY
  · exact .add (.add (.add (.add CXX CXY) CXY) CXX) CXY
  · exact .add (.add CXX CXY) CXY
  · exact .add (.add CXY CXX) CXY
  · exact .add (.add (.add CXX CXY) CXX) CXY
  · exact .add (.add (.add (.add CXX CXY) CXY) CXX) CXY
  · exact .add (.add CXX CXY) CXX
  · exact .add (.add (.add CXY CXY) CXY) CXX
  · exact .add (.add CXY CXY) CXX

variable [W.IsElliptic]

lemma addSubMapCoeff_condition (x : Fin 3 → R) (i : Fin 3) :
    ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, j)).eval x *
      (addSubMap W j).eval x = x i ^ (2 + 2) := by
  have hr : 4 * W.b₈ - W.b₂ * W.b₆ + W.b₄ ^ 2 = 0 := by linear_combination W.b_relation
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum, Units.inv_mul_eq_iff_eq_mul, Fin.sum_univ_three]
  simp only [addSubMap, addSubMapCoeff, Function.uncurry_apply_pair]
  have : -(bRelationCoeffs W i).eval x * (4 * W.b₈ - W.b₂ * W.b₆ + W.b₄ ^ 2) = 0 := by simp [hr]
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_add, map_mul, eval_C, map_pow,
      eval_X, map_neg, Fin.reduceFinMk, Matrix.cons_val, Fin.mk_one, coe_Δ', Δ] <;>
    rw [← sub_eq_zero, ← this] <;> simp [bRelationCoeffs] <;> ring

lemma addSubMap_ne_zero [IsDomain R] {x : Fin 3 → R} (hx : x ≠ 0) :
    (fun i ↦ (addSubMap W i).eval x) ≠ 0 := by
  contrapose! hx
  ext i : 1
  replace hx i : (addSubMap W i).eval x = 0 := by
    rw [Pi.zero_def, funext_iff] at hx
    exact hx i
  simpa [hx] using (addSubMapCoeff_condition W x i).symm

end WeierstrassCurve

namespace WeierstrassCurve

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] (W : WeierstrassCurve K) [W.IsElliptic]

open MvPolynomial

/-- If `W` is an elliptic curve over `K`, then the map `F : ℙ² → ℙ²` given by `addSubMap W`
is a morphism.

This implies that `|logHeight (F x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `F` acts on the coordinate vector. -/
theorem abs_logHeight_addSubMap_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → K,
      |logHeight (fun i ↦ (addSubMap W i).eval x) - 2 * logHeight x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ x : Fin 3 → K,
      logHeight (fun i ↦ (addSubMap W i).eval x) ≤ C₁ + 2 * logHeight x :=
    logHeight_eval_le' <| isHomogeneous_addSubMap W
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ x : Fin 3 → K,
      logHeight (fun i ↦ (addSubMap W i).eval x) ≥ C₂ + 2 * logHeight x := by
    have H (ij : Fin 3 × Fin 3) :
        (C (↑W.Δ'⁻¹ : K) * addSubMapCoeff W ij).IsHomogeneous 2 :=
      IsHomogeneous.C_mul (isHomogenous_addSubMapCoeff W ij) _
    obtain ⟨C₂, h⟩ := logHeight_eval_ge' H
    exact ⟨C₂, fun x ↦ h _ <| addSubMapCoeff_condition W x⟩
  refine ⟨max C₁ (-C₂), fun x ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩ <;> grind

end WeierstrassCurve

-- end #36989

/-
We work with affine points; this seems to be quite a bit less painful
than using projective points.
-/

namespace WeierstrassCurve.Affine

open Height

variable {K : Type*} [Field K] {W : Affine K}

/-- This map sends a pair `P`, `Q` of affine points on `W`
to a triple projectively equivalent to `![x(P) * x(Q), x(P) + x(Q), 1]`.

In more geometric terms, this is the map `Sym² W → Sym² ℙ¹ ≃ ℙ²` induced by `x : W → ℙ¹`. -/
noncomputable def Point.sym2x (P Q : W.Point) : Fin 3 → K :=
  letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]
lemma Point.sym2x_zero_zero : (0 : W.Point).sym2x 0 = ![1, 0, 0] := by
  simp [sym2x]

@[simp]
lemma Point.sym2x_zero_some {x y : K} (h : W.Nonsingular x y) :
    (0 : W.Point).sym2x (some x y h) = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
lemma Point.sym2x_some_zero {x y : K} (h : W.Nonsingular x y) :
    (some x y h : W.Point).sym2x 0 = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
lemma Point.sym2x_some_some {x y x' y' : K} (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') :
    (some x y h : W.Point).sym2x (some x' y' h') = ![x * x', x + x', 1] := by
  simp [sym2x]

lemma Point.sym2x_ne_zero (P Q : W.Point) : P.sym2x Q ≠ 0 := by
  match P, Q with
  | 0, 0 => simp
  | 0, some .. => simp
  | some .., 0 => simp
  | some .., some .. => simp

lemma Point.sym2x_comm (P Q : W.Point) : P.sym2x Q = Q.sym2x P := by
  match P, Q with
  | 0, 0 => simp
  | 0, some .. => simp
  | some .., 0 => simp
  | some .., some .. => simp [mul_comm, add_comm]

lemma Point.sym2x_neg_left (P Q : W.Point) : (-P).sym2x Q = P.sym2x Q := by
  simp only [sym2x, Fin.isValue, P.xRep_neg]

lemma Point.sym2x_neg_right (P Q : W.Point) : P.sym2x (-Q) = P.sym2x Q := by
  simp only [sym2x, Fin.isValue, Q.xRep_neg]

/-!
### `sym2x` and the addition-and-multiplication map

We show that the following diagram commutes.

```
  Sym² W ∋ {P, Q} ↦ {P+Q, P-Q} ∈ Sym² W
     ↓ sym2x                        ↓ sym2x
     ℙ²       - addSubMap -→        ℙ²
```

We now assume that `W` is given by a short Weierstrass equation `y² = x³ + a * x + b` (`hW`)
and is smooth (`hab` is equivalent to the nonvanishing of the discriminant of `W`).
-/

open MvPolynomial Nat

private lemma Point.sym2x_etc_P_zero (P : W.Point) :
    sym2x P P = fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some .. =>
    simp only [sym2x_some_some, succ_eq_add_one, reduceAdd, sym2x_some_zero, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp [pow_two, two_mul]

variable (W) in
private lemma sub_negY_eq (x y : K) : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ :=
  by rw [negY]; ring

private lemma aux {a b c : K} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by
  field

private lemma den_duplication_eq {x y : K} (h : W.Equation x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  have Heq := (W.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination (norm := ring_nf) -4 * Heq

private lemma den_duplication_eq_zero_iff {x y : K} (h : W.Equation x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 ↔ y = W.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only

section Decidable

variable [DecidableEq K]

private lemma addX_x_x_slope_eq {x y : K} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have hn' := (den_duplication_eq_zero_iff h.1).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h.1] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  rw [sub_negY_eq, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h.1]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h.1

private lemma Point.xRep_add_self_of_ne {x y : K} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_x_x_slope_eq h hn, xRep_some]

private lemma Point.xRep_add_self_of_eq {x y : K} (h : W.Nonsingular x y) (hn : y = W.negY x y) :
    (some x y h + some x y h).xRep = ![1, 0] := by
  simp only [add_self_of_Y_eq hn, xRep_zero]

private
lemma Point.sym2x_etc_P_P (P : W.Point) :
    ∃ t : K, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    simp only [add_zero, sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap] <;> ring
    simp only [Hrs]
    by_cases! H : y = W.negY x y
    · simp only [(den_duplication_eq_zero_iff h.1).mpr H]
      refine ⟨x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈, ?_, ?_⟩
      · have HH : 2 * y + W.a₁ * x + W.a₃ = 0 := by
          simp only [negY] at H
          linear_combination H
        have H' := (den_duplication_eq_zero_iff h.1).mpr H
        simp only [b₂, b₄, b₆, b₈] at H' ⊢
        have : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 := by
          have := h.2
          simp [polynomialX, polynomialY, Polynomial.evalEval_pow, Polynomial.evalEval_C] at this
          grind
        contrapose! this
        rw [← sq_eq_zero_iff]
        grobner
      · simp [sym2x, xRep_add_self_of_eq h H]
    · -- In the general case, the denominator of `x(2P)` does not vanish.
      have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      -- This denominator is our `t`.
      refine ⟨_, H', ?_⟩
      simp [sym2x, Point.xRep_add_self_of_ne h H, mul_div_cancel₀ _ H']

lemma Point.sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : K, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (addSubMap W i).eval <| P.sym2x Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_etc_P_P
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, Point.sym2x_comm 0] using P.sym2x_etc_P_P
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_etc_P_zero⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_comm _ Q] using Q.sym2x_etc_P_zero
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    have hxPQ' : (xP - xQ) ^ 2 ≠ 0 := by grind only
    refine ⟨_, hxPQ', ?_⟩
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    rw [add_of_X_ne (h₁ := hP) (h₂ := hQ) hxPQ, sub_eq_add_neg (some ..), neg_some hQ,
      add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hxPQ]
    simp only [addX, slope, hxPQ, ↓reduceIte, addY, negY,
      negAddY, neg_add_rev, sym2x_some_some, succ_eq_add_one, reduceAdd,
      Matrix.smul_cons, smul_eq_mul, mul_one, Matrix.smul_empty, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i
    · simp only [reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val,
        Matrix.cons_val_one, map_sub, map_pow, eval_X, map_mul, eval_C, mul_one, one_pow]
      rw [← mul_right_inj' hxPQ', ← mul_assoc _ (_ - _ - _), mul_left_comm, b₄, b₆, b₈]
      simp_rw [div_pow, sub_sub, mul_sub _ _ (W.a₂ + xP + xQ), mul_add _ (_ / _),
        mul_div_cancel₀ _ hxPQ', aux <| sub_ne_zero.mpr hxPQ]
      grobner
    · simp [div_pow, mul_sub, mul_add, mul_div_cancel₀ _ hxPQ', aux <| sub_ne_zero.mpr hxPQ,
        b₂, b₄, b₆, b₈]
      grobner
    · simp
      ring

end Decidable

/-!
### The naïve height
-/

section AAV

variable [AdmissibleAbsValues K]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. => simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le K
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → K) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

/-- The "approximate parallelogram law" for the naïve height on an elliptic curve
given by a short Weierstrass equation. -/
theorem approx_parallelogram_law [DecidableEq K] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- speed up `grind` below by reducing to the essentials
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end AAV

section Northcott

lemma finite_preimage_xRep (x : K) : {P : W.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : W.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by ext : 1; simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : K) : {P : W.Point | P.xRep 0 = x}.Finite := by
  have : {P : W.Point | P.xRep 0 = x} ⊆ {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset this

variable [AdmissibleAbsValues K]

instance [Northcott (logHeight₁ (K := K))] : Northcott (Point.naiveHeight (K := K) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  exact Northcott.comp_of_finite_fibers _ _ finite_preimage_xRep0

variable [Northcott (logHeight₁ (K := K))]

variable (W) in
/-- The set of `K`-points on `W` with naïve height bounded by `B` is finite.
This is an important ingredient for the *Mordell-Weil Theorem*. -/
lemma finite_naiveHeight_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  Northcott.finite_le B

variable [DecidableEq K] [W.toAffine.IsElliptic]

/-- The **Weak Mordell-Weil Theorem** `(E(K) : 2*E(K)) < ∞` implies the **Mordell-Weil Theorem**:
`E(K)` is finitely generated, for an elliptic curve `E` in short Weierstrass form over a
field `K` that satisfies the Northcott property with respect to `logHeight₁`. -/
theorem weakMW_implies_MW (weakMW : (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.Point := by
  have H₂ (P : W.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' weakMW H₂ hC

end Northcott

end WeierstrassCurve.Affine
