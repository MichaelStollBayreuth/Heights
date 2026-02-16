import Mathlib
import Heights.MvPolynomial
import Heights.Descent

/-!
# The approximate parallelogram law on elliptic curves

If `K` is a field with `AdmissibleAbsoluteValues` and `E` is an elliptic curve over `K`,
let `h : E(K) → ℝ` be the naïve height of the x-coordinate.

The goal of this file is to show the approximate parallelogram law:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C
-/

namespace Height

namespace EllipticCurve

variable {K : Type*} [Field K] (a b : K)

open MvPolynomial

/-- The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the elliptic curve `y² = x³ + a*x + b`. -/
noncomputable def add_sub_map : Fin 3 → MvPolynomial (Fin 3) K :=
  letI s := X 0
  letI t := X 1
  letI u := X 2
  ![s ^ 2 - C (2 * a) * s * u - C (4 * b) * t * u + C (a ^ 2) * u ^ 2,
    C 2 * t * s + C (2 * a) * t * u + C (4 * b) * u ^ 2,
    t ^ 2 - C 4 * s * u]

/-- The coefficient polynomials in linear combinations of the polynomials on `F`
that result in the fourth powers of the variables, multiplied by `32*a^3 + 216*b^2`. -/
noncomputable def add_sub_map_coeff : Fin 3 × Fin 3 → MvPolynomial (Fin 3) K :=
  letI s := X (σ := Fin 3) 0
  letI t := X (σ := Fin 3) 1
  letI u := X (σ := Fin 3) 2
  ![![C (-4 * a ^ 2 * b) * t * s + C (12 * a ^ 3 * b + 96 * b ^ 3) * t * u +
        C (32 * a ^ 3 + 216 * b ^ 2) * s ^ 2 + C (24 * a ^ 4 + 176 * a * b ^ 2) * s * u,
      C (5 * a ^ 4 + 32 * a * b ^ 2 ) * t * s + C (-3 * a ^ 5 - 24 * a ^ 2 * b ^ 2) * t * u +
        C (2 * a ^ 2 * b) * s ^ 2 + C (52 * a ^ 3 * b + 384 * b ^ 3) * s * u,
      C (-10 * a ^ 4 - 64 * a * b ^ 2) * s ^ 2 + C (-4 * a ^ 5 - 32 * a ^ 2 * b ^ 2) * s * u +
        C (6 * a ^ 6 + 96 * a ^ 3 * b ^ 2 + 384 * b ^ 4) * u ^ 2],
    ![C (128 * a * b) * t * u - C (128 * a ^ 2) * s * u + C (384 * b ^ 2) * u ^ 2,
      C (16 * a ^ 2) * t * s + C (16 * a ^ 3 + 384 * b ^ 2) * t * u - C (64 * a * b) * s * u -
        C (96 * a ^ 2 * b) * u ^ 2,
      C (32 * a ^ 3 + 216 * b ^ 2) * t ^ 2 - C (32 * a ^ 2) * s ^ 2 +
        C (64 * a ^ 3 + 96 * b ^ 2) * s * u + C (-32 * a ^ 4 - 256 * a * b ^ 2) * u ^ 2],
    ![C 24 * s * u + C (32 * a) * u ^ 2,
      C (-3) * t * s  + C (5 * a) * t * u + C (54 * b) * u ^ 2,
      C 6 * s ^ 2 - C (4 * a) * s * u - C (10 * a ^ 2) * u ^ 2]].uncurry

-- set_option Elab.async false in
-- #count_heartbeats in -- 1514
lemma isHomogeneous_add_sub_map (i : Fin 3) : (add_sub_map a b i).IsHomogeneous 2 := by
  simp only [add_sub_map]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · refine .add (.sub (.sub (isHomogeneous_X_pow ..) ?_) ?_) (isHomogeneous_C_mul_X_pow ..) <;>
      exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add (.add ?_ ?_) (isHomogeneous_C_mul_X_pow ..) <;>
      exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · exact .sub (isHomogeneous_X_pow ..) <|
      .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

-- set_option Elab.async false in
-- #count_heartbeats in -- 10007
lemma isHomogenous_add_sub_map_coeff (ij : Fin 3 × Fin 3) :
    (add_sub_map_coeff a b ij).IsHomogeneous 2 := by
  simp only [add_sub_map_coeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
  · refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .sub ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .sub (isHomogeneous_C_mul_X_pow ..) (isHomogeneous_C_mul_X_pow ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .sub ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..

variable (hab : 32 * a ^ 3 + 216 * b ^ 2 ≠ 0)

variable {a b}

-- set_option Elab.async false in
-- #count_heartbeats in -- 81414
include hab in
lemma add_sub_map_coeff_condition (x : Fin 3 → K) (i : Fin 3) :
    ∑ j : Fin 3, (C ((32 * a ^ 3 + 216 * b ^ 2)⁻¹) * add_sub_map_coeff a b (i, j)).eval x *
      (add_sub_map a b j).eval x = x i ^ (2 + 2) := by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum, inv_mul_eq_iff_eq_mul₀ hab, Fin.sum_univ_three]
  simp only [add_sub_map, add_sub_map_coeff, Function.uncurry_apply_pair]
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_add, map_mul, eval_C, map_pow,
      eval_X, map_neg, Fin.reduceFinMk, Matrix.cons_val, Fin.mk_one] <;>
    ring

include hab in
lemma add_sub_map_ne_zero {x : Fin 3 → K} (hx : x ≠ 0) :
    (fun i ↦ (add_sub_map a b i).eval x) ≠ 0 := by
  contrapose! hx
  ext1 i
  replace hx i : (add_sub_map a b i).eval x = 0 := by
    rw [Pi.zero_def, _root_.funext_iff] at hx
    exact hx i
  simpa [hx] using (add_sub_map_coeff_condition hab x i).symm

variable [AdmissibleAbsValues K]

include hab in
/-- If `a b : K` and  `D := 32*a^3 + 216*b^2` is nonzero, then the map `F : ℙ² → ℙ²` given by
`(s : t : u) ↦ (s^2 - 2*a*s*u - 4*b*t*u + a²*u² : 2*s*t + 2*a*t*u + 4*b*u² : t² - 4*s*u)`
is a morphism. This implies that `|logHeight (F x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `F` acts on the coordinate vector. -/
theorem abs_logHeight_add_sub_map_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → K,
      |logHeight (fun i ↦ (add_sub_map a b i).eval x) - 2 * logHeight x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ x : Fin 3 → K,
      logHeight (fun i ↦ (add_sub_map a b i).eval x) ≤ C₁ + 2 * logHeight x :=
    logHeight_eval_le' <| isHomogeneous_add_sub_map a b
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ x : Fin 3 → K,
      logHeight (fun i ↦ (add_sub_map a b i).eval x) ≥ C₂ + 2 * logHeight x := by
    have H (ij : Fin 3 × Fin 3) :
        (C ((32 * a ^ 3 + 216 * b ^ 2)⁻¹) * add_sub_map_coeff a b ij).IsHomogeneous 2 :=
      IsHomogeneous.C_mul (isHomogenous_add_sub_map_coeff a b ij) _
    obtain ⟨C₂, h⟩ := logHeight_eval_ge' H
    exact ⟨C₂, fun x ↦ h _ <| add_sub_map_coeff_condition hab x⟩
  refine ⟨max C₁ (-C₂), fun x ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩ <;> grind

end EllipticCurve

end Height

/- We work with affine points; this seems to be quite a bit less painful... -/

namespace WeierstrassCurve.Affine

open Height EllipticCurve

variable {K : Type*} [Field K] {a b : K} {W : Affine K}

lemma Point.exists_x_y_of_ne_zero {P : W.Point} (hP : P ≠ 0) :
    ∃ (x y : K) (h : W.Nonsingular x y), P = .some h := by
  match P with
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h => exact ⟨x, y, h, rfl⟩

def Point.x_of_ne_zero : {P : W.Point} → (hP : P ≠ 0) → K
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _, _ => x

def Point.y_of_ne_zero : {P : W.Point} → (hP : P ≠ 0) → K
  | @WeierstrassCurve.Affine.Point.some _ _ _ _ y _, _ => y

lemma Point.x_eq_iff {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    x_of_ne_zero hP = x_of_ne_zero hQ ↔ Q = P ∨ Q = -P := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · obtain ⟨xP, yP, hP', rfl⟩ := exists_x_y_of_ne_zero hP
    obtain ⟨xQ, yQ, hQ', rfl⟩ := exists_x_y_of_ne_zero hQ
    simp_rw [neg_some, some.injEq]
    rw [← and_or_left]
    exact ⟨H.symm, Y_eq_of_X_eq hQ'.1 hP'.1 H.symm⟩
  · rcases H with rfl | H
    · rfl
    · obtain ⟨xP, yP, hP', rfl⟩ := exists_x_y_of_ne_zero hP
      rw [neg_some] at H
      obtain ⟨xQ, yQ, hQ', rfl⟩ := exists_x_y_of_ne_zero hQ
      rw [some.injEq] at H
      exact H.1.symm

/-- This map sends an affine point `P` on `W` to a representative of its image on ℙ¹
under the x-coordinate map. We take `![1, 0]` for the point at infinity and `[x, 1]`,
where `x` is the x-coordinate of `P` for a finite point. -/
noncomputable def Point.xRep : W.Point → Fin 2 → K
  | 0 => ![1, 0]
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ => ![x, 1]

@[simp]
lemma Point.xRep_zero : (0 : W.Point).xRep = ![1, 0] :=
  rfl

@[simp]
lemma Point.xRep_some {x y : K} (h : W.Nonsingular x y) : (.some h : W.Point).xRep = ![x, 1] :=
  rfl

lemma Point.xRep_ne_zero (P : W.Point) : P.xRep ≠ 0 := by
  match P with
  | 0 => simp
  | .some _ => simp

lemma Point.xRep_neg (P : W.Point) : (-P).xRep = P.xRep := by
  match P with
  | 0 => simp
  | .some _ => simp

/-- This map sends a pair `P`, `Q` of affine points on `W`
to a triple projectively equivalent to `![x(P) * x(Q), x(P) + x(Q), 1]`. -/
noncomputable def Point.sym2x (P Q : W.Point) : Fin 3 → K :=
  letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]
lemma Point.sym2x_zero_zero : (0 : W.Point).sym2x 0 = ![1, 0, 0] := by
  simp [sym2x]

@[simp]
lemma Point.sym2x_zero_some {x y : K} (h : W.Nonsingular x y) :
    (0 : W.Point).sym2x (.some h) = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
lemma Point.sym2x_some_zero {x y : K} (h : W.Nonsingular x y) :
    (.some h : W.Point).sym2x 0 = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
lemma Point.sym2x_some_some {x y x' y' : K} (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') :
    (.some h : W.Point).sym2x (.some h') = ![x * x', x + x', 1] := by
  simp [sym2x]

lemma Point.sym2x_ne_zero (P Q : W.Point) : P.sym2x Q ≠ 0 := by
  match P, Q with
  | 0, 0 => simp
  | 0, .some _ => simp
  | .some _, 0 => simp
  | .some _, .some h => simp

lemma Point.sym2x_symm (P Q : W.Point) : P.sym2x Q = Q.sym2x P := by
  match P, Q with
  | 0, 0 => simp
  | 0, .some _ => simp
  | .some _, 0 => simp
  | .some _, .some h => simp [mul_comm, add_comm]

lemma Point.sym2x_neg_left (P Q : W.Point) : (-P).sym2x Q = P.sym2x Q := by
  simp only [sym2x, Fin.isValue, P.xRep_neg]

lemma Point.sym2x_neg_right (P Q : W.Point) : P.sym2x (-Q) = P.sym2x Q := by
  simp only [sym2x, Fin.isValue, Q.xRep_neg]

variable (hab : 32 * a ^ 3 + 216 * b ^ 2 ≠ 0) (hW : W = (WeierstrassCurve.mk 0 0 0 a b).toAffine)

open MvPolynomial

private
lemma Point.sym2x_etc_P_zero [DecidableEq K] (P : W.Point) :
    sym2x P P = fun i ↦ (add_sub_map a b i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, Nat.succ_eq_add_one, Nat.reduceAdd, add_sub_map, Fin.isValue, C_mul,
      C_pow]
    ext1 i
    fin_cases i <;> simp
  | .some _ =>
    simp only [sym2x_some_some, Nat.succ_eq_add_one, Nat.reduceAdd, sym2x_some_zero, add_sub_map,
      Fin.isValue, C_mul, C_pow]
    ext1 i
    fin_cases i <;> simp [pow_two, two_mul]

include hW in
private
lemma Point.sym2x_etc_P_P [DecidableEq K] (P : W.Point) :
    ∃ t : K, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (add_sub_map a b i).eval <| P.sym2x P := by
  rcases eq_or_ne P 0 with rfl | hP
  · refine ⟨1, one_ne_zero, ?_⟩
    simp only [add_zero, sym2x_zero_zero, Nat.succ_eq_add_one, Nat.reduceAdd, add_sub_map,
      Fin.isValue, C_mul, C_pow]
    ext1 i
    fin_cases i <;> simp
  obtain ⟨x, y, h, rfl⟩ := exists_x_y_of_ne_zero hP
  have Heq := (W.equation_iff x y).mp h.1
  simp only [hW, zero_mul, add_zero] at Heq
  by_cases! H : y = W.negY x y
  · have H' : 4 * (x ^ 3 + a * x + b) = 0 := by
      simp only [negY, hW, zero_mul, sub_zero] at H
      rw [← Heq]
      grind only
    have H'' : x ^ 4 - 2 * a * x ^ 2 - 8 * b * x + a ^ 2 ≠ 0 := by
      have := h.2
      simp only [polynomialX, hW, _root_.map_zero, zero_mul, mul_zero, add_zero, map_add, map_mul,
        map_pow, zero_sub, neg_add_rev, Polynomial.evalEval_add, Polynomial.evalEval_neg,
        Polynomial.evalEval_C, Polynomial.eval_C, Polynomial.evalEval_mul, Polynomial.evalEval_pow,
        Polynomial.eval_X, polynomialY, Polynomial.evalEval_X] at this
      rcases this with H₁ | H₁
      · contrapose! H₁
        rw [← sq_eq_zero_iff]
        linear_combination 2 * x * H' + H₁
      · grind only
    refine ⟨_, H'', ?_⟩
    rw [add_self_of_Y_eq H]
    simp only [sym2x_zero_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul,
      mul_one, mul_zero, Matrix.smul_empty, sym2x_some_some, add_sub_map, Fin.isValue, C_mul, C_pow]
    ext1 i
    fin_cases i
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, map_add, map_sub, map_pow, eval_X, map_mul, eval_C, Matrix.cons_val,
        mul_one, Matrix.cons_val_one, one_pow, add_left_inj]
      ring
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, map_add, map_mul, eval_C, eval_X, Matrix.cons_val, mul_one, map_pow,
        one_pow]
      linear_combination -H'
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue,
        map_sub, map_pow, eval_X, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul, eval_C,
        mul_one]
      ring
  · have H' : 4 * (x ^ 3 + a * x + b) ≠ 0 := by
      simp only [negY, hW, zero_mul, sub_zero] at H
      rw [← Heq]
      grind only
    refine ⟨_, H', ?_⟩
    rw [add_self_of_Y_ne H]
    simp only [addX, addY, negY, negAddY, neg_add_rev, sym2x_some_zero, Nat.succ_eq_add_one,
      Nat.reduceAdd, sym2x_some_some, add_sub_map, Fin.isValue, C_mul, C_pow]
    have Hsl : W.slope x x y y ^ 2 + W.a₁ * W.slope x x y y - W.a₂ =
        (3 * x ^ 2 + a) ^ 2 / (4 * (x ^ 3 + a * x + b)) := by
      rw [slope_of_Y_ne_eq_evalEval rfl H]
      suffices (3 * x ^ 2 + a) ^ 2 / (2 * y) ^ 2 = (3 * x ^ 2 + a) ^ 2 / (4 * (x ^ 3 + a * x + b))
        by simp [polynomialX, polynomialY, hW, Polynomial.evalEval_C, div_pow, this]
      congr
      rw [← Heq]
      ring
    rw [Hsl]
    ext1 i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul,
        map_add, map_sub, map_pow, eval_X, map_mul, eval_C, Matrix.cons_val, mul_one,
        Matrix.cons_val_one, one_pow]
      rw [mul_sub, mul_sub, mul_div_cancel₀ _ H']
      ring
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
        smul_eq_mul, mul_one, map_add, map_mul, eval_C, eval_X, Matrix.cons_val, map_pow, one_pow]
      ring
    · simp only [Fin.reduceFinMk, Pi.smul_apply, Fin.isValue, Matrix.cons_val, smul_eq_mul,
        mul_zero, map_sub, map_pow, eval_X, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul,
        eval_C, mul_one]
      ring

include hW in
lemma Point.sym2x_add_sub_eq_add_sub_map_sym2x [DecidableEq K] (P Q : W.Point) :
    ∃ t : K, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (add_sub_map a b i).eval <| P.sym2x Q := by
  rcases eq_or_ne Q 0 with rfl | hQ₀
  · exact ⟨1, one_ne_zero, by simpa using P.sym2x_etc_P_zero⟩
  rcases eq_or_ne P 0 with rfl | hP₀
  · refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_symm _ Q] using Q.sym2x_etc_P_zero
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_etc_P_P hW
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, sym2x_symm 0] using P.sym2x_etc_P_P hW
  obtain ⟨xP, yP, hP, rfl⟩ := P.exists_x_y_of_ne_zero hP₀
  obtain ⟨xQ, yQ, hQ, rfl⟩ := Q.exists_x_y_of_ne_zero hQ₀
  have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [(x_eq_iff hP₀ hQ₀).mp Heq]
  have hxPQ' : (xP - xQ) ^ 2 ≠ 0 := by grind only
  refine ⟨_, hxPQ', ?_⟩
  rw [add_of_X_ne (h₁ := hP) (h₂ := hQ) hxPQ, sub_eq_add_neg (some _), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hxPQ]
  simp only [addX, slope, hxPQ, ↓reduceIte, hW, zero_mul, add_zero, sub_zero, addY, negY, negAddY,
    neg_add_rev, sub_neg_eq_add, sym2x_some_some, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.smul_cons, smul_eq_mul, mul_one, Matrix.smul_empty]
  simp only [add_sub_map, Fin.isValue, C_mul, C_pow]
  have HeqP := (W.equation_iff xP yP).mp hP.1
  have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
  simp only [hW, zero_mul, add_zero] at HeqP HeqQ
  ext1 i
  fin_cases i
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      map_add, map_sub, map_pow, eval_X, map_mul, eval_C, Matrix.cons_val, mul_one,
      Matrix.cons_val_one, one_pow]
    rw [div_pow, div_pow, ← mul_right_inj' hxPQ', ← mul_assoc _ (_ - _ - _)]
    conv_lhs => enter [2, 1]; rw [mul_sub, mul_sub, mul_div_cancel₀ _ hxPQ']
    rw [mul_left_comm]
    conv_lhs => enter [2]; rw [mul_sub, mul_sub, mul_div_cancel₀ _ hxPQ']
    conv_lhs => ring_nf -- eliminate odd powers of `yP`, `yQ`
    rw [show yP ^ 4 = (yP ^ 2) ^ 2 by ring, show yQ ^ 4 = (yQ ^ 2) ^ 2 by ring, HeqP, HeqQ]
    ring
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero, map_add, map_mul, eval_C, eval_X, Matrix.cons_val, mul_one, map_pow,
      one_pow]
    simp only [div_pow, mul_sub, mul_add, mul_div_cancel₀ _ hxPQ']
    conv_lhs => ring_nf -- eliminate odd powers of `yP`, `yQ`
    rw [HeqP, HeqQ]
    ring
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue,
      map_sub, map_pow, eval_X, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul, eval_C, mul_one]
    ring

/-!
### The naïve height
-/

variable [AdmissibleAbsValues K]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep :=
  rfl

variable (W) in
lemma logHeight_sym2 :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2'_le (K := K)
  obtain ⟨C₂, hC₂⟩ := logHeight_sym2'_ge (K := K)
  refine ⟨max C₁ (-C₂), fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  specialize hC₁ (P.xRep 0) (P.xRep 1) (Q.xRep 0) (Q.xRep 1)
  have H (v : Fin 2 → K) : ![v 0, v 1] = v := by
    ext1 i
    fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC₂ (P.xRep 0) (P.xRep 1) (Q.xRep 0) (Q.xRep 1) (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

-- set_option Elab.async false in
-- #count_heartbeats in -- 8840 / 17416
include hab hW in
/-- The "approximate parallelogram law" for the naïve height on an elliptic curve
given by a short Weierstrass equation. -/
theorem approx_parallelogram_law [DecidableEq K] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2 W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_add_sub_map_sub_two_mul_logHeight_le hab
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_add_sub_map_sym2x hW P Q
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

end WeierstrassCurve.Affine
