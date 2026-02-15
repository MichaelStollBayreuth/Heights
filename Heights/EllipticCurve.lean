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
`(x(P) + x(Q) : x(P) * x(Q) : 1) ↦ (x(P+Q) + x(P-Q) : x(P+Q) * x(P-Q) : 1)`
for points `P`, `Q` on the elliptic curve `y² = x³ + a*x + b`. -/
noncomputable def add_sub_map : Fin 3 → MvPolynomial (Fin 3) K :=
  letI s := X 0
  letI t := X 1
  letI u := X 2
  ![C 2 * (s * t + C a * s * u + C (2 * b) * u ^ 2),
    t ^ 2 - C (2 * a) * t * u - C (4 * b) * s * u + C (a ^ 2) * u ^ 2,
    s ^ 2 - C 4 * t * u]

/-- The coefficient polynomials in linear combinations of the polynomials on `F`
that result in the fourth powers of the variables, multiplied by `8*a^3 + 54*b^2`. -/
noncomputable def add_sub_map_coeff : Fin 3 × Fin 3 → MvPolynomial (Fin 3) K :=
  letI s := X (σ := Fin 3) 0
  letI t := X (σ := Fin 3) 1
  letI u := X (σ := Fin 3) 2
  ![![C (16 * a ^ 2) * s * t + C (16 * a ^ 3 + 384 * b ^ 2) * s * u - C (64 * a * b) * t * u -
        C (96 * a ^ 2 * b) * u ^ 2,
      C (128 * a * b) * s * u - C (128 * a ^ 2) * t * u + C (384 * b ^ 2) * u ^ 2,
      C (32 * a ^ 3 + 216 * b ^ 2) * s ^ 2 - C (32 * a ^ 2) * t ^ 2 +
        C (64 * a ^ 3 + 96 * b ^ 2) * t * u + C (-32 * a ^ 4 - 256 * a * b ^ 2) * u ^ 2],
    ![C (5 * a ^ 4 + 32 * a * b ^ 2 ) * s * t + C (-3 * a ^ 5 - 24 * a ^ 2 * b ^ 2) * s * u +
        C (2 * a ^ 2 * b) * t ^ 2 + C (52 * a ^ 3 * b + 384 * b ^ 3) * t * u,
      C (-4 * a ^ 2 * b) * s * t + C (12 * a ^ 3 * b + 96 * b ^ 3) * s * u +
        C (32 * a ^ 3 + 216 * b ^ 2) * t ^ 2 + C (24 * a ^ 4 + 176 * a * b ^ 2) * t * u,
      C (-10 * a ^ 4 - 64 * a * b ^ 2) * t ^ 2 + C (-4 * a ^ 5 - 32 * a ^ 2 * b ^ 2) * t * u +
        C (6 * a ^ 6 + 96 * a ^ 3 * b ^ 2 + 384 * b ^ 4) * u ^ 2],
    ![C (-3) * s * t  + C (5 * a) * s * u + C (54 * b) * u ^ 2,
      C 24 * t * u + C (32 * a) * u ^ 2,
      C 6 * t ^ 2 - C (4 * a) * t * u - C (10 * a ^ 2) * u ^ 2]].uncurry

private lemma _root_.MvPolynomial.IsHomogeneous.mul' {σ R : Type*} [CommSemiring R]
    {φ ψ : MvPolynomial σ R} {m n k : ℕ} (hφ : φ.IsHomogeneous m) (hψ : ψ.IsHomogeneous n)
    (hk : k = m + n) :
    (φ * ψ).IsHomogeneous k :=
  hk ▸ .mul hφ hψ

lemma isHomogeneous_add_sub_map (i : Fin 3) : (add_sub_map a b i).IsHomogeneous 2 := by
  simp only [add_sub_map]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · refine .C_mul (.add (.add ?_ ?_) (isHomogeneous_C_mul_X_pow ..)) 2
    · exact .mul (m := 1) (n := 1) (isHomogeneous_X ..) (isHomogeneous_X ..)
    · exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add (.sub (.sub (isHomogeneous_X_pow ..) ?_) ?_) (isHomogeneous_C_mul_X_pow ..)
     <;> exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · exact .sub (isHomogeneous_X_pow ..) <|
      .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

lemma isHomogenous_add_sub_map_coeff (ij : Fin 3 × Fin 3) :
    (add_sub_map_coeff a b ij).IsHomogeneous 2 := by
  simp only [add_sub_map_coeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
  · refine .sub ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .sub (isHomogeneous_C_mul_X_pow ..) (isHomogeneous_C_mul_X_pow ..)
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
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .sub ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..

variable (hab : 32 * a ^ 3 + 216 * b ^ 2 ≠ 0)

variable {a b}

-- set_option Elab.async false in
-- #count_heartbeats in -- 80607
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
`(s : t : u) ↦ (2*(s*t + a*s*u + 2*b*u²) : t^2 - 2*a*t*u - 4*b*s*u + a²*u² : s² - 4*t*u)`
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

namespace WeierstrassCurve.Projective

open Height EllipticCurve

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {a b : K}

/-- The map that sends a pair `P`, `Q` of representatives of projective points on `W`
to a triple projectively equivalent to `![x(P) + x(Q), x(P) * x(Q), 1]`. -/
noncomputable def sym2 (P Q : Fin 3 → K) : Fin 3 → K :=
  ![P 0 * Q 2 + P 2 * Q 0, P 0 * Q 0, P 2 * Q 2]

lemma sym2_ne_zero {W : Projective K} {P Q : W.Point} {P' Q' : Fin 3 → K}
    (hP : P.point = ⟦P'⟧) (hQ : Q.point = ⟦Q'⟧) : sym2 P' Q' ≠ 0 := by
  sorry

variable (hab : 32 * a ^ 3 + 216 * b ^ 2 ≠ 0)

/-
-- Working with the projective addition formulas looks like it is going to be very painful...
include hab in
lemma sym2_add_sub_eq_add_sub_map_sym2
    {P Q : (WeierstrassCurve.mk 0 0 0 a b).toProjective.Point} {P' Q' : Fin 3 → K}
    (hP : P.point = ⟦P'⟧) (hQ : Q.point = ⟦Q'⟧) :
    letI W := (WeierstrassCurve.mk 0 0 0 a b).toProjective
    -- this is false; one has to scale both sides and use the curve equation
    sym2 (W.add P' Q') (W.add P' (W.neg Q')) = fun i ↦ (add_sub_map a b i).eval <| sym2 P' Q' := by
  let W := (WeierstrassCurve.mk 0 0 0 a b).toProjective
  by_cases h : P' ≈ Q'
  · sorry
  · rw [add_of_not_equiv h]
    by_cases h' : P' ≈ W.neg Q'
    · sorry
    · rw [add_of_not_equiv h']
      simp [sym2, addXYZ_X, addXYZ_Z, addX, addZ, neg_X, neg_Y, neg_Z, negY, W]
      ext1 i
      fin_cases i
      · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
          Matrix.cons_val_zero]
        simp only [add_sub_map]
        simp only [Fin.isValue, map_mul, map_pow, Matrix.cons_val_zero, MvPolynomial.eval_C,
          map_add, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val]
        -- rw [← sub_eq_zero]
        have eP : W.Equation P' := by sorry
        have eQ : W.Equation Q' := by sorry
        simp [equation_iff, W] at eP eQ
        conv => enter [1, 2]; rw [mul_comm]
        rw [← add_mul]
        conv => enter [1, 1]; ring_nf

        --grobner
        sorry
      · sorry
      · sorry
      -- ring_nf
 -/

/- We need to be careful with `sym2` when one of the points is the origin! -/

include hab in
lemma sym2_add_sub_eq_add_sub_map_sym2 {W : Projective K}
    (hW : W = (WeierstrassCurve.mk 0 0 0 a b).toProjective) {P Q : W.Point} {P' Q' : Fin 3 → K}
    (hP : P.point = ⟦P'⟧) (hQ : Q.point = ⟦Q'⟧) :
    ∃ t : K, t ≠ 0 ∧ t • sym2 (W.add P' Q') (W.add P' (W.neg Q')) =
      fun i ↦ (add_sub_map a b i).eval <| sym2 P' Q' := by
  sorry

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def _root_.WeierstrassCurve.Affine.Point.naiveHeight {W : Affine K} : W.Point → ℝ
  | .zero => 0
  | @Affine.Point.some _ _ _ x _ _ => logHeight₁ x

/-- The naïve logarithmic height of a projective point on `W`. -/
noncomputable def Point.naiveHeight {W : Projective K} (P : W.Point) :=
  P.toAffineLift.naiveHeight

lemma Point.naiveHeight_eq_logHeight {W : Projective K} {P : W.Point} {P' : Fin 3 → K}
    (hP : P.point = ⟦P'⟧) :
    P.naiveHeight = logHeight ![P' 0, P' 2] := by
  sorry

lemma logHeight_sym2 (W : Projective K) :
    ∃ C, ∀ {P Q : W.Point} {P' Q' : Fin 3 → K} (hP : P.point = ⟦P'⟧) (hQ : Q.point = ⟦Q'⟧),
      |logHeight (sym2 P' Q') - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2'_le (K := K)
  obtain ⟨C₂, hC₂⟩ := logHeight_sym2'_ge (K := K)
  refine ⟨max C₁ (-C₂), fun {P Q P' Q'} hP hQ ↦ ?_⟩
  rw [Point.naiveHeight_eq_logHeight hP, Point.naiveHeight_eq_logHeight hQ, sym2]
  rcases eq_or_ne ![P' 0, P' 2] 0 with hx | hx
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_eq_zero_iff,
      Matrix.zero_empty, and_true] at hx
    simp [hx.1, hx.2]
    -- not provable; need to use projection to ℙ¹ that gives ![1, 0] for the origin
    sorry
  rcases eq_or_ne ![Q' 0, Q' 2] 0 with hy | hy
  · sorry
  have H₁ := logHeight_fun_mul_eq hx hy
  specialize hC₁ (P' 0) (P' 2) (Q' 0) (Q' 2)
  specialize hC₂ (P' 0) (P' 2) (Q' 0) (Q' 2)
  have : logHeight ![P' 0 * Q' 2 + P' 2 * Q' 0, P' 0 * Q' 0, P' 2 * Q' 2] =
      logHeight ![P' 0 * Q' 0, P' 0 * Q' 2 + P' 2 * Q' 0, P' 2 * Q' 2] := by
    let e := Equiv.swap (α := Fin 3) 0 1
    convert logHeight_comp_equiv e _
    ext1 i
    fin_cases i <;> simp [e, Equiv.swap_apply_of_ne_of_ne]
  rw [this]
  grind only [= abs.eq_1, = max_def]

include hab in
/-- The "approximate parallelogram law" for the naïve height on an elliptic curve
given by a short Weierstrass equation. -/
theorem approx_parallelogram_law {W : Projective K}
    (hW : W = (WeierstrassCurve.mk 0 0 0 a b).toProjective) :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2 W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_add_sub_map_sub_two_mul_logHeight_le hab
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  let P' := P.point.out
  let Q' := Q.point.out
  have hP : P.point = ⟦P'⟧ := P.point.out_eq.symm
  have hQ : Q.point = ⟦Q'⟧ := Q.point.out_eq.symm
  have hadd : (P + Q).point = ⟦W.add P' Q'⟧ := by rw [Point.add_point, hP, hQ, addMap_eq]
  have hsub : (P - Q).point = ⟦W.add P' (W.neg Q')⟧ := by
    rw [sub_eq_add_neg, Point.add_point, Point.neg_point, hP, hQ, negMap_eq, addMap_eq]
  obtain ⟨t, ht₀, ht⟩ := sym2_add_sub_eq_add_sub_map_sym2 hab hW hP hQ
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ hP hQ
  have haddsub := hC₁ hadd hsub
  have hC := ht ▸ hC₂ (sym2 P' Q')
  -- speed up `grind` below by reducing to the essentials
  clear ht ht₀ t hsub hadd
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight (sym2 (W.add P' Q') (W.add P' (W.neg Q'))) = B at hC haddsub ⊢
  generalize logHeight (sym2 P' Q') = B' at hPQ hC ⊢
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  clear hQ hP Q' P' Q P hC₂ hC₁ hW W hab
  grind only [= abs.eq_1, = max_def]

end WeierstrassCurve.Projective
