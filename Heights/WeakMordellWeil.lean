import Mathlib.GroupTheory.QuotientGroup.Defs
import Heights.EllipticCurve

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite when `E` is an elliptic curve
over a number field `K`.

We will use the `x-T` map approach. At least for now, we will restrict to elliptic curves
given by a short Weierstrass equation `y² = x³ + ax + b =: f(x)`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   We write `θ` for the image of `X` in `A`.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
3. Show that `μ` is a group homomorphism.
4. Show that `ker μ = 2E(K)`.
5. Show that `im μ ⊆ A(S,2)`, where `S` is the set of "bad" primes, i.e., primes dividing `2`
   or the (numerator of the) discriminant of `E` or the denominator of `a` or `b`.
6. Show that `A(S,2)` is finite. (There is some preliminary stuff in
   `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, but finiteness is still a TODO there.)
-/

section API

section Group

variable {G H : Type*} [Group G] [Group H]

@[to_additive]
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

end Group

section Units

variable {α : Type*} [Monoid α]

@[to_additive]
lemma exists_unit_pow_eq_isUnitUnit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · apply_fun Units.val at hx
    simpa using hx
  · match n with
    | 0 =>
      refine ⟨1, ?_⟩
      apply_fun Units.val using Units.val_injective
      simp_all
    | m + 1 =>
      exact ⟨isUnit_pow_succ_iff.mp (hx ▸ h) |>.unit, Units.ext hx⟩

end Units

section RingQuotient

variable {R : Type*} [CommRing R]

lemma Ideal.Quotient.algebraMap_eq_zero_iff_mem {I : Ideal R} {r : R} :
    algebraMap R (R ⧸ I) r = 0 ↔ r ∈ I := by
  rw [algebraMap_eq, eq_zero_iff_mem]

lemma Ideal.Quotient.algebraMap_span_eq_zero_iff_dvd {a : R} {r : R} :
    algebraMap R (R ⧸ Ideal.span {a}) r = 0 ↔ a ∣ r := by
  rw [algebraMap_eq_zero_iff_mem, mem_span_singleton]

end RingQuotient

end API

namespace WeierstrassCurve

/-!
### Step 1: define `A` and `θ`
-/

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- The `a` coefficient of a short Weierstrass curve. -/
abbrev a : K := W.a₄

/-- The `b` coefficient of a short Weierstrass curve. -/
abbrev b : K := W.a₆

open Polynomial

/-- The polynomial on the right hand side of a short Weierstrass equation. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a * X + C W.b

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] := X ^ 2 + C x * X + C (x ^ 2 + W.a)

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp [fCofactor, f]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma three_sq_add_a_ne_zero [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + W.a ≠ 0 := by
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hx
  have := W.Δ_of_isShortNF ▸ W.isUnit_Δ |>.ne_zero
  rw [a, b] at *
  contrapose! this
  grobner

/-- The étale algebra associated to a short Weierstrass curve. -/
noncomputable abbrev A : Type _ := K[X] ⧸ Ideal.span {W.f}

/- /-- The generator of `W.A`, which is the image of `X` under the canonical map. -/
noncomputable abbrev θ : W.A := Ideal.Quotient.mk _ X

lemma θ_eq_algebraMap : W.θ = algebraMap K[X] W.A X := rfl

lemma θ_eq : W.θ = (X : K[X]) • 1 := by
  rw [θ_eq_algebraMap, Algebra.algebraMap_eq_smul_one] -/

/- lemma f_smul_eq_zero : W.f • (1 : W.A) = 0 := by
  rw [Algebra.smul_def W.f (1 : W.A), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.mk_singleton_self, zero_mul] -/

/-- The étale algebra associated to the cofactor of `f`. -/
noncomputable abbrev A' (x : K) : Type _ := K[X] ⧸ Ideal.span {W.fCofactor x}

lemma eq_in_A_iff [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    algebraMap K[X] W.A p = algebraMap K[X] W.A q ↔
      p.eval x = q.eval x ∧ algebraMap K[X] (W.A' x) p = algebraMap K[X] (W.A' x) q := by
  rw [← sub_eq_zero]; nth_rw 2 [← sub_eq_zero]; nth_rw 3 [← sub_eq_zero]
  rw [← map_sub, ← eval_sub, ← map_sub, Ideal.Quotient.algebraMap_span_eq_zero_iff_dvd,
    Ideal.Quotient.algebraMap_span_eq_zero_iff_dvd]
  generalize p - q = r
  refine ⟨fun H ↦ ⟨?_, dvd_trans ⟨_, f_eq_mul_of_eval_eq_zero W hx⟩ H⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := H
    simp [hx]
  · rw [f_eq_mul_of_eval_eq_zero W hx]
    refine IsCoprime.mul_dvd ?_ H₂ <| dvd_iff_isRoot.mpr H₁
    refine ⟨C (3 * x ^ 2 + W.a)⁻¹, -(C (3 * x ^ 2 + W.a)⁻¹ * (X + C (2 * x))), ?_⟩
    rw [fCofactor, neg_mul, ← sub_eq_add_neg, mul_assoc, ← mul_sub,
      show X ^ 2 + C x * X + C (x ^ 2 + W.a) - (X + C (2 * x)) * (X - C x) = C (3 * x ^ 2 + W.a) by
        simp only [C_eq_algebraMap]; algebra,
      ← C_mul, inv_mul_cancel₀ <| W.three_sq_add_a_ne_zero hx, map_one]

variable {W}

lemma isUnit_sub_theta_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| algebraMap K[X] W.A (C x - X) := by
  refine .of_mul_eq_one
    (algebraMap K[X] W.A (C (W.f.eval x)⁻¹ * (X ^ 2 + C x * X + C (x ^2 + W.a)))) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = algebraMap K[X] W.A (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow]
  have : (C x - X) * (X ^ 2 + C x * X + (C x ^ 2 + C W.a)) =
      -X ^ 3 - C W.a * X - C W.b + C (x ^3 + W.a * x + W.b) := by
    simp; ring
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  rw [this, mul_add, ← C_mul, inv_mul_cancel₀ h, map_one]
  ring

namespace Affine

variable {W : Affine K}

lemma eval_linePolynomial_left [DecidableEq K] (xP xQ yP yQ : K) :
    eval xP (linePolynomial xP yP (W.slope xP xQ yP yQ)) = yP := by
  simp [linePolynomial]

lemma eval_linePolynomial_right [DecidableEq K] (xP xQ yP yQ : K) (h : xP ≠ xQ) :
    eval xQ (linePolynomial xP yP (W.slope xP xQ yP yQ)) = yQ := by
  simp only [linePolynomial, slope, if_neg h]
  simp
  field (disch := grind)

section

variable [W.IsShortNF]

lemma equation_iff_of_isShortNF (x y : K) :
    W.Equation x y ↔ y ^ 2 = x ^ 3 + W.a * x + W.b := by
  rw [W.equation_iff, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF, a, b]
  ring_nf

lemma Point.y_eq_zero_of_eval_f_x_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rw [equation_iff_of_isShortNF x y] at h
  rw [← sq_eq_zero_iff, h, ← hf]
  simp [f]

variable [W.IsElliptic]

lemma isUnit_sub_theta_add_eval_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| algebraMap K[X] W.A <| C x - X + W.fCofactor x := by
  let u : K[X] :=
    C (-48 * x ^ 2 + 48 * W.a * x - 64 * W.a - 144 * W.b) * X ^ 2 +
      C (-48 * W.a * x ^ 2 - 16 * W.a * x - 64 * W.a ^ 2 + 48 * W.b) * X +
      C ((-64 * W.a + 144 * W.b) * x ^ 2 + (64 * W.a ^ 2 + 48 * W.b) * x - 64 * W.a ^ 2)
  let q : K[X] :=
    C (-48 * x ^ 2 + 48 * W.a * x - 64 * W.a - 144 * W.b) * X +
      C (48 * x ^ 2 + (-80 * W.a - 144 * W.b) * x - 64 * W.a ^ 2 + 64 * W.a + 240 * W.b)
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  have : C x - X + (X ^ 2 + C x * X + C (x ^ 2 + a W)) = X ^ 2 + C (x - 1) * X + C (x ^ 2 + x + W.a) := by
    simp
    ring
  have H : (C x - X + W.fCofactor x) * u = q * W.f + C W.Δ := by
    simp only [Δ_of_isShortNF W, show W.a₄ = W.a from rfl, show W.a₆ = W.b from rfl, f, fCofactor, q, u]
    rw [this]
    simp only [add_mul, sub_mul, mul_add, ← mul_assoc, mul_comm (X ^ _) (C _),
      mul_right_comm (C _ ) X (C _), ← C_mul]
    simp_rw [mul_assoc, ← pow_add, ← pow_succ, ← pow_succ', ← sq]
    norm_num1
    simp only [C_mul']
    simp_rw [C_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
    match_scalars <;> grobner
  have h' : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  apply_fun Algebra.algebraMap K[X] W.A at H
  rw [map_mul] at H; nth_rewrite 3 [map_add] at H; rw [map_mul] at H
  rw [show algebraMap K[X] W.A W.f = 0 by simp [A], mul_zero, zero_add] at H
  refine .of_mul_eq_one (algebraMap K[X] W.A <| C (W.Δ⁻¹) * u) ?_
  rw [map_mul]; nth_rewrite 2 [mul_comm]
  apply_fun (· * algebraMap K[X] W.A (C W.Δ⁻¹)) at H
  rw [← mul_assoc, H, ← map_mul, ← C_mul, mul_inv_cancel₀ h', map_one, map_one]

end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of units modulo squares of `W.A`. -/
noncomputable abbrev M : Type _ := W.Aˣ ⧸ (powMonoidHom (α := W.Aˣ) 2).range

-- This gives a time-out without bumping `maxSynthPendingDepth`.
set_option maxSynthPendingDepth 2 in
instance : IsMulCommutative W.Aˣ := inferInstance

@[simp] lemma M_mul_self (m : W.M) : m * m = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  rw [QuotientGroup.mk'_apply, ← sq, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr <| by simp

set_option maxSynthPendingDepth 2 in
noncomputable instance : CommGroup W.M := inferInstance

variable [DecidableEq K] [W.IsShortNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ =>
    if hx : W.f.eval x = 0
      then (isUnit_sub_theta_add_eval_fCofactor_of_eval_f_eq_zero hx).unit
      else (isUnit_sub_theta_of_eval_f_ne_zero hx).unit

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some_of_f_eval_eq_zero {x y : K} (h : W.Nonsingular x y) (hx : W.f.eval x = 0) :
    W.μ₀ (.some x y h) = (isUnit_sub_theta_add_eval_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μ₀, dif_pos hx]

@[simp] lemma μ₀_some_of_f_eval_ne_zero {x y : K} (h : W.Nonsingular x y) (hx : W.f.eval x ≠ 0) :
    W.μ₀ (.some x y h) = (isUnit_sub_theta_of_eval_f_ne_zero hx).unit := by
  simp only [μ₀, dif_neg hx]

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_⟩
  have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
    by_contra H
    simp [add_of_Y_eq H.1 H.2] at hPQR
  have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
  rw [neg_eq_iff_eq_neg] at this
  convert this using 1
  · congr
    rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
    grind
  · simp [addPolynomial, polynomial]

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h =>
    rw [Point.neg_some h]
    have h' : W.Nonsingular x (W.negY x y) := (nonsingular_neg x y).mpr h
    rcases eq_or_ne (W.f.eval x) 0 with H | H
    · rw [μ₀_some_of_f_eval_eq_zero h H, μ₀_some_of_f_eval_eq_zero h' H, M_mul_self]
    · rw [μ₀_some_of_f_eval_ne_zero h H, μ₀_some_of_f_eval_ne_zero h' H, M_mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

omit [W.IsElliptic] in
private lemma xQ_ne_xP_of_eq_zero (h : W.f.eval xP = 0) : xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_x_eq_zero hP.1 h, y_eq_zero_of_eval_f_x_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp [negY], zero_add]
  exact some_ne_zero hR

lemma μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero (h : W.f.eval xP = 0) :
    μ₀ (some xP yP hP) * μ₀ (some xQ yQ hQ) * μ₀ (some xR yR hR) = 1 := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eq_zero hP hQ hR hPQR h
  have hPR : xR ≠ xP := by rw [add_right_comm] at hPQR; exact xQ_ne_xP_of_eq_zero hP hR hQ hPQR h


  sorry

lemma μ₀_some_mul_μ₀_some_mul_μ₀_some :
    μ₀ (some xP yP hP) * μ₀ (some xQ yQ hQ) * μ₀ (some xR yR hR) = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (μ₀ (Point.some xP yP hP))]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero hR hP hQ hPQR HR
  rw [μ₀_some_of_f_eval_ne_zero hP HP, μ₀_some_of_f_eval_ne_zero hQ HQ,
    μ₀_some_of_f_eval_ne_zero hR HR]
  obtain ⟨pol, hpol⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  simp only [MonoidHom.mem_range, powMonoidHom_apply, ← IsUnit.unit_mul,
    exists_unit_pow_eq_isUnitUnit_iff]
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P with
  | 0 =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP =>
    match Q with
    | 0 =>
      rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
      rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
    | .some xQ yQ hQ =>
      match R with
      | 0 =>
        rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
        rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
      | .some xR yR hR =>
        exact μ₀_some_mul_μ₀_some_mul_μ₀_some hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

end Affine

end WeierstrassCurve
