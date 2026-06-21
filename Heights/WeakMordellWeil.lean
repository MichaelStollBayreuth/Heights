import Mathlib.GroupTheory.QuotientGroup.Defs
import Heights.EllipticCurve

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite when `E` is an elliptic curve
over a number field `K`.

We will use the `x-T` map approach. At least for now, we will restrict to elliptic curves
given by a short Weierstrass equation `y² = x³ + ax + b =: f(x)`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   => done.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
   => done (the bare map is defined as `μ₀`).
3. Show that `μ` is a group homomorphism.
   => done.
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

section Polynomial

variable {K : Type*} [Field K]

lemma Polynomial.isRelPrime_X_sub_C_X_sub_C_of_ne {a b : K} (h : a ≠ b) :
    IsRelPrime (X - C a) (X - C b) := by
  rwa [isRelPrime_comm, Irreducible.isRelPrime_iff_not_dvd (irreducible_X_sub_C b), dvd_iff_isRoot,
    root_X_sub_C]

end Polynomial

end API

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

lemma ringChar_ne_two_of_isElliptic_of_isShortNF [W.IsElliptic] [W.IsShortNF] :
    ringChar K ≠ 2 := by
  have := W.isUnit_Δ.ne_zero
  contrapose! this
  rw [Δ_of_isShortNF W, show (16 : K) = (2 :) * 8 by norm_num]
  nth_rewrite 1 [← this]
  simp

/-!
### Step 1: define `A`
-/

/-- The `a` coefficient of a short Weierstrass curve. -/
abbrev a : K := W.a₄

/-- The `b` coefficient of a short Weierstrass curve. -/
abbrev b : K := W.a₆

open Polynomial

/-- The polynomial on the right hand side of a short Weierstrass equation. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a * X + C W.b

lemma separable_f [W.IsElliptic] [W.IsShortNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [f, separable_def',
    show derivative (X ^ 3 + C W.a * X + C W.b) = C 3 * X ^ 2 + C W.a by simp [C_ofNat]; norm_num]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a) * X - C (432 * W.b)),
    C (W.Δ)⁻¹ * (C (-96 * W.a) * X ^ 2 + C (144 * W.b) * X + C (-64 * W.a ^ 2)), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isShortNF, a, b]
  simp only [C_eq_algebraMap]
  algebra

lemma equation_iff_eval_f_x_eq_y_pow_two {W : Affine K} [W.IsElliptic] [W.IsShortNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [Affine.equation_iff x y, eq_comm]
  simp [f, a, b]

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] := X ^ 2 + C x * X + C (x ^ 2 + W.a)

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp [fCofactor, f]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have hP₀ : W.f.eval xP = 0 := by rw [hf]; simp
  have hQ₀ : W.f.eval xQ = 0 := by rw [hf]; simp
  have hR₀ : W.f.eval xR = 0 := by rw [hf]; simp
  refine ⟨?_, ?_, ?_⟩
  · refine mul_left_cancel₀ (X_sub_C_ne_zero xP) ?_
    rw [← mul_assoc, ← hf, W.f_eq_mul_of_eval_eq_zero hP₀, mul_comm]
  · refine mul_left_cancel₀ (X_sub_C_ne_zero xQ) ?_
    rw [mul_comm, ← W.f_eq_mul_of_eval_eq_zero hQ₀, hf, ← mul_assoc, mul_comm (X - C xP)]
  · refine mul_left_cancel₀ (X_sub_C_ne_zero xR) ?_
    rw [mul_comm, ← W.f_eq_mul_of_eval_eq_zero hR₀, hf, ← mul_assoc, ← mul_rotate]

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

/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivAKA' [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  letI eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivAKA'_apply [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivAKA' hx (algebraMap K[X] W.A p) = (p.eval x, algebraMap K[X] (W.A' x) p) :=
  rfl

example {R S : Type*} [Ring R] [Ring S] (f : R ≃+* S) (x y : R) : x = y ↔ f x = f y := by
  exact Iff.symm (EquivLike.apply_eq_iff_eq f)

lemma eq_in_A_iff [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    algebraMap K[X] W.A p = algebraMap K[X] W.A q ↔
      p.eval x = q.eval x ∧ algebraMap K[X] (W.A' x) p = algebraMap K[X] (W.A' x) q := by
  rw [← EquivLike.apply_eq_iff_eq <| W.equivAKA' hx]
  simpa only [equivAKA'_apply] using Prod.mk_inj

lemma isUnit_in_A_iff [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (algebraMap K[X] W.A p) ↔ IsUnit (p.eval x) ∧ IsUnit (algebraMap K[X] (W.A' x) p) := by
  let e := W.equivAKA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivAKA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, algebraMap K[X] (W.A' x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivAKA'_apply hx]

variable {W}

lemma isUnit_algebraMap_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
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

lemma isUnit_algebraMap_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| algebraMap K[X] W.A <| C x - X + W.fCofactor x := by
  rw [isUnit_in_A_iff W h]
  have H₀ : 3 * x ^ 2 + W.a ≠ 0 := three_sq_add_a_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + W.a := by
    simp; ring
  have H₂ : (algebraMap K[X] (W.A' x)) (C x - X + W.fCofactor x) =
      algebraMap K[X] (W.A' x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := algebraMap K[X] (W.A' x) <| C (3 * x ^ 2 + W.a)⁻¹ * (X + C (2 * x))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + a W)⁻¹ * (X + C (2 * x))) = C (3 * x ^ 2 + a W)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + W.a) * ·) using mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp

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
      then (isUnit_algebraMap_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
      else (isUnit_algebraMap_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some_of_f_eval_eq_zero {x y : K} (h : W.Nonsingular x y) (hx : W.f.eval x = 0) :
    W.μ₀ (.some x y h) = (isUnit_algebraMap_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μ₀, dif_pos hx]

@[simp] lemma μ₀_some_of_f_eval_ne_zero {x y : K} (h : W.Nonsingular x y) (hx : W.f.eval x ≠ 0) :
    W.μ₀ (.some x y h) = (isUnit_algebraMap_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μ₀, dif_neg hx]

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

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

lemma μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero_of_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    μ₀ (some xP yP hP) * μ₀ (some xQ yQ hQ) * μ₀ (some xR yR hR) = 1 := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eq_zero hP hQ hR hPQR h₁
  have hPR : xR ≠ xP := by
    rw [add_right_comm] at hPQR
    exact xQ_ne_xP_of_eq_zero hP hR hQ hPQR h₁
  have hQR : xR ≠ xQ := by
    rw [add_rotate] at hPQR
    exact xQ_ne_xP_of_eq_zero hQ hR hP hPQR h₂
  have hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
    obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
    have hpol₀ : pol = 0 := by
      refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        apply_fun (·.eval x) at hpol
        rcases hx with rfl | rfl <;>
          rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
          simpa using hpol
      · grind
    rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  have hrp₁ : IsRelPrime ((X - C xP) * (X - C xQ)) (X - C xR) := by
    rw [IsRelPrime.mul_left_iff]
    exact ⟨isRelPrime_X_sub_C_X_sub_C_of_ne hPR.symm,
      isRelPrime_X_sub_C_X_sub_C_of_ne hQR.symm⟩
  rw [μ₀_some_of_f_eval_eq_zero hP h₁, μ₀_some_of_f_eval_eq_zero hQ h₂,
    μ₀_some_of_f_eval_eq_zero hR h₃]
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  simp only [MonoidHom.mem_range, powMonoidHom_apply, ← IsUnit.unit_mul,
    exists_unit_pow_eq_isUnitUnit_iff, hfcP, hfcQ, hfcR]
  simp only [show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
    (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  have key {a b c : W.A} (h : a * b * c = 0) :
      (a * b + a * c + b * c) ^ 2 = ((b * c - a) * (a * c - b) * (a * b - c)) := by
    have : (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * (a * b * c) = 0 := by
      simp [h]
    conv_rhs => rw [← add_zero (_ * _ * _), ← this]
    ring
  rw [← key <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

lemma μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero (h : W.f.eval xP = 0) :
    μ₀ (some xP yP hP) * μ₀ (some xQ yQ hQ) * μ₀ (some xR yR hR) = 1 := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eq_zero hP hQ hR hPQR h
  have hPR : xR ≠ xP := by rw [add_right_comm] at hPQR; exact xQ_ne_xP_of_eq_zero hP hR hQ hPQR h
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero_of_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μ₀_some_mul_μ₀_some_mul_μ₀_some_of_eq_zero_of_eq_zero hP hR hQ hPQR h hR₀
  rw [μ₀_some_of_f_eval_eq_zero hP h, μ₀_some_of_f_eval_ne_zero hQ hQ₀,
    μ₀_some_of_f_eval_ne_zero hR hR₀]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  simp only [MonoidHom.mem_range, powMonoidHom_apply, ← IsUnit.unit_mul,
    exists_unit_pow_eq_isUnitUnit_iff]
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    have : eval xP pol = 0 := by simpa using hpol
    rw [← IsRoot.def, ← dvd_iff_isRoot] at this
    obtain ⟨p, rfl⟩ := this
    rw [mul_comm]
    suffices p.natDegree = 0 by
      rw [natDegree_eq_zero] at this
      obtain ⟨γ, rfl⟩ := this
      exact ⟨_, rfl⟩
    contrapose! hpol₁
    replace hpol₁ : 1 ≤ p.natDegree := by lia
    rw [natDegree_mul (X_sub_C_ne_zero _) (ne_zero_of_natDegree_gt hpol₁), natDegree_X_sub_C xP]
    lia
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  have key {a b c d e : W.A} (had : a * d = 0) (h : b * c = d - e ^ 2 * a) :
      (d + e * a) ^ 2 = (d - a) * b * c := by
    grobner
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← key (e := algebraMap K[X] W.A (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

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
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
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

/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/-- A criterion for a nonsingular point in affine coordinates to be divisble by 2. -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ ?_, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  · match P with
    | 0 => simp at hP -- cannot occur
    | .some ξ η h' =>
      rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate, Point.neg_some] at hP
      have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
      obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero H H h hP
      rw [← sq] at hpol
      obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
      exact ⟨_, _, _, hpol⟩
  · have : ringChar K ≠ 2 := ringChar_ne_two_of_isElliptic_of_isShortNF W
    have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero this
    have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
        X ^ 3 - C (l ^ 2) * X ^ 2 + C (W.a - 2 * l * m) * X - C (-W.b + m ^ 2) := by
      simp only [f] at H
      convert H using 1 <;> simp only [C_eq_algebraMap] <;> algebra
    have H₂ : x + 2 * ξ = l ^ 2 := by
      apply_fun (fun p ↦ -(p.coeff 2)) at H'
      simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
      simpa using H'
    have H₁ : 2 * x * ξ + ξ ^ 2 = W.a - 2 * l * m := by
      apply_fun (fun p ↦ p.coeff 1) at H'
      simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
      simpa using H'
    have H₀ : x * ξ ^ 2 = -W.b + m ^ 2 := by
      apply_fun (fun p ↦ -(p.coeff 0)) at H'
      simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
      simpa using H'
    have hy₀ : l * ξ + m ≠ 0 := by
      have hΔ := W.isUnit_Δ.ne_zero
      rw [Δ_of_isShortNF W, show W.a₄ = W.a from rfl, show W.a₆ = W.b from rfl] at hΔ
      contrapose! hΔ
      grobner
    have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
      simp only [negY, a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero]
      grind
    have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
      rw [slope_of_Y_ne rfl hy]
      simp only [a₂_of_isShortNF, mul_zero, zero_mul, add_zero, a₁_of_isShortNF,
        sub_zero, negY, a₃_of_isShortNF]
      rw [sub_neg_eq_add, ← two_mul, show W.a₄ = W.a from rfl]
      rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
      field_simp
      grobner
    have heq : W.Equation ξ (l * ξ + m) := by
      rw [equation_iff_eval_f_x_eq_y_pow_two, ← sub_eq_zero, eq_comm]
      apply_fun (·.eval ξ) at H
      simpa using H
    let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
    suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) by
      rcases this with hyp | hyp <;> exact ⟨_, hyp⟩
    conv => enter [2]; rw [smul_neg]
    simp only [P]
    rw [two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX, a₁_of_isShortNF,
      a₂_of_isShortNF, zero_mul, add_zero, sub_zero]
    linear_combination H₂

end Affine

end WeierstrassCurve
