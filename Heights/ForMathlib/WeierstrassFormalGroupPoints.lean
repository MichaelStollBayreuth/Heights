import Heights.ForMathlib.WeierstrassFormalGroup

/-!
# 𝔪-adic evaluation of the formal group data of a Weierstrass curve

For a Weierstrass curve `W` over a complete adic local ring `O` (the standing setting of
the vendored `p`-adic kit), the fixed-point series `w` and the chord data evaluate at
parameters `t` in the maximal ideal via `ChabautyColeman.MvPSeries.eval`.  This file
provides that evaluation layer: the value `W.wEval t`, its defining Weierstrass fixed-point
equation, the factorization `w(t) = t³·v(t)` with `v(t) ≡ 1 mod 𝔪`, and the uniqueness of
solutions of the fixed-point equation in `𝔪`.  This is the analytic input for the
equivalence between the `𝔪`-points of the formal group and the kernel of reduction
`E₁(K_v)` (Silverman, VII.2.2).
-/

open ChabautyColeman IsLocalRing MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- An element of `1 + 𝔪` in a local ring is a unit. -/
theorem _root_.IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal {u : O}
    (h : u - 1 ∈ maximalIdeal O) : IsUnit u := by
  by_contra hu
  have h1 : (1 : O) ∈ maximalIdeal O := by
    have h2 := Ideal.sub_mem _ ((mem_maximalIdeal u).mpr hu) h
    simp only [sub_sub_cancel] at h2
    exact h2
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable (W : WeierstrassCurve O)

/-- The Weierstrass fixed-point polynomial: the right-hand side of the equation
`w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³` satisfied by `w = w(t)`. -/
def wPoly (t r : O) : O :=
  t ^ 3 + W.a₁ * t * r + W.a₂ * t ^ 2 * r + W.a₃ * r ^ 2 + W.a₄ * t * r ^ 2 + W.a₆ * r ^ 3

/-- Solutions in `𝔪` of the Weierstrass fixed-point equation at a parameter `t ∈ 𝔪` are
unique: the difference of two solutions is contracted by a factor in `𝔪`. -/
theorem eq_of_wPoly_fixed {t r r' : O} (ht : t ∈ maximalIdeal O) (hr : r ∈ maximalIdeal O)
    (hr' : r' ∈ maximalIdeal O) (h : r = W.wPoly t r) (h' : r' = W.wPoly t r') : r = r' := by
  have hm : W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (r + r') + W.a₄ * t * (r + r') +
      W.a₆ * (r ^ 2 + r * r' + r' ^ 2) ∈ maximalIdeal O := by
    refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact Ideal.mul_mem_left _ _ ht
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ht 2 two_pos)
    · exact Ideal.mul_mem_left _ _ (add_mem hr hr')
    · exact Ideal.mul_mem_left _ _ (add_mem hr hr')
    · exact Ideal.mul_mem_left _ _ (add_mem (add_mem (Ideal.pow_mem_of_mem _ hr 2 two_pos)
        (Ideal.mul_mem_right _ _ hr)) (Ideal.pow_mem_of_mem _ hr' 2 two_pos))
  have hkey : (1 - (W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (r + r') +
      W.a₄ * t * (r + r') + W.a₆ * (r ^ 2 + r * r' + r' ^ 2))) * (r - r') = 0 := by
    simp only [wPoly] at h h'
    linear_combination h - h'
  have hu : IsUnit (1 - (W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (r + r') +
      W.a₄ * t * (r + r') + W.a₆ * (r ^ 2 + r * r' + r' ^ 2))) :=
    IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal (by simpa using neg_mem hm)
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hkey)

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- The value of the fixed-point series `w` at a parameter `t`. -/
noncomputable def wEval (t : O) : O := MvPSeries.eval (fun _ : Unit ↦ t) W.wSeries

/-- The value of the unit-part series `v` (with `w = t³·v`) at a parameter `t`. -/
noncomputable def vEval (t : O) : O := MvPSeries.eval (fun _ : Unit ↦ t) W.vSeries

variable {t : O} (ht : t ∈ maximalIdeal O)

include ht

theorem wEval_mem : W.wEval t ∈ maximalIdeal O :=
  MvPSeries.eval_mem_maximalIdeal (MvPSeries.hasEval_of_mem fun _ ↦ ht) (fun _ ↦ ht)
    W.wSeries (by rw [W.constantCoeff_wSeries_mv]; exact zero_mem _)

/-- The value of `w` satisfies the Weierstrass fixed-point equation. -/
theorem wEval_eq : W.wEval t = W.wPoly t (W.wEval t) := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.wSeries_eq
  simp only [map_add, map_mul, map_pow, MvPSeries.evalRingHom_apply] at h
  rw [show (PowerSeries.C : O →+* PowerSeries O) = MvPowerSeries.C from rfl,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl] at h
  simp only [MvPSeries.eval_C, MvPSeries.eval_X] at h
  exact h.trans (by rw [wPoly, wEval])

/-- The factorization `w(t) = t³ · v(t)` of the value of `w`. -/
theorem wEval_eq_cube_mul : W.wEval t = t ^ 3 * W.vEval t := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.wSeries_eq_X_pow_three_mul
  simp only [map_mul, map_pow, MvPSeries.evalRingHom_apply,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
    MvPSeries.eval_X] at h
  exact h

theorem vEval_sub_one_mem : W.vEval t - 1 ∈ maximalIdeal O := by
  have h := MvPSeries.eval_sub_constantCoeff_mem (MvPSeries.hasEval_of_mem fun _ ↦ ht)
    (fun _ ↦ ht) W.vSeries
  rwa [show MvPowerSeries.constantCoeff W.vSeries = PowerSeries.constantCoeff W.vSeries
    from rfl, W.constantCoeff_vSeries] at h

theorem isUnit_vEval : IsUnit (W.vEval t) :=
  IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal (W.vEval_sub_one_mem ht)

omit ht in
theorem wEval_ne_zero [IsDomain O] (ht : t ∈ maximalIdeal O) (ht0 : t ≠ 0) :
    W.wEval t ≠ 0 := by
  rw [W.wEval_eq_cube_mul ht]
  exact mul_ne_zero (pow_ne_zero 3 ht0) (W.isUnit_vEval ht).ne_zero

end WeierstrassCurve

/-!
### The kernel of reduction as the image of the `𝔪`-points of the formal group

Over `𝒪_v`, the parameter `t ∈ 𝔪` of a point of the formal group gives the affine point
`(t/w(t), -1/w(t))` of `E(K_v)`, with `v(x) = v(t)⁻²`, so `t ∈ 𝔪^(n+1)` corresponds to
the filtration step `E_{n+1}(K_v)`.
-/

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
  {t : v.adicCompletionIntegers K}

private lemma algebraMap_eq_coe (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x =
      (x : v.adicCompletion K) := rfl

section

include hW

private lemma coe_a₁ : ((W₀.a₁ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₁ := by
  rw [← hW, WeierstrassCurve.map_a₁, algebraMap_eq_coe]

private lemma coe_a₂ : ((W₀.a₂ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₂ := by
  rw [← hW, WeierstrassCurve.map_a₂, algebraMap_eq_coe]

private lemma coe_a₃ : ((W₀.a₃ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₃ := by
  rw [← hW, WeierstrassCurve.map_a₃, algebraMap_eq_coe]

private lemma coe_a₄ : ((W₀.a₄ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₄ := by
  rw [← hW, WeierstrassCurve.map_a₄, algebraMap_eq_coe]

private lemma coe_a₆ : ((W₀.a₆ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₆ := by
  rw [← hW, WeierstrassCurve.map_a₆, algebraMap_eq_coe]

/-- On an affine point of the kernel of reduction, `v(y)² = v(x)³`; in particular `y ≠ 0`,
and the parameter `-x/y` and the value `-1/y` lie in the maximal ideal. -/
private lemma valued_of_mem {x y : v.adicCompletion K} (hxy : W.Equation x y)
    (hx : exp (2 : ℤ) ≤ Valued.v x) :
    y ≠ 0 ∧ Valued.v (-x / y) ≤ exp (-1 : ℤ) ∧ Valued.v (-1 / y) ≤ exp (-1 : ℤ) := by
  have hcoeff : ∀ a : v.adicCompletionIntegers K, Valued.v (a : v.adicCompletion K) ≤ 1 :=
    fun a ↦ by have h := a.2; rwa [mem_adicCompletionIntegers] at h
  have ha₁ : Valued.v W.a₁ ≤ 1 := coe_a₁ hW ▸ hcoeff W₀.a₁
  have ha₂ : Valued.v W.a₂ ≤ 1 := coe_a₂ hW ▸ hcoeff W₀.a₂
  have ha₃ : Valued.v W.a₃ ≤ 1 := coe_a₃ hW ▸ hcoeff W₀.a₃
  have ha₄ : Valued.v W.a₄ ≤ 1 := coe_a₄ hW ▸ hcoeff W₀.a₄
  have ha₆ : Valued.v W.a₆ ≤ 1 := coe_a₆ hW ▸ hcoeff W₀.a₆
  set A := Valued.v x with hA
  have hA1 : (1 : ℤᵐ⁰) < A :=
    lt_of_lt_of_le (by rw [← exp_zero]; exact exp_lt_exp.mpr (by lia)) hx
  have hA0 : A ≠ 0 := (zero_lt_one.trans hA1).ne'
  set B := Valued.v y with hB
  have heq' : y ^ 2 + (W.a₁ * x * y + W.a₃ * y) =
      x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) := by
    linear_combination (W.equation_iff x y).mp hxy
  have hval := congrArg Valued.v heq'
  have hApow : A ^ 2 < A ^ 3 := pow_lt_pow_right₀ hA1 (by lia)
  -- the right-hand side has valuation `A³`
  have hRHS : Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = A ^ 3 := by
    have h1 : Valued.v (W.a₂ * x ^ 2) ≤ A ^ 2 := by
      rw [map_mul, map_pow]
      exact (mul_le_mul' ha₂ le_rfl).trans_eq (one_mul _)
    have h2 : Valued.v (W.a₄ * x) ≤ A ^ 2 := by
      rw [map_mul]
      exact ((mul_le_mul' ha₄ le_rfl).trans_eq (one_mul _)).trans
        (le_self_pow hA1.le (by lia))
    have h3 : Valued.v W.a₆ ≤ A ^ 2 := ha₆.trans (hA1.le.trans (le_self_pow hA1.le (by lia)))
    have hlow : Valued.v (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) < A ^ 3 :=
      lt_of_le_of_lt ((Valued.v.map_add _ _).trans
        (max_le h1 ((Valued.v.map_add _ _).trans (max_le h2 h3)))) hApow
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hlow), map_pow]
  -- `B ≤ A` is impossible: the left-hand side would be too small
  have hBA : A < B := by
    by_contra hle
    push Not at hle
    have h1 : Valued.v (y ^ 2) ≤ A ^ 2 := by
      rw [map_pow]
      exact pow_le_pow_left' hle 2
    have h2 : Valued.v (W.a₁ * x * y) ≤ A ^ 2 := by
      rw [map_mul, map_mul]
      calc Valued.v W.a₁ * A * B ≤ 1 * A * A := mul_le_mul' (mul_le_mul' ha₁ le_rfl) hle
        _ = A ^ 2 := by rw [one_mul, sq]
    have h3 : Valued.v (W.a₃ * y) ≤ A ^ 2 := by
      rw [map_mul]
      exact ((mul_le_mul' ha₃ hle).trans_eq (one_mul _)).trans (le_self_pow hA1.le (by lia))
    have hLHS_le : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) ≤ A ^ 2 :=
      (Valued.v.map_add _ _).trans
        (max_le h1 ((Valued.v.map_add _ _).trans (max_le h2 h3)))
    rw [hval, hRHS] at hLHS_le
    exact absurd hLHS_le (not_le.mpr hApow)
  have hB1 : (1 : ℤᵐ⁰) < B := hA1.trans hBA
  have hB0 : B ≠ 0 := (zero_lt_one.trans hB1).ne'
  have hy0 : y ≠ 0 := by
    intro h
    rw [hB, h, map_zero] at hBA
    simp at hBA
  -- the left-hand side has valuation `B²`, so `B² = A³`
  have hBA3 : B ^ 2 = A ^ 3 := by
    have h2 : Valued.v (W.a₁ * x * y) < B ^ 2 := by
      rw [map_mul, map_mul]
      calc Valued.v W.a₁ * A * B ≤ 1 * A * B := mul_le_mul' (mul_le_mul' ha₁ le_rfl) le_rfl
        _ = A * B := by rw [one_mul]
        _ < B * B := mul_lt_mul_of_pos_right hBA (zero_lt_one.trans hB1)
        _ = B ^ 2 := (sq B).symm
    have h3 : Valued.v (W.a₃ * y) < B ^ 2 := by
      rw [map_mul]
      calc Valued.v W.a₃ * B ≤ 1 * B := mul_le_mul' ha₃ le_rfl
        _ = B := one_mul B
        _ < B ^ 2 := by
          calc B = B ^ 1 := (pow_one B).symm
            _ < B ^ 2 := pow_lt_pow_right₀ hB1 (by lia)
    have hsum : Valued.v (W.a₁ * x * y + W.a₃ * y) < B ^ 2 :=
      lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt h2 h3)
    have hLHS : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = B ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hsum), map_pow]
    rw [← hLHS, hval, hRHS]
  -- pass to exponents
  obtain ⟨a, ha⟩ : ∃ a : ℤ, A = exp a := ⟨log A, (exp_log hA0).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, B = exp b := ⟨log B, (exp_log hB0).symm⟩
  have h2a : (2 : ℤ) ≤ a := by rwa [ha, exp_le_exp] at hx
  have h23 : 2 * b = 3 * a := by
    have h := hBA3
    rw [ha, hb, ← exp_nsmul, ← exp_nsmul, exp_inj] at h
    push_cast [nsmul_eq_mul] at h
    exact h
  refine ⟨hy0, ?_, ?_⟩
  · rw [map_div₀, Valuation.map_neg, ← hA, ← hB, ha, hb, ← exp_sub, exp_le_exp]
    lia
  · rw [map_div₀, Valuation.map_neg, map_one, ← hB, hb, ← exp_zero, ← exp_sub, exp_le_exp]
    lia

end

/-- The valuation of the `x`-coordinate `t/w(t)` is `v(t)⁻²`. -/
theorem valued_formalPoint_x
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (ht0 : t ≠ 0) :
    Valued.v ((t : v.adicCompletion K) / (W₀.wEval t : v.adicCompletion K)) =
      (Valued.v (t : v.adicCompletion K))⁻¹ ^ 2 := by
  have hvE : Valued.v ((W₀.vEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    obtain ⟨u, hu⟩ := W₀.isUnit_vEval ht
    have hmulinv : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
          v.adicCompletion K) = 1 := by
      have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
        u.mul_inv
      push_cast at h
      exact h
    have h1 := congrArg Valued.v hmulinv
    rw [map_mul, map_one] at h1
    have h2 := ((u : v.adicCompletionIntegers K)).2
    have h3 := (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)).2
    rw [mem_adicCompletionIntegers] at h2 h3
    rw [← hu]
    refine le_antisymm h2 ?_
    calc (1 : ℤᵐ⁰) = _ * _ := h1.symm
      _ ≤ Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * 1 := by gcongr
      _ = _ := mul_one _
  have hw : ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (t : v.adicCompletion K) ^ 3 * ((W₀.vEval t : v.adicCompletionIntegers K) :
        v.adicCompletion K) := by
    rw [W₀.wEval_eq_cube_mul ht]
    push_cast
    rfl
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact ht0
  rw [map_div₀, hw, map_mul, map_pow, hvE, mul_one, inv_pow, pow_succ',
    div_mul_eq_div_div, div_self ht0', one_div]

variable [DecidableEq (v.adicCompletion K)] [W.IsElliptic]

include hW in
/-- The parametrized point of the kernel of reduction attached to a parameter `t ∈ 𝔪`,
`t ≠ 0`, is nonsingular. -/
theorem formalPoint_nonsingular
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (ht0 : t ≠ 0) :
    W.Nonsingular ((t : v.adicCompletion K) / (W₀.wEval t : v.adicCompletion K))
      (-1 / (W₀.wEval t : v.adicCompletion K)) := by
  refine W.chord_point_nonsingular ?_ ?_ W.isUnit_Δ.ne_zero
  · have h := congrArg (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      (W₀.wEval_eq ht)
    rw [wPoly] at h
    simp only [map_add, map_mul, map_pow, algebraMap_eq_coe] at h
    rw [← hW]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, algebraMap_eq_coe]
    exact h
  · simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact W₀.wEval_ne_zero ht ht0

/-- The point of the kernel of reduction attached to an `𝔪`-point of the formal group of
the integral model `W₀`: the parameter `t` gives the affine point `(t/w(t), -1/w(t))`,
and `t = 0` gives the point at infinity. -/
noncomputable def formalPoint (z : W₀.formalGroupLaw.Points) : W.Point :=
  if h0 : (z () : v.adicCompletionIntegers K) = 0 then 0
  else .some _ _ (formalPoint_nonsingular hW (z ()).2 h0)

@[simp]
lemma formalPoint_of_param_eq_zero {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) = 0) : formalPoint hW z = 0 :=
  dif_pos h0

lemma formalPoint_of_param_ne_zero {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0) :
    formalPoint hW z = .some _ _ (formalPoint_nonsingular hW (z ()).2 h0) :=
  dif_neg h0

/-- The filtration correspondence: the parameter lies in `𝔪^(n+1)` exactly when the
associated point lies in the filtration step `E_{n+1}(K_v)`. -/
theorem mem_pow_iff_formalPoint_mem_filtration (z : W₀.formalGroupLaw.Points) (n : ℕ) :
    (z () : v.adicCompletionIntegers K) ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
      formalPoint hW z ∈ filtration hW n := by
  rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0
  · simp [h0]
  · rw [formalPoint_of_param_ne_zero hW h0, some_mem_filtration,
      valued_formalPoint_x (z ()).2 h0, mem_maximalIdeal_pow_iff]
    have ht0' : Valued.v ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
      simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
      simpa using h0
    obtain ⟨m, hm⟩ : ∃ m : ℤ,
        Valued.v ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) = exp m :=
      ⟨_, (exp_log ht0').symm⟩
    rw [hm, ← exp_neg, ← exp_nsmul, exp_le_exp, exp_le_exp, nsmul_eq_mul]
    push_cast
    constructor <;> intro h <;> lia

/-- The parametrization of the kernel of reduction is injective. -/
theorem formalPoint_injective : Function.Injective (formalPoint hW) := by
  intro z z' h
  have key : (z () : v.adicCompletionIntegers K) = z' () := by
    rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0 <;>
      rcases eq_or_ne (z' () : v.adicCompletionIntegers K) 0 with h0' | h0'
    · rw [h0, h0']
    · rw [formalPoint_of_param_eq_zero hW h0, formalPoint_of_param_ne_zero hW h0'] at h
      exact absurd h.symm (by simp)
    · rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_eq_zero hW h0'] at h
      exact absurd h (by simp)
    · rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_ne_zero hW h0'] at h
      simp only [Point.some.injEq] at h
      obtain ⟨hX, hY⟩ := h
      have hw0 : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := by
        simp only [ne_eq, ZeroMemClass.coe_eq_zero]
        exact W₀.wEval_ne_zero (z ()).2 h0
      have hw0' : ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := by
        simp only [ne_eq, ZeroMemClass.coe_eq_zero]
        exact W₀.wEval_ne_zero (z' ()).2 h0'
      have hw : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
          ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        field_simp at hY
        exact (neg_injective hY).symm
      rw [hw, div_eq_div_iff hw0' hw0'] at hX
      exact_mod_cast mul_right_cancel₀ hw0' hX
  funext i
  exact Subtype.ext key

/-- Every point of the kernel of reduction comes from a parameter in `𝔪`:
the parametrization by the `𝔪`-points of the formal group is surjective onto
`filtration hW 0`. -/
theorem formalPoint_surjective {P : W.Point} (hP : P ∈ filtration hW 0) :
    ∃ z : W₀.formalGroupLaw.Points, formalPoint hW z = P := by
  match P with
  | .zero => exact ⟨0, formalPoint_of_param_eq_zero hW (by simp)⟩
  | .some x y h =>
    rw [some_mem_filtration] at hP
    have hx : exp (2 : ℤ) ≤ Valued.v x := by
      convert hP using 2
      norm_num
    obtain ⟨hy0, hs, hr⟩ := valued_of_mem hW h.left hx
    have hexp1 : (exp (-1 : ℤ) : ℤᵐ⁰) ≤ 1 := by
      rw [← exp_zero, exp_le_exp]
      lia
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx
      simp at hx
    set t : v.adicCompletionIntegers K :=
      ⟨-x / y, by rw [mem_adicCompletionIntegers]; exact hs.trans hexp1⟩ with htdef
    set r : v.adicCompletionIntegers K :=
      ⟨-1 / y, by rw [mem_adicCompletionIntegers]; exact hr.trans hexp1⟩ with hrdef
    have htm : t ∈ maximalIdeal (v.adicCompletionIntegers K) := by
      have hiff := mem_maximalIdeal_pow_iff (K := K) (x := t) (n := 1)
      rw [pow_one] at hiff
      exact hiff.mpr hs
    have hrm : r ∈ maximalIdeal (v.adicCompletionIntegers K) := by
      have hiff := mem_maximalIdeal_pow_iff (K := K) (x := r) (n := 1)
      rw [pow_one] at hiff
      exact hiff.mpr hr
    have ht0 : t ≠ 0 := by
      intro hteq
      have h0 : (-x / y : v.adicCompletion K) = 0 := congrArg Subtype.val hteq
      rw [div_eq_zero_iff, neg_eq_zero] at h0
      exact h0.elim hx0 hy0
    -- `-1/y` satisfies the Weierstrass fixed-point equation at the parameter `-x/y`
    have hfixK : (-1 / y : v.adicCompletion K) =
        (-x / y) ^ 3 + W.a₁ * (-x / y) * (-1 / y) + W.a₂ * (-x / y) ^ 2 * (-1 / y) +
          W.a₃ * (-1 / y) ^ 2 + W.a₄ * (-x / y) * (-1 / y) ^ 2 + W.a₆ * (-1 / y) ^ 3 := by
      have heq := (W.equation_iff x y).mp h.left
      field_simp
      linear_combination -heq
    have hfixO : r = W₀.wPoly t r := by
      refine Subtype.coe_injective ?_
      rw [wPoly]
      push_cast
      rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW]
      exact hfixK
    have huniq : W₀.wEval t = r :=
      W₀.eq_of_wPoly_fixed htm (W₀.wEval_mem htm) hrm (W₀.wEval_eq htm) hfixO
    refine ⟨fun _ ↦ ⟨t, htm⟩, ?_⟩
    rw [formalPoint_of_param_ne_zero hW ht0]
    simp only [Point.some.injEq]
    have hrcoe : ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = -1 / y := by
      rw [huniq]
    constructor
    · rw [hrcoe]
      show (-x / y) / (-1 / y) = x
      field_simp
    · rw [hrcoe]
      show -1 / (-1 / y) = y
      field_simp

/-- The `𝔪`-points of the formal group law of an integral model `W₀` of `W` are the kernel
of reduction `E₁(K_v) = filtration hW 0`, via `z ↦ (x, y)` with `x = z/w(z)`,
`y = -1/w(z)`; the equivalence matches the filtration by valuation on both sides
(Silverman, VII.2.2). -/
theorem exists_points_equiv_filtration :
    ∃ θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0,
      ∀ (z : W₀.formalGroupLaw.Points) (n : ℕ),
        ((z () : v.adicCompletionIntegers K) ∈
            maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
          ((θ z : filtration hW 0) : W.Point) ∈ filtration hW n) :=
  sorry

end WeierstrassCurve.Affine
