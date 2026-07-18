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
  {v : HeightOneSpectrum R} [DecidableEq (v.adicCompletion K)] [CharZero K]
  [Finite (R ⧸ v.asIdeal)] {W : Affine (v.adicCompletion K)} [W.IsElliptic]
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
  {t : v.adicCompletionIntegers K}

private lemma algebraMap_eq_coe (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x =
      (x : v.adicCompletion K) := rfl

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
