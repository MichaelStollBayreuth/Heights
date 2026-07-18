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

end WeierstrassCurve
