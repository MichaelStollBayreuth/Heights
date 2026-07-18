/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/Series/PSeries.lean`), stripped of the module system.

import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Heights.ForMathlib.Chabauty.AdicTopology

import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Heights.ForMathlib.Chabauty.PadicInt

/-!
# The p-adic kit: evaluation of power series

Evaluation of a power series `h ∈ O⟦X⟧` at a point `z₀` of the maximal ideal of `O`
(`ChabautyColeman.PSeries.eval`), as the convergent sum `∑ aₖ z₀ᵏ`
(`ChabautyColeman.PSeries.hasSum_eval`). This is a thin layer over Mathlib's
`PowerSeries.eval₂`; the point of this file is the standing hypothesis pack of the
whole `p`-adic kit:

`O` is a complete Hausdorff uniform ring that is local with `𝔪`-adic topology
(`[Fact (IsAdic (maximalIdeal O))]`). The model case is `O = ℤ_p`
(`PadicInt.instFactIsAdic`); rings of integers of finite extensions of `ℚ_p` also
qualify. From the `Fact` we derive `IsLinearTopology O O` and topological nilpotency of
the points of `𝔪` (`ChabautyColeman.PSeries.hasEval_of_mem`), which is what Mathlib's
evaluation machinery consumes.

The evaluation calculus: evaluation is a ring homomorphism
(`ChabautyColeman.PSeries.evalRingHom`); it is compatible with the composition
`ChabautyColeman.PSeries.comp` of power series, defined for inner series with constant
coefficient in `𝔪` by evaluating in `O⟦X⟧` with the product topology
(`ChabautyColeman.PSeries.eval_comp`) — this is more general than Mathlib's algebraic
`PowerSeries.subst`, which requires a nilpotent constant coefficient. The formal
derivative computes the first-order behaviour of evaluation, with an explicit
second-order remainder (`ChabautyColeman.PSeries.eval_deriv`).

The setting is complete: `ChabautyColeman.PSeries.instIsAdicComplete` derives
`IsAdicComplete (maximalIdeal O) O` from completeness and separatedness of the adic
topology, so Mathlib's Weierstrass preparation
(`PowerSeries.exists_isWeierstrassFactorization`, uniqueness
`PowerSeries.IsWeierstrassFactorization.elim`) applies to `O⟦X⟧` as-is.

Blueprint nodes: `def:eval`, `lem:eval-hom`, `thm:wprep`.
-/


open PowerSeries IsLocalRing Filter Topology
open scoped PowerSeries.WithPiTopology

namespace ChabautyColeman

namespace PSeries

variable {O : Type*} [CommRing O] [UniformSpace O]

/-- Evaluation of a power series `h ∈ O⟦X⟧` at a point `z₀` of the maximal ideal:
the convergent sum `∑ aₖ z₀ᵏ` (Mathlib's `PowerSeries.eval₂`; the value is junk
for `z₀` outside the maximal ideal). -/
noncomputable def eval (z₀ : O) (h : O⟦X⟧) : O :=
  PowerSeries.eval₂ (RingHom.id O) z₀ h

theorem eval_eq_eval₂ (z₀ : O) (h : O⟦X⟧) : eval z₀ h = PowerSeries.eval₂ (RingHom.id O) z₀ h :=
  rfl

@[simp]
theorem eval_coe (f : Polynomial O) (z₀ : O) : eval z₀ (f : O⟦X⟧) = f.eval z₀ := by
  rw [eval_eq_eval₂, eval₂_coe, Polynomial.eval₂_id]

@[simp]
theorem eval_C (r : O) (z₀ : O) : eval z₀ (C r) = r :=
  eval₂_C _ _ r

@[simp]
theorem eval_X (z₀ : O) : eval z₀ (X : O⟦X⟧) = z₀ :=
  eval₂_X _ _

/-- Composition `h ↦ h(k(X))` of power series, for `k` with constant coefficient in the
maximal ideal (junk otherwise); defined by evaluating `h` at the point `k` of `O⟦X⟧`
with the product topology. In contrast to Mathlib's algebraic `PowerSeries.subst`,
the constant coefficient of `k` need not be nilpotent. -/
noncomputable def comp (k h : O⟦X⟧) : O⟦X⟧ :=
  PowerSeries.eval₂ (C (R := O)) k h

theorem comp_eq_eval₂ (k h : O⟦X⟧) : comp k h = PowerSeries.eval₂ (C (R := O)) k h := rfl

variable [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))]

instance instIsLinearTopology : IsLinearTopology O O :=
  (Fact.out : IsAdic (maximalIdeal O)).isLinearTopology

instance instNonarchimedeanRing : NonarchimedeanRing O :=
  (Fact.out : IsAdic (maximalIdeal O)).nonarchimedeanRing

/-- In a linearly topologized ring, multiplying a null sequence by an arbitrary
sequence gives a null sequence. -/
theorem tendsto_mul_zero_of_tendsto_zero {ι : Type*} {l : Filter ι} {f g : ι → O}
    (hf : Tendsto f l (𝓝 0)) : Tendsto (fun k ↦ f k * g k) l (𝓝 0) := by
  rw [IsLinearTopology.hasBasis_ideal.tendsto_right_iff] at hf ⊢
  intro I hI
  filter_upwards [hf I hI] with k hk
  exact I.mul_mem_right _ hk

theorem isClosed_maximalIdeal : IsClosed ((maximalIdeal O : Ideal O) : Set O) := by
  have := IsAdic.isClosed_pow (I := maximalIdeal O) Fact.out 1
  simpa using this

/-- Points of the maximal ideal are legitimate evaluation points for power series. -/
theorem hasEval_of_mem {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) : PowerSeries.HasEval z₀ :=
  (Fact.out : IsAdic (maximalIdeal O)).isTopologicallyNilpotent_of_mem hz₀

/-- Power series with constant coefficient in the maximal ideal are legitimate
evaluation points in `O⟦X⟧`. -/
theorem hasEval_of_constantCoeff_mem {k : O⟦X⟧} (hk : constantCoeff k ∈ maximalIdeal O) :
    PowerSeries.HasEval k :=
  MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff
    (hasEval_of_mem hk)

variable [IsUniformAddGroup O] [CompleteSpace O]

/-- The adic summability test: a series whose terms lie in growing powers of the
maximal ideal is summable. -/
theorem summable_of_mem_pow {f : ℕ → O} {m : ℕ}
    (hf : ∀ n, f n ∈ maximalIdeal O ^ (n - m)) : Summable f := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop,
    (Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff]
  refine fun i _ ↦ eventually_atTop.mpr ⟨i + m, fun n hn ↦ ?_⟩
  exact Ideal.pow_le_pow_right (by lia) (hf n)

variable [T2Space O]

/-- The standing hypotheses make `O` a complete local ring in the algebraic sense, so
Mathlib's Weierstrass preparation applies to `O⟦X⟧` (blueprint node `thm:wprep`). -/
instance instIsAdicComplete : IsAdicComplete (maximalIdeal O) O :=
  ((Fact.out : IsAdic (maximalIdeal O)).isAdicComplete_iff).mpr ⟨‹_›, ‹_›⟩

-- Weierstrass preparation is available in the standing setting
example (g : O⟦X⟧) (hg : g.map (residue O) ≠ 0) :
    ∃ (W : Polynomial O) (u : O⟦X⟧), g.IsWeierstrassFactorization W u :=
  g.exists_isWeierstrassFactorization hg

variable [IsTopologicalRing O]
variable {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)

include hz₀ in
/-- The defining series of `PSeries.eval` converges. -/
theorem hasSum_eval (h : O⟦X⟧) :
    HasSum (fun k ↦ coeff k h * z₀ ^ k) (eval z₀ h) :=
  hasSum_eval₂ continuous_id (hasEval_of_mem hz₀) h

include hz₀ in
theorem eval_eq_tsum (h : O⟦X⟧) : eval z₀ h = ∑' k, coeff k h * z₀ ^ k :=
  (hasSum_eval hz₀ h).tsum_eq.symm

/-! ### Evaluation as a ring homomorphism (blueprint node `lem:eval-hom`) -/

/-- Evaluation at a point of the maximal ideal, as a ring homomorphism. -/
noncomputable def evalRingHom (hz₀ : z₀ ∈ maximalIdeal O) : O⟦X⟧ →+* O :=
  PowerSeries.eval₂Hom (φ := RingHom.id O) continuous_id (hasEval_of_mem hz₀)

theorem coe_evalRingHom : ⇑(evalRingHom hz₀) = eval z₀ :=
  coe_eval₂Hom (φ := RingHom.id O) continuous_id (hasEval_of_mem hz₀)

@[simp]
theorem evalRingHom_apply (h : O⟦X⟧) : evalRingHom hz₀ h = eval z₀ h :=
  congrFun (coe_evalRingHom hz₀) h

theorem continuous_evalRingHom : Continuous (evalRingHom hz₀) := by
  rw [coe_evalRingHom]
  exact continuous_eval₂ (φ := RingHom.id O) continuous_id (hasEval_of_mem hz₀)

include hz₀

theorem eval_add (h₁ h₂ : O⟦X⟧) : eval z₀ (h₁ + h₂) = eval z₀ h₁ + eval z₀ h₂ := by
  simpa using map_add (evalRingHom hz₀) h₁ h₂

theorem eval_mul (h₁ h₂ : O⟦X⟧) : eval z₀ (h₁ * h₂) = eval z₀ h₁ * eval z₀ h₂ := by
  simpa using map_mul (evalRingHom hz₀) h₁ h₂

theorem eval_pow (h : O⟦X⟧) (n : ℕ) : eval z₀ (h ^ n) = eval z₀ h ^ n := by
  simpa using map_pow (evalRingHom hz₀) h n

theorem eval_sub (h₁ h₂ : O⟦X⟧) : eval z₀ (h₁ - h₂) = eval z₀ h₁ - eval z₀ h₂ := by
  simpa using map_sub (evalRingHom hz₀) h₁ h₂

omit hz₀

/-! ### Compatibility with composition -/

variable {k : O⟦X⟧} (hk : constantCoeff k ∈ maximalIdeal O)

include hk hz₀ in
/-- Evaluation of a composition is the composition of the evaluations. -/
theorem eval_comp (h : O⟦X⟧) : eval z₀ (comp k h) = eval (eval z₀ k) h := by
  have key := PowerSeries.comp_eval₂ WithPiTopology.continuous_C
    (hasEval_of_constantCoeff_mem hk) (continuous_evalRingHom hz₀)
    (φ := C (R := O)) (ε := (evalRingHom hz₀ : O⟦X⟧ →+* O))
  have h1 : (evalRingHom hz₀ : O⟦X⟧ →+* O).comp (C (R := O)) = RingHom.id O :=
    RingHom.ext fun r ↦ by simp
  have h2 := congrFun key h
  simpa [h1, eval_eq_eval₂, comp_eq_eval₂] using h2

include hk in
/-- The constant coefficient of a composition is the value of `h` at the constant
coefficient of `k`. -/
theorem constantCoeff_comp (h : O⟦X⟧) :
    constantCoeff (comp k h) = eval (constantCoeff k) h := by
  have hcont : Continuous (constantCoeff (R := O)) := by
    have := (WithPiTopology.uniformContinuous_coeff (R := O) 0).continuous
    simpa [funext_iff] using this
  have key := PowerSeries.comp_eval₂ WithPiTopology.continuous_C
    (hasEval_of_constantCoeff_mem hk) hcont
    (φ := C (R := O)) (ε := (constantCoeff : O⟦X⟧ →+* O))
  have h1 : (constantCoeff : O⟦X⟧ →+* O).comp (C (R := O)) = RingHom.id O :=
    RingHom.ext fun r ↦ by simp
  have h2 := congrFun key h
  simpa [h1, eval_eq_eval₂, comp_eq_eval₂] using h2

/-! ### The derivative and difference quotients -/

-- the binomial expansion with the first two terms peeled off
private lemma add_pow_eq {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y
      + (∑ j ∈ Finset.range (n - 1), n.choose j * x ^ j * y ^ (n - 2 - j)) * y ^ 2 := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    have hsplit : ∑ j ∈ Finset.range (n + 1), x ^ j * y ^ (n + 2 - j) * (n + 2).choose j
        = (∑ j ∈ Finset.range (n + 2 - 1),
              ((n + 2).choose j : R) * x ^ j * y ^ (n + 2 - 2 - j)) * y ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj2 : n + 2 - j = (n - j) + 2 := by
        have := Finset.mem_range.mp hj; lia
      rw [hj2, pow_add]
      push_cast
      ring
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ, hsplit]
    simp only [Nat.choose_self, Nat.choose_succ_self_right, Nat.sub_self, pow_zero,
      show n + 2 - (n + 1) = 1 by lia, pow_one]
    push_cast
    ring

include hz₀ in
/-- Taylor expansion to second order: the formal derivative gives the first-order
behaviour of evaluation, with an explicit second-order remainder. -/
theorem eval_deriv {w : O} (hw : w ∈ maximalIdeal O) (h : O⟦X⟧) :
    ∃ r : O, eval (z₀ + w) h
      = eval z₀ h + eval z₀ (PowerSeries.derivative O h) * w + r * w ^ 2 := by
  set c : ℕ → O := fun n ↦
    ∑ j ∈ Finset.range (n - 1), n.choose j * z₀ ^ j * w ^ (n - 2 - j) with hc
  -- the tail coefficients lie in high powers of the maximal ideal, so `∑ aₙ cₙ` converges
  have hmem (n : ℕ) : coeff n h * c n ∈ maximalIdeal O ^ (n - 2) := by
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun j hj ↦ ?_)
    have hj2 : j + (n - 2 - j) = n - 2 := by
      have := Finset.mem_range.mp hj; lia
    have hmul := Ideal.mul_mem_mul (Ideal.pow_mem_pow hz₀ j)
      (Ideal.pow_mem_pow hw (n - 2 - j))
    rw [← pow_add, hj2] at hmul
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ hmul
  obtain ⟨r, hr⟩ := summable_of_mem_pow hmem
  refine ⟨r, ?_⟩
  -- identify the three convergent series
  have hB := hasSum_eval hz₀ h
  have hD := hasSum_eval hz₀ (PowerSeries.derivative O h)
  have hD' : HasSum (fun (n : ℕ) ↦ (n : O) * coeff n h * z₀ ^ (n - 1) * w)
      (eval z₀ (PowerSeries.derivative O h) * w) := by
    have h0 : (fun (n : ℕ) ↦ (n : O) * coeff n h * z₀ ^ (n - 1) * w) 0 = 0 := by simp
    rw [← hasSum_nat_add_iff' 1]
    simpa [Finset.sum_range_one, h0, PowerSeries.coeff_derivative, mul_comm, mul_assoc,
      mul_left_comm] using hD.mul_right w
  have hsum : HasSum (fun n ↦ coeff n h * (z₀ + w) ^ n)
      (eval z₀ h + eval z₀ (PowerSeries.derivative O h) * w + r * w ^ 2) := by
    have := (hB.add hD').add ((hr.mul_right (w ^ 2)))
    convert this using 2 with n
    rw [add_pow_eq]
    ring
  exact (hasSum_eval (Ideal.add_mem _ hz₀ hw) h).unique hsum

include hz₀ in
/-- The value of a power series at a point of the maximal ideal is congruent to its
constant coefficient modulo the maximal ideal. -/
theorem eval_sub_constantCoeff_mem (h : O⟦X⟧) :
    eval z₀ h - constantCoeff h ∈ maximalIdeal O := by
  obtain ⟨g, hg⟩ : (X : O⟦X⟧) ∣ h - PowerSeries.C (constantCoeff h) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have key : eval z₀ h - constantCoeff h = z₀ * eval z₀ g := by
    rw [show eval z₀ h - constantCoeff h
        = eval z₀ (h - PowerSeries.C (constantCoeff h)) by rw [eval_sub hz₀, eval_C],
      hg, eval_mul hz₀, eval_X]
  rw [key]
  exact Ideal.mul_mem_right _ _ hz₀

end PSeries

end ChabautyColeman

-- the standing hypotheses are satisfied by `ℤ_p`
section instantiation

open IsLocalRing in
example {p : ℕ} [Fact p.Prime] (h : PowerSeries ℤ_[p]) {z₀ : ℤ_[p]}
    (hz₀ : z₀ ∈ maximalIdeal ℤ_[p]) :
    HasSum (fun k ↦ PowerSeries.coeff k h * z₀ ^ k) (ChabautyColeman.PSeries.eval z₀ h) :=
  ChabautyColeman.PSeries.hasSum_eval hz₀ h

end instantiation

