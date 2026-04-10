import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.NumberTheory.Height.MvPolynomial

-- NOTE: There is some slight divergence between this file and the contents of the corresponding
--       file in the sequence of PRs.

namespace Height

variable {K : Type*} [Field K]

open Function

-- use `NonnegHomClass`
lemma iSup_eq_iSup_subtype {ι K M : Type*} [Finite ι] [Zero K] [Zero M]
    [ConditionallyCompleteLattice M] {x : ι → K} (hx : x ≠ 0) {v : K → M}
    (hv₀ : v 0 = 0) (hv : ∀ k, 0 ≤ v k) :
    ⨆ i, v (x i) =  ⨆ i : {j // x j ≠ 0}, v (x i) := by
  obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := ne_iff.mp hx
  have : Nonempty {j // x j ≠ 0} := .intro ⟨i, hi⟩
  have : Nonempty ι := .intro i
  refine le_antisymm ?_ <| ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl
  refine ciSup_le fun j ↦ ?_
  rcases eq_or_ne (x j) 0 with h | h
  · rw [h, hv₀]
    exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨i, hi⟩ (hv ..)
  · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl

lemma iSup_abv_eq_iSup_subtype {ι : Type*} [Finite ι] (v : AbsoluteValue K ℝ) {x : ι → K}
    (hx : x ≠ 0) :
    ⨆ i, v (x i) =  ⨆ i : {j // x j ≠ 0}, v (x i) :=
  iSup_eq_iSup_subtype hx v.map_zero v.nonneg

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

-- Finiteness of the multiplicative support for some relevant functions.
@[fun_prop]
lemma mulSupport_iSup_nonarchAbsVal_finite {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  simp only [iSup_abv_eq_iSup_subtype _ hx]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| ne_iff.mp hx
  fun_prop (disch := grind)

end Height

/-!
# Height bounds for polynomial maps

We prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family of
homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K` with `ι` finite.
-/

section aux

-- Auxiliary stuff

-- in Basic
private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

-- -> Basic
private lemma iSup_fun_eq_max (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
  rw [show f = ![f 0, f 1] from List.ofFn_inj.mp rfl]
  exact (max_eq_iSup ..).symm

end aux

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues

namespace MvPolynomial

lemma mulHeightBound_zero_one : mulHeightBound ![(0 : MvPolynomial (Fin 2) K), 1] = 1 := by
  simp only [mulHeightBound, Nat.succ_eq_add_one, Nat.reduceAdd, iSup_fun_eq_max]
  conv_rhs => rw [← one_mul 1]
  congr
  · convert Multiset.prod_map_one with v
    simp [MvPolynomial.sum_def, support_one]
  · refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
    rw [show ![(0 : MvPolynomial (Fin 2) K), 1] 1 = 1 from rfl, support_one]
    simp

end MvPolynomial

namespace Polynomial

/-- The constant in the upper height bound for `p.eval x`. -/
noncomputable
def mulHeight₁Bound (p : K[X]) : ℝ :=
  max (mulHeightBound p.toTupleMvPolynomial) 1

open Finset MvPolynomial in
/-- A formula for `mulHeight₁Bound p` in terms of the coefficients of `p`. -/
lemma mulHeight₁Bound_eq (p : K[X]) :
    p.mulHeight₁Bound =
      (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
      ∏ᶠ v : nonarchAbsVal,
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [mulHeight₁Bound, toTupleMvPolynomial] using mulHeightBound_zero_one.le
  have hsupp₀ : Nonempty (MvPolynomial.X (R := K) (σ := Fin 2) 1 ^ p.natDegree).support :=
    Nonempty.to_subtype <| MvPolynomial.support_nonempty.mpr <| by simp
  have hsupp₁ : Nonempty (p.homogenize p.natDegree).support :=
    Nonempty.to_subtype <| MvPolynomial.support_nonempty.mpr <|
      mt (eq_zero_of_homogenize_eq_zero le_rfl) hp
  simp only [mulHeight₁Bound, mulHeightBound_eq]
  rw [max_eq_left ?h]
  case h => -- side goal
    refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun _ _ ↦ ?_) <|
      one_le_finprod fun v ↦ Finite.le_ciSup_of_le 1 <| le_max_right ..
    exact Finite.le_ciSup_of_le 1 <| by simp [toTupleMvPolynomial, MvPolynomial.X_pow_eq_monomial]
  congr <;> ext v
  · simp [iSup_fun_eq_max, toTupleMvPolynomial, finsuppSum_homogenize_eq,
      MvPolynomial.X_pow_eq_monomial]
  · have H : (⨆ s : (MvPolynomial.X (R := K) (σ := Fin 2) 1 ^ p.natDegree).support,
        if (fun₀ | 1 => p.natDegree : Fin 2 →₀ ℕ) = s then 1 else 0) = (1 : ℝ) := by
      rw [MvPolynomial.support_X_pow (R := K) (1 : Fin 2) p.natDegree]
      simp [ciSup_unique]
    suffices ⨆ s : (p.homogenize p.natDegree).support, v.val (p.coeff (s.val 0)) =
        (range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n) by
      set_option backward.isDefEq.respectTransparency false in -- temporary measure
      simpa [← Finite.ciSup_sup, iSup_fun_eq_max, toTupleMvPolynomial, coeff_homogenize,
        MvPolynomial.X_pow_eq_monomial, p.sum_eq_natDegree_of_mem_support_homogenize, H]
        using congrArg (max · 1) this
    rw [sup'_eq_csSup_image, sSup_image']
    refine le_antisymm (ciSup_le fun s ↦ Finite.le_ciSup_of_le ⟨s.val 0, ?_⟩ le_rfl) ?_
    · grind only [= mem_coe, = mem_range, p.sum_eq_natDegree_of_mem_support_homogenize s.prop]
    · have := (nonempty_range_add_one (n := p.natDegree)).to_subtype
      refine ciSup_le fun n ↦ ?_
      rcases eq_or_ne (p.coeff n) 0 with h | h
      · simpa [h] using Real.iSup_nonneg_of_nonnegHomClass ..
      · refine Finite.le_ciSup_of_le ⟨fun₀ | 0 => n | 1 => p.natDegree - n, ?_⟩ <| by simp
        set_option backward.isDefEq.respectTransparency false in -- temporary measure
        simpa [coeff_homogenize, h] using Nat.add_sub_of_le <| le_natDegree_of_ne_zero h

/-- The multiplicative height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree`. -/
theorem mulHeight₁_eval_le (p : K[X]) (x : K) :
    mulHeight₁ (p.eval x) ≤ p.mulHeight₁Bound * mulHeight₁ x ^ p.natDegree := by
  rw [p.eval_eq_div_eval_toTupleMvPolynomial, mulHeight₁_div_eq_mulHeight, mulHeight₁_eq_mulHeight]
  convert mulHeight_eval_le p.isHomogeneous_toTupleMvPolynomial _ with i
  fin_cases i <;> simp

open Real in
/-- The logarithmic height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `log p.mulHeight₁Bound + p.natDegree * logHeight₁ x`. -/
lemma logHeight₁_eval_le (p : K[X]) (x : K) :
    logHeight₁ (p.eval x) ≤ log p.mulHeight₁Bound + p.natDegree * logHeight₁ x := by
  simp_rw [logHeight₁_eq_log_mulHeight₁]
  have : p.mulHeight₁Bound ≠ 0 := by have : 1 ≤ mulHeight₁Bound p := le_max_right ..; grind
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight₁_eval_le p x

end Polynomial
