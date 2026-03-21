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
  convert mulHeight_eval_le p.isHomogenous_toTupleMvPolynomial _ with i
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

-- #35941
/-!
### Bounds for the height of ![x*y, x+y, 1]

We show that the multiplicative height of `![a*c, a*d + b*c, b*d]` is bounded from above and from
below by a positive constant times the product of the multiplicative heights of `![a, b]` and
`![c, d]` (and the analogous statements for the logarithmic heights).

The constants are unspecified here; with (likely considerably, but trivial) more work,
we could make them explicit.
-/

section sym2

namespace Height

lemma mulHeight_mul_mulHeight {a b c d : K} (hab : ![a, b] ≠ 0) (hcd : ![c, d] ≠ 0) :
    mulHeight ![a, b]* mulHeight ![c, d] = mulHeight ![a * c, a * d, b * c, b * d] := by
  simp only [← mulHeight_fun_mul_eq hab hcd]
  convert mulHeight_comp_equiv finProdFinEquiv _ with i
  fin_cases i <;> simp [finProdFinEquiv]

open MvPolynomial

variable (K)

lemma mulHeight_sym2_le :
    ∃ C > 0, ∀ (a b c d : K),
      mulHeight ![a * c, a * d + b * c, b * d] ≤ C * mulHeight ![a, b] * mulHeight ![c, d] := by
  let p : Fin 3 → MvPolynomial (Fin 4) K := ![X 0, X 1 + X 2, X 3]
  have hom i : (p i).IsHomogeneous 1 := by
    fin_cases i <;> simp [p, isHomogeneous_X, IsHomogeneous.add]
  obtain ⟨C, hC₀, hC⟩ := mulHeight_eval_le' hom
  simp only [pow_one] at hC
  refine ⟨max C 1, by grind, fun a b c d ↦ ?_⟩
  by_cases hab : ![a, b] = 0
  · rw [hab, mulHeight_zero, mul_one, show a = 0 from congrFun hab 0,
      show b = 0 from congrFun hab 1,
      show ![0 * c, 0 * d + 0 * c, 0 * d] = 0 by ext i; fin_cases i <;> simp, mulHeight_zero]
    grw [← one_le_mulHeight]
    grind
  by_cases hcd : ![c, d] = 0
  · rw [hcd, mulHeight_zero, mul_one, show c = 0 from congrFun hcd 0,
      show d = 0 from congrFun hcd 1,
      show ![a * 0, a * 0 + b * 0, b * 0] = 0 by ext i; fin_cases i <;> simp, mulHeight_zero]
    grw [← one_le_mulHeight]
    grind
  rw [mul_assoc, mulHeight_mul_mulHeight hab hcd]
  grw [← le_max_left C 1]
  convert hC _ with i
  fin_cases i <;> simp [p]

lemma mulHeight_sym2_ge :
    ∃ C > 0, ∀ {a b c d : K}, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      C * mulHeight ![a, b] * mulHeight ![c, d] ≤ mulHeight ![a * c, a * d + b * c, b * d] := by
  let p : Fin 3 → MvPolynomial (Fin 4) K := ![X 0, X 1 + X 2, X 3]
  let q : Fin 4 × Fin 3 → MvPolynomial (Fin 4) K :=
    ![![X 0, 0, 0], ![0, X 1, -X 0], ![0, X 2, -X 0], ![0, 0, X 3]].uncurry
  have hom a : (q a).IsHomogeneous 1 := by
    fin_cases a <;> simp [q] <;> grind only [!isHomogeneous_X, isHomogeneous_zero, IsHomogeneous.neg]
  obtain ⟨C, hC₀, hC⟩ := mulHeight_eval_ge' (M := 1) (N := 1) hom
  simp only [pow_one] at hC
  refine ⟨C, hC₀, fun hab hcd ↦ ?_⟩
  rw [mul_assoc, mulHeight_mul_mulHeight hab hcd]
  convert hC p fun j ↦ ?H  with i
  case H => fin_cases j <;> simp [p, q, Fin.sum_univ_three] <;> ring
  fin_cases i <;> simp [p]

open Real in
lemma logHeight_sym2_le :
    ∃ C, ∀ (a b c d : K), logHeight ![a * c, a * d + b * c, b * d] ≤
      C + logHeight ![a, b] + logHeight ![c, d] := by
  obtain ⟨C', hC₀, hC⟩ := mulHeight_sym2_le K
  refine ⟨log C', fun a b c d ↦ ?_⟩
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) (hC ..)

open Real in
lemma logHeight_sym2_ge :
    ∃ C, ∀ {a b c d : K}, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      C + logHeight ![a, b] + logHeight ![c, d] ≤ logHeight ![a * c, a * d + b * c, b * d] := by
  obtain ⟨C', hC₀, hC⟩ := mulHeight_sym2_ge K
  refine ⟨log C', fun hab hcd ↦ ?_⟩
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) (hC hab hcd)

lemma abs_logHeight_sym2_sub_le :
    ∃ C, ∀ {a b c d : K}, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      |logHeight ![a * c, a * d + b * c, b * d] - (logHeight ![a, b] + logHeight ![c, d])| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2_le K
  obtain ⟨C₂, hC₂⟩ := logHeight_sym2_ge K
  -- `grind` does it without the `specialize`, but is slow
  exact ⟨max C₁ (-C₂), fun hab hcd ↦ by specialize hC₂ hab hcd; grind⟩

/-
lemma mulHeight_sym2_le' :
    ∃ C > 0, ∀  (x y : K), mulHeight ![x * y, x + y, 1] ≤ C * mulHeight₁ x * mulHeight₁ y := by
  obtain ⟨C, hC₀, hC⟩ := mulHeight_sym2_le K
  refine ⟨C, hC₀, fun x y ↦ ?_⟩
  simp only [mulHeight₁_eq_mulHeight]
  convert hC x 1 y 1 <;> simp

open Function in
lemma mulHeight_sym2_ge' :
    ∃ C > 0, ∀ (x y : K), C * mulHeight₁ x * mulHeight₁ y ≤ mulHeight ![x * y, x + y, 1]:= by
  obtain ⟨C, hC₀, hC⟩ := mulHeight_sym2_ge K
  refine ⟨C, hC₀, fun x y ↦ ?_⟩
  have hx : ![x, 1] ≠ 0 := ne_iff.mpr ⟨1, by simp⟩
  have hy : ![y, 1] ≠ 0 := ne_iff.mpr ⟨1, by simp⟩
  simp only [mulHeight₁_eq_mulHeight]
  convert hC hx hy <;> simp
-/


/-!
### Removing zeros from a tuple does not change the height

We show that the height of `![0, x₁, …, xₙ]` is the same as that of `![x₁, …, xₙ]`
and use this to establish a couple of helpful `simp` lemmas for the (logarithmic) height
of `![x, 0]` and of `![x, y, 0]`.

TODO: Write a `simproc` that removes all (syntactic) zeros from a tuple when
      `mulHeight` or `logHeight` is applied to it.
-/

variable {K}

open Matrix

@[simp]
lemma mulHeight_vecCons_zero {n : ℕ} (x : Fin n → K) :
    mulHeight (vecCons 0 x) = mulHeight x := by
  let e := (Equiv.sumComm ..).trans <| (finSumFinEquiv (m := 1) (n := n)).trans <|
    finCongr (show 1 + n = n.succ from n.one_add)
  have he : Matrix.vecCons 0 x ∘ ⇑e = Sum.elim x 0 := by
    ext j : 1
    match j with
    | .inl _ => simp [e]
    | .inr ⟨i, h⟩ =>
      simp only [show i = 0 by lia]
      simp [e, show Fin.castAdd n 0 = 0 from Fin.castAdd_mk _ _ zero_lt_one]
  rw [← mulHeight_comp_equiv e, he, mulHeight_sumElim_zero_eq]

@[simp]
lemma logHeight_vecCons_zero {n : ℕ} (x : Fin n → K) :
    logHeight (Matrix.vecCons 0 x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
lemma mulHeight_vecCons_vecCons_zero {n : ℕ} (a : K) (x : Fin n → K) :
    mulHeight (vecCons a (vecCons 0 x)) = mulHeight (vecCons a x) := by
  have he : vecCons a (vecCons 0 x) ∘ ⇑(Equiv.swap 0 1) = vecCons 0 (vecCons a x) := by
    ext j : 1
    match j with
    | 0 => simp
    | 1 => simp
    | ⟨i + 2, h⟩ =>
      have h' : (⟨i + 2, h⟩ : Fin n.succ.succ) = Fin.succ (Fin.succ ⟨i, by lia⟩) := by grind
      simp only [Nat.succ_eq_add_one, Function.comp_apply, cons_val_succ']
      rw [h', Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _),
        cons_val_succ, cons_val_succ]
  rw [← mulHeight_comp_equiv (Equiv.swap 0 1), he]
  simp

@[simp]
lemma logHeight_vecCons_vecCons_zero {n : ℕ} (a : K) (x : Fin n → K) :
    logHeight (vecCons a (vecCons 0 x)) = logHeight (vecCons a x) := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
lemma mulHeight_finThree_zero_right (x y : K) : mulHeight ![x, y, 0] = mulHeight ![x, y] := by
  rw [← mulHeight_comp_equiv (finRotate 3).symm,
    show ![x, y, 0] ∘ _ = ![0, x, y] by ext i : 1; fin_cases i <;> simp]
  simp

@[simp]
lemma logHeight_finThree_zero_right (x y : K) : logHeight ![x, y, 0] = logHeight ![x, y] := by
  simp [logHeight_eq_log_mulHeight]

end Height

end sym2
-- end #35941
