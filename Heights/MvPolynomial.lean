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

namespace Polynomial

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues

/-- The constant in the upper height bound for `p.eval x`. -/
noncomputable
def mulHeight₁Bound (p : K[X]) : ℝ :=
  max (mulHeightBound p.toTupleMvPolynomial) 1

open Finset in
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

-- #35940

/-!
### Lower bound for the height of the image under a polynomial map

If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,
then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by an (explicit) positive
constant depending only on `q` times the `N`th power of the mutiplicative height of `x`.
A similar statement holds for the logarithmic height.

The main idea is to reduce this to a combination of `mulHeight_linearMap_apply_le`
and `mulHeight_eval_le`.
-/

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*} [Finite ι] [Fintype ι']

open AdmissibleAbsValues

/-- If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,
then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by an (explicit) positive
constant depending only on `q` times the `N`th power of the mutiplicative height of `x`. -/
theorem mulHeight_eval_ge [Nonempty ι'] {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) (p : ι' → MvPolynomial ι K) {x : ι → K}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    mulHeight (fun j ↦ (p j).eval x) ≥
      (Nat.card ι' ^ totalWeight K * max (mulHeightBound q) 1)⁻¹ * mulHeight x ^ N := by
  let q' : ι × ι' → K := fun a ↦ (q a).eval x
  have H : mulHeight x ^ (M + N) ≤
      Nat.card ι' ^ totalWeight K * mulHeight q' * mulHeight fun j ↦ (p j).eval x := by
    rw [← mulHeight_pow x (M + N)]
    have : x ^ (M + N) = fun k ↦ ∑ j, (q (k, j)).eval x * (p j).eval x := by
      ext1 k
      exact (h k).symm
    simpa [this] using mulHeight_linearMap_apply_le q' _
  rw [ge_iff_le, inv_mul_le_iff₀ ?hC, ← mul_le_mul_iff_left₀ (by positivity : 0 < mulHeight x ^ M)]
  case hC => exact mul_pos (mod_cast Nat.one_le_pow _ _ Nat.card_pos) <| by positivity
  rw [← pow_add, add_comm]
  grw [H, mulHeight_eval_le hq x]
  exact Eq.le (by ring)

/-- If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,
then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by a positive
constant depending only on `q` times the `N`th power of the mutiplicative height of `x`.

The difference to `mulHeight_eval_ge` is that the constant is not made explicit. -/
theorem mulHeight_eval_ge' [Nonempty ι'] {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) :
    ∃ C > 0, ∀ (p : ι' → MvPolynomial ι K) {x : ι → K}
      (_h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)),
      mulHeight (fun j ↦ (p j).eval x) ≥ C * mulHeight x ^ N :=
  have : 0 < Nat.card ι' := Nat.card_pos
  ⟨_, by positivity, mulHeight_eval_ge hq⟩

open Real in
/-- If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,
then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by an (explicit)
constant depending only on `q` plus `N` times the logarithmic height of `x`. -/
theorem logHeight_eval_ge [Nonempty ι'] {M : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) (p : ι' → MvPolynomial ι K) {x : ι → K} {N : ℕ}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    logHeight (fun j ↦ (p j).eval x) ≥
      -log (Nat.card ι' ^ totalWeight K * max (mulHeightBound q) 1) + N * logHeight x:= by
  simp only [logHeight_eq_log_mulHeight]
  have : (Nat.card ι' : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_eval_ge hq p h

/-- If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,
then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by a
constant plus `N` times the logarithmic height of `x`.

The difference to `logHeight_eval_ge` is that the constant is not made explicit. -/
theorem logHeight_eval_ge' [Nonempty ι'] {M : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) :
    ∃ C, ∀ (p : ι' → MvPolynomial ι K) {x : ι → K} {N : ℕ}
      (_h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)),
      logHeight (fun j ↦ (p j).eval x) ≥ C + N * logHeight x :=
  ⟨_, logHeight_eval_ge hq⟩

-- end #35940

-- #35941
/-!
### Bounds for the height of ![x*y, x+y, 1]

We show that the multiplicative height of `![x*y, x+y, 1]` is bounded from above and from below
by a positive constant times the product of the multiplicative heights of `x` and `y`
(and the analogous statements for the logarithmic heights).

The constants are unspecified here; with (likely considerably, but trivial) more work,
we could make them explicit.
-/

section sym2

open Function in
lemma mulHeight₁_mul_mulHeight₁ (x y : K) :
    mulHeight₁ x * mulHeight₁ y = mulHeight ![x * y, x, y, 1] := by
  have hx : ![x, 1] ≠ 0 := ne_iff.mpr ⟨1, by simp⟩
  have hy : ![y, 1] ≠ 0 := ne_iff.mpr ⟨1, by simp⟩
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_fun_mul_eq hx hy]
  convert mulHeight_comp_equiv finProdFinEquiv _ with a
  fin_cases a <;> simp [finProdFinEquiv]

open MvPolynomial

lemma mulHeight_sym2_le :
    ∃ C > 0, ∀  (x y : K), mulHeight ![x * y, x + y, 1] ≤ C * mulHeight₁ x * mulHeight₁ y := by
  let p : Fin 3 → MvPolynomial (Fin 4) K := ![X 0, X 1 + X 2, X 3]
  have hom i : (p i).IsHomogeneous 1 := by
    fin_cases i <;> simp [p, isHomogeneous_X, IsHomogeneous.add]
  obtain ⟨C, hC₀, hC⟩ := mulHeight_eval_le' (p := p) (N := 1) hom
  refine ⟨C, hC₀, fun x y ↦ ?_⟩
  rw [mul_assoc, mulHeight₁_mul_mulHeight₁, ← pow_one (mulHeight ![x * y, x, y, 1])]
  convert hC ![x * y, x, y, 1] with a
  fin_cases a <;> simp [p]

lemma mulHeight_sym2_ge :
    ∃ C > 0, ∀ (x y : K), mulHeight ![x * y, x + y, 1] ≥ C * mulHeight₁ x * mulHeight₁ y := by
  let p : Fin 3 → MvPolynomial (Fin 4) K := ![X 0, X 1 + X 2, X 3]
  let q : Fin 4 × Fin 3 → MvPolynomial (Fin 4) K :=
    ![![X 0, 0, 0], ![0, X 1, -X 0], ![0, X 2, -X 0], ![0, 0, X 3]].uncurry
  have hom a : (q a).IsHomogeneous 1 := by
    fin_cases a <;> simp [q] <;> grind only [!isHomogeneous_X, isHomogeneous_zero, IsHomogeneous.neg]
  obtain ⟨C, hC₀, hC⟩ := mulHeight_eval_ge' (M := 1) (N := 1) hom
  refine ⟨C, hC₀, fun x y ↦ ?_⟩
  rw [mul_assoc, mulHeight₁_mul_mulHeight₁, ← pow_one (mulHeight ![x * y, x, y, 1])]
  have H a : ∑ j, (eval ![x * y, x, y, 1]) (q (a, j)) * (eval ![x * y, x, y, 1]) (p j) =
      ![x * y, x, y, 1] a ^ 2 := by
    fin_cases a <;> simp [p, q, Fin.sum_univ_three] <;> ring
  convert hC p (x := ![x * y, x, y, 1]) H with a
  fin_cases a <;> simp [p]

open Real

variable (K)

lemma logHeight_sym2_le :
    ∃ C, ∀ (x y : K), logHeight ![x * y, x + y, 1] ≤ C + logHeight₁ x + logHeight₁ y := by
  obtain ⟨c, hc₉, hc⟩ := mulHeight_sym2_le (K := K)
  refine ⟨log c, fun x y ↦ ?_⟩
  simp only [logHeight_eq_log_mulHeight, logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact log_le_log (by positivity) (hc x y)

lemma logHeight_sym2_ge :
    ∃ C, ∀  (x y : K), logHeight ![x * y, x + y, 1] ≥ C + logHeight₁ x + logHeight₁ y := by
  obtain ⟨c, hc₉, hc⟩ := mulHeight_sym2_ge (K := K)
  refine ⟨log c, fun x y ↦ ?_⟩
  simp only [logHeight_eq_log_mulHeight, logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact log_le_log (by positivity) (hc x y)

lemma abs_logHeight_sym2_sub_le :
    ∃ C, ∀ (x y : K), |logHeight ![x * y, x + y, 1] - (logHeight₁ x + logHeight₁ y)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2_le K
  obtain ⟨C₂, hC₂⟩ := logHeight_sym2_ge K
  exact ⟨max C₁ (-C₂), by grind⟩

variable {K}

@[simp]
lemma logHeight_zero_right (x : K) : logHeight ![x, 0] = 0 := by
  let e : Unit ⊕ Unit ≃ Fin 2 := {
    toFun | .inl () => 0 | .inr () => 1
    invFun | 0 => .inl () | 1 => .inr ()
    left_inv := by grind
    right_inv := by grind
  }
  have he : ![x, 0] ∘ e = Sum.elim (fun | () => x) (0 : Unit → K) := by
    ext1 j
    fin_cases j <;> simp [e]
  rw [← logHeight_comp_equiv e, he, logHeight_sumElim_zero_eq, logHeight_eq_zero_of_subsingleton]

@[simp]
lemma logHeight_zero_zero_left (x : K) : logHeight ![0, 0, x] = 0 := by
  let e : Unit ⊕ Fin 2 ≃ Fin 3 := {
    toFun | .inr 0 => 0 | .inr 1 => 1 | .inl () => 2
    invFun | 0 => .inr 0 | 1 => .inr 1 | 2 => .inl ()
    left_inv := by grind
    right_inv := by grind
  }
  have he : ![0, 0, x] ∘ e = Sum.elim (fun | () => x) (0 : Fin 2 → K) := by
    ext1 j
    fin_cases j <;> simp [e]
  rw [← logHeight_comp_equiv e, he, logHeight_sumElim_zero_eq, logHeight_eq_zero_of_subsingleton]

@[simp]
lemma logHeight_x_y_zero (x y : K) : logHeight ![x, y, 0] = logHeight ![x, y] := by
  let e : Fin 2 ⊕ Unit ≃ Fin 3 := {
    toFun | .inl 0 => 0 | .inl 1 => 1 | .inr () => 2
    invFun | 0 => .inl 0 | 1 => .inl 1 | 2 => .inr ()
    left_inv := by grind
    right_inv := by grind
  }
  have he : ![x, y, 0] ∘ e = Sum.elim ![x, y] (0 : Unit → K) := by
    ext1 j
    fin_cases j <;> simp [e]
  rw [← logHeight_comp_equiv e, he, logHeight_sumElim_zero_eq]

omit [AdmissibleAbsValues K] in
private lemma ne_zero_of_tuple_ne_zero {a : K} (ha : ![a, 0] ≠ 0) : a ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  fin_cases i
  · simpa using hi
  · simp at hi

variable (K) in
lemma abs_logHeight_sym2_sub_le' :
    ∃ C, ∀ a b c d : K, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      |logHeight ![a * c, a * d + b * c, b * d] - (logHeight ![a, b] + logHeight ![c, d])| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le K
  refine ⟨C, fun a b c d hab hcd ↦ ?_⟩
  have hC₀ : 0 ≤ C := by simpa using hC 0 0
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a ≠ 0 := ne_zero_of_tuple_ne_zero hab
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, zero_mul, add_zero, logHeight_x_y_zero,
      logHeight_zero_right, zero_add]
    rw [← logHeight_smul_eq_logHeight (c := 1 / a) _ (by simp [ha])]
    simpa [field, ha] using hC₀
  rcases eq_or_ne d 0 with rfl | hd
  · have hc : c ≠ 0 := ne_zero_of_tuple_ne_zero hcd
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mul_zero, zero_add, logHeight_x_y_zero,
      logHeight_zero_right, add_zero, mul_comm _  c]
    rw [← logHeight_smul_eq_logHeight (c := 1 / c) _ (by simp [hc])]
    simpa [field, hc] using hC₀
  simp only [← logHeight₁_div_eq_logHeight]
  have H : logHeight ![a * c, a * d + b * c, b * d] = logHeight ![a / b * (c / d), a / b + c / d, 1] := by
    rw [← logHeight_smul_eq_logHeight (c := 1 / (b * d)) _ (by simp [hb, hd])]
    congr
    ext1 i
    fin_cases i <;> simp <;> field
  rw [H]
  exact hC ..

end sym2
-- end #35941

end Height
