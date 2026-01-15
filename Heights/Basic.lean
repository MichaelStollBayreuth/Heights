-- import Heights.Auxiliary
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.NumberTheory.Height.Basic
-- import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We have a `Multiset` of archimedean absolute values on `K` (with values in `ℝ`).
* We also have a `Set` of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`, where the first product is over the multiset of archimedean
  absolute values.

We realize this implementation via the class `Height.AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `Height.mulHeight₁ x` and `Height.logHeight₁ x` for `x : K`.
  This is the height of an element of `K`.
* `Height.mulHeight x` and `Height.logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K` (for `x ≠ 0`).
* `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to any finite subtype containing the support of `x`.
* `Projectivization.mulHeight` and `Projectivization.logHeight` on
  `Projectivization K (ι → K)` (with a finite type `ι`). This is the height of a point
  on projective space (with fixed basis).

## Main results

* Behavior of `mulHeight` and `logHeight` under component-wise exponentiation
  (and as a consequence, the corresponding statements for `mulHeight₁` and `logHeight₁`).
* Scaling invariance of `mulHeight` and `logHeight` (allowing to define heights on
  points in projective space).
* A bound for `mulHeight₁` and `logHeight₁` of sums of two or arbitrarily many elements.

-/

noncomputable section

namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-!
### Heights of tuples and finitely supported maps

We define the multiplicative height of a nonzero tuple `x : ι → K` as the product of the maxima
of `v` on `x`, as `v` runs through the relevant absolute values of `K`. As usual, the
logarithmic height is the logarithm of the multiplicative height.

For a finitely supported function `x : ι →₀ K`, we define the height as the height of `x`
restricted to its support.
-/

variable {ι : Type*}

/-- The multiplicative height of a tuple of elements of `K`.
For the zero tuple we take the junk value `1`. -/
def mulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

lemma mulHeight_eq {x : ι → K} (hx : x ≠ 0) :
    mulHeight x =
      (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) := by
  simp [mulHeight, hx]

@[simp]
lemma mulHeight_zero : mulHeight (0 : ι → K) = 1 := by
  simp [mulHeight]

@[simp]
lemma mulHeight_one : mulHeight (1 : ι → K) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [show (1 : ι → K) = 0 from Subsingleton.elim ..]
    exact mulHeight_zero
  · have hx : (1 : ι → K) ≠ 0 := by simp
    simp [mulHeight_eq hx]

/-- The multiplicative height does not change under re-indexing. -/
lemma mulHeight_comp_equiv {ι' : Type*} (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : x ∘ e ≠ 0 := by
      contrapose! hx
      rw [show x = (x ∘ e) ∘ e.symm by simp [Function.comp_assoc]]
      ext1 i
      simp [hx]
    simp [mulHeight_eq hx, mulHeight_eq hx', Function.comp_apply, H]

lemma mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x] := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  convert mulHeight_comp_equiv e ![y, x]
  ext i
  fin_cases i <;> simp [e]

/-- The logarithmic height of a tuple of elements of `K`. -/
def logHeight (x : ι → K) : ℝ := log (mulHeight x)

lemma logHeight_eq_log_mulHeight (x : ι → K) : logHeight x = log (mulHeight x) := rfl

variable {α : Type*}

/-- The multiplicative height of a finitely supported function. -/
def _root_.Finsupp.mulHeight (x : α →₀ K) : ℝ :=
  Height.mulHeight fun i : x.support ↦ x i

/-- The logarithmic height of a finitely supported function. -/
def _root_.Finsupp.logHeight (x : α →₀ K) : ℝ := log (mulHeight x)

lemma _root_.Finsupp.logHeight_eq_log_mulHeight (x : α →₀ K) :
    logHeight x = log (mulHeight x) := rfl

/-!
### Properties of heights
-/

private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

variable [Finite ι]

private lemma mulSupport_iSup_nonarchAbsVal_finite {x : ι → K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).Finite := by
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  suffices (Function.mulSupport fun v : nonarchAbsVal ↦ ⨆ i : {j // x j ≠ 0}, v.val (x i)).Finite by
    convert this with v
    have ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm ?_ <| ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl
    refine ciSup_le fun j ↦ ?_
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl
  exact (Set.finite_iUnion fun i : {j | x j ≠ 0} ↦ mulSupport_finite i.prop).subset <|
    Function.mulSupport_iSup _

private lemma mulSupport_max_nonarchAbsVal_finite (x : K) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ v.val x ⊔ 1).Finite := by
  convert mulSupport_iSup_nonarchAbsVal_finite (x := ![x, 1]) <| by simp with v
  rw [max_eq_iSup]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The multiplicative height of a (nonzero) tuple does not change under scaling. -/
lemma mulHeight_smul_eq_mulHeight (x : ι → K) {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  simp only [mulHeight_eq hx, mulHeight_eq hcx, Pi.smul_apply, smul_eq_mul, map_mul,
    ← mul_iSup_of_nonneg <| AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (mulSupport_finite hc) (mulSupport_iSup_nonarchAbsVal_finite hx),
    mul_mul_mul_comm, product_formula hc, one_mul]

lemma one_le_mulHeight (x : ι → K) : 1 ≤ mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
  rw [← mulHeight_smul_eq_mulHeight _ <| inv_ne_zero hi, mulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun vx h ↦ ?_) ?_
  · simp only [Pi.smul_apply, smul_eq_mul, AbsoluteValue.map_mul, map_inv₀, Multiset.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    refine le_ciSup_of_le (Finite.bddAbove_range _) i <| le_of_eq ?_
    exact (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v ↦ le_ciSup_of_le (Finite.bddAbove_range _) i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]

lemma mulHeight_pos (x : ι → K) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x

lemma mulHeight.ne_zero (x : ι → K) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'

lemma zero_le_logHeight {x : ι → K} : 0 ≤ logHeight x :=
  log_nonneg <| one_le_mulHeight x

/-- The logarithmic height of a tuple does not change under scaling. -/
lemma logHeight_smul_eq_logHeight (x : ι → K) {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight x hc]

lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  have H (v : AbsoluteValue K ℝ) (x : K) : v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
    have (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
    simpa [this] using max_eq_iSup (v x) 1
  have hx : ![x, 1] ≠ 0 := by simp
  simp only [mulHeight₁_eq, mulHeight_eq hx, H]

lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]

lemma mulHeight₁_div_eq_mulHeight (x y : K) :
    mulHeight₁ (x / y) = mulHeight ![x, y] := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, mulHeight₁_zero]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [show (![0, 0] : Fin 2 → K) = 0 by simp]
      simp
    · have := mulHeight_smul_eq_mulHeight ![1, 0] hx
      simp only [Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty] at this
      rw [this, mulHeight_swap, ← mulHeight₁_eq_mulHeight, mulHeight₁_zero]
  · rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hy]
    simp [mul_div_cancel₀ x hy]

lemma logHeight₁_div_eq_logHeight (x y : K) :
    logHeight₁ (x / y) = logHeight ![x, y] := by
  rw [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_div_eq_mulHeight x y]

/-- The multiplicative height of the coordinate-wise `n`th power of a tuple
is the `n`th power of its multiplicative height. -/
lemma mulHeight_pow (x : ι → K) (n : ℕ) :
    mulHeight (x ^ n) = mulHeight x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have H (v : AbsoluteValue K ℝ) : ⨆ i : ι, v ((x ^ n) i) = (⨆ i, v (x i)) ^ n := by
    simp only [Pi.pow_apply, map_pow]
    simp +singlePass only [← coe_toNNReal _ (v.nonneg _)]
    norm_cast
    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
      (Finite.bddAbove_range _) |>.symm
  have hxn : x ^ n ≠ 0 := by simp [hx]
  simp only [mulHeight_eq hx, mulHeight_eq hxn, H, mul_pow,
    finprod_pow <| mulSupport_iSup_nonarchAbsVal_finite hx, ← Multiset.prod_map_pow]

/-- The logarithmic height of the coordinate-wise `n`th power of a tuple
is `n` times its logarithmic height. -/
lemma logHeight_pow (x : ι → K) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow x n]

/-- The multiplicative height of the inverse of a field element `x`
is the same as the multiplicative height of `x`. -/
lemma mulHeight₁_inv (x : K) : mulHeight₁ (x⁻¹) = mulHeight₁ x := by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have H : x • ![x⁻¹, 1] = ![1, x] := funext fun i ↦ by fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight _ hx, H, mulHeight_swap]

/-- The logarithmic height of the inverse of a field element `x`
is the same as the logarithmic height of `x`. -/
lemma logHeight₁_inv (x : K) : logHeight₁ (x⁻¹) = logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℕ`)
is the `n`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_pow (x : K) (n : ℕ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n := by
  have hx : ![x, 1] ≠ 0 := Function.ne_iff.mpr ⟨1, by simp⟩
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow _ n]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℕ`)
is `n` times the logaritmic height of `x`. -/
lemma logHeight₁_pow (x : K) (n : ℕ) : logHeight₁ (x ^ n) = n * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_pow, log_pow]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℤ`)
is the `|n|`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_zpow (x : K) (n : ℤ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs := by
  rcases le_or_gt 0 n with h | h
  · lift n to ℕ using h
    rw [zpow_natCast, mulHeight₁_pow, Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by grind]
    rw [zpow_neg, mulHeight₁_inv, zpow_natCast, mulHeight₁_pow]

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℤ`)
is `|n|` times the logarithmic height of `x`. -/
lemma logHeight₁_zpow (x : K) (n : ℤ) : logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_zpow, log_pow]

#exit
section aux

-- Some lemmas needed below

private lemma le_mul_max_max_left (a b : ℝ) : b ≤ (b ⊔ 1) * (a ⊔ 1) := by
  nth_rewrite 1 [← mul_one b]
  gcongr <;> grind

private lemma le_mul_max_max_right (a b : ℝ) : a ≤ (b ⊔ 1) * (a ⊔ 1) := by
  rw [mul_comm]
  exact le_mul_max_max_left b a

private lemma one_le_mul_max_max (a b : ℝ) : 1 ≤ (a ⊔ 1) * (b ⊔ 1) := by
  nth_rewrite 1 [← mul_one 1]
  gcongr <;> exact le_max_right ..

end aux

-- needed later (only used once)
@[to_additive]
lemma Function.mulSupport_mul_finite {α β : Type*} [Monoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (mulSupport fun a ↦ f a * g a).Finite :=
  (hf.union hg).subset <| mulSupport_mul f g

/-- The multiplicative height of `x + y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁_eq, totalWeight]
  calc
    _ ≤ (archAbsVal.map fun v ↦ 2 * (max (v y) 1 * max (v x) 1)).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) (fun v hv ↦ sup_le ?_ ?_)
      · refine (v.add_le x y).trans ?_
        rw [two_mul]
        exact add_le_add (le_mul_max_max_right ..) (le_mul_max_max_left ..)
      · refine (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
        exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two
    _ ≤ _ * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 * max (v.val y) 1 := by
      refine mul_le_mul_of_nonneg_left ?_ <| Multiset.prod_nonneg fun _ h ↦ by
        obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
        positivity
      have hf := Function.mulSupport_mul_finite (mulSupport_max_nonarchAbsVal_finite x)
        (mulSupport_max_nonarchAbsVal_finite y)
      refine finprod_mono' (mulSupport_max_nonarchAbsVal_finite _)
        (by grind) hf fun v ↦ sup_le ?_ <| one_le_mul_max_max ..
      exact (isNonarchimedean _ v.prop x y).trans <|
        sup_le (le_mul_max_max_left ..) (le_mul_max_max_right ..)
    _ = _ := by
      simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
        mulSupport_max_nonarchAbsVal_finite, finprod_mul_distrib]
      ring

/-- The logarithmic height of `x + y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`. -/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) ≤ totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  refine (log_le_iff_le_exp <| mulHeight₁_pos _).mpr ?_
  grw [mulHeight₁_add_le]
  simp [exp_add, exp_log, mulHeight₁_pos, exp_nat_mul]

open Finset in
/-- The multiplicative height of a finite sum of field elements is at most
`2 ^ ((n-1) * totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values.
lemma mulHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤ 2 ^ ((#s - 1) * totalWeight K) * ∏ a ∈ s, mulHeight₁ (x a) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have := mulHeight₁_pos (x a)
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      · simp only [ha, not_false_eq_true, sum_insert, card_insert_of_notMem, prod_insert]
        calc
        _ ≤ 2 ^ totalWeight K * mulHeight₁ (x a) * mulHeight₁ (∑ b ∈ s, x b) := mulHeight₁_add_le ..
        _ ≤ _ * (2 ^ ((#s - 1) * totalWeight K) * ∏ b ∈ s, mulHeight₁ (x b)) := by gcongr
        _ = _ := by
          rw [show #s + 1 - 1 = 1 + (#s - 1) by grind]
          ring

/-- The logarithmic height of a finite sum of field elements is at most
`(n-1) * totalWeight K * log 2` plus the sum of the individual logarithmic heights,
where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values.
lemma logHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤
      ((s.card - 1) * totalWeight K : ) * log 2 + ∑ a ∈ s, logHeight₁ (x a) := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  refine (log_le_iff_le_exp <| mulHeight₁_pos _).mpr ?_
  grw [mulHeight₁_sum_le]
  generalize (s.card - 1) * totalWeight K = w -- to avoid `simp` goig into it
  simp [exp_add, exp_sum, exp_log, mulHeight₁_pos, exp_nat_mul]

end Height

/-!
### Heights on projective spaces
-/

namespace Projectivization

open Height AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

private
lemma mulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  h ▸ mulHeight_smul_eq_mulHeight fun H ↦ a.prop <| (H ▸ h).trans <| zero_smul K b.val

private
lemma logHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    logHeight a.val = logHeight b.val :=
  congrArg log <| mod_cast mulHeight_aux a b t h

/-- The multiplicative height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
def mulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.mulHeight r.val) mulHeight_aux

/-- The logarithmic height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
def logHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.logHeight r.val) logHeight_aux

lemma mulHeight_mk {x : ι → K} (hx : x ≠ 0) : mulHeight (mk K x hx) = Height.mulHeight x := rfl

lemma logHeight_mk {x : ι → K} (hx : x ≠ 0) : logHeight (mk K x hx) = Height.logHeight x := rfl

lemma logHeight_eq_log_mulHeight (x : Projectivization K (ι → K)) :
    logHeight x = log (mulHeight x) := by
  rw [← x.mk_rep, mulHeight_mk, logHeight_mk, Height.logHeight]

lemma one_le_mulHeight (x : Projectivization K (ι → K)) : 1 ≤ mulHeight x := by
  rw [← x.mk_rep, mulHeight_mk]
  exact Height.one_le_mulHeight x.rep_nonzero

lemma mulHeight_pos (x : Projectivization K (ι → K)) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x

lemma mulHeight_ne_zero (x : Projectivization K (ι → K)) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'

lemma zero_le_logHeight (x : Projectivization K (ι → K)) : 0 ≤ logHeight x := by
  rw [logHeight_eq_log_mulHeight]
  exact log_nonneg <| x.one_le_mulHeight

end Projectivization
