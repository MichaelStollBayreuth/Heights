import Heights.Auxiliary
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

/-!
### Families of admissible absolute values

We define the class `AdmissibleAbsValues K` for a field `K`, which captures the notion of a
family of absolute values on `K` satisfying a product formula.
-/

/-- A type class capturing an admissible family of (weak) absolute values. -/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The archimedean absolute values as a multiset of `ℝ`-valued absolute values on `K`. -/
  archAbsVal : Multiset (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values as a set of `ℝ`-valued absolute values on `K`. -/
  nonarchAbsVal : Set (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  isNonarchimedean : ∀ v ∈ nonarchAbsVal, IsNonarchimedean v
  /-- Only finitely many (nonarchimedean) absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_finite {x : K} (_ : x ≠ 0) : (fun v : nonarchAbsVal ↦ v.val x).mulSupport.Finite
  /-- The product formula. The archimedean absolute values are taken with their multiplicity. -/
  product_formula {x : K} (_ : x ≠ 0) :
      (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

open AdmissibleAbsValues Real

variable (K : Type*) [Field K] [AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the multiplicities of
the archimedean places. -/
def totalWeight : ℕ := archAbsVal (K := K) |>.card

variable {K}

/-!
### Heights of field elements

We use the subscipt `₁` to denote multiplicative and logarithmic heights of field elements
(this is because we are in the one-dimensional case of (affine) heights).
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ :=
  (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 :=
  rfl

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁_eq]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁_eq]

lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x := by
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun _ h ↦ ?_) ?_
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
    exact le_max_right ..
  · exact one_le_finprod fun _ ↦ le_max_right ..

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_pos (x : K) : 0 < mulHeight₁ x :=
  zero_lt_one.trans_le <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_ne_zero (x : K) : mulHeight₁ x ≠ 0 :=
  (mulHeight₁_pos x).ne'

lemma zero_le_mulHeight₁ (x : K) : 0 ≤ mulHeight₁ x :=
  (mulHeight₁_pos x).le

/-- The logarithmic height of an element of `K`. -/
def logHeight₁ (x : K) : ℝ := log (mulHeight₁ x)

lemma logHeight₁_eq_log_mulHeight₁ (x : K) : logHeight₁ x = log (mulHeight₁ x) := rfl

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  log_nonneg <| one_le_mulHeight₁ x


/-!
### Heights of tuples and finitely supported maps

We define the multiplicative height of a nonzero tuple `x : ι → K` as the product of the maxima
of `v` on `x`, as `v` runs through the relevant absolute values of `K`. As usual, the
logarithmic height is the logarithm of the multiplicative height.

For a finitely supported function `x : ι →₀ K`, we define the height as the height of `x`
restricted to its support.
-/

variable {ι : Type*}

/-- The multiplicative height of a tuple of elements of `K`. -/
def mulHeight (x : ι → K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

lemma mulHeight_eq (x : ι → K) :
    mulHeight x =
      (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) :=
  rfl

/-- The multiplicative height does not change under re-indexing. -/
lemma mulHeight_comp_equiv {ι' : Type*} (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  simp only [mulHeight_eq, Function.comp_apply, H]

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
def Finsupp.mulHeight (x : α →₀ K) : ℝ :=
  Height.mulHeight fun i : x.support ↦ x i

/-- The logarithmic height of a finitely supported function. -/
def Finsupp.logHeight (x : α →₀ K) : ℝ := log (mulHeight x)

lemma Finsupp.logHeight_eq_log_mulHeight (x : α →₀ K) :
    logHeight x = log (mulHeight x) := rfl

/-!
### Properties of heights
-/

variable [Finite ι]

lemma mulSupport_iSup_nonarchAbsVal_finite {x : ι → K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).Finite := by
  simp_rw [AbsoluteValue.iSup_eq_subtype _ hx]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  exact (Set.finite_iUnion fun i : {j | x j ≠ 0} ↦ mulSupport_finite i.prop).subset <|
    Function.mulSupport_iSup _

lemma mulSupport_max_nonarchAbsVal_finite (x : K) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ v.val x ⊔ 1).Finite := by
  convert mulSupport_iSup_nonarchAbsVal_finite (x := ![x, 1]) <| by simp with v
  rw [max_eq_iSup]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The multiplicative height of a (nonzero) tuple does not change under scaling. -/
lemma mulHeight_smul_eq_mulHeight {x : ι → K} {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := .intro (Function.ne_iff.mp hx).choose
  simp only [mulHeight_eq, Pi.smul_apply, smul_eq_mul, map_mul,
    ← mul_iSup_of_nonneg <| AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (mulSupport_finite hc) (mulSupport_iSup_nonarchAbsVal_finite hx),
    mul_mul_mul_comm, product_formula hc, one_mul]

lemma one_le_mulHeight {x : ι → K} (hx : x ≠ 0) : 1 ≤ mulHeight x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  rw [← mulHeight_smul_eq_mulHeight <| inv_ne_zero hi, mulHeight_eq]
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun vx h ↦ ?_) ?_
  · simp only [Pi.smul_apply, smul_eq_mul, AbsoluteValue.map_mul, map_inv₀, Multiset.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    refine le_ciSup_of_le (Finite.bddAbove_range _) i <| le_of_eq ?_
    exact (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v ↦ le_ciSup_of_le (Finite.bddAbove_range _) i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]

lemma mulHeight_pos {x : ι → K} (hx : x ≠ 0) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight hx

lemma mulHeight.ne_zero {x : ι → K} (hx : x ≠ 0) : mulHeight x ≠ 0 :=
  (mulHeight_pos hx).ne'

lemma zero_le_logHeight {x : ι → K} (hx : x ≠ 0) : 0 ≤ logHeight x :=
  log_nonneg <| one_le_mulHeight hx

/-- The logarithmic height of a (nonzero) tuple does not change under scaling. -/
lemma logHeight_smul_eq_logHeight {x : ι → K} {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight hc]

lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  simp only [mulHeight₁_eq, mulHeight_eq, AbsoluteValue.max_one_eq_iSup]

lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]

lemma mulHeight₁_div_eq_mulHeight (x : K) {y : K} (hy : y ≠ 0) :
    mulHeight₁ (x / y) = mulHeight ![x, y] := by
  rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight hy]
  simp [mul_div_cancel₀ x hy]

lemma logHeight₁_div_eq_logHeight (x : K) {y : K} (hy : y ≠ 0) :
    logHeight₁ (x / y) = logHeight ![x, y] := by
  rw [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_div_eq_mulHeight x hy]

/-- The multiplicative height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n`th power of its multiplicative height. -/
lemma mulHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) :
    mulHeight (x ^ n) = mulHeight x ^ n := by
  have : Fintype ι := Fintype.ofFinite ι
  have : Nonempty ι := Nonempty.intro (Function.ne_iff.mp hx).choose
  simp [mulHeight, ← iSup_pow_of_nonneg fun _ ↦ AbsoluteValue.nonneg .., mul_pow,
    finprod_pow <| mulSupport_iSup_nonarchAbsVal_finite hx, ← Multiset.prod_map_pow]

/-- The logarithmic height of the coordinate-wise `n`th power of a (nonzero) tuple
is `n` times its logarithmic height. -/
lemma logHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow hx]

/-- The multiplicative height of the inverse of a field element `x`
is the same as the multiplicative height of `x`. -/
lemma mulHeight₁_inv (x : K) : mulHeight₁ (x⁻¹) = mulHeight₁ x := by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have H : x • ![x⁻¹, 1] = ![1, x] := funext fun i ↦ by fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight hx, H, mulHeight_swap]

/-- The logarithmic height of the inverse of a field element `x`
is the same as the logarithmic height of `x`. -/
lemma logHeight₁_inv (x : K) : logHeight₁ (x⁻¹) = logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℕ`)
is the `n`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_pow (x : K) (n : ℕ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n := by
  have hx : ![x, 1] ≠ 0 := Function.ne_iff.mpr ⟨1, by simp⟩
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow hx]
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
