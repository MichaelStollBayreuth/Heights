import Heights.Auxiliary
-- import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We have a multiset of archimedean absolute values on `K` (with values in `ℝ`).
* We also have a set of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`, where the first product is over the multiset of archimedean
  absolute values.

We realize this implementation via the class `AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `mulHeight₁ x` and `logHeight₁ x` for `x : K`. This is the height of an element of `K`.
* `mulHeight x` and `logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K` (for `x ≠ 0`).
* `mulHeight_finsupp x` and `logHeight_finsupp x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to any finite subtype containing the support of `x`.
* `Projectivization.mulHeight` and `Projectivization.logHeight` on
  `Projectivization K (ι → K)` (with a `Fintype ι`). This is the height of a point
  on projective space (with fixed basis).

## Main results


-/

section aux

-- Some lemmas needed later

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

noncomputable section

namespace Height

/-!
### Families of admissible absolute values

We define the class `AdmissibleAbsValues K` for a field `K`, which captures the notion of a
family of absolute values on `K` satisfying a product formula.
-/

/-- A type class capturing an admissible family of (weak) absolute values. -/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The archimedean absolute values. -/
  archAbsVal : Multiset (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values. -/
  nonarchAbsVal : Set (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  strong_triangle_ineq : ∀ v ∈ nonarchAbsVal, IsNonarchimedean v
  /-- Only finitely many absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_nonarchAbsVal_finite {x : K} (_ : x ≠ 0) :
      (fun v : nonarchAbsVal ↦ v.val x).mulSupport.Finite
  /-- The product formula -/
  product_formula {x : K} (_ : x ≠ 0) :
      (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

open AdmissibleAbsValues

variable (K : Type*) [Field K] [aav : AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the weights of
the archimedean places. -/
def totalWeight : ℕ := archAbsVal (K := K).card

variable {K}

/-!
### Heights of field elements
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ :=
  (archAbsVal.map (fun v ↦ max (v x) 1)).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁]

lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x := by
  classical
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · refine Multiset.one_le_prod fun _ h ↦ ?_
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
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
def logHeight₁ (x : K) : ℝ := Real.log (mulHeight₁ x)

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| one_le_mulHeight₁ x


/-!
### Heights of tuples and finitely supported maps
-/

variable {ι : Type*} [Fintype ι]

lemma mulSupport_iSup_absValue_finite {x : ι → K} (hx : x ≠ 0) :
    (Function.mulSupport (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i))).Finite := by
  simp_rw [AbsoluteValue.iSup_eq_subtype _ hx]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  exact (Set.finite_iUnion fun i : {j | x j ≠ 0} ↦ mulSupport_nonarchAbsVal_finite i.prop).subset <|
    Function.mulSupport_iSup _

lemma mulSupport_max_absValue_finite (x : K) :
    (Function.mulSupport fun v : nonarchAbsVal ↦ v.val x ⊔ 1).Finite := by
  convert mulSupport_iSup_absValue_finite (x := ![x, 1]) <| by simp with v
  rw [max_eq_iSup]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The multiplicative height of a tuple of elements of `K`. -/
def mulHeight (x : ι → K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

omit [Fintype ι] in
/-- The multiplicative height does not change under re-indexing. -/
lemma mulHeight_comp_equiv {ι' : Type*} (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  simp only [mulHeight, Function.comp_apply, H]

lemma mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x] := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  convert mulHeight_comp_equiv e ![y, x]
  ext i
  fin_cases i <;> simp [e]

/-- The logarithmic height of a tuple of elements of `K`. -/
def logHeight (x : ι → K) : ℝ := Real.log (mulHeight x)

/-- The multiplicative height of a finitely supported function. -/
def mulHeight_finsupp {α : Type*} (x : α →₀ K) : ℝ :=
  mulHeight fun i : x.support ↦ x i

/-- The logarithmic height of a finitely supported function. -/
def logHeight_finsupp {α :Type*} (x : α →₀ K) : ℝ := Real.log (mulHeight_finsupp x)


/-!
### Properties of heights
-/

/-- The multiplicative height of a (nonzero) tuple does not change under scaling. -/
lemma mulHeight_smul_eq_mulHeight {x : ι → K} {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := Nonempty.intro (Function.ne_iff.mp hx).choose
  simp only [mulHeight, Pi.smul_apply, smul_eq_mul, map_mul,
    ← Real.mul_iSup_of_nonneg <| AbsoluteValue.nonneg ..]
  rw [Multiset.prod_map_mul,
    finprod_mul_distrib (mulSupport_nonarchAbsVal_finite hc) (mulSupport_iSup_absValue_finite hx),
    mul_mul_mul_comm, product_formula hc, one_mul]

lemma one_le_mulHeight {x : ι → K} (hx : x ≠ 0) : 1 ≤ mulHeight x := by
  have ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  rw [← mulHeight_smul_eq_mulHeight <| inv_ne_zero hi, mulHeight]
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · refine Multiset.one_le_prod fun vx h ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, AbsoluteValue.map_mul, map_inv₀, Multiset.mem_map] at h
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
  Real.log_nonneg <| one_le_mulHeight hx

/-- The logarithmic height of a (nonzero) tuple does not change under scaling. -/
lemma logHeight_smul_eq_logHeight {x : ι → K} {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight, mulHeight_smul_eq_mulHeight hc]

lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  simp only [mulHeight₁, mulHeight, Nat.succ_eq_add_one, Nat.reduceAdd]
  congr <;> ext1 v
  · rw [v.max_one_eq_iSup]
  · exact AbsoluteValue.max_one_eq_iSup ..

lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁, logHeight, mulHeight₁_eq_mulHeight x]

lemma mulHeight₁_div_eq_mulHeight (x : K) {y : K} (hy : y ≠ 0) :
    mulHeight₁ (x / y) = mulHeight ![x, y] := by
  rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight hy]
  simp [mul_div_cancel₀ x hy]

lemma logHeight₁_div_eq_logHeight (x : K) {y : K} (hy : y ≠ 0) :
    logHeight₁ (x / y) = logHeight ![x, y] := by
  rw [logHeight₁, logHeight, mulHeight₁_div_eq_mulHeight x hy]

/-- The multiplicative height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n`th power of its multiplicative height. -/
lemma mulHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : mulHeight (x ^ n) = mulHeight x ^ n := by
  have : Nonempty ι := Nonempty.intro (Function.ne_iff.mp hx).choose
  simp only [mulHeight, Pi.pow_apply, map_pow]
  rw [mul_pow, finprod_pow <| mulSupport_iSup_absValue_finite hx, ← Multiset.prod_map_pow,]
  congr 2 <;> ext1 v
  · simp only [Real.iSup_pow_of_nonneg fun _ ↦ AbsoluteValue.nonneg ..]
  · exact (Real.iSup_pow_of_nonneg (fun _ ↦ AbsoluteValue.nonneg ..) n).symm

/-- The logarithmic height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n` times its logarithmic height. -/
lemma logHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight, mulHeight_pow hx]

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
  simp only [logHeight₁, mulHeight₁_inv]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℕ`)
is the `n`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_pow (x : K) (n : ℕ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n := by
  have hx : ![x, 1] ≠ 0 := Function.ne_iff.mpr ⟨1, by simp⟩
  simp only [mulHeight₁_eq_mulHeight]
  rw [← mulHeight_pow hx]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℕ`)
is `n` times the multiplicative height of `x`. -/
lemma logHeight₁_pow (x : K) (n : ℕ) : logHeight₁ (x ^ n) = n * logHeight₁ x := by
  simp only [logHeight₁, mulHeight₁_pow, Real.log_pow]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℤ`)
is the `|n|`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_zpow (x : K) (n : ℤ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs := by
  rcases le_or_gt 0 n with h | h
  · lift n to ℕ using h
    rw [zpow_natCast, mulHeight₁_pow, Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by rw [Int.ofNat_natAbs_of_nonpos h.le, neg_neg]]
    rw [zpow_neg, mulHeight₁_inv, zpow_natCast, mulHeight₁_pow]

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℤ`)
is `|n|` times the multiplicative height of `x`. -/
lemma logHeight₁_zpow (x : K) (n : ℤ) : logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x := by
  simp only [logHeight₁, mulHeight₁_zpow, Real.log_pow]

/-- The multiplicative height of `x + y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁, totalWeight]
  rw [--← Finset.prod_pow_eq_pow_sum,
    mul_mul_mul_comm, ← mul_assoc,← mul_assoc, mul_assoc (2 ^ _),
    ← Multiset.prod_map_mul, ← smul_eq_mul (2 ^ _), ← Multiset.card_map, Multiset.smul_prod,
    Multiset.map_map, mul_assoc,
    ← finprod_mul_distrib (mulSupport_max_absValue_finite x) (mulSupport_max_absValue_finite y)]
  simp only [Function.comp_apply, smul_eq_mul]
  gcongr
  · -- 0 ≤ ∏ᶠ (v : NonarchAbsVal K), (nonarchAbsVal v) (x + y) ⊔ 1
    exact finprod_nonneg fun _ ↦ zero_le_one.trans (le_max_right _ 1)
  · -- 0 ≤ (Multiset.map (fun x_1 ↦ 2 * (max (x_1 y) 1 * max (x_1 x) 1)) archAbsVal).prod
    refine Multiset.prod_nonneg fun vx h ↦ ?_
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
    positivity
  · -- (Multiset.map (fun v ↦ max (v (x + y)) 1) archAbsVal).prod ≤
    -- (Multiset.map (fun x_1 ↦ 2 * (max (x_1 y) 1 * max (x_1 x) 1)) archAbsVal).prod
    refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) (fun v hv ↦ sup_le ?_ ?_)
    · refine (v.add_le x y).trans ?_
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_mul, one_mul]
      exact add_le_add (le_mul_max_max_right ..) (le_mul_max_max_left ..)
    · refine (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
      exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two
  · -- ∏ᶠ v, (nonarchAbsVal v) (x + y) ⊔ 1 ≤
    --   ∏ᶠ v, ((nonarchAbsVal v) x ⊔ 1) * ((nonarchAbsVal v) y ⊔ 1)
    have hf := Function.mulSupport_mul_finite (mulSupport_max_absValue_finite x)
      (mulSupport_max_absValue_finite y)
    refine finprod_mono' (mulSupport_max_absValue_finite _)
      (fun _ ↦ zero_le_one.trans <| le_max_right _ 1) hf fun v ↦ sup_le ?_ <| one_le_mul_max_max ..
    exact (strong_triangle_ineq v.val v.prop x y).trans <|
      sup_le (le_mul_max_max_left ..) (le_mul_max_max_right ..)

open Real in
/-- The logarithmic height of `x + y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`. -/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) ≤ totalWeight K * Real.log 2 + logHeight₁ x + logHeight₁ y := by
  have hb : (2 ^ totalWeight K : ℝ) ≠ 0 := NeZero.ne _
  have hx : mulHeight₁ x ≠ 0 := mulHeight₁_ne_zero x
  have hy : mulHeight₁ y ≠ 0 := mulHeight₁_ne_zero y
  simp only [logHeight₁]
  rw [ ← log_pow, ← log_mul hb hx, ← log_mul ((mul_ne_zero_iff_right hx).mpr hb) hy]
  exact log_le_log (zero_lt_one.trans_le <| one_le_mulHeight₁ _) <| mulHeight₁_add_le x y

/-- The multiplicative height of a finite sum of field elements is at most
`2 ^ ((n-1) ' totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values.
lemma mulHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤
      2 ^ ((s.card - 1) * totalWeight K) * ∏ a ∈ s, mulHeight₁ (x a) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      · simp only [ha, not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_notMem,
          add_tsub_cancel_right, Finset.prod_insert]
        calc
        _ ≤ 2 ^ totalWeight K * mulHeight₁ (x a) * mulHeight₁ (∑ b ∈ s, x b) :=
          mulHeight₁_add_le ..
        _ ≤ 2 ^ totalWeight K * mulHeight₁ (x a) *
              (2 ^ ((s.card - 1) * totalWeight K) * ∏ b ∈ s, mulHeight₁ (x b)) := by
          gcongr
          exact mul_nonneg (pow_nonneg zero_le_two _) <| zero_le_mulHeight₁ _
        _ = _ := by
          rw [mul_left_comm, ← mul_assoc, ← mul_assoc, ← pow_add]
          nth_rewrite 2 [← one_mul <| totalWeight K]
          rw [← add_mul, Nat.sub_add_cancel <| Finset.one_le_card.mpr hs, ← mul_assoc]

open Real in
/-- The logarithmic height of a finite sum of field elements is at most
`(n-1) * totalWeight K * log 2` plus the sum of the individual logarithmic heights,
where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values.
lemma logHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤
      ((s.card - 1) * totalWeight K : ) * Real.log 2 + ∑ a ∈ s, logHeight₁ (x a) := by
  simp only [logHeight₁]
  rw [← log_pow, ← log_prod <| fun a _ ↦ mulHeight₁_ne_zero (x a), ← log_mul ?h₁ ?h₂]
  · exact log_le_log (mulHeight₁_pos _) <| mod_cast mulHeight₁_sum_le ..
  case h₁ => exact pow_ne_zero _ two_ne_zero
  case h₂ => exact Finset.prod_ne_zero_iff.mpr fun a _ ↦ mulHeight₁_ne_zero (x a)

end Height

/-!
### Heights on projective spaces
-/

namespace Projectivization

open Height AdmissibleAbsValues

variable {K : Type*} [Field K] [aav : AdmissibleAbsValues K] {ι : Type*} [Fintype ι]

private
lemma mulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  h ▸ mulHeight_smul_eq_mulHeight fun H ↦ a.prop <| (H ▸ h).trans <| zero_smul K b.val

private
lemma logHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    logHeight a.val = logHeight b.val :=
  congrArg Real.log <| mod_cast mulHeight_aux a b t h

/-- The multiplicative height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
def mulHeight (x : Projectivization K (ι → K)) : ℝ :=
  Projectivization.lift (fun r ↦ Height.mulHeight r.val) mulHeight_aux x

/-- The logarithmic height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
def logHeight (x : Projectivization K (ι → K)) : ℝ :=
  Projectivization.lift (fun r ↦ Height.logHeight r.val) logHeight_aux x

lemma mulHeight_mk {x : ι → K} (hx : x ≠ 0) : mulHeight (mk K x hx) = Height.mulHeight x := rfl

lemma logHeight_mk {x : ι → K} (hx : x ≠ 0) : logHeight (mk K x hx) = Height.logHeight x := rfl

lemma logHeight_eq_log_mulHeight (x : Projectivization K (ι → K)) :
    logHeight x = Real.log (mulHeight x) := by
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
  exact Real.log_nonneg <| x.one_le_mulHeight

end Projectivization
