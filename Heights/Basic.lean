import Mathlib

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We need a family of absolute values `|·|_v` on `K`.
* All but finitely many of these are non-archimedean (i.e., `|x+y| ≤ max |x| |y|`).
* For a given `x ≠ 0` in `K`, `|x|_v = 1` for all but finitely many `v`.
* We have the *product formula* `∏ v, |x|_v = 1` for all `x ≠ 0` in `K`.

## Implementation

In the context of the product formula (and to allow for some flexibility as to normalizations),
it makes sense to weaken the triangle inequality for archimedean absolute values from
`|x+y| ≤ |x| + |y|` to `|x+y| ≤ C_v * max |x| |y|` for some constant `C_v`.
(The usual triangle inequality implies this with `C_v = 2`, but it will still be true
for powers of an archimedean absolute value.) The main motivation is that we want
to allow the square of the standard absolute value on a complex embedding of a number field.
The requirement "all but finitely many absolute values are non-archimedean" then translates into
`C_v = 1` for all but finitely many `v`. A disadvantage is that we cannot use the existing
`AbsoluteValue` type (because that requires the usual triangle inequality). Instead, we
use `K →*₀ ℝ≥0` together with the weak triangle inequality above. A further disadvantage
is that the obtain less-than-optimal bounds for heights of sums with more than two terms,
e.g., we get that `H_ℚ (x + y + z) ≤ 4 * H_ℚ x * H_ℚ y * H_ℚ z` instead of `≤ 3 * ⋯`.

A possible alternative could be to use a family of `AbsoluteValue`s together with a family
of exponents `e_v` such that the product formula holds in the form `∏ v, |x|_v ^ e_v = 1`.
Disadvangtages of this approach are the mostly unnecessary additional degrees of freedom
in the pairs `(|·|_v, e_v)` and that we need to separately encode the requirement that
all but finitely many of the absolute values are non-archimedean.

We realize the first alternative above via the class `AdmissibleAbsValues K`.

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

## Main results


-/

/-!
### Auxiliary statements

These fill API gaps in Mathlib and should eventually go there.
-/

section aux

variable {α β : Type*}

lemma max_eq_iSup [ConditionallyCompleteLattice α] (a b : α) : max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

lemma finprod_mono [OrderedCommMonoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (Set.Finite.union hf hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  have hf₁ : f.mulSupport ⊆ s := by
    simp only [Set.coe_toFinset, Set.subset_union_left, s]
  have hg₁ : g.mulSupport ⊆ s := by
    simp only [Set.coe_toFinset, Set.subset_union_right, s]
  rw [finprod_eq_finset_prod_of_mulSupport_subset f hf₁,
    finprod_eq_finset_prod_of_mulSupport_subset g hg₁]
  exact Finset.prod_le_prod' fun i _ ↦ h i

lemma Function.mulSupport_mul_finite [Monoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (Function.mulSupport fun a ↦ f a * g a).Finite :=
  (hf.union hg).subset <| mulSupport_mul f g

end aux

noncomputable section

namespace Height

open NNReal

/-!
### Families of admissible absolute values

We define the class `AdmissibleAbsValues K` for a field `K`, which captures the notion of a
family of absolute values (with possibly relaxed triangle inequality) on `K` satisfying
a product formula.
-/

/-- A type class capturing an admissible family of (weak) absolute values. -/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The type indexing the family of absolute values -/
  Vals : Type*
  /-- The absolute values as `MonoidWithZeroHom` -/
  absValue : Vals → (K →*₀ ℝ≥0)
  /-- The constants for the weak triangle inequality -/
  triangleIneqBound : Vals → ℝ≥0
  /-- The weak triangle inequality -/
  weak_triangle_inequality (v : Vals) (x y : K) :
    absValue v (x + y) ≤ triangleIneqBound v * max (absValue v x) (absValue v y)
  /-- Only finitely many of the bounds are `≠ 1`. -/
  mulSupport_ineqBounds_finite : triangleIneqBound.mulSupport.Finite
  /-- Only finitely many absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_absValues_finite {x : K} (_ : x ≠ 0) : (absValue · x).mulSupport.Finite
  /-- The product formula -/
  product_formula {x : K} (_ : x ≠ 0) : ∏ᶠ v : Vals, absValue v x = 1

def heightSumBound (K : Type*) [Field K] [aav : AdmissibleAbsValues K] : ℝ≥0 :=
  ∏ᶠ v : aav.Vals, aav.triangleIneqBound v

variable {K : Type*} [Field K] [aav : AdmissibleAbsValues K]

open AdmissibleAbsValues

lemma one_le_triangleIneqBound (v : aav.Vals) : 1 ≤ triangleIneqBound v := by
  have := weak_triangle_inequality v 1 0
  simpa only [ge_iff_le, add_zero, map_one, map_zero, zero_le, sup_of_le_left, mul_one] using this

variable (K) in
lemma one_le_heightSumBound : 1 ≤ heightSumBound K :=
  one_le_finprod' one_le_triangleIneqBound

-- This is needed as a side condition in proofs about logarithmic heights
variable (K) in
lemma heightSumBound_ne_zero : (heightSumBound K : ℝ) ≠ 0 :=
  mod_cast (zero_lt_one.trans_le <| one_le_heightSumBound K).ne'

/-!
### Heights of field elements
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ≥0 := ∏ᶠ v, max (absValue v x) 1

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp only [mulHeight₁, map_zero, zero_le, sup_of_le_right, finprod_one]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp only [mulHeight₁, map_one, max_self, finprod_one]

lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x :=
  one_le_finprod' fun _ ↦ le_max_right ..

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_pos (x : K) : 0 < (mulHeight₁ x : ℝ) :=
  mod_cast zero_lt_one.trans_le <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_ne_zero (x : K) : (mulHeight₁ x : ℝ) ≠ 0 :=
  (mulHeight₁_pos x).ne'

/-- The logarithmic height of an element of `K`. -/
def logHeight₁ (x : K) : ℝ := Real.log (mulHeight₁ x)

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp only [logHeight₁, mulHeight₁_zero, coe_one, Real.log_one]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp only [logHeight₁, mulHeight₁_one, coe_one, Real.log_one]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| mod_cast one_le_mulHeight₁ x

/-!
### Heights of tuples and finitely supported maps
-/

variable {ι : Type*} [Fintype ι]

lemma iSup_absValue_eq (x : ι → K) (v : aav.Vals) :
    ⨆ i, absValue v (x i) = ⨆ i : {j // x j ≠ 0}, absValue v (x i) := by
  apply le_antisymm
  · refine ciSup_le' fun i ↦ ?_
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero, ne_eq, zero_le]
    · rw [show i = (⟨i, h⟩ : {j // x j ≠ 0}) from rfl]
      exact le_ciSup (f := fun i : {j // x j ≠ 0} ↦ absValue v (x i)) (Finite.bddAbove_range _) _
  · exact ciSup_le' fun ⟨i, hi⟩ ↦
      le_ciSup (f := fun i ↦ absValue v (x i)) (Finite.bddAbove_range _) i

lemma mulSupport_iSup_absValue_finite {x : ι → K} (hx : x ≠ 0) :
    (Function.mulSupport fun v ↦ ⨆ i, absValue v (x i)).Finite := by
  simp_rw [iSup_absValue_eq]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  exact (Set.finite_iUnion fun i ↦ mulSupport_absValues_finite i.prop).subset <|
    Function.mulSupport_iSup _

lemma mulSupport_max_absValue_finite (x : K) :
    (Function.mulSupport fun v ↦ (absValue v) x ⊔ 1).Finite := by
  convert mulSupport_iSup_absValue_finite (x := ![x, 1]) <| by simp with v
  rw [max_eq_iSup]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The multiplicative height of a tuple of elements of `K`. -/
def mulHeight (x : ι → K) : ℝ≥0 :=
  ∏ᶠ v, ⨆ i, absValue v (x i)

omit [Fintype ι] in
/-- The multiplicative height does not change under re-indexing. -/
lemma mulHeight_comp_equiv {ι' : Type*} (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  simp only [mulHeight, Function.comp_apply]
  congr 1
  ext1 v
  exact e.iSup_congr (congrFun rfl)

lemma mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x] := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  convert mulHeight_comp_equiv e ![y, x]
  ext i
  fin_cases i <;> simp [e]

/-- The logarithmic height of a tuple of elements of `K`. -/
def logHeight (x : ι → K) : ℝ := Real.log (mulHeight x)

/-- The multiplicative height of a finitely supported function. -/
def mulHeight_finsupp {α : Type*} (x : α →₀ K) : ℝ≥0 :=
  mulHeight fun i : x.support ↦ x i

/-- The logarithmic height of a finitely supported function. -/
def logHeight_finsupp {α :Type*} (x : α →₀ K) : ℝ := Real.log (mulHeight_finsupp x)


/-!
### Properties of heights
-/

/-- The multiplicative height of a (nonzero) tuple does not change under scaling. -/
lemma mulHeight_mul_eq_mulHeight {x : ι → K} (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  simp only [mulHeight, Pi.smul_apply, smul_eq_mul, map_mul, ← mul_iSup]
  rw [finprod_mul_distrib (mulSupport_absValues_finite hc) (mulSupport_iSup_absValue_finite hx),
    product_formula hc, one_mul]

/-- The logarithmic height of a (nonzero) tuple does not change under scaling. -/
lemma logHeight_mul_eq_logHeight {x : ι → K} (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight, mulHeight_mul_eq_mulHeight hx hc]

lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  simp only [mulHeight₁, mulHeight, Nat.succ_eq_add_one, Nat.reduceAdd]
  congr
  ext1 v
  have H i : absValue v (![x, 1] i) = ![absValue v x, 1] i := by
    fin_cases i
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.head_cons, map_one]
  simp_rw [H]
  exact max_eq_iSup (absValue v x) 1

lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁, logHeight, mulHeight₁_eq_mulHeight x]

/-- The multiplicative height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n`th power of its multiplicative height. -/
lemma mulHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : mulHeight (x ^ n) = mulHeight x ^ n := by
  have ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := Nonempty.intro i
  rcases n.eq_zero_or_pos with rfl | hn₀
  · simp only [mulHeight, Pi.pow_apply, pow_zero, map_one, ciSup_const, finprod_one]
  simp only [mulHeight, Pi.pow_apply, map_pow]
  rw [finprod_pow <| mulSupport_iSup_absValue_finite hx]
  congr 1
  ext1 v
  refine eq_of_forall_ge_iff fun c ↦ ?_
  rw [ciSup_le_iff <| Finite.bddAbove_range _]
  have hn : 0 < (n : ℝ)⁻¹ := inv_pos_of_pos <| Nat.cast_pos'.mpr hn₀
  conv => enter [1, i]; rw [← rpow_natCast, ← inv_inv (n : ℝ), rpow_inv_le_iff hn]
  conv => enter [2]; rw [← rpow_natCast, ← inv_inv (n : ℝ), rpow_inv_le_iff hn]
  exact (ciSup_le_iff <| Finite.bddAbove_range _).symm

/-- The logarithmic height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n` times its logarithmic height. -/
lemma logHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp only [logHeight, mulHeight_pow hx, coe_pow, Real.log_pow]

/-- The multiplicative height of the inverse of a field element `x`
is the same as the multiplicative height of `x`. -/
lemma mulHeight₁_inv (x : K) : mulHeight₁ (x⁻¹) = mulHeight₁ x := by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, inv_zero]
  · have H : x • ![x⁻¹, 1] = ![1, x] := by
      ext1 i
      fin_cases i <;> simp [hx]
    have H' : ![x⁻¹, 1] ≠ 0 := Function.ne_iff.mpr ⟨1, by simp⟩
    rw [← mulHeight_mul_eq_mulHeight H' hx, H, mulHeight_swap]

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
  simp only [logHeight₁, mulHeight₁_pow, coe_pow, Real.log_pow]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℤ`)
is the `|n|`th power of the multiplicative height of `x`. -/
lemma mulHeight₁_zpow (x : K) (n : ℤ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs := by
  rcases Int.le_or_lt 0 n with h | h
  · lift n to ℕ using h
    rw [zpow_natCast, mulHeight₁_pow, Int.natAbs_ofNat]
  · nth_rewrite 1 [show n = -n.natAbs by rw [Int.ofNat_natAbs_of_nonpos h.le, neg_neg]]
    rw [zpow_neg, mulHeight₁_inv, zpow_natCast, mulHeight₁_pow]

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℤ`)
is `|n|` times the multiplicative height of `x`. -/
lemma logHeight₁_zpow (x : K) (n : ℤ) : logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x := by
  simp only [logHeight₁, mulHeight₁_zpow, coe_pow, Real.log_pow]

/-- The multiplicative height of `x + y` is at most the "height sum bound" of the parent field
times the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ heightSumBound K * mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁, heightSumBound]
  have hf₁ : (Function.mulSupport fun v↦ triangleIneqBound v * ((absValue v) x ⊔ 1)).Finite :=
    Function.mulSupport_mul_finite mulSupport_ineqBounds_finite <| mulSupport_max_absValue_finite x
  have hf₂ : (Function.mulSupport fun v ↦
      triangleIneqBound v * ((absValue v) x ⊔ 1) * ((absValue v) y ⊔ 1)).Finite := by
    refine Function.mulSupport_mul_finite ?_ <| mulSupport_max_absValue_finite y
    exact Function.mulSupport_mul_finite mulSupport_ineqBounds_finite <|
      mulSupport_max_absValue_finite x
  rw [← finprod_mul_distrib mulSupport_ineqBounds_finite (mulSupport_max_absValue_finite x),
    ← finprod_mul_distrib hf₁ (mulSupport_max_absValue_finite y)]
  refine finprod_mono (mulSupport_max_absValue_finite (x + y)) hf₂ fun v ↦ sup_le ?_ ?_
  · rw [mul_assoc]
    refine (weak_triangle_inequality v x y).trans ?_
    gcongr
    refine sup_le ?_ ?_
    · rw [← mul_one <| (absValue v) x]
      gcongr
      · simp only [mul_one, le_sup_left]
      · simp only [le_sup_right]
    · rw [← one_mul <| (absValue v) y]
      gcongr
      · simp only [le_sup_right]
      · simp only [one_mul, le_sup_left]
  · rw [mul_assoc]
    refine one_le_mul (one_le_triangleIneqBound v) <| one_le_mul ?_ ?_
    exact le_max_right ((absValue v) x) 1
    exact le_max_right ((absValue v) y) 1

/-- The logarithmic height of `x + y` is at most the `log` of the "height sum bound"
of the parent field plus the sum of the logarithmic heights of `x` and `y`. -/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) ≤ Real.log (heightSumBound K) + logHeight₁ x + logHeight₁ y := by
  have hb : (heightSumBound K : ℝ) ≠ 0 := heightSumBound_ne_zero K
  have hx : (mulHeight₁ x : ℝ) ≠ 0 := mulHeight₁_ne_zero x
  have hy : (mulHeight₁ y : ℝ) ≠ 0 := mulHeight₁_ne_zero y
  simp only [logHeight₁]
  rw [← Real.log_mul hb hx, ← Real.log_mul (mul_ne_zero hb hx) hy]
  refine Real.log_le_log (zero_lt_one.trans_le <| one_le_mulHeight₁ _) ?_
  exact_mod_cast mulHeight₁_add_le x y

/-- The multiplicative height of a finite sum of field elements is at most the `(n-1)`th power
of the "height sum bound" of the parent field times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values
-- in the definition of `AdmissibleAbsValues`.
lemma mulHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤ heightSumBound K ^ (s.card - 1) * ∏ a ∈ s, mulHeight₁ (x a) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      · simp only [ha, not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_not_mem,
          add_tsub_cancel_right, Finset.prod_insert]
        calc
        _ ≤ heightSumBound K * mulHeight₁ (x a) * mulHeight₁ (∑ b ∈ s, x b) := mulHeight₁_add_le ..
        _ ≤ heightSumBound K * mulHeight₁ (x a) *
              (heightSumBound K ^ (s.card - 1) * ∏ b ∈ s, mulHeight₁ (x b)) := by gcongr
        _ = _ := by
          rw [mul_left_comm, ← mul_assoc, ← mul_assoc, ← pow_succ,
            Nat.sub_add_cancel <| Finset.one_le_card.mpr hs, ← mul_assoc]

/-- The logarithmic height of a finite sum of field elements is at most the `(n-1)` times the `log`
of the "height sum bound" of the parent field plus the sum of the individual multiplicative
heights, where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values
-- in the definition of `AdmissibleAbsValues`.
lemma logHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤
      (s.card - 1 : ) * Real.log (heightSumBound K) + ∑ a ∈ s, logHeight₁ (x a) := by
  simp only [logHeight₁]
  rw [← Real.log_pow, ← Real.log_prod _ _ <| fun a _ ↦ mulHeight₁_ne_zero (x a),
    ← Real.log_mul ?h₁ ?h₂]
  · exact Real.log_le_log (mulHeight₁_pos _) <| mod_cast mulHeight₁_sum_le ..
  case h₁ => exact pow_ne_zero _ <| heightSumBound_ne_zero K
  case h₂ => exact Finset.prod_ne_zero_iff.mpr fun a _ ↦ mulHeight₁_ne_zero (x a)

end Height

/-!
### Heights on projective spaces
-/

namespace Projectivization

open NNReal Height AdmissibleAbsValues

variable {K : Type*} [Field K] [aav : AdmissibleAbsValues K] {ι : Type*} [Fintype ι]

private
lemma mulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  h ▸ mulHeight_mul_eq_mulHeight b.prop fun H ↦ a.prop <| (H ▸ h).trans <| zero_smul K b.val

private
lemma logHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    logHeight a.val = logHeight b.val :=
  congrArg Real.log <| mod_cast mulHeight_aux a b t h

/-- The multiplicative height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
def mulHeight (x : Projectivization K (ι → K)) : ℝ≥0 :=
  Projectivization.lift (fun r ↦ Height.mulHeight r.val) mulHeight_aux x

/-- The logarithmic height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
def logHeight (x : Projectivization K (ι → K)) : ℝ :=
  Projectivization.lift (fun r ↦ Height.logHeight r.val) logHeight_aux x

lemma mulHeight_mk {x : ι → K} (hx : x ≠ 0) : mulHeight (mk K x hx) = Height.mulHeight x := rfl

lemma logHeight_mk {x : ι → K} (hx : x ≠ 0) : logHeight (mk K x hx) = Height.logHeight x := rfl


end Projectivization
