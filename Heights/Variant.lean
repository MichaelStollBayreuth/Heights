import Mathlib

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We need a finite family of archimedean absolute values on `K` (with values in `ℝ`).
* Each of these comes with a weight `weight v`.
* We also have a familiy of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|_v = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|_v^(weight v) * ∏ v : nonarch, |x|_v = 1`
  for all `x ≠ 0` in `K`.

## Implementation

This file implements an alternative to the version outlined in [[Basic.lean]].
The motivation is that trying to use the more uniform structure as defined there
leads to some pain when trying to produce an instance of `AdmissibleAbsValues K`
for a number field `K`: `Vals` is naturally given as `FinitePlace K ⊕ InfinitePlace K`,
so all functions on `Vals` need to be defined via `Sum.elim` (or `match`), and we found
the API for such functions severely lacking.

We realize our alternative implementation via the class `AdmissibleAbsValues K`.

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

/-!
### Auxiliary statements

These fill API gaps in Mathlib and should eventually go there.
-/

section aux

variable {α β : Type*}

lemma max_eq_iSup [ConditionallyCompleteLattice α] (a b : α) : max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

lemma ciSupℝ_pow [Fintype α] [Nonempty α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
    (⨆ a, f a) ^ n = ⨆ a, (f a ^ n) := by
  have H a : ((f a).toNNReal  : ℝ) = f a := Real.coe_toNNReal (f a) (hf a)
  conv => enter [1, 1, 1, a]; rw [← H]
  conv => enter [2, 1, a]; rw [← H]
  norm_cast
  exact Monotone.map_ciSup_of_continuousAt ((continuous_pow n).continuousAt)
    (pow_left_mono n) (Finite.bddAbove_range _)

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

/-- Monotonicity of `finprod`. See `finprod_mono` for a variant
where `β` is a `OrderedCommMonoid`. -/
lemma finprod_mono' [CommMonoidWithZero β] [PartialOrder β] [ZeroLEOneClass β] [PosMulMono β]
    {f g : α → β} (hf : f.mulSupport.Finite) (hf₀ : ∀ a, 0 ≤ f a)
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
  exact Finset.prod_le_prod (fun i _ ↦ hf₀ i) fun i _ ↦ h i

lemma Function.mulSupport_mul_finite [Monoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (Function.mulSupport fun a ↦ f a * g a).Finite :=
  (hf.union hg).subset <| mulSupport_mul f g

lemma one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preorder M] [ZeroLEOneClass M]
    [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ ↦ one_le_mul_of_one_le_of_one_le) hf

lemma Finset.one_le_prod [DecidableEq α] (s : Finset α) {M : Type*} [CommMonoidWithZero M]
    [Preorder M] [ZeroLEOneClass M] [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s h ih => simpa [h] using one_le_mul_of_one_le_of_one_le (hf a) ih

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

lemma AbsoluteValue.iSup_eq_subtype (v : AbsoluteValue K ℝ) {x : ι → K} (hx : x ≠ 0) :
    ⨆ i, v (x i) = ⨆ i : {j // x j ≠ 0}, v (x i) := by
  have ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty {j // x j ≠ 0} := Nonempty.intro ⟨i, hi⟩
  have : Nonempty ι := Nonempty.intro i
  apply le_antisymm
  · refine ciSup_le fun j ↦ ?_
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, AbsoluteValue.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, AbsoluteValue.nonneg ..⟩
    · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl

lemma AbsoluteValue.max_one_eq_iSup (v : AbsoluteValue K ℝ) (x : K) :
    v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
  have H (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
  simp_rw [H]
  exact max_eq_iSup (v x) 1

lemma NumberField.FinitePlace.add_le [NumberField K] (v : FinitePlace K) (x y : K) :
    v (x + y) ≤ max (v x) (v y) := by
  simp_rw [← NumberField.FinitePlace.norm_embedding_eq, map_add]
  rcases le_total ‖embedding v.maximalIdeal x‖ ‖embedding v.maximalIdeal y‖ with h | h
  · refine le_sup_of_le_right ?_
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact sup_of_le_right h ▸ Valuation.map_add_le_max' Valued.v ..
  · refine le_sup_of_le_left ?_
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact sup_of_le_left h ▸ Valuation.map_add_le_max' Valued.v ..

private lemma le_mul_max_max_left (a b : ℝ) : b ≤ (b ⊔ 1) * (a ⊔ 1) := by
  nth_rewrite 1 [← mul_one b]
  gcongr
  · exact le_max_left _ 1
  · exact le_max_right _ 1

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
  /-- The type indexing the family of archimedean absolute values -/
  ArchAbsVal : Type*
  /-- The archimedean absolute values. -/
  archAbsVal : ArchAbsVal → AbsoluteValue K ℝ
  /-- There are only finitely many archimedean absolute values. -/
  [archAbsVal_fintype : Fintype ArchAbsVal]
  /-- The weights of the archimedean absolute values.
      They show up as exponents in the product formula. -/
  weight : ArchAbsVal → ℕ
  /-- The weights are positive. -/
  weight_pos : ∀ v, 0 < weight v
  /-- The type indexing the nonarchimedean absolute values. -/
  NonarchAbsVal : Type*
  /-- The nonarchimedean absolute values. -/
  nonarchAbsVal : NonarchAbsVal → AbsoluteValue K ℝ
  /-- The nonarchiemdean absolute values are indeed nonarchimedean. -/
  strong_triangle_ineq :
      ∀ (v : NonarchAbsVal) (x y : K), nonarchAbsVal v (x + y) ≤
        max (nonarchAbsVal v x) (nonarchAbsVal v y)
  /-- Only finitely many absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_nonarchAbsVal_finite {x : K} (_ : x ≠ 0) : (nonarchAbsVal · x).mulSupport.Finite
  /-- The product formula -/
  product_formula {x : K} (_ : x ≠ 0) :
      (∏ v, archAbsVal v x ^ weight v) * ∏ᶠ v, nonarchAbsVal v x = 1

open AdmissibleAbsValues

attribute [instance] archAbsVal_fintype

variable (K : Type*) [Field K] [aav : AdmissibleAbsValues K]

def totalWeight : ℕ := ∑ v : ArchAbsVal K, weight v

variable {K}

/-!
### Instance for number fields
-/

section number_field

open NumberField

instance _root_.NumberField.instAdmissibleAbsValues [NumberField K] : AdmissibleAbsValues K where
  ArchAbsVal := InfinitePlace K
  archAbsVal v := v.val
  archAbsVal_fintype := inferInstance
  weight := InfinitePlace.mult
  weight_pos _ := InfinitePlace.mult_pos
  NonarchAbsVal := FinitePlace K
  nonarchAbsVal v := v.val
  strong_triangle_ineq := FinitePlace.add_le
  mulSupport_nonarchAbsVal_finite := FinitePlace.mulSupport_finite
  product_formula := prod_abs_eq_one

end number_field


/-!
### Heights of field elements
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ :=
  (∏ v, max (archAbsVal v x) 1 ^ weight v) * ∏ᶠ v, max (nonarchAbsVal v x) 1

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  -- 600 vs. 3700 heartbeats without "only"
  simp only [mulHeight₁, map_zero, zero_le_one, sup_of_le_right, one_pow, Finset.prod_const_one,
    finprod_one, mul_one]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁]

lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x := by
  classical
  unfold mulHeight₁
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · exact Finset.one_le_prod Finset.univ fun _ ↦ one_le_pow₀ <| le_max_right ..
  · exact one_le_finprod fun _ ↦ le_max_right ..

lemma zero_le_mulHeight₁ (x : K) : 0 ≤ mulHeight₁ x :=
  zero_le_one.trans <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_pos (x : K) : 0 < mulHeight₁ x :=
  zero_lt_one.trans_le <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_ne_zero (x : K) : mulHeight₁ x ≠ 0 :=
  (mulHeight₁_pos x).ne'

/-- The logarithmic height of an element of `K`. -/
def logHeight₁ (x : K) : ℝ := Real.log (mulHeight₁ x)

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| mod_cast one_le_mulHeight₁ x


/-!
### Heights of tuples and finitely supported maps
-/

variable {ι : Type*} [Fintype ι]

lemma mulSupport_iSup_absValue_finite {x : ι → K} (hx : x ≠ 0) :
    (Function.mulSupport fun v ↦ ⨆ i, nonarchAbsVal v (x i)).Finite := by
  simp_rw [AbsoluteValue.iSup_eq_subtype _ hx]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  exact (Set.finite_iUnion fun i ↦ mulSupport_nonarchAbsVal_finite i.prop).subset <|
    Function.mulSupport_iSup _

lemma mulSupport_max_absValue_finite (x : K) :
    (Function.mulSupport fun v ↦ (nonarchAbsVal v) x ⊔ 1).Finite := by
  convert mulSupport_iSup_absValue_finite (x := ![x, 1]) <| by simp with v
  rw [max_eq_iSup]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The multiplicative height of a tuple of elements of `K`. -/
def mulHeight (x : ι → K) : ℝ :=
  (∏ v, ⨆ i, archAbsVal v (x i) ^ weight v) * ∏ᶠ v, ⨆ i, nonarchAbsVal v (x i)

omit [Fintype ι] in
/-- The multiplicative height does not change under re-indexing. -/
lemma mulHeight_comp_equiv {ι' : Type*} (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  simp only [mulHeight, Function.comp_apply]
  congr 2 <;> { ext1 v; exact e.iSup_congr (congrFun rfl) }

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
lemma mulHeight_mul_eq_mulHeight {x : ι → K} (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  have  : Nonempty ι := by
    have ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    exact Nonempty.intro i
  simp only [mulHeight, Pi.smul_apply, smul_eq_mul, map_mul]
  conv =>
    enter [1, 1, 2, v]
    rw [← ciSupℝ_pow fun i ↦ mul_nonneg (AbsoluteValue.nonneg ..) (AbsoluteValue.nonneg ..),
      ← Real.mul_iSup_of_nonneg <| AbsoluteValue.nonneg .., mul_pow,
      ciSupℝ_pow fun i ↦ (AbsoluteValue.nonneg ..)]
  conv =>
    enter [1, 2, 1, v]
    rw [← Real.mul_iSup_of_nonneg <| AbsoluteValue.nonneg ..]
  rw [Finset.prod_mul_distrib,
    finprod_mul_distrib (mulSupport_nonarchAbsVal_finite hc) (mulSupport_iSup_absValue_finite hx),
    mul_mul_mul_comm, product_formula hc, one_mul]

/-- The logarithmic height of a (nonzero) tuple does not change under scaling. -/
lemma logHeight_mul_eq_logHeight {x : ι → K} (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight, mulHeight_mul_eq_mulHeight hx hc]

lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  simp only [mulHeight₁, mulHeight, Nat.succ_eq_add_one, Nat.reduceAdd]
  congr
  · ext1 v
    rw [(archAbsVal v).max_one_eq_iSup, ciSupℝ_pow fun _ ↦ AbsoluteValue.nonneg ..]
  · ext1 v
    exact AbsoluteValue.max_one_eq_iSup ..

lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁, logHeight, mulHeight₁_eq_mulHeight x]

/-- The multiplicative height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n`th power of its multiplicative height. -/
lemma mulHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : mulHeight (x ^ n) = mulHeight x ^ n := by
  have : Nonempty ι := Nonempty.intro (Function.ne_iff.mp hx).choose
  simp only [mulHeight, Pi.pow_apply, map_pow]
  rw [mul_pow, finprod_pow <| mulSupport_iSup_absValue_finite hx, ← Finset.prod_pow]
  congr 2
  · ext1 v
    rw [ciSupℝ_pow fun _ ↦ pow_nonneg (AbsoluteValue.nonneg ..) _]
    simp only [pow_right_comm]
  · ext1 v
    exact (ciSupℝ_pow (fun _ ↦ AbsoluteValue.nonneg ..) n).symm

/-- The logarithmic height of the coordinate-wise `n`th power of a (nonzero) tuple
is the `n` times its logarithmic height. -/
lemma logHeight_pow {x : ι → K} (hx : x ≠ 0) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight, mulHeight_pow hx]

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
  simp only [logHeight₁, mulHeight₁_pow, Real.log_pow]

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
  simp only [logHeight₁, mulHeight₁_zpow, Real.log_pow]

/-- The multiplicative height of `x + y` is at most the `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁, totalWeight]
  have hf₂ : (Function.mulSupport fun v ↦
      ((nonarchAbsVal v) x ⊔ 1) * ((nonarchAbsVal v) y ⊔ 1)).Finite :=
    Function.mulSupport_mul_finite (mulSupport_max_absValue_finite x)
      (mulSupport_max_absValue_finite y)
  rw [← Finset.prod_pow_eq_pow_sum, mul_mul_mul_comm, ← mul_assoc, ← mul_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, mul_assoc,
    ← finprod_mul_distrib (mulSupport_max_absValue_finite x) (mulSupport_max_absValue_finite y)]
  simp_rw [← mul_pow]
  gcongr with v
  · -- 0 ≤ ∏ᶠ (v : NonarchAbsVal K), (nonarchAbsVal v) (x + y) ⊔ 1
    exact finprod_nonneg fun _ ↦ zero_le_one.trans (le_max_right _ 1)
  · -- (archAbsVal v) (x + y) ⊔ 1 ≤ 2 * ((archAbsVal v) y ⊔ 1) * ((archAbsVal v) x ⊔ 1)
    refine sup_le ?_ ?_
    · refine ((archAbsVal v).add_le x y).trans ?_
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_mul, one_mul, add_mul]
      exact add_le_add (le_mul_max_max_right ..) (le_mul_max_max_left ..)
    · refine (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two
  · -- ∏ᶠ v, (nonarchAbsVal v) (x + y) ⊔ 1 ≤ ∏ᶠ v, ((nonarchAbsVal v) x ⊔ 1) * ((nonarchAbsVal v) y ⊔ 1)
    refine finprod_mono' (mulSupport_max_absValue_finite _)
      (fun _ ↦ zero_le_one.trans <| le_max_right _ 1) hf₂ fun v ↦ sup_le ?_ <| one_le_mul_max_max ..
    exact (strong_triangle_ineq v x y).trans <|
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
  exact log_le_log (zero_lt_one.trans_le <| one_le_mulHeight₁ _) <| mod_cast mulHeight₁_add_le x y

/-- The multiplicative height of a finite sum of field elements is at most
`2 ^ ((n-1) ' totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values.
lemma mulHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤ 2 ^ ((s.card - 1) * totalWeight K) * ∏ a ∈ s, mulHeight₁ (x a) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      · simp only [ha, not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_not_mem,
          add_tsub_cancel_right, Finset.prod_insert]
        calc
        _ ≤ 2 ^ totalWeight K * mulHeight₁ (x a) * mulHeight₁ (∑ b ∈ s, x b) := mulHeight₁_add_le ..
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
`(n-1) * totalWeight K * log 2` plus the sum of the individual multiplicative
heights, where `n` is the number of terms. -/
-- We can get better bounds if we are more specific with the archimedean absolute values.
lemma logHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤
      ((s.card - 1) * totalWeight K : ) * Real.log 2 + ∑ a ∈ s, logHeight₁ (x a) := by
  simp only [logHeight₁]
  rw [← log_pow, ← log_prod _ _ <| fun a _ ↦ mulHeight₁_ne_zero (x a), ← log_mul ?h₁ ?h₂]
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
  h ▸ mulHeight_mul_eq_mulHeight b.prop fun H ↦ a.prop <| (H ▸ h).trans <| zero_smul K b.val

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


end Projectivization
