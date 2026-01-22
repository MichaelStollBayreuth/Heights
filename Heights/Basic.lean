-- import Heights.Auxiliary
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.NumberTheory.Height.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
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

/-!
### Properties of heights
-/

section aux

@[to_additive]
lemma Multiset.prod_map_prod {ι α M : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α}
    {f : ι → α  → M} :
    (m.map fun i ↦ ∏ a ∈ s, f i a).prod = ∏ a ∈ s, (m.map fun i ↦ f i a).prod := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, Multiset.prod_map_mul, ih]

-- Some lemmas needed below
namespace Height

private lemma le_mul_max_max_left (a b : ℝ) : b ≤ (b ⊔ 1) * (a ⊔ 1) := by
  nth_rewrite 1 [← mul_one b]
  gcongr <;> grind

private lemma le_mul_max_max_right (a b : ℝ) : a ≤ (b ⊔ 1) * (a ⊔ 1) := by
  rw [mul_comm]
  exact le_mul_max_max_left b a

private lemma one_le_mul_max_max (a b : ℝ) : 1 ≤ (a ⊔ 1) * (b ⊔ 1) := by
  nth_rewrite 1 [← mul_one 1]
  gcongr <;> exact le_max_right ..

variable {K : Type*} [Field K]

private lemma max_abv_add_one_le (v : AbsoluteValue K ℝ) (x y : K) :
    max (v (x + y)) 1 ≤ 2 * (max (v x) 1 * max (v y) 1) := by
  refine sup_le ?_ ?_
  · refine (v.add_le x y).trans ?_
    rw [two_mul]
    exact add_le_add (le_mul_max_max_left ..) (le_mul_max_max_right ..)
  · refine (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
    exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two

private lemma max_abv_add_one_le_of_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (x y : K) :
    max (v (x + y)) 1 ≤ (max (v x) 1 * max (v y) 1) := by
  refine sup_le ?_ <| one_le_mul_max_max ..
  exact (hv x y).trans <| sup_le (le_mul_max_max_left ..) (le_mul_max_max_right ..)

private lemma le_prod_max_one {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) (f : ι → ℝ)
    (hf : 0 ≤ f i) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [Finset.prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  rw [this]
  exact Finset.prod_le_prod (fun _ _ ↦ by grind) fun _ _ ↦ by grind

private lemma sup_abv_add_one_le (v : AbsoluteValue K ℝ) {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → K) :
    max (v (∑ i ∈ s, f i)) 1 ≤ s.card * ∏ i ∈ s, max (v (f i)) 1 := by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    grw [v.sum_le s f]
    gcongr with i hi
    exact le_prod_max_one hi (fun i ↦ v (f i)) (v.nonneg _)
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · norm_num [hs]
    · exact s.one_le_prod fun _ ↦ le_max_right ..

private lemma sup_abv_add_one_le_of_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → K) :
    max (v (∑ i ∈ s, f i)) 1 ≤ ∏ i ∈ s, max (v (f i)) 1 := by
  refine sup_le ?_ <| s.one_le_prod fun _ ↦ le_max_right ..
  grw [hv.apply_sum_le_sup_of_isNonarchimedean hs]
  exact Finset.sup'_le hs (fun i ↦ v (f i))
    fun i hi ↦ le_prod_max_one hi (fun i ↦ v (f i)) (v.nonneg _)

end Height

end aux

-- needed later (only used once)
/- @[to_additive]
lemma Function.mulSupport_mul_finite {α β : Type*} [Monoid β] {f g : α → β} (hf : f.mulSupport.Finite)
    (hg : g.mulSupport.Finite) :
    (mulSupport fun a ↦ f a * g a).Finite :=
  (hf.union hg).subset <| mulSupport_mul f g -/

variable {α β : Type*}

/-- Monotonicity of `finprod`. See `finprod_le_finprod` for a variant where
`β` is a `CommMonoidWithZero`. -/
@[to_additive /-- Monotonicity of `finsum.` -/]
lemma finprod_le_finprod' [CommMonoid β] [PartialOrder β] [MulLeftMono β] {f g : α → β}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) (h : f ≤ g) :
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

/-- Monotonicity of `finprod`. See `finprod_le_finprod'` for a variant where
`β` is an ordered `CommMonoid`. -/
lemma finprod_le_finprod [CommMonoidWithZero β] [PartialOrder β] [ZeroLEOneClass β] [PosMulMono β]
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

-- Mathlib.Algebra.BigOperators.Finprod ?

namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

private lemma mulSupport_iSup_nonarchAbsVal_finite {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
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

/-- The multiplicative height of `x + y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁_eq, totalWeight]
  calc
    _ ≤ (archAbsVal.map fun v ↦ 2 * (max (v x) 1 * max (v y) 1)).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity)
        fun _ _ ↦ max_abv_add_one_le ..
    _ ≤ _ * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 * max (v.val y) 1 := by
      refine mul_le_mul_of_nonneg_left ?_ <| Multiset.prod_nonneg fun _ h ↦ by
        obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
        positivity
      have hf := ((mulSupport_max_nonarchAbsVal_finite x).union
        (mulSupport_max_nonarchAbsVal_finite y)).subset <| Function.mulSupport_mul ..
      exact finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _)
        (by grind) hf fun v ↦ max_abv_add_one_le_of_nonarch (isNonarchimedean _ v.prop) ..
    _ = _ := by
      simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
        mulSupport_max_nonarchAbsVal_finite, finprod_mul_distrib]
      ring

-- attribute [positivity mulHeight₁ _] mulHeight₁_pos

/-- The logarithmic height of `x + y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`. -/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) ≤ totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  have hx : 0 < mulHeight₁ x := mulHeight₁_pos x
  have hy : 0 < mulHeight₁ y := mulHeight₁_pos y
  pull (disch := positivity) log
  exact (log_le_log <| mulHeight₁_pos _) <| mulHeight₁_add_le ..

open Finset in
/-- The multiplicative height of a nonempty finite sum of field elements is at most
`n ^ (totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
lemma mulHeight₁_sum_le {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤ #s ^ (totalWeight K) * ∏ a ∈ s, mulHeight₁ (x a) := by
  simp only [mulHeight₁_eq, totalWeight]
  calc
    _ ≤ (archAbsVal.map fun v ↦ (s.card : ℝ) * ∏ i ∈ s, max (v (x i)) 1).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity)
        fun _ _ ↦ sup_abv_add_one_le _ hs x
    _ ≤ _ * ∏ᶠ (v : ↑nonarchAbsVal), ∏ i ∈ s, max (v.val (x i)) 1 := by
      refine mul_le_mul_of_nonneg_left ?_ <| Multiset.prod_nonneg fun _ h ↦ by
        obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
        positivity
      refine finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _) (fun v ↦ by grind) ?_ ?_
      · refine Set.Finite.subset ?_ <|
          s.mulSupport_prod fun i (v : nonarchAbsVal) ↦ max (v.val (x i)) 1
        exact Set.Finite.biUnion s.finite_toSet fun i _ ↦ mulSupport_max_nonarchAbsVal_finite _
      · exact Pi.le_def.mpr fun v ↦ sup_abv_add_one_le_of_nonarch (isNonarchimedean _ v.prop) hs x
    _ = _ := by
      rw [finprod_prod_comm _ _ fun i _ ↦ mulSupport_max_nonarchAbsVal_finite (x i),
        Multiset.prod_map_mul, Multiset.prod_map_prod, Multiset.map_const',
        Multiset.prod_replicate, Finset.prod_mul_distrib]
      ring

/-- The logarithmic height of a nonempty finite sum of field elements is at most
`totalWeight K * log n` plus the sum of the individual logarithmic heights,
where `n` is the number of terms. -/
lemma logHeight₁_sum_le {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤
      (totalWeight K : ) * log s.card + ∑ a ∈ s, logHeight₁ (x a) := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  have : ∀ a ∈ s, mulHeight₁ (x a) ≠ 0 := fun _ _ ↦ (mulHeight₁_pos _).ne'
  have : 0 < ∏ i ∈ s, mulHeight₁ (x i) := by refine Finset.prod_pos fun _ _ ↦ mulHeight₁_pos _
  have : (s.card : ℝ) ^ totalWeight K ≠ 0 := by simp [hs.ne_empty]
  pull (disch := first | positivity | assumption) log
  refine (log_le_log <| mulHeight₁_pos _) <| mulHeight₁_sum_le hs x

end Height

#exit
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
