-- import Heights.Auxiliary
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.NumberTheory.Height.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Tactic.Positivity.Core

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.LinearAlgebra.Projectivization.Basic

import Heights.FiniteMulSupport

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
### Bounds for the height of sums of field elements
-/

section aux

@[to_additive]
lemma Multiset.prod_map_prod {ι α M : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α}
    {f : ι → α  → M} :
    (m.map fun i ↦ ∏ a ∈ s, f i a).prod = ∏ a ∈ s, (m.map fun i ↦ f i a).prod := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, prod_map_mul, ih]

-- [Mathlib.Algebra.BigOperators.Group.Finset.Basic]

section

variable {α M : Type*}

/-- Monotonicity of `finprod`. See `finprod_le_finprod` for a variant where
`β` is a `CommMonoidWithZero`. -/
@[to_additive /-- Monotonicity of `finsum.` -/]
lemma finprod_le_finprod' [CommMonoid M] [PartialOrder M] [MulLeftMono M] {f g : α → M}
    (hf : f.mulSupport.Finite) (hg : g.mulSupport.Finite) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finset_prod_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finset_prod_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod' fun i _ ↦ h i

/-- Monotonicity of `finprod`. See `finprod_le_finprod'` for a variant where
`β` is an ordered `CommMonoid`. -/
lemma finprod_le_finprod [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M] [PosMulMono M]
    {f g : α → M} (hf : f.mulSupport.Finite) (hf₀ : ∀ a, 0 ≤ f a)
    (hg : g.mulSupport.Finite) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finset_prod_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finset_prod_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod (fun i _ ↦ hf₀ i) fun i _ ↦ h i

-- #find_home! finprod_le_finprod
-- Mathlib.Algebra.BigOperators.Finprod ?

end
-- Some helper lemmas needed below

namespace Height

/- private lemma le_mul_max_max_left (a b : ℝ) : a ≤ (max a 1) * (max b 1) :=
  calc
    a = a * 1 := (mul_one a).symm
    _  ≤ _ := by gcongr <;> grind -/

/- private lemma le_mul_max_max_right (a b : ℝ) : b ≤ (max a 1) * (max b 1) := by
  rw [mul_comm]
  exact le_mul_max_max_left b a -/

/- private lemma one_le_mul_max_max (a b : ℝ) : 1 ≤ (max a 1) * (max b 1) :=
  calc
    (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ _ := by gcongr <;> grind -/

variable {K : Type*} [Field K]

/- -- The "local" version of the height bound for `x + y` for archimedean `v`.
private lemma max_abv_add_one_le (v : AbsoluteValue K ℝ) (x y : K) :
    max (v (x + y)) 1 ≤ 2 * (max (v x) 1 * max (v y) 1) := by
  refine sup_le ((v.add_le x y).trans ?_) <| (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
  · rw [two_mul]
    exact add_le_add (le_mul_max_max_left ..) (le_mul_max_max_right ..)
  · exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two -/

/- -- The "local" version of the height bound for `x + y` for nonarchimedean `v`.
private lemma max_abv_add_one_le_of_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (x y : K) :
    max (v (x + y)) 1 ≤ (max (v x) 1 * max (v y) 1) := by
  refine sup_le ?_ <| one_le_mul_max_max ..
  exact (hv x y).trans <| sup_le (le_mul_max_max_left ..) (le_mul_max_max_right ..) -/

private lemma le_prod_max_one {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) (f : ι → ℝ) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le (by positivity)).le
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [Finset.prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  exact this ▸ Finset.prod_le_prod (fun _ _ ↦ by grind) fun _ _ ↦ by grind

-- The "local" version of the height bound for arbitrary sums for archimedean `v`.
private lemma max_abv_sum_one_le (v : AbsoluteValue K ℝ) {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (x : ι → K) :
    max (v (∑ i ∈ s, x i)) 1 ≤ s.card * ∏ i ∈ s, max (v (x i)) 1 := by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    grw [v.sum_le s x]
    gcongr with i hi
    exact le_prod_max_one hi (fun i ↦ v (x i))
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · simp [hs]
    · exact s.one_le_prod fun _ ↦ le_max_right ..

-- The "local" version of the height bound for arbitrary sums for nonarchimedean `v`.
private lemma max_abv_sum_one_le_of_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (x : ι → K) :
    max (v (∑ i ∈ s, x i)) 1 ≤ ∏ i ∈ s, max (v (x i)) 1 := by
  refine sup_le ?_ <| s.one_le_prod fun _ ↦ le_max_right ..
  grw [hv.apply_sum_le_sup_of_isNonarchimedean hs]
  exact Finset.sup'_le hs (fun i ↦ v (x i)) fun i hi ↦ le_prod_max_one hi (fun i ↦ v (x i))

private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

@[fun_prop]
lemma AdmissibleAbsValues.hasFiniteMulSupport {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : nonarchAbsVal ↦ v.val x :=
  mulSupport_finite hx

-- Finiteness of the multiplicative support for some relevant functions.
@[fun_prop]
private lemma mulSupport_iSup_nonarchAbsVal_finite {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| Function.ne_iff.mp hx
  suffices (fun v : nonarchAbsVal ↦ ⨆ i : {j // x j ≠ 0}, v.val (x i)).HasFiniteMulSupport by
    convert this with v
    obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm ?_ <| ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl
    refine ciSup_le fun j ↦ ?_
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl
  fun_prop (disch := grind)
  -- exact (Set.finite_iUnion fun i : {j | x j ≠ 0} ↦ mulSupport_finite i.prop).subset <|
  --   Function.mulSupport_iSup _

@[fun_prop]
private lemma mulSupport_max_nonarchAbsVal_finite (x : K) :
    (fun v : nonarchAbsVal ↦ max (v.val x) 1).HasFiniteMulSupport := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp; fun_prop
  fun_prop (disch := assumption)
  -- simp_rw [max_eq_iSup]
  -- convert mulSupport_iSup_nonarchAbsVal_finite (x := ![x, 1]) <| by simp with v i
  -- fin_cases i <;> simp

end Height

end aux

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Height

/-- Extension for the `positivity` tactic: `Height.mulHeight₁` is always positive. -/
@[positivity Height.mulHeight₁ _]
meta def evalMulHeight₁ : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.positive q(@mulHeight₁_pos $K $KF $KA $a))
  | _, _, _ => throwError "not Height.mulHeight₁"

/-- Extension for the `positivity` tactic: `Height.logHeight₁` is always nonnegative. -/
@[positivity Height.logHeight₁ _]
meta def evalLogHeight₁ : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.nonnegative q(@zero_le_logHeight₁ $K $KF $KA $a))
  | _, _, _ => throwError "not Height.logHeight₁"

/-- Extension for the `positivity` tactic: `Height.mulHeight` is always positive. -/
@[positivity Height.mulHeight _]
meta def evalMulHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight $K $KF $KA $ι $a) =>
    assertInstancesCommute
    -- Check wether there is a `Finite` instance for `$ι` around.
    let o : Option Q(Finite $ι) := ← do
      let .some instFinite ← trySynthInstanceQ q(Finite $ι) | return none
      return some instFinite
    match o with
    | some instFinite =>
      assertInstancesCommute
      return .positive q(@mulHeight_pos $K $KF $KA $ι $instFinite $a)
    | none => throwError "index type in Height.mulHeight not known to be finite"
  | _, _, _ => throwError "not Height.mulHeight"

/-- Extension for the `positivity` tactic: `Height.logHeight` is always nonnegative. -/
@[positivity Height.logHeight _]
meta def evalLogHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $a) =>
    assertInstancesCommute
    -- Check wether there is a `Finite` instance for `$ι` around.
    let o : Option Q(Finite $ι) := ← do
      let .some instFinite ← trySynthInstanceQ q(Finite $ι) | return none
      return some instFinite
    match o with
    | some instFinite =>
      assertInstancesCommute
      return .nonnegative q(@zero_le_logHeight $K $KF $KA $ι $instFinite $a)
    | none => throwError "index type in Height.logHeight not known to be finite"
  | _, _, _ => throwError "not Height.logHeight"

end Mathlib.Meta.Positivity

section aux

-- For the next PR
lemma Real.log_finprod {α : Type*} {f : α → ℝ} (h : ∀ a, 0 < f a) :
    log (∏ᶠ a, f a) = ∑ᶠ a, log (f a) := by
  classical
  simp only [finprod_def, finsum_def]
  have H : f.mulSupport = (fun i ↦ log (f i)).support := by
    ext a
    refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;> { simp at h' ⊢; grind }
  simp only [← H]
  split_ifs with h₁
  · exact log_prod fun a _ ↦ (h a).ne'
  · simp

end aux

namespace Height

open AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

-- For the next PR
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (archAbsVal.map fun v ↦ log⁺ (v x)).sum + ∑ᶠ v : nonarchAbsVal, log⁺ (v.val x) := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq]
  have H : mulHeight₁ x ≠ 0 := mulHeight₁_ne_zero x
  rw [mulHeight₁_eq] at H
  have : ∀ a ∈ archAbsVal.map (fun v ↦ max (v x) 1), a ≠ 0 := by
    intro a ha
    contrapose! ha
    rw [ha]
    exact Multiset.prod_eq_zero_iff.not.mp <| left_ne_zero_of_mul H
  rw [log_mul (left_ne_zero_of_mul H) (right_ne_zero_of_mul H), log_multiset_prod this,
    Multiset.map_map, log_finprod (fun _ ↦ by positivity)]
  congr 2 <;> simp [max_comm, posLog_eq_log_max_one]

open Finset Multiset in
/-- The multiplicative height of a nonempty finite sum of field elements is at most
`n ^ (totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
lemma mulHeight₁_sum_le {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤ #s ^ (totalWeight K) * ∏ a ∈ s, mulHeight₁ (x a) := by
  simp only [mulHeight₁_eq, totalWeight]
  calc
    _ ≤ (archAbsVal.map fun v ↦ (s.card : ℝ) * ∏ i ∈ s, max (v (x i)) 1).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      exact prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) fun _ _ ↦ max_abv_sum_one_le _ hs x
    _ ≤ _ * ∏ᶠ (v : ↑nonarchAbsVal), ∏ i ∈ s, max (v.val (x i)) 1 := by
      refine mul_le_mul_of_nonneg_left ?_ <| prod_nonneg fun _ h ↦ by
        obtain ⟨v, -, rfl⟩ := mem_map.mp h
        positivity
      refine finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _) (fun v ↦ by grind) ?_ ?_
      · change Function.HasFiniteMulSupport _
        fun_prop
      --   refine Set.Finite.subset ?_ <|
      --     s.mulSupport_prod fun i (v : nonarchAbsVal) ↦ max (v.val (x i)) 1
      --   exact s.finite_toSet.biUnion fun _ _ ↦ mulSupport_max_nonarchAbsVal_finite _
      · exact fun v ↦ max_abv_sum_one_le_of_nonarch (isNonarchimedean _ v.prop) hs x
    _ = _ := by
      rw [finprod_prod_comm _ _ fun i _ ↦ mulSupport_max_nonarchAbsVal_finite (x i),
        prod_map_mul, prod_map_prod, map_const', prod_replicate, prod_mul_distrib]
      ring

open Finset in
/-- The logarithmic height of a finite sum of field elements is at most
`totalWeight K * log n` plus the sum of the individual logarithmic heights,
where `n` is the number of terms.

(Note that here we do not need to assume that `s` is nonempty, due to the convenient
junk value `log 0 = 0`.) -/
lemma logHeight₁_sum_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤ (totalWeight K) * log #s + ∑ a ∈ s, logHeight₁ (x a) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp only [logHeight₁_eq_log_mulHeight₁]
  have : ∀ a ∈ s, mulHeight₁ (x a) ≠ 0 := fun _ _ ↦ (mulHeight₁_pos _).ne'
  have : (s.card : ℝ) ^ totalWeight K ≠ 0 := by simp [hs.ne_empty]
  pull (disch := first | positivity | assumption) log
  exact (log_le_log <| by positivity) <| mulHeight₁_sum_le hs x

/-- The multiplicative height of `x + y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  rw [show x + y = Finset.univ.sum ![x, y] by simp, mul_assoc]
  grw [mulHeight₁_sum_le Finset.univ_nonempty ![x, y]]
  simp

/-- The logarithmic height of `x + y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`. -/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) ≤ totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact (log_le_log <| by positivity) <| mulHeight₁_add_le ..

end Height

/-!
### Height bounds for values of polynomials

(This is probably better done as a special case of results on polynomial maps on tuples.)
-/

namespace Polynomial

open Height

variable {K : Type*} [Field K]

open Finset in
-- The "local" bound for archimedean absolute values.
private lemma max_abv_eval_one_le (p : K[X]) (x : K) (v : AbsoluteValue K ℝ) :
    max (v (p.eval x)) 1 ≤ max (p.sum fun _ c ↦ v c) 1 * (max (v x) 1) ^ p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine max_le ?_ ?_
  · rw [eval_eq_sum_range, sum_over_range p fun _ ↦ v.map_zero]
    grw [v.sum_le]
    simp_rw [v.map_mul, v.map_pow]
    calc
      _ ≤ ∑ n ∈ range (p.natDegree + 1), v (p.coeff n) * (max (v x) 1) ^ n := by gcongr; grind
      _ ≤ (∑ n ∈ range (p.natDegree + 1), v (p.coeff n)) * (max (v x) 1) ^ p.natDegree := by
          rw [sum_mul]
          gcongr <;> grind
      _ ≤ _ := by gcongr; grind
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · exact le_max_right ..
    · rw [MonotoneOn.map_sup pow_left_monotoneOn] <;> simp

open Finset in
-- The "local" bound for nonarchimedean absolute values.
private lemma max_abv_eval_one_le_of_nonarch (p : K[X]) (x : K) {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) :
    max (v (p.eval x)) 1 ≤
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v (p.coeff n)) 1 *
        (max (v x) 1) ^ p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine max_le ?_ ?_
  · rw [eval_eq_sum_range]
    grw [hv.apply_sum_le_sup_of_isNonarchimedean nonempty_range_add_one]
    simp_rw [v.map_mul, v.map_pow]
    calc
      _ ≤ (range (p.natDegree + 1)).sup' nonempty_range_add_one
            fun n ↦ v (p.coeff n) * (max (v x) 1) ^ n := by gcongr; grind
      _ ≤ ((range (p.natDegree + 1)).sup' nonempty_range_add_one
            fun n ↦ v (p.coeff n)) * (max (v x) 1) ^ p.natDegree := by
          rw [sup'_mul₀ (by positivity) _ _ nonempty_range_add_one]
          gcongr <;> grind
      _ ≤ _ := by
          gcongr
          refine Finset.sup'_le nonempty_range_add_one _ fun n hn ↦ ?_
          grw [← le_max_left]
          exact Finset.le_sup' (fun n ↦ v (p.coeff n)) hn
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · exact le_max_right ..
    · rw [MonotoneOn.map_sup pow_left_monotoneOn] <;> simp

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues Finset

/-- The constant in the height bound on values of `p`. -/
def mulHeight₁Bound (p : K[X]) : ℝ :=
  (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
    ∏ᶠ v : nonarchAbsVal,
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1

lemma mulHeight₁Bound_eq (p : K[X]) :
    p.mulHeight₁Bound =
      (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
      ∏ᶠ v : nonarchAbsVal,
        max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1 :=
  rfl

@[simp]
lemma mulHeight₁Bound_zero : (0 : K[X]).mulHeight₁Bound = 1 := by
  simp [Polynomial.mulHeight₁Bound]

lemma one_le_mulHeight₁Bound (p : K[X]) : 1 ≤ p.mulHeight₁Bound := by
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun _ h ↦ ?_) ?_
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
    exact le_max_right ..
  · exact one_le_finprod fun _ ↦ le_max_right ..

@[fun_prop]
private lemma mulSupport_max_sup'_nonarchAbsVal_finite (p : K[X]) :
    (fun v : nonarchAbsVal ↦
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1)
      |>.HasFiniteMulSupport := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp; fun_prop
  suffices (fun v : nonarchAbsVal ↦ max ((p.support).sup' (support_nonempty.mpr hp)
              fun n ↦ v.val (p.coeff n)) 1).HasFiniteMulSupport by
    convert this using 3 with v
    refine le_antisymm (Finset.sup'_le nonempty_range_add_one _ fun i hi ↦ ?_) ?_
    · by_cases h : i ∈ p.support
      · exact Finset.le_sup' (fun i ↦ v.val (p.coeff i)) h
      · simp only [mem_support_iff, ne_eq, not_not] at h
        simp only [h, AbsoluteValue.map_zero, le_sup'_iff, mem_support_iff, apply_nonneg, and_true]
        refine ⟨p.natDegree, ?_⟩
        rw [Polynomial.coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hp
    · refine Finset.sup'_mono _ (fun i hi ↦ ?_) (support_nonempty.mpr hp)
      exact mem_range_succ_iff.mpr <| le_natDegree_of_mem_supp i hi
  fun_prop (disch := grind)
  -- let x := Fin.snoc (α := fun _ ↦ K) (fun n : Fin (p.natDegree + 1) ↦ p.coeff n) 1
  -- have hx : x ≠ 0 := Function.ne_iff.mpr ⟨Fin.last _, by simp [x]⟩
  -- convert mulSupport_iSup_nonarchAbsVal_finite hx with v
  -- -- `max ((range (p.natDegree + 1)).sup' ⋯ fun n ↦ ↑v (p.coeff n)) 1 = ⨆ i, ↑v (x i)`
  -- -- Can this be done in a more elegant way?
  -- refine le_antisymm (max_le ?_ ?_) <| ciSup_le fun i ↦ ?_
  -- · refine Finset.sup'_le _ _ fun n hn ↦ le_ciSup_of_le (Finite.bddAbove_range _) ⟨n, by grind⟩ ?_
  --   simp only [x]
  --   convert le_rfl
  --   have : (⟨n, by grind⟩ : Fin (p.natDegree + 1 + 1)) =
  --             (⟨n, by grind⟩ : Fin (p.natDegree + 1)).castSucc := by
  --     grind
  --   rw [this]
  --   exact Fin.snoc_castSucc ..
  -- · exact le_ciSup_of_le (Finite.bddAbove_range _) (Fin.last _) <| by simp [x]
  -- · rcases eq_or_ne i (Fin.last _) with rfl | hi
  --   · simp [x]
  --   · simp only [le_sup_iff, le_sup'_iff, mem_range, Order.lt_add_one_iff, x]
  --     refine .inl ⟨i.val, by grind, ?_⟩
  --     convert le_rfl
  --     have : i = Fin.castSucc ⟨i.val, by grind⟩ := by grind
  --     nth_rewrite 2 [this]
  --     exact (Fin.snoc_castSucc (α := fun _ ↦ K) (n := p.natDegree + 1) _ (fun n ↦ p.coeff ↑n)
  --       ⟨i.val, by grind⟩).symm

open Multiset in
/-- The multiplicative height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree`. -/
lemma mulHeight₁_eval_le (p : K[X]) (x : K) :
    mulHeight₁ (p.eval x) ≤ p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree := by
  simp only [mulHeight₁_eq, p.mulHeight₁Bound_eq]
  -- have H : (fun v : nonarchAbsVal ↦ max (v.val x) 1 ^ p.natDegree).HasFiniteMulSupport :=
  --   (mulSupport_max_nonarchAbsVal_finite x).subset <| Function.mulSupport_pow ..
  calc
    _ ≤ (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1 * (max (v x) 1) ^ p.natDegree).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      exact prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) fun _ _ ↦ max_abv_eval_one_le ..
    _ ≤ _ * ∏ᶠ (v : ↑nonarchAbsVal), max ((Finset.range (p.natDegree + 1)).sup' nonempty_range_add_one
          fun n ↦ v.val (p.coeff n)) 1 * (max (v.val x) 1) ^ p.natDegree := by
      refine mul_le_mul_of_nonneg_left ?_ <| Multiset.prod_nonneg fun a ha ↦ ?_
      · refine finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _) (fun v ↦ by grind) ?_ ?_
        · change Function.HasFiniteMulSupport _
          fun_prop
          -- refine Set.Finite.subset ?_ <| Function.mulSupport_mul ..
          -- exact p.mulSupport_max_sup'_nonarchAbsVal_finite.union H
        · exact Pi.le_def.mpr fun v ↦ max_abv_eval_one_le_of_nonarch p x (isNonarchimedean _ v.prop)
      · obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
        positivity
    _ = _ := by
      rw [prod_map_mul, mul_pow, prod_map_pow,
        finprod_mul_distrib p.mulSupport_max_sup'_nonarchAbsVal_finite
          (by change Function.HasFiniteMulSupport _; fun_prop),
        finprod_pow (mulSupport_max_nonarchAbsVal_finite x)]
      ring

open Real

/-- The logarithmic height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `log p.mulHeight₁Bound + p.natDegree * logHeight₁ x`. -/
lemma logHeight₁_eval_le (p : K[X]) (x : K) :
    logHeight₁ (p.eval x) ≤ log p.mulHeight₁Bound + p.natDegree * logHeight₁ x := by
  simp_rw [logHeight₁_eq_log_mulHeight₁]
  have : p.mulHeight₁Bound ≠ 0 := by grind [one_le_mulHeight₁Bound]
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight₁_eval_le p x

end Polynomial


-- #exit
/-!
### Heights on projective spaces
-/

-- New file NumberTheory/Height/Projectivization.lean ?

namespace Projectivization

open Height AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

private
lemma mulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  have ht : t ≠ 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ mulHeight_smul_eq_mulHeight _ ht

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
  exact Height.one_le_mulHeight _

lemma mulHeight_pos (x : Projectivization K (ι → K)) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x

lemma mulHeight_ne_zero (x : Projectivization K (ι → K)) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'

lemma zero_le_logHeight (x : Projectivization K (ι → K)) : 0 ≤ logHeight x := by
  rw [logHeight_eq_log_mulHeight]
  exact log_nonneg <| x.one_le_mulHeight

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Projectivization

/-- Extension for the `positivity` tactic: `Projectivization.mulHeight` is always positive. -/
@[positivity Projectivization.mulHeight _]
meta def evalProjMulHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q(@mulHeight_pos $K $KF $KA $ι $ιF $a))
  | _, _, _ => throwError "not Projectivization.mulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.logHeight` is always nonnegative. -/
@[positivity Projectivization.logHeight _]
meta def evalProjLogHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(@zero_le_logHeight $K $KF $KA $ι $ιF $a))
  | _, _, _ => throwError "not Projectivization.logHeight"

end Mathlib.Meta.Positivity
