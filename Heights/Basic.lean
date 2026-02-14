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

import Mathlib.Algebra.Order.Group.CompleteLattice

import Heights.FiniteSupport

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

## TODO

* Fix names `mulHeight.ne_zero` → `mulHeight_ne_zero` and `zero_le_...` → `..._nonneg`.
* `@[to_fun]` on `mulHeight_zero` (see below), plus `logHeight_zero`.
* Refactor `mulHeight_comp_equiv` via a weaker form for arbitrary maps.
* PR `logHeight₁_eq`.
* PR Segre results.
* PR bounds for linear maps.
* PR upper and lower bounds for polynomial maps.

-/

attribute [to_fun (attr := simp)] Height.mulHeight_zero
attribute [to_fun (attr := simp)] Height.mulHeight_one

noncomputable section

section aux

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

namespace Multiset

-- #34330

variable {α R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

lemma prod_map_nonneg {s : Multiset α} {f : α → R} (h : ∀ a ∈ s, 0 ≤ f a) :
    0 ≤ (s.map f).prod := by
  refine prod_nonneg fun r hr ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

-- #find_home! prod_map_nonneg -- [Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset]

lemma one_le_prod_map {s : Multiset α} {f : α → R} (h : ∀ a ∈ s, 1 ≤ f a) :
    1 ≤ (s.map f).prod := by
  refine one_le_prod fun r hr ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

-- #find_home! one_le_prod_map -- [Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset]

end Multiset

namespace Finite

-- #35260

-- Add versions of `le_ciSup_of_le` and `ciSup_mono` for finite index types;
-- see `Finite.le_ciSup` in [Mathlib.Order.ConditionallyCompleteLattice.Finset].

variable {α ι : Type*} [Finite ι] [ConditionallyCompleteLattice α]

lemma le_ciSup_of_le {a : α} {f : ι → α} (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  _root_.le_ciSup_of_le (bddAbove_range f) c h

lemma ciSup_mono {f g : ι → α} (H : ∀ (x : ι), f x ≤ g x) : iSup f ≤ iSup g :=
  _root_.ciSup_mono (bddAbove_range g) H

-- #find_home! le_ciSup_of_le -- [Mathlib.Data.Fintype.Order]
-- #find_home! ciSup_mono -- [Mathlib.Data.Fintype.Order]

lemma ciSup_sup [Nonempty ι] {f : ι → α} {a : α} :
    (⨆ i, f i) ⊔ a = ⨆ i, f i ⊔ a := by
  refine le_antisymm (sup_le ?_ ?_) <| ciSup_le fun i ↦ sup_le_sup_right (le_ciSup f i) a
  · exact ciSup_le fun i ↦ le_ciSup_of_le i le_sup_left
  · exact le_ciSup_of_le (Classical.arbitrary ι) le_sup_right

-- #find_home! ciSup_sup -- [Mathlib.Order.ConditionallyCompleteLattice.Finset]

end Finite

namespace AbsoluteValue

variable {K : Type*} [Semiring K]

lemma iSup_abv_nonneg {ι : Type*} (v : AbsoluteValue K ℝ) {x : ι → K} : 0 ≤ ⨆ i, v (x i) :=
  Real.iSup_nonneg fun j ↦ by positivity

lemma iSup_abv_fun_mul_eq_iSup_abv_mul_iSup_abv (v : AbsoluteValue K ℝ) {ι ι' : Type*}
    [Finite ι] [Finite ι'] (x : ι → K) (y : ι' → K) :
    ⨆ a : ι × ι', v (x a.1 * y a.2) = (⨆ i, v (x i)) * ⨆ j, v (y j) := by
  rcases isEmpty_or_nonempty ι
  · simp
  rcases isEmpty_or_nonempty ι'
  · simp
  simp only [map_mul]
  refine le_antisymm (ciSup_le fun a ↦ ?_) ?_
  · gcongr
    · exact iSup_abv_nonneg v
    · exact Finite.le_ciSup (fun i ↦ v (x i)) a.1
    · exact Finite.le_ciSup (fun j ↦ v (y j)) a.2
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (x i))
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j ↦ v (y j))
    rw [← hi, ← hj]
    exact Finite.le_ciSup (fun a : ι × ι' ↦ v (x a.1) * v (y a.2)) ⟨i, j⟩

end AbsoluteValue

namespace Finset

lemma le_prod_max_one {ι M : Type*} [CommMonoidWithZero M] [LinearOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {s : Finset ι} {i : ι} (hi : i ∈ s) (f : ι → M) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| Finset.prod_nonneg fun _ _ ↦ le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [Finset.prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  exact this ▸ Finset.prod_le_prod (fun _ _ ↦ by grind [zero_le_one]) fun _ _ ↦ by grind

-- #find_home! le_prod_max_one  -- [Mathlib.Algebra.Order.BigOperators.Ring.Finset]

variable {R S : Type*} [Semiring R] [CommSemiring S] [LinearOrder S] [IsOrderedRing S]

/-- The "local" version of the height bound for arbitrary sums for general (possibly archimedean)
absolute values. -/
lemma max_abv_sum_one_le [CharZero S] (v : AbsoluteValue R S) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (x : ι → R) :
    max (v (∑ i ∈ s, x i)) 1 ≤ #s * ∏ i ∈ s, max (v (x i)) 1 := by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← sum_const]
    grw [v.sum_le s x]
    gcongr with i hi
    exact le_prod_max_one hi fun i ↦ v (x i)
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · simp [hs]
    · exact s.one_le_prod fun _ ↦ le_max_right ..
-- #min_imports says
-- import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
-- import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-- The "local" version of the height bound for arbitrary sums for nonarchimedean
absolute values. -/
lemma max_abv_sum_one_le_of_isNonarchimedean {v : AbsoluteValue R S} (hv : IsNonarchimedean v)
   {ι : Type*} (s : Finset ι) (x : ι → R) :
    max (v (∑ i ∈ s, x i)) 1 ≤ ∏ i ∈ s, max (v (x i)) 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  refine sup_le ?_ <| s.one_le_prod fun _ ↦ le_max_right ..
  grw [hv.apply_sum_le_sup_of_isNonarchimedean hs]
  exact sup'_le hs (fun i ↦ v (x i)) fun i hi ↦ le_prod_max_one hi fun i ↦ v (x i)
-- plus import Mathlib.Algebra.Order.Ring.IsNonarchimedean

end Finset

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues Function

@[to_fun (attr := simp)]
lemma logHeight_zero {ι : Type*} : logHeight (0 : ι → K) = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[to_fun (attr := simp)]
lemma logHeight_one {ι : Type*} : logHeight (1 : ι → K) = 0 := by
  simp [logHeight_eq_log_mulHeight]

-- @[fun_prop]
lemma AdmissibleAbsValues.hasFiniteMulSupport {x : K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ v.val x).mulSupport.Finite :=
  mulSupport_finite hx

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

-- Finiteness of the multiplicative support for some relevant functions.
-- @[fun_prop]
lemma mulSupport_iSup_nonarchAbsVal_finite {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).mulSupport.Finite := by
  simp only [iSup_eq_iSup_subtype hx (map_zero _) (AbsoluteValue.nonneg _)]
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| ne_iff.mp hx
  -- suffices (fun v : nonarchAbsVal ↦ ⨆ i : {j // x j ≠ 0}, v.val (x i)).mulSupport.Finite by
  --   convert this with v
  --   obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := ne_iff.mp hx
  --   have : Nonempty ι := .intro i
  --   refine le_antisymm ?_ <| ciSup_le fun ⟨j, hj⟩ ↦ le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl
  --   refine ciSup_le fun j ↦ ?_
  --   rcases eq_or_ne (x j) 0 with h | h
  --   · rw [h, v.val.map_zero]
  --     exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
  --   · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨j, h⟩ le_rfl
  -- -- fun_prop (disch := grind)
  -- -- solve_by_elim [Set.finite_iUnion, Set.Finite.subset, mulSupport_iSup, mulSupport_finite]
  exact finite_mulSupport_iSup fun i ↦ mulSupport_finite i.prop
  -- exact (Set.finite_iUnion fun i : {j | x j ≠ 0} ↦ mulSupport_finite i.prop).subset <|
  --   mulSupport_iSup _

-- @[fun_prop]
lemma mulSupport_max_nonarchAbsVal_finite (x : K) :
    (fun v : nonarchAbsVal ↦ max (v.val x) 1).mulSupport.Finite := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  -- fun_prop (disch := assumption)
  exact finite_mulSupport_max (mulSupport_finite hx) finite_mulSupport_one
  -- simp_rw [max_eq_iSup]
  -- convert mulSupport_iSup_nonarchAbsVal_finite (x := ![x, 1]) <| by simp with v i
  -- fin_cases i <;> simp

lemma mulHeight_comp_le {ι ι' : Type*} [Finite ι] [Finite ι'] (f : ι → ι') (x : ι' → K) :
    mulHeight (x ∘ f) ≤ mulHeight x := by
  rcases eq_or_ne (x ∘ f) 0 with h₀ | h₀
  · simpa [h₀] using one_le_mulHeight _
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nonempty ι := .intro (ne_iff.mp h₀).choose
  rw [mulHeight_eq h₀, mulHeight_eq hx]
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v ((x ∘ f) i) ≤ ⨆ i, v (x i) :=
    ciSup_le fun i ↦ Finite.le_ciSup_of_le (f i) le_rfl
  gcongr
  · exact finprod_nonneg fun v ↦ v.val.iSup_abv_nonneg
  · exact Multiset.prod_map_nonneg fun v _ ↦ v.iSup_abv_nonneg
  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ v.iSup_abv_nonneg) fun v _ ↦ H v
  · exact finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h₀)
      (fun v ↦ v.val.iSup_abv_nonneg) (mulSupport_iSup_nonarchAbsVal_finite hx) fun v ↦ H v.val

/-!
### Heights and "Segre embedding"

We show that the multiplicative height of `fun (i, j) ↦ x i * y j` is the product of the
multiplicative heights of `x` and `y` (and the analogous statement for logarithmic heights).
-/

section Segre

section two

variable {ι ι' : Type*} [Finite ι] [Finite ι']

/-- The multiplicative height of the "multiplication table" `fun (i, j) ↦ x i * y j`
is the product of the multiplicative heights of `x` and `y`. -/
lemma mulHeight_fun_mul_eq {x : ι → K} (hx : x ≠ 0) {y : ι' → K} (hy : y ≠ 0) :
    mulHeight (fun a : ι × ι' ↦ x a.1 * y a.2) = mulHeight x * mulHeight y := by
  have hxy : (fun a : ι × ι' ↦ x a.1 * y a.2) ≠ 0 := by
    obtain ⟨i, hi⟩ := ne_iff.mp hx
    obtain ⟨j, hj⟩ := ne_iff.mp hy
    exact ne_iff.mpr ⟨⟨i, j⟩, mul_ne_zero hi hj⟩
  rw [mulHeight_eq hx, mulHeight_eq hy, mulHeight_eq hxy, mul_mul_mul_comm, ← Multiset.prod_map_mul,
    ← finprod_mul_distrib
        (mulSupport_iSup_nonarchAbsVal_finite hx) (mulSupport_iSup_nonarchAbsVal_finite hy)]
  congr <;> ext1 v
  · exact v.iSup_abv_fun_mul_eq_iSup_abv_mul_iSup_abv ..
  · exact v.val.iSup_abv_fun_mul_eq_iSup_abv_mul_iSup_abv ..

open Real in
/-- The logarithmic height of the "multiplication table" `fun (i, j) ↦ x i * y j`
is the sum of the logarithmic heights of `x` and `y`. -/
lemma logHeight_fun_mul_eq {x : ι → K} (hx : x ≠ 0) {y : ι' → K} (hy : y ≠ 0) :
    logHeight (fun a : ι × ι' ↦ x a.1 * y a.2) = logHeight x + logHeight y := by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  rw [mulHeight_fun_mul_eq hx hy]

end two

section many

universe u v

variable {α : Type u} [Fintype α] {ι : α → Type v} [∀ a, Finite (ι a)]

open Finset in
/-- Consider a finite family `x : (a : α) → ι a → K` of tuples. Then the multiplicative height
of the "multiplication table" `fun (I : (a : α) → ι a ↦ ∏ a, x a (I a))` is the product
of the multiplicative heights of all the `x a`. -/
lemma mulHeight_fun_prod_eq {x : (a : α) → ι a → K} (hx : ∀ a, x a ≠ 0) :
    mulHeight (fun I : (a : α) → ι a ↦ ∏ a, x a (I a)) = ∏ a, mulHeight (x a) := by
  revert x ι
  refine @Fintype.induction_empty_option
    (fun α _ ↦ ∀ (ι : α → Type v) [∀ a, Finite (ι a)] {x : (a : α) → ι a → K} (hx : ∀ a, x a ≠ 0),
      mulHeight (fun I : (a : α) → ι a ↦ ∏ a, x a (I a)) = ∏ a, mulHeight (x a))
    (fun β β' _ e H ι _ x hx ↦ ?equiv) ?empty (fun β hβ ih ι _ x hx ↦ ?option) α inferInstance
  case empty => simp
  case equiv =>
    have (a : β) : Finite ((ι ∘ ⇑e) a) := inferInstanceAs <| Finite (ι (e a))
    specialize H (ι ∘ ⇑e) (x := fun b ↦ x (e b)) (by simp [hx])
    rw [prod_equiv e (t := .univ) (by simp) (g := fun b ↦ mulHeight (x b)) (fun _ _ ↦ rfl)] at H
    rw [← H, ← mulHeight_comp_equiv (e.piCongrLeft ι).symm]
    refine congrArg mulHeight <| funext fun I ↦ ?_
    simp only [comp_apply]
    let : Fintype β := .ofEquiv β' e.symm
    refine prod_equiv e.symm (s := .univ) (t := .univ) (by simp) fun b _ ↦ ?_
    rw [e.piCongrLeft_symm_apply, e.apply_symm_apply]
  case option =>
    simp only [Fintype.prod_option]
    have (b : β) : Finite ((ι ∘ some) b) := by grind
    rw [← ih (ι ∘ Option.some) (x := fun b i ↦ x (some b) i) (by grind),
      ← mulHeight_fun_mul_eq (hx none) ?hprod]
    case hprod =>
      choose J hJ using fun b ↦ ne_iff.mp (hx (some b))
      exact ne_iff.mpr ⟨J, prod_ne_zero_iff.mpr fun b _ ↦ hJ b⟩
    rw [← mulHeight_comp_equiv <| Equiv.piOptionEquivProd (α := β) (β := ι), comp_def]
    -- `rfl` also works here, but smells of defeq abuse.
    simp only [comp_apply, Equiv.piOptionEquivProd_apply]

open Real in
/-- Consider a finite family `x : (a : α) → ι a → K` of tuples. Then the logarithmic height
of the "multiplication table" `fun (I : (a : α) → ι a ↦ ∏ a, x a (I a))` is the sum
of the logarithmic heights of all the `x a`. -/
lemma logHeight_fun_prod_eq {x : (a : α) → ι a → K} (hx : ∀ a, x a ≠ 0) :
    logHeight (fun I : (a : α) → ι a ↦ ∏ a, x a (I a)) = ∑ a, logHeight (x a) := by
  simp only [logHeight_eq_log_mulHeight]
  rw [← log_prod fun a _ ↦ mulHeight.ne_zero _]
  exact congrArg log <| mulHeight_fun_prod_eq hx

end many

end Segre

/-!
### Bounds for the height of sums of field elements
-/


/- -- The "local" version of the height bound for `x + y` for archimedean `v`.
private lemma max_abv_add_one_le (v : AbsoluteValue K ℝ) (x y : K) :
    max (v (x + y)) 1 ≤ 2 * (max (v x) 1 * max (v y) 1) := by
  refine sup_le ((v.add_le x y).trans ?_) <| (show (1 : ℝ) ≤ 2 * 1 by norm_num).trans ?_
  · rw [two_mul]
    exact add_le_add (le_mul_max_max_left ..) (le_mul_max_max_right ..)
  · exact mul_le_mul_of_nonneg_left (one_le_mul_max_max ..) zero_le_two -/

/- -- The "local" version of the height bound for `x + y` for nonarch)imedean `v`.
private lemma max_abv_add_one_le_of_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (x y : K) :
    max (v (x + y)) 1 ≤ (max (v x) 1 * max (v y) 1) := by
  refine sup_le ?_ <| one_le_mul_max_max ..
  exact (hv x y).trans <| sup_le (le_mul_max_max_left ..) (le_mul_max_max_right ..) -/

/- private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two] -/



end Height

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

-- #find_home! Real.log_finprod -- [Mathlib.Analysis.SpecialFunctions.Log.Basic]

open Finite in
lemma Real.ciSup_mul_le {ι : Type*} [Finite ι] {x y : ι → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⨆ i, x i * y i ≤ (⨆ i, x i) * ⨆ i, y i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  exact ciSup_le fun i ↦ mul_le_mul (le_ciSup x i) (le_ciSup y i) (hy i) <| iSup_nonneg hx

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
        obtain ⟨v, -, rfl⟩ := mem_map.mp h -- use `Multiset.prod_map_nonneg` when available!
        positivity
      refine finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _) (fun v ↦ by grind) ?_ ?_
      · -- change HasFiniteMulSupport _
        --fun_prop
        refine Set.Finite.subset ?_ <|
          s.mulSupport_prod fun i (v : nonarchAbsVal) ↦ max (v.val (x i)) 1
        exact s.finite_toSet.biUnion fun _ _ ↦ mulSupport_max_nonarchAbsVal_finite _
      · exact fun v ↦ max_abv_sum_one_le_of_isNonarchimedean (isNonarchimedean _ v.prop) _ x
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

/-!
### Height bound for products
-/

@[simp]
lemma mulHeight_eq_one_of_isEmpty {ι : Type*} [IsEmpty ι] (x : ι → K) :
    mulHeight x = 1 := by
  rw [show x = 0 from Subsingleton.elim ..]
  exact mulHeight_zero

/-- The multiplicative height of a pointwise product of tuples is bounded by the product
of their multiplicative heights. -/
lemma mulHeight_mul_le {ι : Type*} [Finite ι] (x y : ι → K) :
    mulHeight (x * y) ≤ mulHeight x * mulHeight y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mulHeight y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using one_le_mulHeight x
  rcases eq_or_ne (x * y) 0 with hxy | hxy
  · rw [hxy, mulHeight_zero, ← one_mul 1]
    gcongr <;> exact one_le_mulHeight _
  rw [mulHeight_eq hx, mulHeight_eq hy, mulHeight_eq hxy, mul_mul_mul_comm, ← Multiset.prod_map_mul,
    ← finprod_mul_distrib (mulSupport_iSup_nonarchAbsVal_finite hx)
        (mulSupport_iSup_nonarchAbsVal_finite hy)]
  simp only [Pi.mul_apply, map_mul]
  have H₁ : 0 ≤ (archAbsVal.map fun v ↦ (⨆ i, v (x i)) * ⨆ i, v (y i)).prod := by
    refine Multiset.prod_nonneg fun a ha ↦ ?_
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha -- use `Multiset.prod_map_nonneg` when available!
    refine mul_nonneg ?_ ?_ <;> exact v.iSup_abv_nonneg
  have H₂ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) * v.val (y i) := by
    refine finprod_nonneg fun v ↦ iSup_nonneg fun i ↦ mul_nonneg ?_ ?_ <;> exact v.val.nonneg _
  gcongr
  · refine Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ iSup_nonneg fun i ↦ by positivity)
      fun v hv ↦ Real.ciSup_mul_le ?_ ?_ <;> exact fun _ ↦ by positivity
  · refine finprod_le_finprod ?_ (fun v ↦ ?_) ?_ (Pi.le_def.mpr fun v ↦ ?_)
    · simpa only [← map_mul] using mulSupport_iSup_nonarchAbsVal_finite hxy
    · simpa only [← map_mul] using v.val.iSup_abv_nonneg
    · refine Function.finite_mulSupport_mul ?_ ?_ <;> exact mulSupport_iSup_nonarchAbsVal_finite ‹_›
    · refine Real.ciSup_mul_le ?_ ?_ <;> exact fun i ↦ by positivity

/-- The logarithmic height of a pointwise product of tuples is bounded by the sum
of their logarithmic heights. -/
lemma logHeight_mul_le {ι : Type*} [Finite ι] (x y : ι → K) :
    logHeight (x * y) ≤ logHeight x + logHeight y := by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) <| mulHeight_mul_le ..

/-- The multiplicative height of `x * y` is at most the product of the multiplicative heights
of `x` and `y`. -/
lemma mulHeight₁_mul_le (x y : K) : mulHeight₁ (x * y) ≤ mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁_eq_mulHeight]
  rw [show ![x * y, 1] = ![x, 1] * ![y, 1] by ext i; fin_cases i <;> simp]
  exact mulHeight_mul_le ![x, 1] ![y, 1]

/-- The logarithmic height of `x * y` is at most the sum of the logarithmic heights
of `x` and `y`. -/
lemma logHeight₁_mul_le (x y : K) : logHeight₁ (x * y) ≤ logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact log_le_log (by positivity) <| mulHeight₁_mul_le ..

/-- The multiplicative height of the pointwise negative of a tuple
equals its multiplicative height. -/
@[simp]
lemma mulHeight_neg {ι : Type*} [Finite ι] (x : ι → K) : mulHeight (-x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp [mulHeight_eq hx, mulHeight_eq <| neg_ne_zero.mpr hx]

/-- The logarithmic height of the pointwise negative of a tuple
equals its logarithmic height. -/
@[simp]
lemma logHeight_neg {ι : Type*} [Finite ι] (x : ι → K) : logHeight (-x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

end Height

#exit

/-!
### Height bounds for values of polynomials

This is better done as a special case of results on polynomial maps on tuples.
See MvPolynomial.lean.
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

open AdmissibleAbsValues Finset Function

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

-- @[fun_prop]
private lemma mulSupport_max_sup'_nonarchAbsVal_finite (p : K[X]) :
    (fun v : nonarchAbsVal ↦
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1)
      |>.mulSupport.Finite := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have h (v : AbsoluteValue K ℝ) :
      (range (p.natDegree + 1)).sup' nonempty_range_add_one (fun n ↦ v (p.coeff n)) =
        (p.support).sup' (support_nonempty.mpr hp) fun n ↦ v (p.coeff n) := by
    refine le_antisymm (Finset.sup'_le nonempty_range_add_one _ fun i hi ↦ ?_) ?_
    · by_cases h : i ∈ p.support
      · exact Finset.le_sup' (fun i ↦ v (p.coeff i)) h
      · simp only [mem_support_iff, ne_eq, not_not] at h
        simp only [h, AbsoluteValue.map_zero, le_sup'_iff, mem_support_iff, apply_nonneg, and_true]
        exact ⟨p.natDegree, Polynomial.coeff_natDegree (p := p) ▸ leadingCoeff_ne_zero.mpr hp⟩
    · refine Finset.sup'_mono _ (fun i hi ↦ ?_) (support_nonempty.mpr hp)
      exact mem_range_succ_iff.mpr <| le_natDegree_of_mem_supp i hi
  simp only [h]
  refine finite_mulSupport_max ?_ finite_mulSupport_one
  refine finite_mulSupport_sup' p.support (fun _ _ ↦ ?_) (support_nonempty.mpr hp)
  exact mulSupport_finite (by grind)
  -- fun_prop (disch := grind)
  /- refine (Set.Finite.union ?_ ?_).subset <| mulSupport_max ..
  · have : ∀ i ∈ p.support, (fun v : nonarchAbsVal ↦ v.val (p.coeff i)).mulSupport.Finite :=
      fun i hi ↦ mulSupport_finite <| mem_support_iff.mp hi
    refine (p.support.finite_toSet.biUnion this).subset fun v hv ↦ ?_
    simp only [mem_mulSupport, SetLike.mem_coe, Set.mem_iUnion, exists_prop] at hv ⊢
    contrapose! hv
    exact Finset.sup'_eq_of_forall _ (fun i ↦ v.val (p.coeff i)) hv
  · exact mulSupport_fun_one (M := ℝ) ▸ Set.finite_empty -/

open Multiset in
/-- The multiplicative height of the value of a polynomial `p : K[X]` at `x : K` is bounded
by `p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree`. -/
lemma mulHeight₁_eval_le (p : K[X]) (x : K) :
    mulHeight₁ (p.eval x) ≤ p.mulHeight₁Bound * (mulHeight₁ x) ^ p.natDegree := by
  simp only [mulHeight₁_eq, p.mulHeight₁Bound_eq]
  have H : (fun v : nonarchAbsVal ↦ max (v.val x) 1 ^ p.natDegree).mulSupport.Finite :=
    finite_mulSupport_pow (mulSupport_max_nonarchAbsVal_finite _) _
    -- (mulSupport_max_nonarchAbsVal_finite x).subset <| mulSupport_pow ..
  calc
    _ ≤ (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1 * (max (v x) 1) ^ p.natDegree).prod * _ := by
      refine mul_le_mul_of_nonneg_right ?_ <| finprod_nonneg fun _ ↦ by grind
      exact prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) fun _ _ ↦ max_abv_eval_one_le ..
    _ ≤ _ * ∏ᶠ (v : ↑nonarchAbsVal), max ((Finset.range (p.natDegree + 1)).sup' nonempty_range_add_one
          fun n ↦ v.val (p.coeff n)) 1 * (max (v.val x) 1) ^ p.natDegree := by
      refine mul_le_mul_of_nonneg_left ?_ <| Multiset.prod_nonneg fun a ha ↦ ?_
      · refine finprod_le_finprod (mulSupport_max_nonarchAbsVal_finite _) (fun v ↦ by grind) ?_ ?_
        · -- change HasFiniteMulSupport _
          -- fun_prop
          exact finite_mulSupport_mul (mulSupport_max_sup'_nonarchAbsVal_finite p) H
          -- refine Set.Finite.subset ?_ <| mulSupport_mul ..
          -- exact p.mulSupport_max_sup'_nonarchAbsVal_finite.union H
        · exact Pi.le_def.mpr fun v ↦ max_abv_eval_one_le_of_nonarch p x (isNonarchimedean _ v.prop)
      · obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
        positivity
    _ = _ := by
      rw [prod_map_mul, mul_pow, prod_map_pow,
        finprod_mul_distrib p.mulSupport_max_sup'_nonarchAbsVal_finite H,
          -- (by change HasFiniteMulSupport _; fun_prop),
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
    pure (.positive q(mulHeight_pos $a))
  | _, _, _ => throwError "not Projectivization.mulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.logHeight` is always nonnegative. -/
@[positivity Projectivization.logHeight _]
meta def evalProjLogHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(zero_le_logHeight $a))
  | _, _, _ => throwError "not Projectivization.logHeight"

end Mathlib.Meta.Positivity
