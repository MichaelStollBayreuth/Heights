import Heights.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Height bounds for polynomial maps

We prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family of
homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K` with `ι` finite.
-/

section aux

-- Auxiliary stuff

private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

private lemma iSup_fun_eq_max (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
  rw [show f = ![f 0, f 1] from List.ofFn_inj.mp rfl]
  exact (max_eq_iSup ..).symm

namespace Finsupp

-- @Finsupp.sum : {α : Type u_2} → {M : Type u_1} → {N : Type} → [inst : Zero M] →
--    [AddCommMonoid N] → (α →₀ M) → (α → M → N) → N

lemma single_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] (f : α →₀ M) {g : M → N} (hg : g 0 = 0) (h : ∀ m, 0 ≤ g m) (a : α) :
    g (f a) ≤ f.sum fun _ m ↦ g m := by
  rcases eq_or_ne (f a) 0 with H | H
  · rw [H, hg]
    exact sum_nonneg' fun a ↦ h _
  · exact Finset.single_le_sum (fun a _ ↦ h (f a)) <| mem_support_iff.mpr H

-- #find_home! single_le_sum -- [Mathlib.Data.Finsupp.Order]

end Finsupp

namespace Multiset

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

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {ι : Type*}

-- possibly useful more generally?
lemma IsHomogeneous.degree_eq_sum_deg_support {p : MvPolynomial ι R} {N : ℕ}
    (hp : p.IsHomogeneous N) {s : ι →₀ ℕ} (hs : s ∈ p.support) :
    N = ∑ i ∈ s.support, s i := by
  rw [IsHomogeneous, IsWeightedHomogeneous] at hp
  rw [← hp <| mem_support_iff.mp hs, ← Finsupp.degree_apply, Finsupp.degree_eq_weight_one,
    Pi.one_def]

-- #find_home! sum_deg_support_eq_degree -- [Mathlib.RingTheory.MvPolynomial.Homogeneous]

lemma support_one_eq [Nontrivial R] : (1 : MvPolynomial ι R).support = {0} := by
  classical
  rw [show support (1 : MvPolynomial ι R) = if (1 : R) = 0 then ∅ else {0} from rfl]
  simp

-- #find_home! support_one_eq -- [Mathlib.Algebra.MvPolynomial.Basic]

end MvPolynomial

namespace Polynomial

variable {R : Type*} [CommSemiring R]

lemma eq_zero_of_homogenize_eq_zero {p : R[X]} {N : ℕ} (hN : p.natDegree ≤ N)
    (h : p.homogenize N = 0) :
    p = 0 := by
  ext n
  simp only [coeff_zero]
  rcases le_or_gt n p.natDegree with H | H
  · have : p.coeff n = (p.homogenize N).coeff fun₀ | 0 => n | 1 => N - n := by
      simp [coeff_homogenize]
      lia
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H

/-- Given a polynomial `p : R[X]`, this is the family `![p₀, p₁]` of homogeneous bivariate
polynomials of degree `p.natDegree` such that `p(x) = p₀(x,1)/p₁(x,1)`. -/
noncomputable
def to_tuple_mvPolynomial (p : R[X]) : Fin 2 → MvPolynomial (Fin 2) R :=
  ![p.homogenize p.natDegree, (MvPolynomial.X 1) ^ p.natDegree]

-- #find_home! to_tuple_mvPolynomial -- [Mathlib.Algebra.Polynomial.Homogenize]

lemma isHomogenous_toTupleMvPolynomial (p : R[X]) :
    ∀ i, (p.to_tuple_mvPolynomial i).IsHomogeneous p.natDegree := by
  intro i
  fin_cases i
  · simp [to_tuple_mvPolynomial]
  · simpa [to_tuple_mvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

lemma eval_eq_div_eval_toTupleMvPolynomial {R : Type*} [Field R] (p : R[X]) (x : R) :
    p.eval x =
      (p.to_tuple_mvPolynomial 0).eval ![x, 1] / (p.to_tuple_mvPolynomial 1).eval ![x, 1] := by
  simp [to_tuple_mvPolynomial, eval_homogenize]

lemma sum_eq_natDegree_of_mem_support_homogenize (p : R[X]) {s : Fin 2 →₀ ℕ}
    (hs : s ∈ (p.homogenize p.natDegree).support) :
    s 0 + s 1 = p.natDegree := by
  simp [(isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

lemma finsuppSum_homogenize_eq {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R → M} :
    (Finsupp.sum (p.homogenize p.natDegree) fun _ c ↦ f c) = p.sum fun _ c ↦ f c := by
  rw [MvPolynomial.sum_def, sum_def p]
  refine Finset.sum_nbij' (fun s ↦ s 0) (fun n ↦ fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs ↦ ?_) (fun n hn ↦ ?_) (fun s hs ↦ ?_) (fun n hn ↦ by simp)
    fun s hs ↦ ?_
  · simpa [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [coeff_homogenize, mem_support_iff.mp hn]
      using Nat.add_sub_of_le <| le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply, #9d71, #e6fa, #a431, #4bd8,
      sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs]

end Polynomial

namespace Finite

-- Add versions of `le_ciSup_of_le` and `ciSup_mono` for finite index types;
-- see `Finite.le_ciSup`in  Mathlib.Order.ConditionallyCompleteLattice.Finset.

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

end Finite

namespace IsNonarchimedean

variable {R α : Type*} [CommRing R]

/- The ultrametric triangle inequality for finite sums. -/
private lemma apply_sum_le {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v) {l : α → R} {s : Finset α} :
    v (∑ i ∈ s, l i) ≤ ⨆ i : s, v (l i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    grw [hv .., ih]
    refine max_le ?_ ?_
    · exact Finite.le_ciSup_of_le ⟨_, s.mem_insert_self a⟩ le_rfl
    · rcases isEmpty_or_nonempty s with hs | hs
      · simpa using v.iSup_abv_nonneg
      exact ciSup_le fun i ↦ Finite.le_ciSup_of_le (⟨i.val, Finset.mem_insert_of_mem i.prop⟩) le_rfl

end IsNonarchimedean

end aux

/-!
### Upper bound for the height of the image under a polynomial map

If `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`
and `x : ι → K`, then the multiplicative height of `fun j ↦ (p j).eval x` is bounded above by
an (explicit) constant depending only on `p` times the `N`th power of the multiplicative
height of `x`. A similar statement holds for the logarithmic height.
-/

namespace Height

open MvPolynomial

variable {K : Type*} [Field K] {ι : Type*}

-- The "local" version of the height bound for (archimedean) absolute values.
private lemma mvPolynomial_bound [Finite ι] (v : AbsoluteValue K ℝ) {p : MvPolynomial ι K} {N : ℕ}
    (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ p.sum (fun _ c ↦ v c) * (⨆ i, v (x i)) ^ N := by
  rw [eval_eq, sum_def, Finset.sum_mul]
  grw [AbsoluteValue.sum_le]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  gcongr
  rw [hp.degree_eq_sum_deg_support hs, ← Finset.prod_pow_eq_pow_sum]
  gcongr with i
  exact Finite.le_ciSup (fun j ↦ v (x j)) i

-- The "local" version of the height bound for nonarchimedean absolute values.
private lemma mvPolynomial_bound_of_IsNonarchimedean [Finite ι] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ (⨆ s : p.support, v (coeff s p)) * (⨆ i, v (x i)) ^ N := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · simp_all
  rw [eval_eq]
  obtain ⟨s, hs₁, hs₂⟩ :=
    hv.finset_image_add_of_nonempty (fun d ↦ coeff d p * ∏ i ∈ d.support, x i ^ d i)
      (support_nonempty.mpr hp₀)
  grw [hs₂]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  gcongr
  · exact v.iSup_abv_nonneg
  · exact Finite.le_ciSup_of_le (⟨s, hs₁⟩ : p.support) le_rfl
  · rw [hp.degree_eq_sum_deg_support hs₁, ← Finset.prod_pow_eq_pow_sum]
    gcongr with i
    exact Finite.le_ciSup (fun j ↦ v (x j)) i

variable {ι' : Type*}

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

/-- The constant in the (upper) height bound on values of `p`. -/
noncomputable
def mulHeightBound (p : ι' → MvPolynomial ι K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
    ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1

lemma mulHeightBound_eq (p : ι' → MvPolynomial ι K) :
    mulHeightBound p =
     (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
        ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1 :=
  rfl

lemma mulHeightBound_zero_one : mulHeightBound ![(0 : MvPolynomial (Fin 2) K), 1] = 1 := by
  simp only [mulHeightBound, Nat.succ_eq_add_one, Nat.reduceAdd, iSup_fun_eq_max]
  conv_rhs => rw [← one_mul 1]
  congr
  · convert Multiset.prod_map_one with v
    simp [MvPolynomial.sum_def, MvPolynomial.support_one_eq]
  · refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
    rw [show ![(0 : MvPolynomial (Fin 2) K), 1] 1 = 1 from rfl, MvPolynomial.support_one_eq]
    simp

variable [Finite ι']

open Function in
private lemma finite_mulSupport_iSup_max_iSup_one (h : Nonempty ι') (p : ι' → MvPolynomial ι K) :
    (fun v : nonarchAbsVal ↦
      ⨆ j, max (⨆ s : (p j).support, v.val (coeff s.val (p j))) 1).mulSupport.Finite := by
  -- fun_prop (disch := assumption)
  refine finite_mulSupport_iSup fun j ↦ ?_
  rcases isEmpty_or_nonempty (p j).support with hs₀ | hs₀
  · simp
  refine finite_mulSupport_max ?_ finite_mulSupport_one
  exact finite_mulSupport_iSup fun ⟨s, hs⟩ ↦ mulSupport_finite <| mem_support_iff.mp hs

open Real Multiset Finsupp in
-- set_option Elab.async false in
-- #count_heartbeats in -- 6794
private lemma mulHeight_constantCoeff_le_mulHeightBound {p : ι' → MvPolynomial ι K}
    (h : (fun j ↦ constantCoeff (p j)) ≠ 0) :
    mulHeight (fun j ↦ constantCoeff (p j)) ≤ mulHeightBound p := by
  simp only [mulHeight_eq h, mulHeightBound_eq]
  gcongr
  · exact finprod_nonneg fun v ↦ v.val.iSup_abv_nonneg
  · exact prod_map_nonneg fun v _ ↦ iSup_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ by positivity
  · have H (v : AbsoluteValue K ℝ) (j : ι') : v (constantCoeff (p j)) ≤ sum (p j) fun _ c ↦ v c :=
      single_le_sum _ v.map_zero (fun _ ↦ by positivity) _
    exact prod_map_le_prod_map₀ _ _ (fun v _ ↦ v.iSup_abv_nonneg) fun v _ ↦ Finite.ciSup_mono (H v)
  · refine finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h)
      (fun v ↦ v.val.iSup_abv_nonneg) ?_ ?_
    · exact finite_mulSupport_iSup_max_iSup_one (Function.ne_iff.mp h).nonempty p
    · refine fun v ↦ Finite.ciSup_mono fun j ↦ ?_
      rw [show constantCoeff (p j) = coeff 0 (p j) from rfl]
      rcases eq_or_ne (coeff 0 (p j)) 0 with h₀ | h₀
      · simp [h₀]
      · exact le_sup_of_le_left <| Finite.le_ciSup_of_le ⟨0, by simp [h₀]⟩ le_rfl

variable [Finite ι]

open Real Finsupp Multiset in
-- set_option Elab.async false in
-- #count_heartbeats in -- 20170
/-- Let `K` be a field with an admissible family of absolute values (giving rise
to a multiplicative height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables indexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the multiplicative height of `fun j : ι' ↦ eval x (p j)` is bounded by a constant
(which is made explicit) times `mulHeight x ^ N`. -/
theorem mulHeight_eval_le {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N)
    (x : ι → K) :
    mulHeight (fun j ↦ (p j).eval x) ≤ max (mulHeightBound p) 1 * mulHeight x ^ N := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne (fun j ↦ constantCoeff (p j)) 0 with h | h
    · simp [h]
    · simpa using le_max_of_le_left <| mulHeight_constantCoeff_le_mulHeightBound h
  rcases eq_or_ne (fun j ↦ eval x (p j)) 0 with h₀ | h₀
  · grw [← le_max_right]
    simpa [h₀, mulHeight_zero] using one_le_pow₀ <| one_le_mulHeight x
  have F₁ := finite_mulSupport_iSup_max_iSup_one (Function.ne_iff.mp h₀).nonempty p
  have F₂ := mulSupport_iSup_nonarchAbsVal_finite hx
  have F₃ := Function.finite_mulSupport_pow F₂ N
  have H₀ (v : AbsoluteValue K ℝ) : 0 ≤ ⨆ j, Finsupp.sum (p j) fun _ c ↦ v c :=
    iSup_nonneg (fun j ↦ sum_nonneg' <| fun s ↦ by positivity)
  -- The following four statements are used in the `gcongr`s below.
  have H₁ : 0 ≤ (archAbsVal.map (fun v ↦ ⨆ j, Finsupp.sum (p j) fun _ c ↦ v c)).prod :=
    prod_map_nonneg fun v _ ↦ H₀ v
  have H₂ : 0 ≤ (archAbsVal.map (fun v ↦ ⨆ i, v (x i))).prod :=
    prod_map_nonneg fun v _ ↦ v.iSup_abv_nonneg
  have H₃ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val ((eval x) (p i)) :=
    finprod_nonneg fun v ↦ v.val.iSup_abv_nonneg
  have H₄ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) :=
    finprod_nonneg fun v ↦ v.val.iSup_abv_nonneg
  -- The following two statements are helpful for discharging the goals left by `gcongr`.
  have HH₁ (v : AbsoluteValue K ℝ) : 0 ≤ (⨆ i, v (x i)) ^ N := pow_nonneg v.iSup_abv_nonneg N
  have HH₂ (f : ι' → ℝ) (j : ι') : f j ≤ ⨆ j, f j := Finite.le_ciSup ..
  simp only [mulHeight_eq hx, mulHeight_eq h₀, mulHeightBound_eq]
  grw [← le_max_left]
  rw [mul_pow, mul_mul_mul_comm]
  gcongr
  · -- archimedean part: reduce to "local" statement `mvPolynomial_bound`
    rw [← prod_map_pow, ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ v.iSup_abv_nonneg)
      fun v _ ↦ Real.iSup_le (fun j ↦ ?_) <| mul_nonneg (H₀ v) (HH₁ v)
    grw [mvPolynomial_bound v (hp j) x]
    gcongr
    · exact HH₁ v
    · exact HH₂ (fun j ↦ Finsupp.sum (p j) fun _ c ↦ v c) j
  · -- nonarchimedean part: reduce to "local" statement `mvPolynomial_bound_nonarch`
    rw [finprod_pow F₂, ← finprod_mul_distrib F₁ F₃]
    refine finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h₀)
      (fun v ↦ v.val.iSup_abv_nonneg) (Function.finite_mulSupport_mul F₁ F₃)
      fun v ↦ Real.iSup_le (fun j ↦ ?_) ?_
    · grw [mvPolynomial_bound_of_IsNonarchimedean (isNonarchimedean _ v.prop) (hp j) x]
      gcongr
      · exact HH₁ v.val
      · grw [le_max_left (iSup ..) 1]
        exact HH₂ (fun j ↦ max (⨆ s : (p j).support, v.val (coeff s.val (p j))) 1) j
    · exact mul_nonneg (iSup_nonneg fun _ ↦ by positivity) <| by simp only [HH₁]

open Real in
/-- Let `K` be a field with an admissible family of absolute values (giving rise
to a logarithmic height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables indexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the logarithmic height of `fun j : ι' ↦ eval x (p j)` is bounded by a constant
(which is made explicit) plus `N * logHeight x`. -/
theorem logHeight_eval_le {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N)
    (x : ι → K) :
    logHeight (fun j ↦ (p j).eval x) ≤ log (max (mulHeightBound p) 1) + N * logHeight x := by
  simp_rw [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_eval_le hp x

end Height

namespace Polynomial

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues

/-- The constant in the upper height bound for `p.eval x`. -/
noncomputable
def mulHeight₁Bound (p : K[X]) : ℝ :=
  max (mulHeightBound p.to_tuple_mvPolynomial) 1

open Finset in
/-- A formula for `mulHeight₁Bound p` in terms of the coefficients of `p`. -/
lemma mulHeight₁Bound_eq (p : K[X]) :
    p.mulHeight₁Bound =
      (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
      ∏ᶠ v : nonarchAbsVal,
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [mulHeight₁Bound, to_tuple_mvPolynomial] using mulHeightBound_zero_one.le
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
    exact Finite.le_ciSup_of_le 1 <| by simp [to_tuple_mvPolynomial, MvPolynomial.X_pow_eq_monomial]
  congr <;> ext v
  · simp [iSup_fun_eq_max, to_tuple_mvPolynomial, finsuppSum_homogenize_eq,
      MvPolynomial.X_pow_eq_monomial]
  · have H : (⨆ s : (MvPolynomial.X (R := K) (σ := Fin 2) 1 ^ p.natDegree).support,
        if (fun₀ | 1 => p.natDegree : Fin 2 →₀ ℕ) = s then 1 else 0) = (1 : ℝ) := by
      rw [MvPolynomial.support_X_pow (R := K) (1 : Fin 2) p.natDegree]
      simp [ciSup_unique]
    suffices ⨆ s : (p.homogenize p.natDegree).support, v.val (p.coeff (s.val 0)) =
        (range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n) by
      simpa [← Finite.ciSup_sup, iSup_fun_eq_max, to_tuple_mvPolynomial, coeff_homogenize,
        MvPolynomial.X_pow_eq_monomial, p.sum_eq_natDegree_of_mem_support_homogenize, H]
        using congrArg (max · 1) this
    rw [sup'_eq_csSup_image, sSup_image']
    refine le_antisymm (ciSup_le fun s ↦ Finite.le_ciSup_of_le ⟨s.val 0, ?_⟩ le_rfl) ?_
    · grind only [= mem_coe, = mem_range, p.sum_eq_natDegree_of_mem_support_homogenize s.prop]
    · have := (nonempty_range_add_one (n := p.natDegree)).to_subtype
      refine ciSup_le fun n ↦ ?_
      rcases eq_or_ne (p.coeff n) 0 with h | h
      · simpa [h] using v.val.iSup_abv_nonneg
      · refine Finite.le_ciSup_of_le ⟨fun₀ | 0 => n | 1 => p.natDegree - n, ?_⟩ <| by simp
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

/-!
### Upper bound for the height of the image under a linear map
-/

namespace Height

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [Finite ι']

-- The "local" version of the bound for (archimedean) absolute values.
lemma linearMap_apply_bound [Nonempty ι'] (v : AbsoluteValue K ℝ) (A : ι' × ι → K) (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ Nat.card ι * (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  refine ciSup_le fun j ↦ ?_
  grw [v.sum_le]
  simp only [map_mul]
  grw [Finset.sum_le_sum (g := fun _ ↦ (⨆ ji, v (A ji)) * ⨆ i, v (x i)) fun i _ ↦ ?h]
  case h =>
    simp only
    gcongr
    · exact v.iSup_abv_nonneg
    · exact Finite.le_ciSup_of_le (j, i) le_rfl
    · exact Finite.le_ciSup_of_le i le_rfl
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, Finset.card_univ, Nat.card_eq_fintype_card]

-- The "local" version of the bound for nonarchimedean absolute values.
lemma linearMap_apply_bound_of_isNonarchimedean [Nonempty ι] [Nonempty ι'] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (A : ι' × ι → K) (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  refine ciSup_le fun j ↦ ?_
  grw [hv.apply_sum_le]
  simp only [map_mul]
  have (f : ι → ℝ) : ⨆ i : ↥Finset.univ, f i.val = ⨆ i, f i :=
    Function.Surjective.iSup_comp (fun i ↦ ⟨⟨i, Finset.mem_univ i⟩, rfl⟩) f
  rw [this fun i ↦ v (A (j, i)) * v (x i)]
  refine ciSup_le fun i ↦ ?_
  gcongr
  · exact v.iSup_abv_nonneg
  · exact Finite.le_ciSup_of_le (j, i) le_rfl
  · exact Finite.le_ciSup_of_le i le_rfl

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

open Multiset in
/-- Let `A : ι' × ι → K`, which we can interpret as an `ι' × ι` matrix over `K`.
Let `x : ι → K` be a tuple. Then the multiplicative height of `A x` is bounded by
`#ι ^ totalWeight K * mulHeight A * mulHeight x` (if `ι` is nonempty). -/
theorem mulHeight_linearMap_apply_le [Nonempty ι] (A : ι' × ι → K) (x : ι → K) :
    mulHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
  have H₀ : 1 ≤ Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
    rw [show (1 : ℝ) = 1 * 1 * 1 by ring]
    gcongr
    · exact_mod_cast Nat.one_le_pow _ _ Nat.card_pos
    · exact one_le_mulHeight _
    · exact one_le_mulHeight _
  rcases isEmpty_or_nonempty ι' with hι' | hι'
  · simpa only [mulHeight_eq_one_of_isEmpty, mul_one] using H₀
  rcases eq_or_ne (fun j ↦ ∑ i, A (j, i) * x i) 0 with h | h
  · simpa only [h, mulHeight_zero] using H₀
  rcases eq_or_ne A 0 with rfl | hA
  · rwa [show (fun j ↦ ∑ i, (0 : ι' × ι → K) (j, i) * x i) = 0 by simp [Pi.zero_def],
      mulHeight_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · rwa [show (fun j ↦ ∑ i, A (j, i) * (0 : ι → K) i) = 0 by simp [Pi.zero_def], mulHeight_zero]
  rw [mulHeight_eq h, mulHeight_eq hA, mulHeight_eq hx,
    mul_mul_mul_comm, ← mul_assoc, ← mul_assoc, mul_assoc (_ * _ * _)]
  gcongr
  · exact finprod_nonneg fun v ↦ v.val.iSup_abv_nonneg
  · refine mul_nonneg (mul_nonneg (by simp) ?_) ?_ <;>
      exact prod_map_nonneg fun v _ ↦ v.iSup_abv_nonneg
  · -- archimedean part: reduce to "local" statement `linearMap_apply_bound`
    rw [mul_assoc, ← prod_map_mul, ← prod_replicate, totalWeight, ← map_const', ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ v.iSup_abv_nonneg) fun v _ ↦ ?_
    rw [mul_comm (iSup _), ← mul_assoc]
    exact linearMap_apply_bound v A x
  · -- nonarchimedean part: reduce to "local" statement `linearMap_apply_bound_of_isNonarchimedean`
    rw [← finprod_mul_distrib (mulSupport_iSup_nonarchAbsVal_finite hA)
      (mulSupport_iSup_nonarchAbsVal_finite hx)]
    refine finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h)
      (fun v ↦ v.val.iSup_abv_nonneg) ?_ fun v ↦ ?_
    · exact Function.finite_mulSupport_mul (mulSupport_iSup_nonarchAbsVal_finite hA)
        (mulSupport_iSup_nonarchAbsVal_finite hx)
    · exact linearMap_apply_bound_of_isNonarchimedean (isNonarchimedean _ v.prop) A x

open Real in
/-- Let `A : ι' × ι → K`, which we can interpret as an `ι' × ι` matrix over `K`.
Let `x : ι → K` be a tuple. Then the logarithmic height of `A x` is bounded by
`totalWeight K * log #ι + logHeight A + logHeight x`.

(Note that here we do not need to assume that `ι` is nonempty, due to the convenient
junk value `log 0 = 0`.) -/
theorem logHeight_linearMap_apply_le (A : ι' × ι → K) (x : ι → K) :
    logHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      totalWeight K * log (Nat.card ι) + logHeight A + logHeight x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · suffices 0 ≤ logHeight A + logHeight x by simpa [← Pi.zero_def] using this
    positivity
  simp only [logHeight_eq_log_mulHeight]
  have : (Nat.card ι : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_linearMap_apply_le ..

end Height

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
theorem mulHeight_eval_ge [Nonempty ι'] {M N : ℕ} (p : ι' → MvPolynomial ι K)
    {q : ι × ι' → MvPolynomial ι K} (hq : ∀ a, (q a).IsHomogeneous M) {x : ι → K}
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

open Real in
/-- If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,
then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by an (explicit) positive
constant depending only on `q` plus `N` times the logarithmic height of `x`. -/
theorem logHeight_eval_ge [Nonempty ι'] {M N : ℕ} (p : ι' → MvPolynomial ι K)
    {q : ι × ι' → MvPolynomial ι K} (hq : ∀ a, (q a).IsHomogeneous M) {x : ι → K}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    logHeight (fun j ↦ (p j).eval x) ≥
      -log (Nat.card ι' ^ totalWeight K * max (mulHeightBound q) 1) + N * logHeight x:= by
  simp only [logHeight_eq_log_mulHeight]
  have : (Nat.card ι' : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_eval_ge p hq h

end Height
