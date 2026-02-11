import Heights.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic.DepRewrite

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

end aux

namespace Height

open MvPolynomial

variable {K : Type*} [Field K] {ι : Type*}

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

private lemma mvPolynomial_bound_nonarch [Finite ι] {v : AbsoluteValue K ℝ}
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

/-- The constant in the height bound on values of `p`. -/
noncomputable
def mulHeightBound (p : ι' → MvPolynomial ι K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
    ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1

lemma mulHeightBound_eq (p : ι' → MvPolynomial ι K) :
    mulHeightBound p =
     (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
        ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1 :=
  rfl

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
-- #count_heartbeats in -- 6888
private lemma mulHeight_constantCoeff_le_mulHeightBound {p : ι' → MvPolynomial ι K}
    (h : (fun j ↦ constantCoeff (p j)) ≠ 0) :
    (mulHeight fun j ↦ constantCoeff (p j)) ≤ mulHeightBound p := by
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
-- #count_heartbeats in -- 17798
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
    · grw [mvPolynomial_bound_nonarch (isNonarchimedean _ v.prop) (hp j) x]
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

open Polynomial

/-- The constant in the upper height bound for `p.eval x`. -/
noncomputable
def _root_.Polynomial.mulHeight₁Bound (p : K[X]) : ℝ :=
  max (mulHeightBound p.to_tuple_mvPolynomial) 1

private lemma iSup_fun_eq_max (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
  rw [show f = ![f 0, f 1] from List.ofFn_inj.mp rfl]
  exact (max_eq_iSup ..).symm

lemma mulHeightBound_zero_one : mulHeightBound ![(0 : MvPolynomial (Fin 2) K), 1] = 1 := by
  simp only [mulHeightBound, Nat.succ_eq_add_one, Nat.reduceAdd]
  conv_rhs => rw [← one_mul 1]
  congr
  · convert Multiset.prod_map_one with v
    rw [iSup_fun_eq_max]
    suffices max 0 (Finsupp.sum (1 : MvPolynomial (Fin 2) K) fun x c ↦ v c) = 1 by
      simpa using this
    rw [max_eq_right <|  Finsupp.sum_nonneg' fun s ↦ by positivity, MvPolynomial.sum_def,
      support_one_eq]
    simp
  · refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
    rw [iSup_fun_eq_max]
    suffices ⨆ s : (1 : MvPolynomial (Fin 2) K).support, v.val (MvPolynomial.coeff s.val 1) ≤ 1 by
      simpa using this
    have : Nonempty (1 : MvPolynomial (Fin 2) K).support := by
      simp [MvPolynomial.support_one_eq]
    refine ciSup_le fun s ↦ ?_
    have : s = (0 : Fin 2 →₀ ℕ) := by grind [MvPolynomial.support_one_eq]
    simp [this]

open Finset in
lemma mulHeight₁Bound_eq (p : K[X]) :
    p.mulHeight₁Bound =
      (archAbsVal.map fun v ↦ max (p.sum fun _ c ↦ v c) 1).prod *
      ∏ᶠ v : nonarchAbsVal,
      max ((range (p.natDegree + 1)).sup' nonempty_range_add_one fun n ↦ v.val (p.coeff n)) 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa [mulHeight₁Bound, to_tuple_mvPolynomial] using mulHeightBound_zero_one.le
  have hsupp₀ : Nonempty (MvPolynomial.X (R := K) (σ := Fin 2) 1 ^ p.natDegree).support := by
    simp only [MvPolynomial.mem_support_iff, nonempty_subtype]
    refine ⟨fun₀ | 1 => p.natDegree, ?_⟩
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    simp
  have hsupp₁ : Nonempty ↥(p.homogenize p.natDegree).support := by
    refine Finset.Nonempty.to_subtype ?_
    rw [MvPolynomial.support_nonempty]
    contrapose! hp
    exact eq_zero_of_homogenize_eq_zero le_rfl hp
  simp [mulHeight₁Bound, mulHeightBound_eq]
  rw [max_eq_left ?h]
  case h => -- side goal
    refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun a ha ↦ ?_) ?_
    · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
      exact Finite.le_ciSup_of_le 1 <| by
        simp [to_tuple_mvPolynomial, MvPolynomial.X_pow_eq_monomial]
    · exact one_le_finprod fun v ↦ Finite.le_ciSup_of_le 1 <| le_max_right ..
  congr <;> ext v
  · rw [iSup_fun_eq_max]
    congr 1
    · simp [to_tuple_mvPolynomial, finsuppSum_homogenize_eq]
    · simp [to_tuple_mvPolynomial, MvPolynomial.X_pow_eq_monomial]
  · have (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
      convert (max_eq_iSup ..).symm
      ext i; fin_cases i <;> simp
    rw [← Finite.ciSup_sup, this]
    simp [to_tuple_mvPolynomial, coeff_homogenize, MvPolynomial.X_pow_eq_monomial,
      p.sum_eq_natDegree_of_mem_support_homogenize]
    have : (⨆ s : (MvPolynomial.X (R := K) (σ := Fin 2) 1 ^ p.natDegree).support,
        if (fun₀ | 1 => p.natDegree : Fin 2 →₀ ℕ) = s then 1 else 0) = (1 : ℝ) := by
      refine le_antisymm ?_ ?_
      · refine ciSup_le fun s ↦ ?_; grind
      · refine Finite.le_ciSup_of_le
          ⟨fun₀ | 1 => p.natDegree, by simp [MvPolynomial.coeff_X_pow]⟩ <| by simp
    rw [this, sup_right_idem]
    congr
    rw [sup'_eq_csSup_image, sSup_image']
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun s ↦ Finite.le_ciSup_of_le ⟨s.val 0, ?_⟩ le_rfl
      grind only [= mem_coe, = mem_range, p.sum_eq_natDegree_of_mem_support_homogenize s.prop]
    · have : Nonempty (↑↑(range (p.natDegree + 1)) : Type) := by
        simp only [mem_range, Order.lt_add_one_iff, nonempty_subtype]
        exact ⟨_, le_rfl⟩
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

end Height
