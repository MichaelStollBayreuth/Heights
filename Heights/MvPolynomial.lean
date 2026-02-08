import Heights.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Height bounds for polynomial maps

We prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family of
homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K` with `ι` finite.
-/

-- Auxiliary stuff

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

end MvPolynomial

namespace Height

open MvPolynomial

variable {K : Type*} [Field K] {ι : Type*}

private lemma iSup_abv_nonneg (v : AbsoluteValue K ℝ) {x : ι → K} : 0 ≤ ⨆ i, v (x i) :=
  Real.iSup_nonneg fun j ↦ by positivity

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
  exact le_ciSup (Finite.bddAbove_range fun i ↦ v (x i)) i

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
  · exact iSup_abv_nonneg v
  · exact le_ciSup_of_le (Finite.bddAbove_range _) (⟨s, hs₁⟩ : p.support) le_rfl
  · rw [hp.degree_eq_sum_deg_support hs₁, ← Finset.prod_pow_eq_pow_sum]
    gcongr with i
    exact le_ciSup (Finite.bddAbove_range fun i ↦ v (x i)) i

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

private lemma finite_mulSupport_iSup_max_iSup_one (h : Nonempty ι') (p : ι' → MvPolynomial ι K) :
    (fun v : nonarchAbsVal ↦
      ⨆ j, max (⨆ s : (p j).support, v.val (coeff s.val (p j))) 1).mulSupport.Finite := by
  -- fun_prop (disch := assumption)
  refine Function.finite_mulSupport_iSup fun j ↦ ?_
  rcases isEmpty_or_nonempty (p j).support with hs₀ | hs₀
  · simp
  refine Function.finite_mulSupport_max ?_ Function.finite_mulSupport_one
  exact Function.finite_mulSupport_iSup fun ⟨s, hs⟩ ↦ mulSupport_finite <| mem_support_iff.mp hs

open Real Multiset Finsupp in
-- set_option Elab.async false in
-- #count_heartbeats in -- 6888
private lemma mulHeight_constantCoeff_le_mulHeightBound {p : ι' → MvPolynomial ι K}
    (h : (fun j ↦ constantCoeff (p j)) ≠ 0) :
    (mulHeight fun j ↦ constantCoeff (p j)) ≤ mulHeightBound p := by
  simp only [mulHeight_eq h, mulHeightBound_eq]
  gcongr
  · exact finprod_nonneg fun v ↦ iSup_abv_nonneg v.val
  · exact prod_map_nonneg fun v _ ↦ iSup_nonneg fun j ↦ sum_nonneg fun s _ ↦ by positivity
  · have (v : AbsoluteValue K ℝ) (j : ι') : v (constantCoeff (p j)) ≤ sum (p j) fun _ c ↦ v c :=
      single_le_sum _ v.map_zero (fun x ↦ by positivity) _
    exact prod_map_le_prod_map₀ _ _ (fun v _ ↦ iSup_abv_nonneg v)
      fun v _ ↦ ciSup_mono (Finite.bddAbove_range _) (this v)
  · refine finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h)
      (fun v ↦ iSup_abv_nonneg v.val) ?_ ?_
    · exact finite_mulSupport_iSup_max_iSup_one (Function.ne_iff.mp h).nonempty p
    · refine fun v ↦ ciSup_mono (Finite.bddAbove_range _) fun j ↦ ?_
      rw [show constantCoeff (p j) = coeff 0 (p j) from rfl]
      rcases eq_or_ne (coeff 0 (p j)) 0 with h₀ | h₀
      · simp [h₀]
      · exact le_sup_of_le_left <| le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, by simp [h₀]⟩ le_rfl

variable [Finite ι]

open Real Finsupp Multiset in
-- set_option Elab.async false in
-- #count_heartbeats in -- 18235
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
    prod_map_nonneg fun v _ ↦ iSup_abv_nonneg v
  have H₃ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val ((eval x) (p i)) :=
    finprod_nonneg fun v ↦ iSup_abv_nonneg v.val
  have H₄ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) :=
    finprod_nonneg fun v ↦ iSup_abv_nonneg v.val
  have HH₁ (v : AbsoluteValue K ℝ) : 0 ≤ (⨆ i, v (x i)) ^ N := pow_nonneg (iSup_abv_nonneg v) N
  have HH₂ (f : ι' → ℝ) (j : ι') : f j ≤ ⨆ j, f j := le_ciSup (Finite.bddAbove_range _) _
  simp only [mulHeight_eq hx, mulHeight_eq h₀, mulHeightBound_eq]
  grw [← le_max_left]
  rw [mul_pow, mul_mul_mul_comm]
  gcongr
  · -- archimedean part: reduce to "local" statement `mvPolynomial_bound`
    rw [← prod_map_pow, ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ iSup_abv_nonneg v)
      fun v _ ↦ Real.iSup_le (fun j ↦ ?_) <| mul_nonneg (H₀ v) (HH₁ v)
    grw [mvPolynomial_bound v (hp j) x]
    gcongr
    · exact HH₁ v
    · exact HH₂ (fun j ↦ Finsupp.sum (p j) fun _ c ↦ v c) j
  · -- nonarchimedean part: reduce to "local" statement `mvPolynomial_bound_nonarch`
    rw [finprod_pow F₂, ← finprod_mul_distrib F₁ F₃]
    refine finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h₀)
      (fun v ↦ iSup_abv_nonneg v.val) (Function.finite_mulSupport_mul F₁ F₃)
      fun v ↦ Real.iSup_le (fun j ↦ ?_) ?_
    · grw [mvPolynomial_bound_nonarch (isNonarchimedean _ v.prop) (hp j) x]
      gcongr
      · exact HH₁ v.val
      · grw [le_max_left (iSup ..) 1]
        exact HH₂ (fun j ↦ max (⨆ s : (p j).support, v.val (coeff s.val (p j))) 1) j
    · exact mul_nonneg (iSup_nonneg fun j ↦ by positivity) <| by simp only [HH₁]

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
