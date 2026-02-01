import Heights.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Height bounds for polynomial maps

We prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family of
homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K` with `ι` finite.
-/

namespace Height

open MvPolynomial

variable {K : Type*} [Field K]

variable {ι : Type*}

-- possibly useful more generally?
private lemma sum_deg_support_eq_degree {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N)
    {s : ι →₀ ℕ} (hs : s ∈ p.support) :
    N = ∑ i ∈ s.support, s i := by
  rw [IsHomogeneous, IsWeightedHomogeneous] at hp
  rw [← hp <| mem_support_iff.mp hs, ← Finsupp.degree_apply, Finsupp.degree_eq_weight_one,
    Pi.one_def]

variable [Finite ι]

private lemma mvPolynomial_bound (v : AbsoluteValue K ℝ) {p : MvPolynomial ι K} {N : ℕ}
    (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ p.sum (fun _ c ↦ v c) * (⨆ i, v (x i)) ^ N := by
  rw [eval_eq, sum_def, Finset.sum_mul]
  grw [AbsoluteValue.sum_le]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  gcongr
  rw [sum_deg_support_eq_degree hp hs, ← Finset.prod_pow_eq_pow_sum]
  gcongr with i
  exact le_ciSup (Finite.bddAbove_range fun i ↦ v (x i)) i

private lemma mvPolynomial_bound_nonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N) (x : ι → K) :
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
  · exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  · exact le_ciSup_of_le (Finite.bddAbove_range _) (⟨s, hs₁⟩ : p.support) le_rfl
  · rw [sum_deg_support_eq_degree hp hs₁, ← Finset.prod_pow_eq_pow_sum]
    gcongr with i
    exact le_ciSup (Finite.bddAbove_range fun i ↦ v (x i)) i

variable {ι' : Type*} [Finite ι']

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

/-- The constant in the height bound on values of `p`. -/
noncomputable
def mulHeightBound (p : ι' → MvPolynomial ι K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
    ∏ᶠ v : nonarchAbsVal, ⨆ j, ⨆ s : (p j).support, v.val (coeff s (p j))

omit [Finite ι] [Finite ι'] in
lemma mulHeightBound_eq (p : ι' → MvPolynomial ι K) :
    mulHeightBound p =
     (archAbsVal.map fun v ↦ ⨆ j, (p j).sum (fun _ c ↦ v c)).prod *
        ∏ᶠ v : nonarchAbsVal, ⨆ j, ⨆ s : (p j).support, v.val (coeff s (p j)) :=
  rfl

-- @Finsupp.sum : {α : Type u_2} → {M : Type u_1} → {N : Type} → [inst : Zero M] →
--    [AddCommMonoid N] → (α →₀ M) → (α → M → N) → N

lemma _root_.Finsupp.single_le_sum {α M N : Type*} [Zero M] [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] (f : α →₀ M) {g : M → N} (hg : g 0 = 0) (h : ∀ m, 0 ≤ g m) (a : α) :
    g (f a) ≤ f.sum fun _ m ↦ g m := by
  rcases eq_or_ne (f a) 0 with H | H
  · rw [H, hg]
    exact Finsupp.sum_nonneg' fun a ↦ h _
  · exact Finset.single_le_sum (fun a _ ↦ h (f a)) <| Finsupp.mem_support_iff.mpr H

theorem mulHeight_eval_le {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N)
    (x : ι → K) :
    mulHeight (fun j ↦ (p j).eval x) ≤ max (mulHeightBound p) 1 * mulHeight x ^ N := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [eval_zero, mulHeight_zero, one_pow, mul_one]
    rcases eq_or_ne (fun j ↦ constantCoeff (p j)) 0 with h | h
    · simp [h]
    · refine le_max_of_le_left ?_
      simp only [mulHeight_eq h, mulHeightBound_eq]
      gcongr
      · exact finprod_nonneg fun v ↦ Real.iSup_nonneg fun j ↦ by positivity
      · refine Multiset.prod_nonneg fun a ha ↦ ?_
        obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
        exact Real.iSup_nonneg fun j ↦ Finsupp.sum_nonneg' fun s ↦ by positivity
      · refine Multiset.prod_map_le_prod_map₀ _ _ (fun v hv ↦ ?_) fun v hv ↦ ?_
        · exact Real.iSup_nonneg fun j ↦ by positivity
        · refine ciSup_mono (Finite.bddAbove_range _) fun j ↦ ?_
          exact Finsupp.single_le_sum _ v.map_zero (fun _ ↦ by positivity) _
      · refine finprod_le_finprod ?_ (fun v ↦ ?_) ?_ ?_
        · -- change Function.HasFiniteMulSupport _
          -- fun_prop (disch := assumption)
          have : Nonempty ι' := (Function.ne_iff.mp h).nonempty
          refine Function.finite_mulSupport_iSup fun i ↦ ?_
          refine mulSupport_finite ?_
          sorry
        · exact Real.iSup_nonneg fun j ↦ by positivity
        · -- change Function.HasFiniteMulSupport _
          -- fun_prop (disch := assumption)
          sorry
        · refine fun v ↦ ciSup_mono (Finite.bddAbove_range _) fun j ↦ ?_
          rw [show constantCoeff (p j) = coeff 0 (p j) from rfl]
          -- refine le_ciSup (α := ℝ) ?_ 0
          sorry
  simp only [mulHeight_eq hx, mulHeightBound_eq]
  sorry

end Height
