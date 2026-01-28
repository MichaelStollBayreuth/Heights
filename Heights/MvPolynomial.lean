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

variable {ι' : Type*} [Finite ι] [Finite ι']

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

end Height
