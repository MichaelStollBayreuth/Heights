import Mathlib

/-!
# Monic polynomials of given degree

This file defines the predicate `Polynomial.IsMonicOfDegree p n` that states that
the polynomial `p` is monic and has degree `n` (i.e., `p.natDegree = n`.)

We also provide some basic API. (See #26507)
-/

namespace Polynomial

/-!
### Lemmas for more specific base fields
-/

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`.
This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
lemma IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 2)) :
    ∃ f₁ f₂ : ℝ[X], IsMonicOfDegree f₁ 2 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos f <| by have := hf.natDegree_eq; omega
  obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor f hu
  have hdeg := hgi.natDegree_le_two
  set m := g.natDegree with hm
  have hg : IsMonicOfDegree g m := ⟨hm.symm, hgm⟩
  interval_cases m
  · -- m = 0
    exact (hm ▸ Irreducible.natDegree_pos hgi).false.elim
  · -- m = 1
    obtain ⟨f₁, hf₁⟩ := hgd
    rw [hf₁, show n + 2 = 1 + (1 + n) by omega] at hf
    have hf₁' : IsMonicOfDegree f₁ (1 + n) := hg.of_mul_left hf
    have hu₁ : ¬ IsUnit f₁ := not_isUnit_of_natDegree_pos f₁ <| by have := hf₁'.natDegree_eq; omega
    obtain ⟨g₁, hgm₁, hgi₁, hgd₁⟩ := exists_monic_irreducible_factor f₁ hu₁
    obtain ⟨f₂, hf₂⟩ := hgd₁
    have hdeg₁ := hgi₁.natDegree_le_two
    set m₁ := g₁.natDegree with hm₁
    have hg₁ : IsMonicOfDegree g₁ m₁ := ⟨hm₁.symm, hgm₁⟩
    interval_cases m₁
    · -- m₁ = 0
      exact (hm₁ ▸ hgi₁.natDegree_pos).false.elim
    · -- m₁ = 1
      rw [hf₂, ← mul_assoc] at hf₁ hf
      rw [show 1 + (1 + n) = 2 + n by omega] at hf
      exact ⟨g * g₁, f₂, hg.mul hg₁, (hg.mul hg₁).of_mul_left hf, hf₁⟩
    · -- m₁ = 2
      rw [hf₂, mul_left_comm] at hf₁ hf
      rw [show 1 + (1 + n) = 2 + n by omega] at hf
      exact ⟨g₁, g * f₂, hg₁, hg₁.of_mul_left hf, hf₁⟩
  · -- m = 2
    obtain ⟨f₂, hf₂⟩ := hgd
    rw [hf₂, add_comm] at hf
    exact ⟨g, f₂, hg, hg.of_mul_left hf, hf₂⟩

/-- If `f : F[X]` is monic of degree `≥ 1` and `F` is an algebraically closed field,
then `f = f₁ * f₂` with `f₁` monic of degree `1` and `f₂` monic of degree `f.natDegree - 1`. -/
lemma IsMonicOfDegree.eq_mul_isMonicOfDegree_one_isMonicOfDegree {F : Type*} [Field F]
    [IsAlgClosed F] {f : F[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 1)) :
    ∃ f₁ f₂ : F[X], IsMonicOfDegree f₁ 1 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos f <| by have := hf.natDegree_eq; omega
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ := exists_monic_irreducible_factor f hu
  have hf₁ : IsMonicOfDegree f₁ 1 := by
    refine ⟨?_, hf₁m⟩
    exact natDegree_eq_of_degree_eq_some <| IsAlgClosed.degree_eq_one_of_irreducible F hf₁i
  rw [hf₂, add_comm] at hf
  exact ⟨f₁, f₂, hf₁, hf₁.of_mul_left hf, hf₂⟩

end Polynomial
