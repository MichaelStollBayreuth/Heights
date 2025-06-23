import Mathlib

/-!
# Monic polynomials of given degree

This file defines the predicate `Polynomial.IsMonicOfDegree p n` that states that
the polynomial `p` is monic and has degree `n` (i.e., `p.natDegree = n`.)

We also provide some basic API.
-/

namespace Polynomial

/-- This says that `p` has `natDegree` `n` and is monic. -/
abbrev IsMonicOfDegree {R : Type*} [Semiring R] (p : R[X]) (n : ℕ) : Prop :=
  p.natDegree = n ∧ p.Monic

lemma IsMonicOfDegree.monic {R : Type*} [Semiring R] {p : R[X]} {n : ℕ}
    (h : IsMonicOfDegree p n) :
    p.Monic :=
  h.2

lemma IsMonicOfDegree.natDegree_eq {R : Type*} [Semiring R] {p : R[X]} {n : ℕ}
    (h : IsMonicOfDegree p n) :
    p.natDegree = n :=
  h.1

lemma IsMonicOfDegree.ne_zero {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (h : IsMonicOfDegree p n) :
    p ≠ 0 :=
  h.2.ne_zero

@[simp]
lemma isMonicOfDegree_zero {R : Type*} [Semiring R] {p : R[X]} :
    IsMonicOfDegree p 0 ↔ p = 1 := by
  unfold IsMonicOfDegree
  refine ⟨fun ⟨H₁, H₂⟩ ↦ eq_one_of_monic_natDegree_zero H₂ H₁, fun H ↦ ?_⟩
  subst H
  simp

lemma IsMonicOfDegree.leadingCoeff_eq {R : Type*} [Semiring R] {p : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) :
    p.leadingCoeff = 1 := by
  rw [← Monic.def]
  exact monic hp

@[simp]
lemma isMonicOfDegree_iff_of_subsingleton {R : Type*} [Semiring R] [Subsingleton R]
    (p : R[X]) (n : ℕ) :
    IsMonicOfDegree p n ↔ n = 0 := by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ ↦ ?_, fun H ↦ ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, isMonicOfDegree_zero]

lemma IsMonicOfDegree.mul {R : Type*} [Semiring R] {p q : R[X]} {m n : ℕ}
    (hp : IsMonicOfDegree p m) (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p * q) (m + n) := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.2.mul hq.2⟩
  have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' this, hp.1, hq.1]

lemma IsMonicOfDegree.pow {R : Type*} [Semiring R] {p : R[X]} {m : ℕ} (hp : IsMonicOfDegree p m)
    (n : ℕ) :
    IsMonicOfDegree (p ^ n) (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one]
    exact ih.mul hp

lemma isMonicOfDegree_iff {R : Type*} [Semiring R] [Nontrivial R] (p : R[X]) (n : ℕ) :
    IsMonicOfDegree p n ↔ p.natDegree ≤ n ∧ p.coeff n = 1 := by
  simp only [IsMonicOfDegree]
  refine ⟨fun ⟨H₁, H₂⟩ ↦ ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ ↦ ⟨?_, ?_⟩⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero H₁ <| H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂

lemma isMonicOfDegree_X (R : Type*) [Semiring R] [Nontrivial R] : IsMonicOfDegree (X : R[X]) 1 :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

lemma isMonicOfDegree_X_pow (R : Type*) [Semiring R] [Nontrivial R] (n : ℕ) :
    IsMonicOfDegree ((X : R[X]) ^ n) n :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

lemma IsMonicOfDegree.coeff_eq {R : Type*} [Semiring R] {p q : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : IsMonicOfDegree q n) {m : ℕ} (hm : n ≤ m) :
    p.coeff m = q.coeff m := by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp, coeff_eq_zero_of_natDegree_lt hq]

lemma IsMonicOfDegree.of_mul_left {R : Type*} [Semiring R] {p q : R[X]} {m n : ℕ}
    (hp : IsMonicOfDegree p m) (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree q n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.2.of_mul_monic_left hpq.2
  refine ⟨?_, h₂⟩
  have := hpq.1
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, h₂.leadingCoeff, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hp.1] at this
  exact (Nat.add_left_cancel this.symm).symm

lemma IsMonicOfDegree.of_mul_right {R : Type*} [Semiring R]  {p q : R[X]} {m n : ℕ}
    (hq : IsMonicOfDegree q n) (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree p m := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.2.of_mul_monic_right hpq.2
  refine ⟨?_, h₂⟩
  have := hpq.1
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [h₂.leadingCoeff, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hq.1] at this
  exact (Nat.add_right_cancel this.symm).symm

lemma IsMonicOfDegree.add_left {R : Type*} [Semiring R] {p q : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p + q) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2

lemma IsMonicOfDegree.sub {R : Type*} [Ring R] {p q : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add_left <| (natDegree_neg q) ▸ hq

lemma IsMonicOfDegree.add_right {R : Type*} [Semiring R] {p q : R[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p + q) n := by
  rw [add_comm]
  exact hq.add_left hp

lemma IsMonicOfDegree.aeval_add {R : Type*} [CommRing R] {p : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X + C r) p) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  have : (X + C r).natDegree = 1 := by compute_degree!
  constructor
  · have h : p.leadingCoeff * (X + C r).leadingCoeff ^ p.natDegree ≠ 0 := by
      have : (X + C r).leadingCoeff = 1 := by monicity
      rw [hp.leadingCoeff_eq, this, one_mul, one_pow]
      exact one_ne_zero
    rw [← Polynomial.comp_eq_aeval, Polynomial.natDegree_comp_eq_of_mul_ne_zero h, this,
      hp.natDegree_eq, mul_one]
  · refine Polynomial.Monic.comp hp.monic (by monicity) <| by rw [this]; exact one_ne_zero

lemma IsMonicOfDegree.aeval_sub {R : Type*} [CommRing R] {p : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X - C r) p) n := by
  rw [sub_eq_add_neg, ← map_neg]
  exact aeval_add hp (-r)

lemma isMonicOfDegree_X_add_one {R : Type*} [Semiring R] [Nontrivial R] (r : R) :
    IsMonicOfDegree (X + C r) 1 :=
  (isMonicOfDegree_X R).add_left (by compute_degree!)

lemma isMonicOfDegree_X_sub_one {R : Type*} [Ring R] [Nontrivial R] (r : R) :
    IsMonicOfDegree (X - C r) 1 :=
  (isMonicOfDegree_X R).sub (by compute_degree!)

lemma isMonicOfDegree_one_iff {R : Type*} [Semiring R] [Nontrivial R] {f : R[X]} :
    IsMonicOfDegree f 1 ↔ ∃ r : R, f = X + C r := by
  refine ⟨fun H ↦ ?_, fun ⟨r, H⟩ ↦ H ▸ isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (isMonicOfDegree_X_add_one _) (by omega)

lemma isMonicOfDegree_sub_sq_add_two {R : Type*} [CommRing R] [Nontrivial R] (s t : R) :
    IsMonicOfDegree ((X - C s) ^ 2 + C t) 2 := by
  have : IsMonicOfDegree (X - C s) 1 := isMonicOfDegree_X_sub_one s
  exact (this.pow 2).add_left <| by compute_degree!

lemma isMonicOfDegree_two_iff {R : Type*} [CommRing R] [Nontrivial R] [Algebra ℚ R] {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ s t : R, f = (X - C s) ^ 2 + C t := by
  refine ⟨fun H ↦ ?_, fun ⟨s, t, h⟩ ↦ h ▸ isMonicOfDegree_sub_sq_add_two s t⟩
  refine ⟨-(1 / 2 : ℚ) • f.coeff 1, f.coeff 0 - ((1 / 2 : ℚ) • f.coeff 1) ^ 2, ?_⟩
  ext1 n
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := by omega
    simp [sub_sq, ← map_pow, add_sq]
  · simp [-one_div, sub_sq, ← map_pow, add_sq, two_mul, add_mul, ← add_smul]
  exact H.coeff_eq (isMonicOfDegree_sub_sq_add_two ..) (by omega)

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`.
This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
lemma IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 2)) :
    ∃ f₁ f₂ : ℝ[X], IsMonicOfDegree f₁ 2 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos f <| by omega
  obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor f hu
  have hdeg := Irreducible.natDegree_le_two hgi
  set m := g.natDegree with hm
  have hg : IsMonicOfDegree g m := ⟨hm.symm, hgm⟩
  interval_cases m
  · -- m = 0
    exact (hm ▸ Irreducible.natDegree_pos hgi).false.elim
  · -- m = 1
    obtain ⟨f₁, hf₁⟩ := hgd
    rw [hf₁, show n + 2 = 1 + (1 + n) by omega] at hf
    have hf₁' : IsMonicOfDegree f₁ (1 + n) := hg.of_mul_left hf
    have hu₁ : ¬ IsUnit f₁ := not_isUnit_of_natDegree_pos f₁ <| by omega
    obtain ⟨g₁, hgm₁, hgi₁, hgd₁⟩ := exists_monic_irreducible_factor f₁ hu₁
    obtain ⟨f₂, hf₂⟩ := hgd₁
    have hdeg₁ := Irreducible.natDegree_le_two hgi₁
    set m₁ := g₁.natDegree with hm₁
    have hg₁ : IsMonicOfDegree g₁ m₁ := ⟨hm₁.symm, hgm₁⟩
    interval_cases m₁
    · -- m₁ = 0
      exact (hm₁ ▸ Irreducible.natDegree_pos hgi₁).false.elim
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
  have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos f <| by omega
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ := exists_monic_irreducible_factor f hu
  have hf₁ : IsMonicOfDegree f₁ 1 := by
    refine ⟨?_, hf₁m⟩
    exact natDegree_eq_of_degree_eq_some <| IsAlgClosed.degree_eq_one_of_irreducible F hf₁i
  rw [hf₂, add_comm] at hf
  exact ⟨f₁, f₂, hf₁, hf₁.of_mul_left hf, hf₂⟩

end Polynomial
