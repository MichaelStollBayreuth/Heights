import Mathlib

/-!
# A (new?) proof of the Gelfand-Mazur Theorem

The goal of this file is to prove the following version of the Gelfand-Mazur Theorem:

Let `F` be a field that is complete with respect to an archimedean absolute value `v`.
Then `F` is isomorphic, as a field with absolute value, to either `ℝ` or `ℂ` with
an absolute value that is equivalent to the standard absolute value.

One can fairly easily conclude from the assumptions that `F` is an `ℝ`-algebra
and that the restriction of `v` to `ℝ` is equivalent to the standard absolute value.
There is then an absolute value `v'` on `F` that is equivalent to `v` and restricts
to the standard absolute value on `ℝ`; in this way, `F` is a normed `ℝ`-algebra.
So we will use this assumption in the following.

The main idea is to show that each element of `F` satisfies a polynomial equation
over `ℝ`; this implies that `F` is an algebraic field extension of `ℝ`, and so
either `F` is already isomorphic to `ℝ` via the algebra map, or else `F` is isomorphic
to `ℂ` as a normed `ℝ`-algebra.

Since irreducible polynomials over `ℝ` have degree at most `2`, it is actually the case
that each element is annihilated by a monic polynomial of degree `2`. We can state this as
`∃ p : ℝ[X], p.natDegree = 2 ∧ p.Monic ∧ p.aeval x = 0`.

Because the space `ℝ²` of monic polynomials of degree `2` is complete and locally compact
and `‖p.aeval x‖` gets large when `p` has large coefficients, there will be some `p₀`
such that `‖p₀.aeval x‖` attains a minimum. We assume that this is positive and derive
a contradiction. Let `M := ‖p₀.aeval x‖ > 0` be the minimal value.
Since every monic polynomial `f : ℝ[X]` of even degree can be written as a product
of monic polynomials of degree `2`, it follows that `‖f.aeval x‖ ≥ M^(f.natDegree / 2)`.

Write `p₀ = X^2 - 2*s*X + t` with `s t : ℝ`. We define two sequences of polynomials,
the second of which depends on a parameter `c : ℝ`:
* `y 0 := 2`, `y 1 := 2*(X-s)`, `y (n+2) := 2*(X-s)*(y (n+1)) - p₀*(y n)`
* `z c 0 := 0`, `z c 1 := 1`, `z c (n+2) := p₀^(n+1) + 2*c*(X-s)*(z c (n+1)) - c^2*p₀*(z c n) + c^(2*n+2)`

They have the following properties.
* `∀ c, ∀ n ≠ 0, (z c n).Monic ∧ (z c n).natDegree = 2*(n-1)`
* `∀ c n, p₀^n - c^n*(y n) + c^(2*n) = p₀.aeval (X-c) * (z c n)`
* `∃ C ≥ 0, ∀ n, ‖(y n).aeval x‖ ≤ 2*C^n`

This implies that
`‖(p₀.aeval (X-c)).aeval x‖ = ‖(p₀^n - c^n*(y n) + c^(2*n)).aeval x‖ / ‖(z c n).aeval x‖`,
which is bounded by
`(M^n + |c|^n * ‖(y n).aeval x‖ + |c|^(2*n)) / M^(n-1) = M * (1 + (|c|/M)^n * ‖(y n).aeval x‖ + (|c|^2/M)^n)`.
If we take `c : ℝ` such that `|c| < min √M (M/C)`, then as `n` tends to infinity, we obtain that
`M ≤ ‖(p₀.aeval (X-c)).aeval x‖ ≤ M`.

Restricting to the one-dimensional subset of polynomials of the form `p₀.aeval (X-c)`,
we see that the subset `S := {c : ℝ | ‖p₀.aeval (X-c)‖ = M}` of `ℝ` is closed
(because `c ↦ ‖p₀.aeval (X-c)‖` is continuous), but also open (because for a minimizing `c`,
it contains an open interval around `c` by the same argument, applied to the shifted polynomial).
Since `0 ∈ S`, it follows that `S = ℝ`, but this contradicts the fact that for large `c`,
the value of `‖p₀.aeval (X-c)‖` tends to infinity.
-/


section auxiliary

namespace Real

lemma isBounded_of_abs_le (C : ℝ) : Bornology.IsBounded {x : ℝ | |x| ≤ C} := by
  convert Metric.isBounded_Icc (-C) C
  ext1
  simp [abs_le]

end Real

namespace Continuous

lemma exists_forall_le_of_isBounded {α β : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α] [PseudoMetricSpace β] [ProperSpace β]
    {f : β → α} (hf : Continuous f) (x₀ : β) (h : Bornology.IsBounded {x : β | f x ≤ f x₀}) :
    ∃ x, ∀ (y : β), f x ≤ f y := by
  refine hf.exists_forall_le' (x₀ := x₀) ?_
  have hU : {x : β | f x₀ < f x} ∈ Filter.cocompact β := by
    refine Filter.mem_cocompact'.mpr ⟨_, ?_, fun ⦃_⦄ a ↦ a⟩
    simp only [Set.compl_setOf, not_lt]
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) (by fun_prop)) h
  filter_upwards [hU] with x hx
  exact hx.le

end Continuous

namespace Algebra

variable {A : Type*} [SeminormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

@[simp]
lemma norm_smul_one_eq_abs (x : ℝ) : ‖x • (1 : A)‖ = |x| := by
  rw [← Algebra.algebraMap_eq_smul_one, norm_algebraMap', Real.norm_eq_abs]

end Algebra

namespace Polynomial

lemma coeff_pow_mul_natDegree' {R : Type*} [Semiring R] {p : R[X]} {m : ℕ}
    (h : p.natDegree = m) (n : ℕ) :
    (p ^ n).coeff (n * m) = p.coeff m ^ n := by
  rw [← h, coeff_pow_mul_natDegree, coeff_natDegree]

abbrev IsMonicOfDegree {R : Type*} [Semiring R] (p : R[X]) (n : ℕ) : Prop :=
  p.natDegree = n ∧ p.Monic

lemma IsMonicOfDegree.ne_zero {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (h : IsMonicOfDegree p n) :
    p ≠ 0 :=
  h.2.ne_zero

@[simp]
lemma isMonicOfDegree_zero {R : Type*} [Semiring R] (p : R[X]) :
    IsMonicOfDegree p 0 ↔ p = 1 := by
  unfold IsMonicOfDegree
  refine ⟨fun ⟨H₁, H₂⟩ ↦ eq_one_of_monic_natDegree_zero H₂ H₁, fun H ↦ ?_⟩
  subst H
  simp

lemma IsMonicOfDegree.mul {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m) (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p * q) (m + n) := by
  refine ⟨?_, hp.2.mul hq.2⟩
  rw [natDegree_mul hp.ne_zero hq.ne_zero, hp.1, hq.1]

lemma IsMonicOfDegree.pow {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    {p : R[X]} {m : ℕ} (hp : IsMonicOfDegree p m) (n : ℕ) :
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

lemma IsMonicOfDegree.monic {R : Type*} [Semiring R] {p : R[X]} {n : ℕ}
    (h : IsMonicOfDegree p n) :
    p.Monic :=
  h.2

lemma IsMonicOfDegree.natDegree_eq {R : Type*} [Semiring R] {p : R[X]} {n : ℕ}
    (h : IsMonicOfDegree p n) :
    p.natDegree = n :=
  h.1

lemma coeff_eq_of_isMonicOfDegree {R : Type*} [Semiring R] {p q : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : IsMonicOfDegree q n) {m : ℕ} (hm : n ≤ m) :
    p.coeff m = q.coeff m := by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp, coeff_eq_zero_of_natDegree_lt hq]

lemma isMonicOfDegree_of_mul_left {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m) (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree q n := by
  have h₂ : q.Monic := hp.2.of_mul_monic_left hpq.2
  refine ⟨?_, h₂⟩
  have := hpq.1
  rw [natDegree_mul hp.ne_zero h₂.ne_zero, hp.1] at this
  exact (Nat.add_left_cancel this.symm).symm

lemma isMonicOfDegree_of_mul_right {R : Type*} [Semiring R] [Nontrivial R] [NoZeroDivisors R]
    {p q : R[X]} {m n : ℕ} (hq : IsMonicOfDegree q n) (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree p m := by
  have h₂ : p.Monic := hq.2.of_mul_monic_right hpq.2
  refine ⟨?_, h₂⟩
  have := hpq.1
  rw [natDegree_mul h₂.ne_zero hq.ne_zero, hq.1] at this
  exact (Nat.add_right_cancel this.symm).symm

lemma IsMonicOfDegree.add_left {R : Type*} [Semiring R] [Nontrivial R] {p q : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p + q) n := by
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2

lemma IsMonicOfDegree.sub {R : Type*} [Ring R] [Nontrivial R] {p q : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add_left <| (natDegree_neg q) ▸ hq

lemma IsMonicOfDegree.add_right {R : Type*} [Semiring R] [Nontrivial R] {p q : R[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p + q) n := by
  rw [add_comm]
  exact hq.add_left hp

@[simp]
lemma aeval_ofNat {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (n : ℕ)
    [n.AtLeastTwo] :
    (Polynomial.aeval (R := R) x) (ofNat(n) : R[X]) = n :=
  aeval_natCast x _

end Polynomial

end auxiliary


namespace GelfandMazur

section sequences

variable {R : Type*} [CommRing R]

open Polynomial

/-- The sequence `y s t n` for the polynomial `X ^ 2 - 2 * s * X + t`. -/
noncomputable
def y (s t : R) : ℕ → R[X]
| 0 => 2
| 1 => 2 • (X - C s)
| n + 2 => 2 • (X - C s) * y s t (n + 1) - (X ^ 2 - s • 2 * X + C t) * y s t n

/-- The sequence `z s t c n` for the polynomial `X ^ 2 - 2 * s * X + t` and a constant `c`. -/
noncomputable
def z (s t c : R) : ℕ → R[X]
| 0 => 0
| 1 => 1
| n + 2 => (X ^ 2 - s • 2 * X + C t) ^ (n + 1) + 2 * c • (X - C s) * z s t c (n + 1)
             - c ^ 2 • (X ^ 2 - 2 * s • X + C t) * z s t c n + C (c ^ (2 * n + 2))

/-- The terms of `z s t c n` are monic of degree `2 * (n - 1)` for `n ≠ 0`. -/
lemma z_isMonicOfDegree [Nontrivial R] [NoZeroDivisors R] (s t c : R) (n : ℕ) :
    IsMonicOfDegree (z s t c (n + 1)) (2 * n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [z, IsMonicOfDegree]
  | one =>
    simp only [z, Algebra.smul_mul_assoc, zero_add, pow_one, Algebra.mul_smul_comm, mul_one,
      smul_add, smul_C, smul_eq_mul, map_mul, map_pow, mul_zero, sub_zero]
    rw [sub_eq_add_neg, add_assoc, add_assoc, add_assoc]
    exact (isMonicOfDegree_X_pow R 2).add_left <| by compute_degree!
  | more n ih₂ ih₁ =>
    rw [z, sub_eq_add_neg, add_assoc, add_assoc]
    have : IsMonicOfDegree (X ^ 2 - s • 2 * X + C t) 2 := by
      rw [sub_eq_add_neg, add_assoc]
      exact (isMonicOfDegree_X_pow R 2).add_left <| by compute_degree!
    refine (this.pow (n + 1 + 1)).add_left ?_ --<| Nat.lt_add_one_of_le ?_
    compute_degree!
    rw [ih₁.natDegree_eq, ih₂.natDegree_eq]
    omega

/-- The relation that `y s t n` and `z s t c n` satisfy. -/
lemma y_z_rel (s t c : R) (n : ℕ) :
    (X ^ 2 - 2 * s • X + C t) ^ n - c ^ n • y s t n + C (c ^ (2 * n)) =
      ((X - C c) ^ 2 - 2 * s • (X - C c) + C t) * z s t c n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Algebra.mul_smul_comm, pow_zero, one_smul, mul_zero, map_one, y, z]
    norm_num
  | one =>
    simp only [Algebra.mul_smul_comm, pow_one, y, smul_sub, nsmul_eq_mul, Nat.cast_ofNat, smul_C,
      map_mul, mul_one, map_pow, smul_eq_mul, z,
      -- need to add these to make `ring` work:
      smul_eq_C_mul, sub_sq, show (2 : R[X]) = C (2 : R) from rfl]
    ring
  | more n ih₂ ih₁ =>
    rw [y, z]
    simp only [smul_eq_C_mul, show (2 : R[X]) = C (2 : R) from rfl] at *
    -- the following should work, but fails because `ring` does not deal well with polyomials
    -- linear_combination (C c) * (C 2 * (X - C s)) * ih₁ - (C c) ^ 2 * (X ^ 2 - C s * C 2 * X + C t) * ih₂
    rw [sub_add_eq_add_sub, sub_eq_iff_eq_add', eq_comm, ← eq_sub_iff_add_eq] at ih₂ ih₁
    conv =>
      enter [1, 1, 2]
      rw [add_comm n 2, show 2 + n = 1 + (1 + n) by omega, pow_add, map_mul, pow_one, mul_assoc]
      enter [2]
      rw [mul_sub]
      conv =>
        enter [1]
        rw [add_comm 1 n, ← Nat.cast_smul_eq_nsmul R, smul_eq_C_mul, Nat.cast_two, ← mul_assoc,
          mul_comm (C (c ^ (n + 1))), mul_assoc, ih₁]
      enter [2]
      rw [pow_add, pow_one, map_mul, mul_assoc]
      enter [2]
      rw [mul_left_comm, ih₂]
    simp [smul_eq_C_mul, sub_sq, show (2 : R[X]) = C (2 : R) from rfl]
    ring

variable {F : Type*} [NormedField F] [Algebra R F]

/-- If `F` is a normed field that is an `R`-algebra, then for a given `x : F`, the norm
of gthe value of `y s t n` at `x` is bounded by `2 * C ^ n` for some `C ≥ 0`. -/
lemma y_bound (s t : R) (x : F) : ∃ C > 0, ∀ n, ‖(y s t n).aeval x‖ ≤ 2 * C ^ n := by
  suffices ∃ C ≥ 0, ∀ n, ‖(y s t n).aeval x‖ ≤ 2 * C ^ n by
    obtain ⟨C, hC₀, hC⟩ := this
    refine ⟨C + 1, by positivity, fun n ↦ ?_⟩
    have H : 2 * C ^ n ≤ 2 * (C + 1) ^ n := by gcongr; linarith
    exact (hC n).trans H
  set a := ‖2 * (x - (algebraMap R F) s)‖
  set b := ‖x ^ 2 - s • (2 * x) + (algebraMap R F) t‖
  let C : ℝ := max (max ‖x - (algebraMap R F) s‖ (2 * a)) (Real.sqrt (2 * b))
  have h₂ : ‖(2 : F)‖ ≤ 2 := by simpa using Nat.norm_cast_le (α := F) 2
  have hC₁ : ‖x - (algebraMap R F) s‖ ≤ C := le_sup_of_le_left <| le_sup_of_le_left le_rfl
  have hC (n : ℕ) : a * (2 * C ^ (n + 1)) + b * (2 * C ^ n) ≤ 2 * C ^ (n + 2) := by
    have hCab₁ : a * C ≤ C ^ 2 / 2 := by
      rw [show C ^ 2 / 2 = (C / 2) * C by ring]
      gcongr
      rw [le_div_iff₀' zero_lt_two]
      exact le_sup_of_le_left (le_max_right ..)
    have hCab₂ : b ≤ C ^ 2 / 2 := by
      rw [le_div_iff₀' zero_lt_two, ← Real.sq_sqrt (by positivity : 0 ≤ 2 * b)]
      gcongr
      exact le_max_right ..
    rw [show a * (2 * C ^ (n + 1)) + b * (2 * C ^ n) = (a * C + b) * (2 * C ^ n) by ring,
      show 2 * C ^ (n + 2) = C ^ 2 * (2 * C ^ n) by ring, ← add_halves (C ^ 2)]
    gcongr
  refine ⟨C, by positivity, fun n ↦ ?_⟩
  induction n using Nat.twoStepInduction with
  | zero => simpa [y] using h₂
  | one =>
    simp only [y, nsmul_eq_mul, Nat.cast_ofNat, map_mul, aeval_ofNat, map_sub, aeval_X, aeval_C,
      norm_mul, pow_one]
    gcongr
  | more n ih₂ ih₁ =>
    rw [y]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Algebra.smul_mul_assoc, map_sub, map_mul, aeval_ofNat,
      aeval_X, aeval_C, map_add, map_pow, map_smul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    nth_rewrite 2 [norm_mul]
    refine LE.le.trans ?_ (hC n)
    gcongr

end sequences


variable {F : Type*} [NormedField F] [NormedAlgebra ℝ F]

open Polynomial

noncomputable
abbrev p (s t : ℝ) : ℝ[X] := (X - C s) ^ 2 + C t

lemma isMonicOfDegree_p_two (s t : ℝ) : IsMonicOfDegree (p s t) 2 := by
  rw [p]
  have : IsMonicOfDegree (X - C s) 1 := (isMonicOfDegree_X ℝ).sub <| by compute_degree!
  exact (this.pow  2).add_left <| by compute_degree!

lemma isMonicOfDegree_two_iff {f : ℝ[X]} : IsMonicOfDegree f 2 ↔ ∃ s t : ℝ, f = p s t := by
  refine ⟨fun H ↦ ?_, fun ⟨s, t, h⟩ ↦ h ▸ isMonicOfDegree_p_two s t⟩
  refine ⟨-f.coeff 1 / 2, f.coeff 0 - (f.coeff 1 / 2) ^ 2, ?_⟩
  ext1 n
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := by omega
    simp [sub_sq, ← map_pow]
    ring
  · simp [sub_sq, ← map_pow]
    ring
  replace hn : 2 ≤ n := by omega
  exact coeff_eq_of_isMonicOfDegree H (isMonicOfDegree_p_two ..) hn

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`. -/
lemma aux₂ {f : ℝ[X]} {n : ℕ} (hf : IsMonicOfDegree f (n + 2)) :
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
    have hf₁' : IsMonicOfDegree f₁ (1 + n) := isMonicOfDegree_of_mul_left hg hf
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
      exact ⟨g * g₁, f₂, hg.mul hg₁, isMonicOfDegree_of_mul_left (hg.mul hg₁) hf, hf₁⟩
    · -- m₁ = 2
      rw [hf₂, mul_left_comm] at hf₁ hf
      rw [show 1 + (1 + n) = 2 + n by omega] at hf
      exact ⟨g₁, g * f₂, hg₁, isMonicOfDegree_of_mul_left hg₁ hf, hf₁⟩
  · -- m = 2
    obtain ⟨f₂, hf₂⟩ := hgd
    rw [hf₂, add_comm] at hf
    exact ⟨g, f₂, hg, isMonicOfDegree_of_mul_left hg hf, hf₂⟩

lemma aux₁ (x : F) {s t : ℝ} (h : ∀ s' t' : ℝ, ‖(p s t).aeval x‖ ≤ ‖(p s' t').aeval x‖)
    {f : ℝ[X]} {n : ℕ} (hf : IsMonicOfDegree f (2 * n)) :
    ‖(p s t).aeval x‖ ^ n ≤ ‖f.aeval x‖ := by
  induction n generalizing f with
  | zero =>
    simp only [mul_zero, isMonicOfDegree_zero] at hf
    simp [hf]
  | succ n ih =>
    rw [mul_add, mul_one] at hf
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := aux₂ hf
    specialize ih hf₂
    obtain ⟨s', t', hst⟩ := isMonicOfDegree_two_iff.mp hf₁
    rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, hst]
    specialize h s' t'
    gcongr

/-- The key step in the proof: if `s` and `t` are real numbers minimizing `‖(p s t).aeval x‖`,
then for `s'` in some open interval around `s`, `‖(p s' t).aeval x‖` is constant.-/
lemma aux (x : F) {s t : ℝ} (h₀ : (p s t).aeval x ≠ 0)
    (h : ∀ s' t' : ℝ, ‖(p s t).aeval x‖ ≤ ‖(p s' t').aeval x‖) :
    ∃ ε > 0, ∀ c : ℝ, |c| < ε → ‖(p (s + c) t).aeval x‖ = ‖(p s t).aeval x‖ := by
  have H₀ : 0 < ‖(p s t).aeval x‖ := norm_pos_iff.mpr h₀
  obtain ⟨C, hC₀, hC⟩ := y_bound s (s ^ 2 + t) x
  have aux (f : ℝ[X]) n := aux₁ x h (f := f) (n := n)
  set M : ℝ := ‖aeval x (p s t)‖ with hM
  refine ⟨min M.sqrt (M / C), by positivity, fun c hc ↦ ?_⟩
  suffices ∀ n > 0, ‖aeval x (p (s + c) t)‖ ≤ -- use `n + 1`?
      M * (1 + (|c| / M) ^ n * ‖aeval x (y s (s ^ 2 + t) n)‖ + (|c| ^ 2 / M) ^ n) by
    rw [eq_comm]
    refine le_antisymm (h ..) ?_
    have key : Filter.Tendsto
        (fun n : ℕ ↦ M * (1 + (|c| / M) ^ n * ‖(aeval x) (y s (s ^ 2 + t) n)‖ + (|c| ^ 2 / M) ^ n))
        Filter.atTop (nhds M) := by
      conv => enter [3, 1]; rw [← mul_one M, ← add_zero 1, ← add_zero (1 + 0), add_assoc]
      conv => enter [1, n, 2]; rw [add_assoc]
      refine tendsto_const_nhds.mul <| tendsto_const_nhds.add <| Filter.Tendsto.add ?_ ?_
      · replace hC (n : ℕ) : (|c| / M) ^ n * ‖(aeval x) (y s (s ^ 2 + t) n)‖ ≤ 2 * (|c| / (M / C)) ^ n := by
          have := hC n
          rw [show 2 * (|c| / (M / C)) ^ n = (|c| / M) ^ n * (2 * C ^ n) by
            rw [mul_left_comm, ← mul_pow]; congr; field_simp]
          gcongr
        refine squeeze_zero (fun _ ↦ by positivity) hC ?_
        conv => enter [3, 1]; rw [← mul_zero 2]
        refine tendsto_const_nhds.mul <| tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
        rw [abs_of_nonneg (by positivity), div_lt_one (by positivity)]
        exact (lt_min_iff.mp hc).2
      · refine tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
        rw [abs_of_nonneg (by positivity), div_lt_one H₀, ← M.sq_sqrt H₀.le]
        gcongr
        exact (lt_min_iff.mp hc).1
    refine ge_of_tendsto key ?_
    have H : {n : ℕ | n > 0} ∈ Filter.atTop := by
      refine Filter.mem_atTop_sets.mpr ⟨1, fun m hm ↦ ?_⟩
      simp only [Set.mem_setOf_eq]
      omega
    filter_upwards [H]
    exact this
  intro n hn
  have hrel := y_z_rel s (s ^ 2 + t) c n
  apply_fun aeval x at hrel
  simp only [Algebra.mul_smul_comm, map_pow, map_add, map_sub, aeval_X, map_smul, map_mul,
    aeval_ofNat, Nat.cast_ofNat, aeval_C] at hrel
  have H₁ : aeval x (p s t) = x ^ 2 - s • (2 * x) + ((algebraMap ℝ F) s ^ 2 + (algebraMap ℝ F) t) := by
    simp only [map_add, sub_sq, two_mul, map_sub, map_pow, aeval_X, map_mul, aeval_C, add_assoc,
      smul_add, add_left_inj, sub_right_inj]
    rw [mul_comm, Algebra.smul_def, mul_add]
  have H₂ : aeval x (p (s + c) t) =
      (x - (algebraMap ℝ F) c) ^ 2 - s • (2 * (x - (algebraMap ℝ F) c)) +
        ((algebraMap ℝ F) s ^ 2 + (algebraMap ℝ F) t) := by
    simp [sub_sq, add_assoc, mul_add, two_mul, Algebra.smul_def, add_mul, add_sq, mul_sub]
    ring
  rw [← H₁, ← H₂, eq_comm] at hrel
  apply_fun (‖·‖) at hrel
  rw [norm_mul] at hrel
  replace hrel := hrel.trans_le (norm_add_le ..) |>.trans <| add_le_add_right (norm_sub_le ..) _
  have hz : M ^ (n - 1) ≤ ‖aeval x (z s (s ^ 2 + t) c n)‖ := by
    refine aux _ _ ?_
    convert z_isMonicOfDegree s (s ^ 2 + t) c (n - 1)
    omega
  have HH : ‖(aeval x) (p (s + c) t)‖ * M ^ (n - 1) ≤
      M ^ n + |c| ^ n * ‖(aeval x) (y s (s ^ 2 + t) n)‖ + |c| ^ (2 * n) := by
    calc ‖(aeval x) (p (s + c) t)‖ * M ^ (n - 1)
    _ ≤ ‖(aeval x) (p (s + c) t)‖ * ‖(aeval x) (z s (s ^ 2 + t) c n)‖ := by gcongr
    _ ≤ ‖(aeval x) (p s t) ^ n‖ + ‖c ^ n • (aeval x) (y s (s ^ 2 + t) n)‖
          + ‖(algebraMap ℝ F) c ^ (2 * n)‖ := hrel
    _ = M ^ n + |c| ^ n * ‖aeval x (y s (s ^ 2 + t) n)‖ + |c| ^ (2 * n) := by
      rw [norm_pow, hM, norm_smul, norm_pow, norm_pow, norm_algebraMap, c.norm_eq_abs, norm_one, mul_one]
  rw [← le_div_iff₀ (by positivity)] at HH
  convert HH using 1
  field_simp
  ring_nf -- not optimal...
  simp only [← pow_add, ← pow_succ']
  rw [show n - 1 + 1 = n by omega, show n + 1 + (n - 1) = n * 2 by omega, pow_mul' |c|, sq_abs,
    ← pow_mul']
  ring

lemma continuous_norm_aeval_p (x : F) (t : ℝ) : Continuous fun s : ℝ ↦ ‖(p s t).aeval x‖ := by
  simp only [map_add, map_sub, map_pow, aeval_X, map_mul, aeval_ofNat, Nat.cast_ofNat, aeval_C]
  fun_prop

lemma min_ex_deg_one (x : F) : ∃ u : ℝ, ∀ r : ℝ, ‖x - u • 1‖ ≤ ‖x - r • 1‖ := by
  have hf : Continuous fun r : ℝ ↦ ‖x - r • 1‖ := by fun_prop
  refine hf.exists_forall_le_of_isBounded 0 <| (2 * ‖x‖).isBounded_of_abs_le.subset fun r hr ↦ ?_
  simp only [zero_smul, sub_zero, Set.mem_setOf_eq] at hr ⊢
  have : |r| - ‖x‖ ≤ ‖x - r • 1‖ := by
    rw [norm_sub_rev]
    convert norm_sub_norm_le (r • 1) x
    exact (Algebra.norm_smul_one_eq_abs r).symm
  linarith

lemma min_ex_deg_two (x : F) :
    ∃ a b : ℝ, ∀ a' b' : ℝ, ‖x ^ 2 - a • x + b • 1‖ ≤ ‖x ^ 2 - a' • x + b' • 1‖ := by
  obtain ⟨u, hu⟩ := min_ex_deg_one x
  set c := ‖x - u • 1‖ with hc
  rcases eq_or_ne c 0 with hc₀ | hc₀
  · refine ⟨u, 0, fun s' t' ↦ ?_⟩
    rw [zero_smul, add_zero, sq, show u • x = (u • 1) * x by simp, ← sub_mul, norm_mul, ← hc, hc₀,
      zero_mul]
    exact norm_nonneg _
  replace hc₀ : 0 < c := by positivity
  suffices ∃ z : ℝ × ℝ, ∀ z' : ℝ × ℝ, ‖x ^ 2 - z.1 • x + z.2 • 1‖ ≤ ‖x ^ 2 - z'.1 • x + z'.2 • 1‖ by
    obtain ⟨z, h⟩ := this
    exact ⟨z.1, z.2, fun a' b' ↦ h (a', b')⟩
  have hf : Continuous fun z : ℝ × ℝ ↦ ‖x ^ 2 - z.1 • x + z.2 • 1‖ := by fun_prop
  refine hf.exists_forall_le_of_isBounded (0, 0) ?_
  simp only [zero_smul, sub_zero, add_zero, norm_pow]
  refine ((2 * ‖x‖ ^ 2 / c).isBounded_of_abs_le.prod
            (2 * ‖x‖ ^ 2 + 2 * ‖x‖ ^ 3 / c).isBounded_of_abs_le).subset fun (a, b) hab ↦ ?_
  simp only [Set.mem_prod, Set.mem_setOf_eq] at hab ⊢
  have ha : |a| ≤ 2 * ‖x‖ ^ 2 / c := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [abs_zero]
      positivity
    rw [le_div_iff₀ hc₀]
    calc |a| * c
    _ ≤ |a| * ‖x - (b / a) • 1‖ := by gcongr; exact hu _
    _ = ‖a • x - b • 1‖ := by
        rw [← Real.norm_eq_abs, ← norm_smul, smul_sub, smul_smul, mul_div_cancel₀ _ ha]
    _ ≤ ‖x‖ ^ 2 + ‖x ^ 2 - a • x + b • 1‖ := by
        rw [sub_add, ← norm_pow, norm_sub_rev (x ^ 2)]
        exact norm_le_norm_add_norm_sub' ..
    _ ≤ _ := by rw [two_mul]; gcongr
  refine ⟨ha, ?_⟩
  rw [two_mul, add_assoc, ← sub_le_iff_le_add, ← sub_sub]
  calc |b| - ‖x‖ ^ 2 - 2 * ‖x‖ ^ 3 / c
  _ ≤ |b| - ‖x‖ ^ 2 - |a| * ‖x‖ := by
      rw [show 2 * ‖x‖ ^ 3 / c = 2 * ‖x‖ ^ 2 / c * ‖x‖ by ring]
      gcongr
  _ = ‖b • (1 : F)‖ - ‖a • x‖ - ‖x ^ 2‖ := by rw [sub_right_comm, norm_smul a]; simp
  _ ≤ ‖b • 1 - a • x‖ - ‖x ^ 2‖ := by gcongr; exact norm_sub_norm_le ..
  _ ≤ ‖b • 1 - a • x + x ^ 2‖ := norm_sub_le_norm_add ..
  _ = ‖x ^ 2 - a • x + b • 1‖ := congrArg  _ <| by ring
  _ ≤ ‖x‖ ^ 2 := hab


/-- There are real numbers `s` and `t` such that `‖(x - s • 1) ^ 2 + t • 1‖` is minimal. -/
lemma minimum_exists (x : F) : ∃ s t : ℝ, ∀ s' t' : ℝ, ‖(p s t).aeval x‖ ≤ ‖(p s' t').aeval x‖ := by
  have (a b : ℝ) : (p a b).aeval x = x ^ 2 - 2 * a • x + (a ^ 2 + b) • 1 := by
    simp [Algebra.algebraMap_eq_smul_one, sub_sq]
    rw [add_assoc, add_smul, _root_.smul_pow, one_pow]
  simp only [this]
  obtain ⟨a, b, hab⟩ := min_ex_deg_two x
  refine ⟨a / 2, b - (a / 2) ^ 2, fun s' t' ↦ ?_⟩
  convert hab (2 * s') (s' ^ 2 + t') using 4
  · rw [two_mul, ← add_smul, add_halves]
  · ring
  · rw [two_mul, ← add_smul, ← two_mul]

/-- Every `x : F` is the root of a monic quadratic polynomial with real coefficients. -/
lemma satisfies_quadratic_rel (x : F) : ∃ f : ℝ[X], f.IsMonicOfDegree 2 ∧ aeval x f = 0 := by
  suffices ∃ s t : ℝ, (p s t).aeval x = 0 by
    obtain ⟨s, t, hst⟩ := this
    exact ⟨p s t, isMonicOfDegree_p_two s t, hst⟩
  obtain ⟨s, t, hst⟩ := minimum_exists x
  rcases eq_or_ne ((p s t).aeval x) 0 with h₀ | h₀
  · exact ⟨s, t, h₀⟩
  by_contra! H
  let S : Set ℝ := {c | ‖(p c t).aeval x‖ = ‖(p s t).aeval x‖}
  have hS₁ : IsClosed S := isClosed_eq (continuous_norm_aeval_p x t) (by fun_prop)
  have hS₂ : IsOpen S := by
    refine isOpen_iff_forall_mem_open.mpr fun c hc ↦ ?_
    change ‖(aeval x) (p c t)‖ = ‖(aeval x) (p s t)‖ at hc
    have h₀' : (p c t).aeval x ≠ 0 := H c t
    obtain ⟨ε, hε₀, hε⟩ := aux x h₀' (fun s' t' ↦ hc ▸ hst s' t')
    refine ⟨Set.Ioo (c - ε) (c + ε), fun u hu ↦ ?_, isOpen_Ioo, ?_⟩
    · simp only [Set.mem_setOf, S, ← hc]
      convert hε (u - c) ?_
      · abel
      · simp only [Set.mem_Ioo] at hu
        exact abs_sub_lt_iff.mpr ⟨sub_left_lt_of_lt_add hu.2, sub_lt_comm.mp hu.1⟩
    · refine Set.mem_Ioo.mpr ⟨?_, ?_⟩ <;> linarith
  have hS₃ : S.Nonempty := Set.nonempty_of_mem rfl
  have key : S = Set.univ := IsClopen.eq_univ ⟨hS₁, hS₂⟩ hS₃
  replace key (c : ℝ) : ‖(aeval x) (p c t)‖ = ‖(aeval x) (p s t)‖ := by
    simp only [S] at key
    simpa only [← key] using Set.mem_univ c
  have hx₀ : x ≠ 0 := by
    rintro rfl
    simpa using H 0 0
  set a := ‖(aeval x) (p s t)‖
  have hh {c : ℝ} (hc : 0 ≤ c) : (c - ‖algebraMap ℝ F s - x‖) ^ 2 - ‖algebraMap ℝ F s - x‖ ^ 2 ≤ 2 * a := by
    rw [two_mul a]
    nth_rewrite 1 [← key s]
    rw [← key (s + c)]
    refine LE.le.trans ?_ (norm_sub_le ..)
    conv =>
      enter [2]
      simp only [map_add, map_pow, map_sub, aeval_X, aeval_C, add_sub_add_right_eq_sub]
      rw [pow_two_sub_pow_two, norm_mul, sub_add_eq_sub_sub, sub_sub_self, ← add_sub_assoc, ← two_mul]
    simp only [norm_algebraMap', Real.norm_eq_abs, tsub_le_iff_right, sub_sq]
    gcongr
    rw [show c ^ 2 - 2 * c * ‖(algebraMap ℝ F) s - x‖ =
      (c - 2 * ‖(algebraMap ℝ F) s - x‖) * c by ring,
      abs_of_nonneg hc]
    gcongr
    trans ‖(algebraMap ℝ F) c‖ - ‖2 * (x - (algebraMap ℝ F) s)‖
    · refine le_of_eq ?_
      congr
      · simp [abs_of_nonneg hc]
      · rw [norm_mul, norm_sub_rev]
        congr
        -- extract this?
        rw [show (2 : F) = (2 : ℝ) • 1 by rw [← Algebra.algebraMap_eq_smul_one, map_ofNat],
          norm_smul, Real.norm_ofNat, norm_one, mul_one]
    · rw [norm_sub_rev]
      exact norm_sub_norm_le ..
  set b := ‖(algebraMap ℝ F) s - x‖
  let c : ℝ := (2 * a + b ^ 2).sqrt + b + 1
  have hc₀ : 0 ≤ c := by positivity
  specialize hh hc₀
  simp only [tsub_le_iff_right, c] at hh
  conv at hh => enter [1, 1]; ring_nf
  ring_nf at hh
  rw [Real.sq_sqrt (by positivity)] at hh
  conv at hh => enter [2]; rw [← zero_add (a * 2 + b ^ 2)]
  contrapose! hh
  gcongr
  positivity

/-- A variant of the **Gelfand-Mazur Theorem** over `ℝ`:

If `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`. -/
theorem nonempty_algEquiv_or : Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ IsIntegral.isAlgebraic ?_⟩
    obtain ⟨f, hf, hfx⟩ := satisfies_quadratic_rel x
    exact (hfx ▸ isIntegral_zero).of_aeval_monic hf.monic <|
      hf.natDegree_eq.trans_ne two_ne_zero
  exact Real.nonempty_algEquiv_or F

-- without going via `IsIntegral`:
/-
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨f, hf, hfx⟩ := satisfies_quadratic_rel x
    refine (hfx ▸ isAlgebraic_zero).of_aeval f ?_ ?_
    · exact hf.natDegree_eq.trans_ne two_ne_zero
    · rw [hf.monic.leadingCoeff]
      exact Submonoid.one_mem (nonZeroDivisors ℝ)
-/

end GelfandMazur
