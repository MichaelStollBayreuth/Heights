import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Analysis.Complex.Polynomial.Basic

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

### The complex case

The proof we use here is a variant of a proof for the complex case (any normed `ℂ`-algebra
is isomorphic to `ℂ`) that is originally due to Ostrowski
[(Section 7 in *Über einige Lösungen der Funktionalgleichung φ(x)⋅φ(y)=φ(xy)*,
Acta Math. 41, 271-284 (1917))}(https://doi.org/10.1007/BF02422947).
See also the concise version provided by Peter Scholze on
[Math Overflow](https://mathoverflow.net/questions/10535/ways-to-prove-the-fundamental-theorem-of-algebra/420803#420803).

This proof goes as follows. Let `x : F` be arbitrary; we need to show that `x = z•1`
for some `z : ℂ`. We consider the function `z ↦ ‖x - z•1‖`. It has a minimum `M`,
which it attains at some point `z`, which (upon replacing `x` by `x + z•1`) we can
assume to be zero. If `M = 0`, we are done, so assume not. For `n : ℕ`,
a primitive `n`th root of unity `ζ : ℂ`, and `z : ℂ` with `|z| < M = ‖x‖` we then have that
`M ≤ ‖x - z•1‖ = ‖x^n - z^n•1‖ / ∏ k ∈ Ioo 0 n, ‖x - (ζ^k*z)•1‖`,
which is bounded by `(M^n + |z|^n)/M^(n-1) = M*(1 + (|z|/M)^n)`.
Letting `n` tend to infinity then shows that `‖x - z•1‖ = M`.
This implies that the set of `z` such that `‖x - z•1‖ = M` is closed and open
(and nonempty), so it is all of `ℂ`, which contradicts `‖x - z•1‖ ≥ |z| - M`
when `|z|` is sufficiently large.

This shows that when `F` is a nontrivial normed `ℂ`-algebra *with multiplicative norm*,
then `F` is isomorphic to `ℂ` as a `ℂ`-algebra (see `GelfandMazur.Complex.algEquivOfNormMul`
for the isomorphism).

A version of the result exists as `NormedRing.algEquivComplexOfComplete` (which gives
the isomorphism) in Mathlib, with different assumptions (and a different proof):
* `F` is assumed to be complete,
* `F` is assumed to be a (nontrivial) division ring,
* but the norm is only required to be submultiplicative.

### The real case

THe usual proof for the real case is "either `F` contains a square root of `-1`;
then `F` is in fact a normed `ℂ`-agebra and we can use the result above, or else
we adjoin a square root of `-1` to `F` to obtain a normed `ℂ`-agebra `F'` and
apply the result to `F'`". The difficulty with formalizing this is that
Mathlib does not provide a normed `ℂ`-algebra instance for `F'` (neither for
`F' := AdjoinRoot (X^2 + 1 : F[X])` nor for `F' := TensorProduct ℝ ℂ F`),
and it is not so straight-forward to set this up. So we take inspiration from the
proof sketched above for the complex case to obtain a direct proof.

Since irreducible polynomials over `ℝ` have degree at most `2`, it is actually the case
that each element is annihilated by a monic polynomial of degree `2`. We can state this as
`∃ p : ℝ[X], IsMonicOfDegree p 2 ∧ p.aeval x = 0`, where `Polynomial.IsMonicOfDegree`
has the obvious meaning (we define this predicate and provide API for it
in a separate file). We fix `x : F` in the following.

Because the space `ℝ²` of monic polynomials of degree `2` is complete and locally compact
and `‖aeval x p‖` gets large when `p` has large coefficients (*), there will be some `p₀`
such that `‖aeval x p₀‖` attains a minimum (see `GelfandMazur.exists_minimum_of_f`).
We assume that this is positive and derive a contradiction. Let `M := ‖aeval x p₀‖ > 0`
be the minimal value.
Since every monic polynomial `f : ℝ[X]` of even degree can be written as a product
of monic polynomials of degree `2`
(see `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree`),
it follows that `‖aeval x f‖ ≥ M^(f.natDegree / 2)`.

(*) This is actually somewhat more subtle. It is certainly true for `‖x - r•1‖` with `r : ℝ`.
If the minimum of this is zero, then the minimum for monic polynomials of degree `2`
will also be zero (and is attained on a one-dimensional subset). Otherwise, one can
indeed show that a bound on `‖x^2 - a•x + b•1‖` implies bounds on `|a|` and `|b|`.

The goal is now to show that when `a` and `b` achieve the minimum `M` of `‖x^2 - a•x + b•1‖`,
and `M > 0`, then we can find some neighborhood `U` of `(a,b)` in `ℝ × ℝ`
such that `‖x^2 - a'•x + b'•1‖ = M` for all `(a',b') ∈ U`
(see `GelfandMazur.constant_on_nhd_of_ne_zero`).
Then the set `S = {(a',b') | ‖x^2 - a'•x + b'•1‖ = M}` must be all of `ℝ × ℝ` (as it is
closed, open, and nonempty). This will lead to a contradiction with the growth
of `‖x^2 - a•x‖` as `|a|` gets large.

To get there, the idea is, similarly to the complex case, to use the fact that
`X^2 - a'*X + b'` divides the difference `(X^2 - a*X + b)^n - ((a'-a)*X - (b'-b))^n`;
this dives us a monic polynomial `p` of degree `2*(n-1)` such that `(X^2 - a'*X + b')*p`
equals this difference. By the above, `‖aeval x p‖ ≥ M^(n-1)`.

Since `(a',b') ↦ x^2 - a'•x + b'•1` is continuous, there will be a neighborhood `U`
of `(a,b)` such that `‖(a'-a)•x - (b'-b)•1‖ = ‖(x^2-a•x+b•1) - (x^2-a'•x+b'•1)‖`
is less than `M` for `(a',b') ∈ U`. For such `(a',b')`, it follows that
`‖x^2 - a'•x + b'•1‖ ≤ ‖(x^2-a•x+b•1)^n - ((a'-a)•x-(b'-b)•1)^n‖ / ‖aeval x p‖`,
which is bounded by `(M^n + c^n) / M^(n-1) = M * (1 + (c/M)^n)`, where
`c = ‖(a'-a)•x-(b'-b)•1‖ < M`. So, letting `n` tend to infinity, we obtain that
`M ≤ ‖x^2 - a'•x + b'•1‖ ≤ M`, as desired.
-/

section auxiliary

namespace Algebra

lemma add_smul_one_sq {A R : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (r : R) :
    (x + r • 1) ^ 2 = x ^ 2 + 2 * x * (r • 1) + (r • 1) ^ 2 := by
    -- `add_sq` assumes `CommSemiring A`
    simp [sq, add_mul, mul_add, smul_add, smul_smul, two_mul, add_assoc]

lemma sub_smul_one_sq {A R : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) (r : R) :
    (x - r • 1) ^ 2 = x ^ 2 - 2 * x * (r • 1) + (r • 1) ^ 2 := by
    -- `sub_sq` assumes `CommRing A`
    simp [sq, sub_mul, mul_sub, smul_sub, smul_smul, two_mul, ← sub_sub, ← sub_add]

-- [Mathlib.Algebra.Algebra.Defs] (after removing Algebra.Lie.* from imports)

section General

variable {R A : Type*} [NormedField R] [SeminormedRing A] [NormedAlgebra R A] [NormOneClass A]

@[simp]
lemma norm_smul_one_eq_norm (z : R) : ‖z • (1 : A)‖ = ‖z‖ := by
  rw [← Algebra.algebraMap_eq_smul_one, norm_algebraMap']

-- [Mathlib.Analysis.Normed.Module.Basic]

end General

section Real

variable {A : Type*} [SeminormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

@[simp]
lemma norm_smul_one_eq_abs (x : ℝ) : ‖x • (1 : A)‖ = |x| := by
  rw [norm_smul_one_eq_norm, x.norm_eq_abs]

@[simp]
lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : A)‖ = (ofNat(n) : ℝ) := by
  rw [← map_ofNat (algebraMap ℝ A) n, norm_algebraMap', Real.norm_eq_abs, n.abs_ofNat]

-- [Mathlib.Analysis.Normed.Module.Basic] for the two lemmas above

end Real

end Algebra

namespace Polynomial

@[simp]
lemma aeval_ofNat {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (n : ℕ)
    [n.AtLeastTwo] :
    (Polynomial.aeval (R := R) x) (ofNat(n) : R[X]) = (ofNat(n) : A) :=
  aeval_natCast x _

-- [Mathlib.Algebra.Polynomial.AlgebraMap]

end Polynomial

end auxiliary

section Complex

/-!
### The complex case

As a proof of concept, we formalize here the proof for normed `ℂ`-algebras.

Fix `x : F` and assume that `M := ‖x - z•1‖` is minimal and non-zero for `z : ℂ`.
Then for `c : ℂ` and `n : ℕ`, we have
`‖x - (z+c)•1‖ = ‖(x - z•1)^n - c^n•1‖/‖aeval (x-z•1) p‖`
with a monic polynomial `p` of degree `n-1`.

Since every monic polynomial of degree `m` over `ℂ` is a product of `m` monic polynomials
of degree `1`, it follows that `‖aeval (x-z•1) p‖ ≥ M^(n-1)`. We obtain
`M ≤ ‖x - (z+c)•1‖ ≤ (‖x - z•1‖^n + |c|^n) / M^(n-1) ≤ M*(1 + (|c|/M)^n)`,
so if `|c| < M`, then as `n → ∞` we see that `‖x - (z+c)•1‖ = M`.

This implies that the function `c ↦ ‖x - c•1‖` is constant, which contradicts that
`‖x - c•1‖ ≥ |c| - ‖x‖ > M` for `|c| > M + ‖x‖`.

So we conclude that there must be `z : ℂ` such that `x = z•1`; i.e., the algebra map
`ℂ → F` is an isomorphism.
-/

open Polynomial

/-- If `f : F[X]` is monic of degree `≥ 1` and `F` is an algebraically closed field,
then `f = f₁ * f₂` with `f₁` monic of degree `1` and `f₂` monic of degree `f.natDegree - 1`. -/
lemma Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_one_isMonicOfDegree {F : Type*} [Field F]
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

namespace GelfandMazur.Complex

variable {F : Type*} [NormedRing F] [NormOneClass F] [NormMulClass F] [NormedAlgebra ℂ F]

lemma le_aeval_of_isMonicOfDegree (x : F) {M : ℝ} (hM : 0 ≤ M) (h : ∀ z' : ℂ, M ≤ ‖x - z' • 1‖)
    {p : ℂ[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (c : ℂ) :
    M ^ n ≤ ‖aeval (x - c • 1) p‖ := by
  induction n generalizing p with
  | zero => simp [isMonicOfDegree_zero_iff.mp hp]
  | succ n ih =>
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := hp.eq_mul_isMonicOfDegree_one_isMonicOfDegree
    obtain ⟨r, hr⟩ := isMonicOfDegree_one_iff.mp hf₁
    have H' (y : F) : aeval y (X + C r) = y + r • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, hr, H', sub_add, ← sub_smul]
    exact mul_le_mul (ih hf₂) (h (c - r)) hM (norm_nonneg _)

lemma constant_on_open_ball_of_ne_zero (x : F) {z :  ℂ} (h₀ : ‖x - z • 1‖ ≠ 0)
    (h : ∀ z' : ℂ, ‖x - z • 1‖ ≤ ‖x - z' • 1‖) :
    ∃ ε > 0, ∀ c : ℂ, ‖c‖ < ε → ‖x - (z + c) • 1‖ = ‖x - z • 1‖ := by
  set M : ℝ := ‖x - z • 1‖ with hM
  have hM₀ : 0 ≤ M := norm_nonneg _
  refine ⟨M, by positivity, fun c hc ↦ ?_⟩
  suffices ∀ n > 0, ‖x - (z + c) • 1‖ ≤ M * (1 + (‖c‖ / M) ^ n) by
    refine (le_antisymm (h _) <|
      ge_of_tendsto ?_ <| Filter.Eventually.mono (Filter.Ioi_mem_atTop 0) this).symm
    conv => enter [3, 1]; rw [show M = M * (1 + 0) by ring] -- preparation
    exact tendsto_const_nhds.mul <| tendsto_const_nhds.add <|
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) <|
      (div_lt_one <| by positivity).mpr hc
  intro n hn
  have := sub_dvd_pow_sub_pow X (C c) n
  obtain ⟨p, hp, hrel⟩ := by
    refine (isMonicOfDegree_X_pow ℂ n).of_dvd_sub (by omega) (isMonicOfDegree_X_sub_one c) ?_ this
    compute_degree!
  rw [eq_comm, ← eq_sub_iff_add_eq] at hrel
  apply_fun (‖aeval (x - z • 1) ·‖) at hrel -- evaluate at `x - z•1` and take norms
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, norm_mul,
    map_pow] at hrel
  rw [mul_comm, sub_sub, ← add_smul] at hrel
  replace hrel := hrel.trans_le (norm_sub_le ..)
  rw [norm_pow, norm_pow, Algebra.norm_smul_one_eq_norm, ← hM] at hrel
  have hz : M ^ (n - 1) ≤ ‖aeval (x - z • 1) p‖ := le_aeval_of_isMonicOfDegree x hM₀ h hp _
  have HH : ‖x - (z + c) • 1‖ * M ^ (n - 1) ≤ M ^ n + ‖c‖ ^ n := by
    calc _
    _ ≤ ‖x - (z + c) • 1‖ * ‖aeval (x - z • 1) p‖ := by gcongr
    _ ≤ M ^ n + ‖c‖ ^ n := hrel
  convert (le_div_iff₀ (by positivity)).mpr HH using 1
  rw [div_pow]
  field_simp
  rw [mul_comm M, ← pow_succ, Nat.sub_add_cancel hn]

omit [NormMulClass F] in
lemma min_ex_deg_one (x : F) : ∃ z : ℂ, ∀ z' : ℂ, ‖x - z • 1‖ ≤ ‖x - z' • 1‖ := by
  have hf : Continuous fun z : ℂ ↦ ‖x - z • 1‖ := by fun_prop
  refine hf.exists_forall_le_of_isBounded 0 <|
     (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨2 * ‖x‖, fun z hz ↦ ?_⟩
  rw [zero_smul, sub_zero, Set.mem_setOf, norm_sub_rev] at hz
  replace hz := (norm_sub_norm_le ..).trans hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  rwa [tsub_le_iff_right, Algebra.norm_smul_one_eq_norm, ← two_mul] at hz

lemma norm_sub_is_constant {x : F} {z : ℂ} (hz : ∀ z' : ℂ, ‖x - z • 1‖ ≤ ‖x - z' • 1‖)
    (H : ∀ z' : ℂ, ‖x - z' • 1‖ ≠ 0) (c : ℂ) :
    ‖x - c • 1‖ = ‖x - z • 1‖ := by
  suffices {c : ℂ | ‖x - c • 1‖ = ‖x - z • 1‖} = Set.univ by
    simpa only [← this] using Set.mem_univ c
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩ <|
    Set.nonempty_of_mem rfl
  refine isOpen_iff_forall_mem_open.mpr fun c hc ↦ ?_
  simp only [Set.mem_setOf_eq] at hc
  obtain ⟨ε, hε₀, hε⟩ := constant_on_open_ball_of_ne_zero x (H c) (fun z' ↦ hc ▸ hz z')
  refine ⟨Metric.ball c ε, fun u hu ↦ ?_, Metric.isOpen_ball, Metric.mem_ball_self hε₀⟩
  rw [Set.mem_setOf, ← hc, show u = c + (u - c) by abel]
  exact hε (u - c) hu

lemma exists_norm_sub_smul_one_eq_zero [Nontrivial F] (x : F) :
    ∃ z : ℂ, ‖x - z • 1‖ = 0 := by
  obtain ⟨z, hz⟩ := min_ex_deg_one x
  set M := ‖x - z • 1‖ with hM
  rcases eq_or_lt_of_le (show 0 ≤ M from norm_nonneg _) with hM₀ | hM₀
  · exact ⟨z, hM₀.symm⟩
  by_contra! H
  have key := norm_sub_is_constant hz H (‖x‖ + M + 1)
  rw [← hM, norm_sub_rev] at key
  replace key := (norm_sub_norm_le ..).trans_eq key
  rw [Algebra.norm_smul_one_eq_norm] at key
  norm_cast at key
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at key
  linarith

variable (F) in
/-- If `F` is a nontrivial normed `ℂ`-algebra with multiplicative norm, then we obtain a
`ℂ`-algebra equivalence with `ℂ`. -/
noncomputable
def algEquivOfNormMul [Nontrivial F] : ℂ ≃ₐ[ℂ] F := by
  let e : ℂ →ₐ[ℂ] F := AlgHom.mk' (algebraMap ℂ F) (algebraMap.coe_smul ℂ ℂ F)
  refine AlgEquiv.ofBijective e ⟨FaithfulSMul.algebraMap_injective ℂ F, fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := exists_norm_sub_smul_one_eq_zero x
  refine ⟨z, ?_⟩
  rw [AlgHom.coe_mk', Algebra.algebraMap_eq_smul_one, eq_comm, ← sub_eq_zero]
  exact norm_eq_zero.mp hz

variable (F) in
/-- A version of the **Gelfand-Mazur Theorem** for nontrivial normed `ℂ`-algebras `F`
with multiplicative norm. -/
theorem mainThm [Nontrivial F] : Nonempty (ℂ ≃ₐ[ℂ] F) := ⟨algEquivOfNormMul F⟩

end GelfandMazur.Complex

end Complex

section Real

/-!
### The real case
-/

open Polynomial

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`.

This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
lemma Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree {f : ℝ[X]} {n : ℕ}
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

/-!
### The key step of the proof
-/

namespace GelfandMazur.Real

variable {F : Type*} [NormedRing F] [NormedAlgebra ℝ F]

abbrev φ (x : F) (u : ℝ × ℝ) : F := x ^ 2 - u.1 • x + u.2 • 1

lemma continuous_φ (x : F) : Continuous (φ x) := by fun_prop

lemma aeval_eq_φ (x : F) (u : ℝ × ℝ) : aeval x (X ^ 2 - C u.1 * X + C u.2) = φ x u := by
  simp [Algebra.algebraMap_eq_smul_one]

variable  [NormOneClass F] [NormMulClass F]

lemma le_aeval_of_isMonicOfDegree {x : F} {M : ℝ} (hM : 0 ≤ M) (h : ∀ z : ℝ × ℝ, M ≤ ‖φ x z‖)
    {p : ℝ[X]} {n : ℕ} (hp : IsMonicOfDegree p (2 * n)) :
    M ^ n ≤ ‖aeval x p‖ := by
  induction n generalizing p with
  | zero => simp_all
  | succ n ih =>
    rw [mul_add, mul_one] at hp
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := hp.eq_mul_isMonicOfDegree_two_isMonicOfDegree
    obtain ⟨a, b, hab⟩ := isMonicOfDegree_two_iff'.mp hf₁
    rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, hab, aeval_eq_φ x (a, b)]
    exact mul_le_mul (ih hf₂) (h (a, b)) hM (norm_nonneg _)

/-- The key step in the proof: if `a` and `b` are real numbers minimizing `‖x^2 - a•x + b•1‖`,
and the minimal value is strictly positive, then the function `(s,t) ↦ ‖x^2 - s•x + t•1‖`
is constant. -/
lemma is_const_norm_sq_sub_add {x : F} {z : ℝ × ℝ} (h : ∀ w, ‖φ x z‖ ≤ ‖φ x w‖) (H : ‖φ x z‖ ≠ 0)
    (w : ℝ × ℝ) :
    ‖φ x w‖ = ‖φ x z‖ := by
  suffices {w : ℝ × ℝ | ‖φ x w‖ = ‖φ x z‖} = Set.univ by simpa only [← this] using Set.mem_univ w
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩ <| Set.nonempty_of_mem rfl
  refine isOpen_iff_mem_nhds.mpr fun w hw ↦ ?_
  simp only [Set.mem_setOf] at hw
  replace H := ((lt_of_le_of_ne (norm_nonneg _) H.symm).trans_le (h w)).ne'
  replace h := hw ▸ h
  set M : ℝ := ‖φ x w‖
  have hM₀ : 0 < M := by positivity
  suffices ∃ U ∈ nhds w, ∀ u ∈ U, ‖φ x u‖ = M by
    obtain ⟨U, hU₁, hU₂⟩ := this
    exact Filter.mem_of_superset hU₁ fun _ hu ↦ Set.mem_setOf.mpr <| hw ▸ hU₂ _ hu
  obtain ⟨U, hU₀, hU⟩ : ∃ U ∈ nhds w, ∀ u ∈ U, ‖φ x u - φ x w‖ < M := by
    refine ⟨φ x ⁻¹' {y : F | ‖y - φ x w‖ < M}, (continuous_φ x).tendsto w ?_,
      fun _ H ↦ by simpa using H⟩
    exact isOpen_lt (by fun_prop) (by fun_prop) |>.mem_nhds (by simpa)
  refine ⟨U, hU₀, fun u hu ↦ ?_⟩; clear hU₀ hw
  suffices ∀ n > 0, ‖φ x u‖ ≤ M * (1 + (‖φ x u - φ x w‖ / M) ^ n) by
    refine (le_antisymm (show M ≤ ‖φ x u‖ from h ..) ?_).symm
    refine ge_of_tendsto ?_ <| Filter.Eventually.mono (Filter.Ioi_mem_atTop 0) this
    conv => enter [3, 1]; rw [show M = M * (1 + 0) by ring] -- preparation
    refine tendsto_const_nhds.mul <| tendsto_const_nhds.add <|
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
    rw [abs_of_nonneg (by positivity)]
    exact (div_lt_one hM₀).mpr <| hU u hu
  intro n hn; clear hU hu
  have HH : M * (1 + (‖φ x u - φ x w‖ / M) ^ n) = (M ^ n + ‖φ x u - φ x w‖ ^ n) / M ^ (n - 1) := by
    rw [mul_comm, eq_div_iff (by positivity), mul_assoc, ← pow_succ', Nat.sub_one_add_one hn.ne',
      add_mul, one_mul, ← mul_pow, div_mul_cancel₀ _ H]
  rw [HH, le_div_iff₀ (by positivity)]; clear HH
  let q (y : ℝ × ℝ) : ℝ[X] := X ^ 2 - C y.1 * X + C y.2
  have hq (y : ℝ × ℝ) : IsMonicOfDegree (q y) 2 := isMonicOfDegree_sub_add_two ..
  have hsub : q w - q u = (C u.1 - C w.1) * X + C w.2 - C u.2 := by simp only [q]; ring
  have hdvd : q u ∣ q w ^ n - (q w - q u) ^ n := by
    nth_rewrite 1 [← sub_sub_self (q w) (q u)]
    exact sub_dvd_pow_sub_pow ..
  have H' : ((q w - q u) ^ n).natDegree < 2 * n := by rw [hsub]; compute_degree; omega
  obtain ⟨p, hp, hrel⟩ := ((hq w).pow n).of_dvd_sub (by omega) (hq u) H' hdvd; clear H' hdvd hsub
  rw [show 2 * n - 2 = 2 * (n - 1) by omega] at hp
  rw [← sub_eq_iff_eq_add, eq_comm, mul_comm] at hrel
  apply_fun (‖aeval x ·‖) at hrel
  rw [map_mul, norm_mul, map_sub, aeval_eq_φ x u] at hrel
  calc
  _ ≤ ‖φ x u‖ * ‖(aeval x) p‖ := by gcongr; exact le_aeval_of_isMonicOfDegree hM₀.le h hp
  _ = ‖aeval x (q w ^ n) - aeval x ((q w - q u) ^ n)‖ := hrel
  _ ≤ ‖aeval x (q w ^ n)‖ + ‖aeval x ((q w - q u) ^ n)‖ := norm_sub_le ..
  _ = _ := by simp only [q, map_pow, norm_pow, map_sub, aeval_eq_φ x]; rw [norm_sub_rev]

/-!
### Existence of a minimizing monic polynomial of degree 2
-/

omit [NormMulClass F] in
lemma min_ex_deg_one (x : F) : ∃ u : ℝ, ∀ r : ℝ, ‖x - u • 1‖ ≤ ‖x - r • 1‖ := by
  have hf : Continuous fun r : ℝ ↦ ‖x - r • 1‖ := by fun_prop
  refine hf.exists_forall_le_of_isBounded 0 <|
    (Metric.isBounded_of_abs_le (2 * ‖x‖)).subset fun r hr ↦ ?_
  simp only [zero_smul, sub_zero, Set.mem_setOf_eq] at hr ⊢
  have : |r| - ‖x‖ ≤ ‖x - r • 1‖ := by
    rw [norm_sub_rev]
    convert norm_sub_norm_le (r • 1) x
    exact (Algebra.norm_smul_one_eq_abs r).symm
  linarith

lemma a_bound {x : F} {c : ℝ} (hc₀ : 0 < c) (hbd : ∀ r : ℝ, c ≤ ‖x - r • 1‖) {a b : ℝ}
    (h : ‖x ^ 2 - a • x + b • 1‖ ≤ ‖x‖ ^ 2) :
    |a| ≤ 2 * ‖x‖ ^ 2 / c := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [abs_zero]
    positivity
  rw [le_div_iff₀ hc₀]
  calc |a| * c
  _ ≤ |a| * ‖x - (b / a) • 1‖ := by gcongr; exact hbd _
  _ = ‖a • x - b • 1‖ := by
      rw [← Real.norm_eq_abs, ← norm_smul, smul_sub, smul_smul, mul_div_cancel₀ _ ha]
  _ ≤ ‖x‖ ^ 2 + ‖x ^ 2 - a • x + b • 1‖ := by
      simpa only [← norm_pow, sub_add, norm_sub_rev (x ^ 2)] using norm_le_norm_add_norm_sub' ..
  _ ≤ _ := by rw [two_mul]; exact add_le_add_left h _

lemma min_ex_deg_two (x : F) : ∃ z : ℝ × ℝ, ∀ w : ℝ × ℝ, ‖φ x z‖ ≤ ‖φ x w‖ := by
  obtain ⟨u, hu⟩ := min_ex_deg_one x
  rcases eq_or_lt_of_le (norm_nonneg (x - u • 1)) with hc₀ | hc₀
  · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hc₀
    exact ⟨(u, 0), fun z' ↦ by simp [φ, hc₀, sq]⟩
  set c := ‖x - u • 1‖
  refine (continuous_φ x).norm.exists_forall_le_of_isBounded (0, 0) ?_
  simp only [φ, zero_smul, sub_zero, add_zero, norm_pow]
  refine ((Metric.isBounded_of_abs_le (2 * ‖x‖ ^ 2 / c)).prod
    (Metric.isBounded_of_abs_le (2 * ‖x‖ ^ 2 + 2 * ‖x‖ ^ 3 / c))).subset fun (a, b) hab ↦ ?_
  simp only [Set.mem_prod, Set.mem_setOf] at hab ⊢
  have ha : |a| ≤ 2 * ‖x‖ ^ 2 / c := a_bound hc₀ hu hab
  refine ⟨ha, ?_⟩
  rw [two_mul, add_assoc, ← sub_le_iff_le_add, ← sub_sub]
  calc |b| - ‖x‖ ^ 2 - 2 * ‖x‖ ^ 3 / c
  _ = |b| - ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 / c * ‖x‖ := by ring
  _ ≤ |b| - ‖x‖ ^ 2 - |a| * ‖x‖ := by gcongr
  _ = ‖b • (1 : F)‖ - ‖a • x‖ - ‖x ^ 2‖ := by rw [sub_right_comm, norm_smul a]; simp
  _ ≤ ‖b • 1 - a • x‖ - ‖x ^ 2‖ := by gcongr; exact norm_sub_norm_le ..
  _ ≤ ‖x ^ 2 - a • x + b • 1‖ := by rw [sub_add_comm]; exact norm_sub_le_norm_add ..
  _ ≤ ‖x‖ ^ 2 := hab

/-!
### The main result
-/

/-- If `F` is a normed `ℝ`-algebra with a multiplicative norm (and such that `‖1‖ = 1`),
e.g., a normed division ring, then every `x : F` is the root of a monic quadratic polynomial
with real coefficients. -/
lemma satisfies_quadratic_rel (x : F) : ∃ p : ℝ[X], IsMonicOfDegree p 2 ∧ aeval x p = 0 := by
  obtain ⟨z, h⟩ := min_ex_deg_two x
  suffices φ x z = 0 from ⟨_, isMonicOfDegree_sub_add_two z.1 z.2, by rwa [aeval_eq_φ]⟩
  by_contra! H
  set M := ‖φ x z‖
  have hM₀ : 0 ≤ M := norm_nonneg _
  -- use that `f x t` is constant to produce an inequality that is false for `c` large enough
  suffices |2 * (‖x‖ ^ 2 / √M + 1)| ≤ 2 * ‖x‖ ^ 2 / √M by
    rw [abs_of_pos <| by positivity, mul_div_assoc] at this
    linarith
  refine a_bound (x := x) (c := √M) (by positivity) (fun r ↦ ?_) (b := 0) ?_
  · rw [← sq_le_sq₀ (Real.sqrt_nonneg M) (norm_nonneg _), Real.sq_sqrt hM₀, ← norm_pow,
      Algebra.sub_smul_one_sq]
    convert h (2 * r, r ^ 2) using 4 <;> simp [two_mul, add_smul, _root_.smul_pow]
  · nth_rewrite 2 [show ‖x‖ ^ 2 = ‖x ^ 2 - (0 : ℝ) • x + (0 : ℝ) • 1‖ by simp]
    rw [is_const_norm_sq_sub_add h (norm_ne_zero_iff.mpr H) (2 * (‖x‖ ^ 2 / √M + 1), 0)]
    exact h (0, 0)

/-- A variant of the **Gelfand-Mazur Theorem** over `ℝ`:

If a field `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`. -/
theorem nonempty_algEquiv_or (F : Type*) [NormedField F] [NormedAlgebra ℝ F]:
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ IsIntegral.isAlgebraic ?_⟩
    obtain ⟨f, hf, hfx⟩ := satisfies_quadratic_rel x
    exact (hfx ▸ isIntegral_zero).of_aeval_monic hf.monic <| hf.natDegree_eq.trans_ne two_ne_zero
  exact _root_.Real.nonempty_algEquiv_or F

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

end GelfandMazur.Real

end Real
