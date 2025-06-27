import Heights.IsMonicOfDegree

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

A version of the result exists as `NormedRing.algEquivComplexOfComplete` (which gives
the isomorphism) in Mathlib (with weaker assumptions and a different proof).

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
in a separate file).

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

Note that any monic polynomial of degree `2` over `ℝ` can be written in the form
`(X - C s)^2 + C t` with (unique) `s t : ℝ` (see `Polynomial.isMonicOfDegree_two_iff`).
The goal is to show that when `s` and `t` achieve the minimum `M` of `‖(x - s•1)^2 + t•1‖`,
and `M > 0`, then we can find some `ε > 0` (depending on `x`, `s`, `t`, and `M`)
such that `‖(x - (s+c)•1)^2 + t•1‖ = M` for all `c : ℝ` such that `|c| < ε`
(see `GelfandMazur.constant_on_nhd_of_ne_zero`).
Then the set `S = {s' | ‖(x - s'•1)^2 + t•1‖ = M}` must be all of `ℝ` (as it is
closed, open, and nonempty). This will lead to a contradiction with the growth
of `‖(x - s'•1)^2 + t•1‖` as `|s'|` gets large.

To get there, the idea is, similarly to the complex case, to use the following relation,
where `n : ℕ` and `c : ℝ` is arbitrary.
```math
  (X^2+t)^n - (c(2X-c))^n = ((X-c)^2+t) p(t,c,n; \, X) \,,
```
where $p(t,c,n;\,X)$ is a monic polynomial of degree `2*(n-1)`, which will be left
implicit: we show that the polynomial on the left in the equation above
is divisible by $(X-c)^2+t$.

For given `x : F`, we then have that `‖c•(2*x-c•1)‖ < M` for small
enough `c : ℝ`. Evaluating the relation above at `x - s•1` and taking norms, this implies that
`‖(x-(s+c)•1)^2 + t‖ = ‖aeval (x-s•1) ((X^2+t)^n - (c•(2*X-c•1))^n)‖ / ‖aeval (x-s•1) p‖`,
which is bounded by
`(M^n + ‖c•(2*(x-s•1)-c•1)‖^n) / M^(n-1) = M * (1 + (‖c•(2*(x-s•1)-c•1)‖/M)^n)`.
So, letting `n` tend to infinity, we obtain that
`M ≤ ‖(x-(s+c)•1)^2 + t‖ ≤ M`, as desired.
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
    ∃ x, ∀ y, f x ≤ f y := by
  refine hf.exists_forall_le' (x₀ := x₀) ?_
  have hU : {x : β | f x₀ < f x} ∈ Filter.cocompact β := by
    refine Filter.mem_cocompact'.mpr ⟨_, ?_, fun ⦃_⦄ a ↦ a⟩
    simp only [Set.compl_setOf, not_lt]
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) (by fun_prop)) h
  filter_upwards [hU] with x hx
  exact hx.le

end Continuous

namespace Algebra

lemma sub_smul_one_sq {A R : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) (r : R) :
    (x - r • 1) ^ 2 = x ^ 2 - 2 * x * (r • 1) + (r • 1) ^ 2 := by
    -- `sub_sq` assumes `CommRing A`
    simp [sq, sub_mul, mul_sub, smul_sub, smul_smul, two_mul, ← sub_sub, ← sub_add]

section Real

variable {A : Type*} [SeminormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

@[simp]
lemma norm_smul_one_eq_abs (x : ℝ) : ‖x • (1 : A)‖ = |x| := by
  rw [← Algebra.algebraMap_eq_smul_one, norm_algebraMap', Real.norm_eq_abs]

@[simp]
lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : A)‖ = (ofNat(n) : ℝ) := by
  rw [← map_ofNat (algebraMap ℝ A) n, norm_algebraMap', Real.norm_eq_abs, n.abs_ofNat]

end Real

section Complex

variable {A : Type*} [SeminormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]

@[simp]
lemma norm_smul_one_eq_norm (z : ℂ) : ‖z • (1 : A)‖ = ‖z‖ := by
  rw [← Algebra.algebraMap_eq_smul_one, norm_algebraMap']

end Complex

end Algebra

namespace Polynomial

@[simp]
lemma aeval_ofNat {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (n : ℕ)
    [n.AtLeastTwo] :
    (Polynomial.aeval (R := R) x) (ofNat(n) : R[X]) = n :=
  aeval_natCast x _

end Polynomial

end auxiliary


namespace GelfandMazur

namespace Complex

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

variable {F : Type*} [NormedRing F] [NormOneClass F] [NormMulClass F] [NormedAlgebra ℂ F]

open Polynomial

lemma le_aeval_of_isMonicOfDegree (x : F) {M : ℝ} (hM : 0 ≤ M) (h : ∀ z' : ℂ, M ≤ ‖x - z' • 1‖)
    {p : ℂ[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (c : ℂ) :
    M ^ n ≤ ‖aeval (x - c • 1) p‖ := by
  induction n generalizing p with
  | zero => simp [isMonicOfDegree_zero.mp hp]
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
  field_simp
  -- `M * (?e * M ^ (n - 1)) = ?e * M ^ n`, not solved by `ring`
  rw [mul_comm M, mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]

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

/-- A version of the **Gelfand-Mazur Theorem** for fields/division rings
that are normed `ℂ`-algebras. -/
theorem mainThm [FaithfulSMul ℂ F] : Nonempty (ℂ ≃ₐ[ℂ] F) := by
  suffices ∀ x : F, ∃ z : ℂ, ‖x - z • 1‖ = 0 by
    let e : ℂ →ₐ[ℂ] F := AlgHom.mk' (algebraMap ℂ F) (algebraMap.coe_smul ℂ ℂ F)
    refine ⟨AlgEquiv.ofBijective e ⟨FaithfulSMul.algebraMap_injective ℂ F, fun x ↦ ?_⟩⟩
    obtain ⟨z, hz⟩ := this x
    refine ⟨z, ?_⟩
    rw [AlgHom.coe_mk', Algebra.algebraMap_eq_smul_one, eq_comm, ← sub_eq_zero]
    exact norm_eq_zero.mp hz
  intro x
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

end Complex

/-!
### The key step of the proof
-/

variable {F : Type*} [NormedRing F] [NormOneClass F] [NormMulClass F] [NormedAlgebra ℝ F]

open Polynomial

/-- We abbreviate the function we are minimizing as `f x : ℝ → ℝ → ℝ`.

In the crucial part of the proof, we will in fact consider `f x t` for some fixed `t : ℝ`
and show that it is constant (unless `f x` takes the value zero somewhere). -/
abbrev f (x : F) (t s : ℝ) : ℝ := ‖(x - s • 1) ^ 2 + t • 1‖

lemma le_aeval_of_isMonicOfDegree (x : F) {s t : ℝ} (h : ∀ s' t' : ℝ, f x t s ≤ f x t' s')
    {p : ℝ[X]} {n : ℕ} (hp : IsMonicOfDegree p (2 * n)) (c : ℝ) :
    f x t s ^ n ≤ ‖aeval (x - c • 1) p‖ := by
  induction n generalizing p with
  | zero =>
    simp only [mul_zero, isMonicOfDegree_zero] at hp
    simp [hp]
  | succ n ih =>
    rw [mul_add, mul_one] at hp
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := hp.eq_mul_isMonicOfDegree_two_isMonicOfDegree
    obtain ⟨s', t', hst⟩ := isMonicOfDegree_two_iff.mp hf₁
    have H' (y : F) : aeval y ((X - C s') ^ 2 + C t') = (y - s' • 1) ^ 2 + t' • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, hst, H', sub_sub, ← add_smul]
    exact mul_le_mul (ih hf₂) (h (c + s') t') (norm_nonneg _) (norm_nonneg _)

/-- The key step in the proof: if `s` and `t` are real numbers minimizing `‖(x-s•1)^2 + t•1‖`,
and the minimal value is strictly positive, then for `s'` in some open interval around `s`,
`‖(x-s'•1)^2 + t•1‖` is constant. -/
lemma constant_on_nhd_of_ne_zero (x : F) {s t : ℝ} (h₀ : f x t s ≠ 0)
    (h : ∀ s' t' : ℝ, f x t s ≤ f x t' s') :
    ∃ U ∈ nhds 0, ∀ c ∈ U, f x t (s + c) = f x t s := by
  set M : ℝ := f x t s
  have hM₀ : 0 < M := by positivity
  let φ (c : ℝ) : ℝ := ‖aeval (x - s • 1) (C c * (2 * X - C c))‖
  have hφ_def (c : ℝ) : φ c = ‖aeval (x - s • 1) (C c * (2 * X - C c))‖ := rfl
  obtain ⟨U, hU₀, hU⟩ : ∃ U ∈ nhds 0, ∀ c ∈ U, φ c < M := by
    have hφ : Continuous φ := by simp [φ]; fun_prop
    replace hφ := (show φ 0 = 0 by simp [φ]) ▸ hφ.tendsto 0
    refine ⟨φ ⁻¹' {r : ℝ | r < M}, hφ ?_, fun c hc ↦ by simpa using hc⟩
    exact isOpen_lt (by fun_prop) (by fun_prop) |>.mem_nhds (by simpa)
  refine ⟨U, hU₀, fun c hc ↦ ?_⟩
  suffices ∀ n > 0, f x t (s + c) ≤ M * (1 + (φ c / M) ^ n) by
    refine (le_antisymm (h ..) ?_).symm
    refine ge_of_tendsto ?_ <| Filter.Eventually.mono (Filter.Ioi_mem_atTop 0) this
    conv => enter [3, 1]; rw [show M = M * (1 + 0) by ring] -- preparation
    refine tendsto_const_nhds.mul <| tendsto_const_nhds.add <|
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
    rw [abs_of_nonneg (by positivity)]
    exact (div_lt_one hM₀).mpr <| hU c hc
  intro n hn
  have hdvd : (X - C c) ^ 2 + C t ∣ (X ^ 2 + C t) ^ n - (C c * (2 * X - C c)) ^ n := by
    convert sub_dvd_pow_sub_pow (X ^ 2 + C t) (C c * (2 * X - C c)) n using 1
    ring
  have H₁ : IsMonicOfDegree ((X ^ 2 + C t) ^ n) (2 * n) :=
    ((isMonicOfDegree_X_pow ℝ 2).add_left (by compute_degree!)).pow n
  have H₂ : ((C c * (2 * X - C c)) ^ n).natDegree < 2 * n := by compute_degree; omega
  obtain ⟨p, hp, hrel⟩ := H₁.of_dvd_sub (by omega) (isMonicOfDegree_sub_sq_add_two c t) H₂ hdvd
  rw [show 2 * n - 2 = 2 * (n - 1) by omega] at hp
  rw [← sub_eq_iff_eq_add, eq_comm, mul_comm] at hrel
  apply_fun (‖aeval (x - s • 1) ·‖) at hrel -- evaluate at `x - s•1` and take norms
  rw [map_mul, norm_mul, map_sub] at hrel
  replace hrel := hrel.trans_le (norm_sub_le ..)
  simp only [map_pow, norm_pow, ← hφ_def, map_add, map_sub, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, sub_sub, ← add_smul] at hrel
  have hp' : M ^ (n - 1) ≤ ‖(aeval (x - s • 1)) p‖ := le_aeval_of_isMonicOfDegree x h hp s
  suffices f x t (s + c) * M ^ (n - 1) ≤ M ^ n + (φ c) ^ n by
    convert (le_div_iff₀ (by positivity)).mpr this using 1
    field_simp
    -- M * (?e * M ^ (n - 1)) = ?e * M ^ n
    rw [mul_comm M, mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
  exact mul_le_mul_of_nonneg_left hp' (norm_nonneg _) |>.trans hrel

/-!
### Existence of a minimizing monic polynomial of degree 2
-/

omit [NormMulClass F] in
lemma min_ex_deg_one (x : F) : ∃ u : ℝ, ∀ r : ℝ, ‖x - u • 1‖ ≤ ‖x - r • 1‖ := by
  have hf : Continuous fun r : ℝ ↦ ‖x - r • 1‖ := by fun_prop
  refine hf.exists_forall_le_of_isBounded 0 <| (2 * ‖x‖).isBounded_of_abs_le.subset fun r hr ↦ ?_
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

lemma min_ex_deg_two (x : F) :
    ∃ a b : ℝ, ∀ a' b' : ℝ, ‖x ^ 2 - a • x + b • 1‖ ≤ ‖x ^ 2 - a' • x + b' • 1‖ := by
  obtain ⟨u, hu⟩ := min_ex_deg_one x
  rcases eq_or_lt_of_le (norm_nonneg (x - u • 1)) with hc₀ | hc₀
  · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hc₀
    exact ⟨u, 0, fun s' t' ↦ by simp [hc₀, _root_.smul_pow, sq]⟩
  set c := ‖x - u • 1‖ with hc
  suffices ∃ z : ℝ × ℝ, ∀ z' : ℝ × ℝ, ‖x ^ 2 - z.1 • x + z.2 • 1‖ ≤ ‖x ^ 2 - z'.1 • x + z'.2 • 1‖ by
    obtain ⟨z, h⟩ := this
    exact ⟨z.1, z.2, fun a' b' ↦ h (a', b')⟩
  have hf : Continuous fun z : ℝ × ℝ ↦ ‖x ^ 2 - z.1 • x + z.2 • 1‖ := by fun_prop
  refine hf.exists_forall_le_of_isBounded (0, 0) ?_
  simp only [zero_smul, sub_zero, add_zero, norm_pow]
  refine ((2 * ‖x‖ ^ 2 / c).isBounded_of_abs_le.prod
            (2 * ‖x‖ ^ 2 + 2 * ‖x‖ ^ 3 / c).isBounded_of_abs_le).subset fun (a, b) hab ↦ ?_
  simp only [Set.mem_prod, Set.mem_setOf] at hab ⊢
  have ha : |a| ≤ 2 * ‖x‖ ^ 2 / c := a_bound hc₀ hu hab
  refine ⟨ha, ?_⟩
  rw [two_mul, add_assoc, ← sub_le_iff_le_add, ← sub_sub]
  calc |b| - ‖x‖ ^ 2 - 2 * ‖x‖ ^ 3 / c
  _ ≤ |b| - ‖x‖ ^ 2 - |a| * ‖x‖ := by
      rw [show 2 * ‖x‖ ^ 3 / c = 2 * ‖x‖ ^ 2 / c * ‖x‖ by ring]
      gcongr
  _ = ‖b • (1 : F)‖ - ‖a • x‖ - ‖x ^ 2‖ := by rw [sub_right_comm, norm_smul a]; simp
  _ ≤ ‖b • 1 - a • x‖ - ‖x ^ 2‖ := by gcongr; exact norm_sub_norm_le ..
  _ ≤ ‖x ^ 2 - a • x + b • 1‖ := by rw [sub_add_comm]; exact norm_sub_le_norm_add ..
  _ ≤ ‖x‖ ^ 2 := hab

/-- There are real numbers `s` and `t` such that `‖(x - s • 1) ^ 2 + t • 1‖` is minimal. -/
lemma exists_minimum_of_f (x : F) : ∃ s t : ℝ, ∀ s' t' : ℝ, f x t s ≤ f x t' s' := by
  obtain ⟨a, b, hab⟩ := min_ex_deg_two x
  refine ⟨a / 2, b - (a / 2) ^ 2, fun s' t' ↦ ?_⟩
  convert hab (2 * s') (s' ^ 2 + t') using 2 <;>
  { simp only [Algebra.sub_smul_one_sq, Algebra.mul_smul_comm, mul_one, _root_.smul_pow, one_pow,
      two_mul]
    module }

/-!
### The main result
-/

lemma f_is_constant {x : F} {s t : ℝ} (hst : ∀ (s' t' : ℝ), f x t s ≤ f x t' s')
    (H : ∀ (s t : ℝ), f x t s ≠ 0) (c : ℝ) :
    f x t c = f x t s := by
  suffices {c | f x t c = f x t s} = Set.univ by simpa only [← this] using Set.mem_univ c
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩ <| Set.nonempty_of_mem rfl
  refine isOpen_iff_forall_mem_open.mpr fun c hc ↦ ?_
  simp only [Set.mem_setOf] at hc
  obtain ⟨U, hU₀, hU⟩ := constant_on_nhd_of_ne_zero x (H c t) (fun s' t' ↦ hc ▸ hst s' t')
  obtain ⟨ε, hε₀, hε⟩ := Metric.mem_nhds_iff.mp hU₀
  refine ⟨Metric.ball c ε, fun u hu ↦ ?_, Metric.isOpen_ball, Metric.mem_ball_self hε₀⟩
  rw [show u = c + (u - c) by abel] at hu ⊢
  rw [add_mem_ball_iff_norm, ← mem_ball_zero_iff] at hu
  simpa only [Set.mem_setOf] using hc ▸ hU _ (hε hu)

/-- If `F` is a normed `ℝ`-algebra with a multiplicative norm (and such that `‖1‖ = 1`),
e.g., a normed division ring, then every `x : F` is the root of a monic quadratic polynomial
with real coefficients. -/
lemma satisfies_quadratic_rel (x : F) : ∃ p : ℝ[X], IsMonicOfDegree p 2 ∧ aeval x p = 0 := by
  suffices ∃ s t : ℝ, f x t s = 0 by
    obtain ⟨s, t, hst⟩ := this
    refine ⟨_, isMonicOfDegree_sub_sq_add_two s t, ?_⟩
    simpa [Algebra.algebraMap_eq_smul_one] using hst
  obtain ⟨s, t, hst⟩ := exists_minimum_of_f x
  rcases eq_or_ne (f x t s) 0 with h₀ | h₀
  · exact ⟨s, t, h₀⟩ -- minimum is zero --> OK!
  -- now we assume the minimum is nonzero and derive a contradiction
  by_contra! H
  -- use that `f x t` is constant to produce an inequality that is false for `c` large enough
  suffices |2 * (‖x‖ ^ 2 / (f x t s).sqrt + 1)| ≤ 2 * ‖x‖ ^ 2 / (f x t s).sqrt by
    rw [abs_of_pos <| by positivity, mul_div_assoc] at this
    linarith
  have H₁ (u v : ℝ) : ‖x ^ 2 - (2 * u) • x + (u ^ 2 + v) • 1‖ = f x v u := by
    congr 1
    simp only [Algebra.sub_smul_one_sq, _root_.smul_pow, one_pow, Algebra.mul_smul_comm, two_mul,
      mul_one]
    module
  have H₂ (c : ℝ) : ‖x ^ 2 - (2 * c) • x + (c ^ 2 + t) • 1‖ ≤ ‖x‖ ^ 2 := by
    simpa [H₁, show ‖x‖ ^ 2 = f x 0 0 by simp [f], f_is_constant hst H] using hst 0 0
  refine a_bound (c := (f x t s).sqrt) (by positivity) (fun r ↦ ?_) (H₂ _)
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), Real.sq_sqrt (norm_nonneg _), ← norm_pow]
  convert hst r 0
  simp

/-- A variant of the **Gelfand-Mazur Theorem** over `ℝ`:

If a field `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`. -/
theorem nonempty_algEquiv_or {F : Type*} [NormedField F] [NormedAlgebra ℝ F]:
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ IsIntegral.isAlgebraic ?_⟩
    obtain ⟨f, hf, hfx⟩ := satisfies_quadratic_rel x
    exact (hfx ▸ isIntegral_zero).of_aeval_monic hf.monic <| hf.natDegree_eq.trans_ne two_ne_zero
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
