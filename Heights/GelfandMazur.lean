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
and `‖p.aeval x‖` gets large when `p` has large coefficients (*), there will be some `p₀`
such that `‖p₀.aeval x‖` attains a minimum (see `GelfandMazur.exists_minimum_of_f`).
We assume that this is positive and derive a contradiction. Let `M := ‖p₀.aeval x‖ > 0`
be the minimal value.
Since every monic polynomial `f : ℝ[X]` of even degree can be written as a product
of monic polynomials of degree `2`
(see `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree`),
it follows that `‖f.aeval x‖ ≥ M^(f.natDegree / 2)`.

(*) This is actually somewhat more subtle. It is certainly true for `‖x - r‖` with `r : ℝ`.
If the minimum of this is zero, then the minimum for monic polynomials of degree `2`
will also be zero (and is attained on a one-dimensional subset). Otherwise, one can
indeed show that a bound on `‖x^2 - a•x + b•1‖` implies bounds on `|a|` and `|b|`.

Note that any monic polynomial of degree `2` over `ℝ` can be written in the form
`(X - C s)^2 + C t` with (unique) `s t : ℝ` (see `Polynomial.isMonicOfDegree_two_iff`).
The goal is to show that when `s` and `t` achieve the minimum `M` of `‖(x - s•1)^2 + t•1‖`,
and `M > 0`, then we can find some `ε > 0` (depending on `x`, `s`, `t`, and `M`)
such that `‖(x - (s+c)•1)^2 + t•1‖ = M` for all `c : ℝ` such that `|c| < ε`
(see `GelfandMazur.constant_on_open_interval_of_ne_zero`).
Then the set `S = {s' | ‖(x - s'•1)^2 + t•1‖ = M}` must be all of `ℝ` (as it is
closed, open, and nonempty). This will lead to a contradiction with the growth
of `‖(x - s'•1)^2 + t•1‖` as `|s'|` gets large.

To get there, the idea is to find a relation among polynomials of the following form,
where `n : ℕ` and `c : ℝ` is arbitrary.
```math
  (X^2+t)^n - c^n y_n(X) + c^{2n} = ((X-c)^2+t) z(X) \,,
```
where $y_n(X)$ has degree at most `n` and the norm of its value at a given `x : F`
can be bounded by a constant (`= 2`) times the `n`th power of another constant `C`;
then $z_n(c,X)$ must be monic of degree `2*(n-1)`. We define a suitable sequence
of polynomials `y x t n` below; the `z` polynomials (which depend on `t`, `c` and `n`)
will be implicit: we show that the polynomial on the left in the equation above
is divisible by $(X-c)^2+t$.

This (and the definition of `y`) is inspired by "taking norms from `ℂ` to `ℝ`"
in the proof above. Consider, for `c : ℝ`, `P t c := ((X-t*I•1)^n - c^n•1)*((X+t*I•1)^n - c^n•1)`;
this is in fact a polynomial with real coefficients. On the one hand, we can write
`P t c = (X^2+t^2•1)^n - c^n•((X-t*I•1)^n + (X+t*I•1)^n)) + |c|^(2*n)•1`,
where the middle term is a polynomial with real coefficients again that depends on `c`
only via the factor `c^n`. On the other hand,
`P t c = (X - (c+t*I)•1)*(X - (c-t*I)•1) * z = ((X-c•1)^2 + t^2•1) * z`,
where `z` is monic of degree `2*(n-1)`. Our definition of `y` is such that
`y x (t^2) n = (x-t*I•1)^n + (x+t*I•1)^n)`.

Evaluating at `x - s•1` and taking norms, this implies that
`‖(x-(s+c)•1)^2 + t‖ = ‖aeval (x-s•1) ((X^2+t)^n - c^n*(y n) + c^(2*n))‖ / ‖aeval (x-s•1) z‖`,
which is bounded by
`(M^n + |c|^n * (2*C^n) + |c|^(2*n)) / M^(n-1) = M * (1 + 2 * (|c|*C/M)^n + (|c|^2/M)^n)`.
If we take `c : ℝ` such that `|c| < min √M (M/C)`, then as `n` tends to infinity, we obtain that
`M ≤ ‖(x-(s+c)•1)^2 + t‖ ≤ M`, as desired.

It remains to define a suitable sequence `y` of polynomials. We set, for `t : ℝ`,
* `y t 0 := 2`, `y t 1 := 2*X`, `y t (n+2) := 2*X*(y t (n+1)) - (X^2+t)*(y t n)`
and we prove that
* `∀ t, ∀ n, (y t n).natDegree ≤ n` (`GelfandMazur.y_degree`)
* `∀ t c n, (X-c)^2+t ∣ (X^2+t)^n - c^n*(y x t n) + c^(2*n)` (`GelfandMazur.y_prop`)
* `∀ (x : F) t, ∃ C ≥ 0, ∀ n, ‖(y n).aeval x‖ ≤ 2*C^n` (`GelfandMazur.y_bound`)
which provides the necessary input.
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

variable {F : Type*} [NormedField F] [NormedAlgebra ℂ F]

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
  have hrel := geom_sum₂_mul X (C c) n
  set p := ∑ i ∈ Finset.range n, X ^ i * C c ^ (n - 1 - i)
  have hp : IsMonicOfDegree p (n - 1) := by
    have : IsMonicOfDegree (X ^ n - C c ^ n) n :=
      (isMonicOfDegree_X_pow ℂ n).sub <| by compute_degree!
    rw [← hrel, show n = n - 1 + 1 by omega] at this
    exact (isMonicOfDegree_X_sub_one c).of_mul_right this
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

/-- A version of the **Gelfand-Mazur Theorem** for fields that are normed `ℂ`-algebras. -/
theorem mainThm : Nonempty (ℂ ≃ₐ[ℂ] F) := by
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
### The sequence y and its properties
-/

section sequence_y

variable {R : Type*} [CommRing R]

open Polynomial

/-- The sequence `y t n` such that (formally) `y (t^2) n = (X-t*I•1)^n + (X+t*I•1)^n)`. -/
noncomputable
def y (t : R) : ℕ → R[X]
| 0 => 2
| 1 => 2 • X
| n + 2 => 2 * X * y t (n + 1) - (X ^ 2 + C t) * y t n

lemma y_degree (t : R) (n : ℕ) : (y t n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [y]
  | one => simp only [y]; compute_degree
  | more n ih₂ ih₁ =>
    simp only [y]
    compute_degree!
    constructor <;> linarith

lemma y_prop (t c : R) (n : ℕ) :
    (X - C c) ^ 2 + C t ∣ (X ^ 2 + C t) ^ n - c ^ n • y t n + C (c ^ (2 * n)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [pow_zero, y, one_smul, mul_zero, map_one]
    norm_num
  | one =>
    simp only [pow_one, y, nsmul_eq_mul, Nat.cast_ofNat, mul_one, map_pow, sub_sq, two_mul,
      smul_eq_C_mul]
    convert dvd_rfl using 1
    ring
  | more n ih₂ ih₁ =>
    simp only [y]
    replace ih₂ := ih₂.mul_left (- C c ^ 2 * (X ^ 2 + C t))
    replace ih₁ := ih₁.mul_left (C c * 2 * X)
    have ih₃ := dvd_mul_left ((X - C c) ^ 2 + C t) ((X ^ 2 + C t) ^ (n + 1) + C c ^ (2 * n + 2))
    convert ih₂.add ih₁ |>.add ih₃ using 1; clear ih₁ ih₂ ih₃
    rw [pow_add, pow_succ (X ^ 2 + C t) n]
    simp only [smul_eq_C_mul, map_mul, map_pow]
    ring

variable {F : Type*} [NormedField F] [Algebra R F]

/-- If `F` is a normed field that is an `R`-algebra, then for a given `x : F`, the norm
of gthe value of `y t n` at `x` is bounded by `2 * C ^ n` for some `C > 0`. -/
lemma y_bound (t : R) (x : F) : ∃ C > 0, ∀ n, ‖aeval x (y t n)‖ ≤ 2 * C ^ n := by
  suffices ∃ C ≥ 0, ∀ n, ‖aeval x (y t n)‖ ≤ 2 * C ^ n by
    obtain ⟨C, hC₀, hC⟩ := this
    refine ⟨C + 1, by positivity, fun n ↦ ?_⟩
    have H : 2 * C ^ n ≤ 2 * (C + 1) ^ n := by gcongr; linarith
    exact (hC n).trans H
  set a := ‖2 * x‖
  set b := ‖x ^ 2 + (algebraMap R F) t‖
  let C : ℝ := max (max ‖x‖ (2 * a)) (Real.sqrt (2 * b))
  have h₂ : ‖(2 : F)‖ ≤ 2 := by simpa using Nat.norm_cast_le (α := F) 2
  refine ⟨C, by positivity, fun n ↦ ?_⟩
  induction n using Nat.twoStepInduction with
  | zero => simpa [y] using h₂
  | one =>
    simp only [y, nsmul_eq_mul, Nat.cast_ofNat, map_mul, aeval_ofNat, aeval_X, norm_mul, pow_one]
    have : ‖x‖ ≤ C := le_sup_of_le_left <| le_max_left ..
    gcongr
  | more n ih₂ ih₁ =>
    simp only [y, map_sub, map_mul, aeval_ofNat, Nat.cast_ofNat, aeval_X, map_add, map_pow, aeval_C]
    calc ‖2 * x * aeval x (y t (n + 1)) - (x ^ 2 + algebraMap R F t) * aeval x (y t n)‖
    _ ≤ ‖2 * x * aeval x (y t (n + 1))‖ + ‖(x ^ 2 + algebraMap R F t) * aeval x (y t n)‖ :=
        norm_sub_le ..
    _ = ‖2 * x‖ * ‖aeval x (y t (n + 1))‖ + ‖x ^ 2 + algebraMap R F t‖ * ‖aeval x (y t n)‖ := by
        simp only [norm_mul]
    _ ≤ a * (2 * C ^ (n + 1)) + b * (2 * C ^ n) := by gcongr
    _ = (a * C + b) * (2 * C ^ n) := by ring
    _ ≤ (C ^ 2 / 2 + C ^ 2 / 2) * (2 * C ^ n) := by
        gcongr -- `a * C ≤ C ^ 2 / 2` and `b ≤ C ^ 2 / 2`
        · have : 2 * a ≤ C := le_sup_of_le_left <| le_max_right ..
          rw [le_div_iff₀' zero_lt_two, ← mul_assoc, sq]
          gcongr
        · have : √(2 * b) ≤ C := le_max_right ..
          rw [le_div_iff₀' zero_lt_two, ← Real.sq_sqrt (by positivity : 0 ≤ 2 * b)]
          gcongr
    _ = 2 * C ^ (n + 2) := by ring

end sequence_y

/-!
### The key step of the proof
-/

variable {F : Type*} [NormedField F] [NormedAlgebra ℝ F]

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

open Filter in
lemma tendsto_M {c C M : ℝ} (hC₀ : C > 0) (H₀ : 0 ≤ M) (hc : |c| < min (√M) (M / C))
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hC : ∀ n, f n ≤ 2 * C ^ n) :
    Tendsto (fun n : ℕ ↦ M * (1 + (|c| / M) ^ n * f n + (|c| ^ 2 / M) ^ n)) atTop (nhds M) := by
  rcases eq_or_lt_of_le H₀ with rfl | H₀
  · simp
  conv => enter [3, 1]; rw [show M = M * (1 + 0 + 0) by ring] -- preparation
  refine tendsto_const_nhds.mul <| (tendsto_const_nhds.add ?_).add  ?_
  · replace hC (n : ℕ) : (|c| / M) ^ n * f n ≤ 2 * (|c| / (M / C)) ^ n := by
      calc (|c| / M) ^ n * f n
      _ ≤ (|c| / M) ^ n * (2 * C ^ n) := by have := hC n; gcongr
      _ = _ := by rw [mul_left_comm, ← mul_pow]; congr 2; field_simp
    refine squeeze_zero (fun n ↦ by have := hf n; positivity) hC ?_
    conv => enter [3, 1]; rw [← mul_zero 2] -- preparation
    refine tendsto_const_nhds.mul <| tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
    rw [abs_of_nonneg (by positivity), div_lt_one (by positivity)]
    exact (lt_min_iff.mp hc).2
  · refine tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
    rw [abs_of_nonneg (by positivity), div_lt_one H₀, ← M.sq_sqrt H₀.le]
    have := (lt_min_iff.mp hc).1
    gcongr


/-- The key step in the proof: if `s` and `t` are real numbers minimizing `‖(x-s•1)^2 + t•1‖`,
and the minimal value is strictly positive, then for `s'` in some open interval around `s`,
`‖(x-s'•1)^2 + t•1‖` is constant. -/
lemma constant_on_open_interval_of_ne_zero (x : F) {s t : ℝ} (h₀ : f x t s ≠ 0)
    (h : ∀ s' t' : ℝ, f x t s ≤ f x t' s') :
    ∃ ε > 0, ∀ c : ℝ, |c| < ε → f x t (s + c) = f x t s := by
  obtain ⟨C, hC₀, hC⟩ := y_bound t (x - s •1)
  set M : ℝ := f x t s
  refine ⟨min M.sqrt (M / C), by positivity, fun c hc ↦ ?_⟩
  suffices ∀ n > 0, f x t (s + c) ≤
      M * (1 + (|c| / M) ^ n * ‖aeval (x - s • 1) (y t n)‖ + (|c| ^ 2 / M) ^ n) by
    -- (this is still true for `n = 0`, but would need a separate proof)
    refine (le_antisymm (h ..) <|
      ge_of_tendsto (tendsto_M hC₀ (norm_nonneg _) hc (fun _ ↦ norm_nonneg _) hC) ?_).symm
    exact Filter.Eventually.mono (Filter.Ioi_mem_atTop 0) this
  intro n hn
  -- use the divisibility relation satisfied by `y t n`
  obtain ⟨p, hrel⟩ := y_prop t c n
  have hp : IsMonicOfDegree p (2 * (n - 1)) := by
    refine IsMonicOfDegree.of_mul_left (isMonicOfDegree_sub_sq_add_two c t) ?_
    rw [← hrel, sub_add, show 2 + 2 * (n - 1) = 2 * n by omega]
    refine IsMonicOfDegree.sub ?_ ?_
    · exact ((isMonicOfDegree_X_pow ℝ 2).add_left <| by compute_degree!).pow _
    · have := y_degree t n
      compute_degree
      -- `(y t n).natDegree < 2 * n`
      omega
  apply_fun (‖aeval (x - s • 1) ·‖) at hrel -- evaluate at `x - s•1` and take norms
  simp only [map_pow, map_add, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, map_smul,
    map_mul, norm_mul] at hrel
  replace hrel := (hrel.symm.trans_le (norm_add_le ..)).trans (add_le_add_right (norm_sub_le ..) _)
  rw [norm_pow, sub_sub, ← add_smul] at hrel
  have hz : M ^ (n - 1) ≤ ‖aeval (x - s • 1) p‖ := le_aeval_of_isMonicOfDegree x h hp s
  have HH : f x t (s + c) * M ^ (n - 1) ≤
      M ^ n + |c| ^ n * ‖aeval (x - s • 1) (y t n)‖ + (|c| ^ 2) ^ n := by
    calc f x t (s + c) * M ^ (n - 1)
    _ ≤ f x t (s + c) * ‖aeval (x - s • 1) p‖ := by gcongr
    _ ≤ f x t s ^ n + ‖c ^ n • aeval (x - s • 1) (y t n)‖ + ‖(c • 1) ^ (2 * n)‖ := hrel
    _ = M ^ n + |c| ^ n * ‖aeval (x - s • 1) (y t n)‖ + (|c| ^ 2) ^ n := by
      simp [M, norm_smul, pow_mul]
  convert (le_div_iff₀ (by positivity)).mpr HH using 1
  field_simp
  -- M * (?e * M ^ (n - 1)) = ?e * M ^ n
  rw [mul_comm M, mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]

/-!
### Existence of a minimizing monic polynomial of degree 2
-/

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
  _ ≤ ‖x ^ 2 - a • x + b • 1‖ := by rw [sub_add_comm]; exact norm_sub_le_norm_add ..
  _ ≤ ‖x‖ ^ 2 := hab

/-- There are real numbers `s` and `t` such that `‖(x - s • 1) ^ 2 + t • 1‖` is minimal. -/
lemma exists_minimum_of_f (x : F) : ∃ s t : ℝ, ∀ s' t' : ℝ, f x t s ≤ f x t' s' := by
  obtain ⟨a, b, hab⟩ := min_ex_deg_two x
  refine ⟨a / 2, b - (a / 2) ^ 2, fun s' t' ↦ ?_⟩
  convert hab (2 * s') (s' ^ 2 + t') using 2 <;>
  { simp only [sub_sq, Algebra.mul_smul_comm, mul_one, _root_.smul_pow, one_pow, two_mul]
    module }

/-!
### The main result
-/

lemma f_is_constant {x : F} {s t : ℝ} (hst : ∀ (s' t' : ℝ), f x t s ≤ f x t' s')
    (H : ∀ (s t : ℝ), f x t s ≠ 0) (c : ℝ) :
    f x t c = f x t s := by
  suffices {c | f x t c = f x t s} = Set.univ by simpa only [← this] using Set.mem_univ c
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩ <|
    Set.nonempty_of_mem rfl
  refine isOpen_iff_forall_mem_open.mpr fun c hc ↦ ?_
  simp only [Set.mem_setOf_eq] at hc
  obtain ⟨ε, hε₀, hε⟩ :=
    constant_on_open_interval_of_ne_zero x (H c t) (fun s' t' ↦ hc ▸ hst s' t')
  refine ⟨Set.Ioo (c - ε) (c + ε), fun u hu ↦ ?_, isOpen_Ioo, ?_⟩
  · simp only [Set.mem_setOf, ← hc]
    convert hε (u - c) ?_
    · abel
    · simp only [Set.mem_Ioo] at hu
      exact abs_sub_lt_iff.mpr ⟨sub_left_lt_of_lt_add hu.2, sub_lt_comm.mp hu.1⟩
  · exact Set.mem_Ioo.mpr ⟨sub_lt_self c hε₀, lt_add_of_pos_right c hε₀⟩

/-- Every `x : F` is the root of a monic quadratic polynomial with real coefficients. -/
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
  set a := f x t s     -- convenient abbreviations
  set b := ‖x - s • 1‖
  have hh (c : ℝ) (hc : 0 ≤ c) : (c - b) ^ 2 - b ^ 2 ≤ 2 * a := by
    calc (c - b) ^ 2 - b ^ 2
    _ = (c - 2 * b) * c := by ring
    _ ≤ ‖c • 1 - 2 * (x - s • 1)‖ * c := by
        gcongr
        convert norm_sub_norm_le ..
        · simp [abs_of_nonneg hc]
        · simp [b]
    _ = ‖(c • 1 - 2 * (x - s • 1)) * (c • 1)‖ := by
        rw [norm_mul, Algebra.norm_smul_one_eq_abs, abs_of_nonneg hc]
    _ = ‖(x - s • 1) ^ 2 + t • 1 - ((x - (s + c) • 1) ^ 2 + t • 1)‖ := by
        rw [norm_sub_rev, add_smul]
        congr 1
        ring
    _ ≤ ‖(x - s • 1) ^ 2 + t • 1‖ + ‖((x - (s + c) • 1) ^ 2 + t • 1)‖ := norm_sub_le ..
    _ = 2 * a := by rw [two_mul a]; exact congrArg (a + ·) <| f_is_constant hst H (s + c)
  -- now get the contradiction by specializing to a suitable value of `c`
  specialize hh ((2 * a + b ^ 2).sqrt + b + 1) (by positivity)
  rw [tsub_le_iff_right, show _ + b + 1 - b = _ + 1 by abel, add_sq, Real.sq_sqrt (by positivity)]
    at hh
  linarith [show 0 ≤ √(2 * a + b ^ 2) by positivity]

/-- A variant of the **Gelfand-Mazur Theorem** over `ℝ`:

If `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`. -/
theorem nonempty_algEquiv_or : Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
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
