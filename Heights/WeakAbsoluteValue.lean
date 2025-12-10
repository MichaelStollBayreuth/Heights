import Mathlib

/-!
# Weak absolute values

We show that (`ℝ`-valued) "weak" absolute values are absolute values.

A weak absolute value `v` satisfies `v (x + y) ≤ 2 * max (v x) (v y)` in place of the standard
triangle inequality. The main result here is that this implies the triangle inequality.
-/

/-!
### Auxiliary results
-/

namespace Real

-- [Mathlib.Analysis.SpecialFunctions.Pow.Real]
lemma max_map_rpow {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    max (x ^ c) (y ^ c) = max x y ^ c := by
  lift x to NNReal using hx
  lift y to NNReal using hy
  exact_mod_cast ((NNReal.monotone_rpow_of_nonneg hc).map_sup ..).symm

open Filter in
lemma le_of_forall_pow_le_mul_pow {a b x y : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : ∀ᶠ (N : ℕ) in atTop, x ^ N ≤ (a * N + b) * y ^ N) :
    x ≤ y := by
  by_contra!
  let c := y / x
  have hc₀ : 0 ≤ c := by positivity
  have hc₁ : c < 1 := (div_lt_one <| by grind).mpr this
  conv at h =>
    enter [1, N]
    rw [show y = c * x from (div_mul_cancel₀ y <| by grind).symm, mul_pow, ← mul_assoc,
      le_mul_iff_one_le_left <| pow_pos (by grind) N]
  suffices Tendsto (fun (N : ℕ) ↦ (a * N + b) * c ^ N) atTop (nhds 0) by
    obtain ⟨n, hn⟩ := eventually_atTop.mp h
    obtain ⟨m, hm⟩ := NormedAddCommGroup.tendsto_atTop.mp this 1 zero_lt_one
    conv at hm =>
      enter [n]
      rw [sub_zero, norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith only [hn (max m n) (le_max_right ..), hm (max m n) (le_max_left ..)]
  have hc₁' : ‖c‖ < 1 := by rwa [norm_eq_abs, abs_of_nonneg hc₀]
  refine (summable_norm_mul_geometric_of_norm_lt_one' hc₁' (k := 2) ?_).of_norm.tendsto_atTop_zero
  refine Asymptotics.isBigO_atTop_iff_eventually_exists.mpr ?_
  filter_upwards [Ici_mem_atTop 1] with n hn
  refine ⟨a + b, fun m hm ↦ ?_⟩
  rw [Nat.cast_pow, norm_eq_abs, abs_of_nonneg (by positivity), norm_eq_abs, abs_sq, add_mul]
  gcongr
  · exact_mod_cast Int.le_self_sq m -- why does this not exist for `ℕ`?
  · exact le_mul_of_one_le_right hb <| one_le_pow₀ (by norm_cast; grind)

end Real

namespace Finset

variable {α : Type*} [SemilatticeSup α]

/-- Write the maximum of `f` over `range (m + n)` as the maximum of two similar terms. -/
lemma sup'_range_eq_max {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (f : ℕ → α) :
    (range (m + n)).sup' (nonempty_range_iff.mpr <| by grind) f =
      max ((range m).sup' (nonempty_range_iff.mpr hm) f)
       ((range n).sup' (nonempty_range_iff.mpr hn) (fun i ↦ f (m + i))) := by
  have : range (m + n) = range m ∪ Ico m (m + n) := by
    rw [range_eq_Ico]
    exact (Ico_union_Ico_eq_Ico m.zero_le (m.le_add_right n)).symm
  simp_rw [this]
  have H : (Ico m (m + n)).Nonempty := by grind [nonempty_Ico]
  rw [sup'_union (by grind) H]
  congr 1
  -- to make `rw` work
  change sup' _ _ (f ∘ id) = sup' _ _ (f ∘ (m + ·))
  rw [sup'_comp_eq_image (f := fun i ↦ m + i), sup'_comp_eq_image H]
  simp only [image_id]
  refine sup'_congr H ?_ fun i hi ↦ rfl
  simp only [range_eq_Ico, image_add_left_Ico, add_zero]

end Finset

/-!
### Weak absolute values

A "weak" (`ℝ`-valued) absolute value on a semiring `R` is a function `v : R → ℝ` such that
* `∀ x, 0 ≤ v x`,
* `∀ x, v x = 0 ↔ x = 0`,
* `∀ x y, v (x * y) = v x * v y`,
* `∀ x y, v (x + y) ≤ 2 * max (v x) (v y)`.
The last of these is a weaker form of the triangle inequality `v (x + y) ≤ v x + v y`.

Our goal is to show that such a `v` is actually an absolute value, i.e., `v` satisfies
the triangle inequality.
-/

namespace AbsoluteValue

section weak

-- Set up the data of a "weak absolute value" on a semiring `R`.
variable {R : Type*} [CommSemiring R] {v : R → ℝ} (hm : ∀ x y, v (x * y) = v x * v y)
  (hn : ∀ x, 0 ≤ v x) (h₀ : ∀ x, v x = 0 ↔ x = 0) (ha : ∀ x y, v (x + y) ≤ 2 * max (v x) (v y))

include hm in
lemma abv_one_sq_eq : v 1 ^ 2 = v 1 :=
  calc
  _ = v 1 * v 1 := by rw [sq]
  _ = v (1 * 1) := (hm 1 1).symm
  _ = v 1 := by rw [mul_one]

include hm in
lemma abv_one_le : v 1 ≤ 1 := by
  by_contra! h
  rcases eq_zero_or_one_of_sq_eq_self (abv_one_sq_eq hm) with h' | h' <;> linarith only [h, h']

include hn h₀ ha

open Finset in
lemma abv_finsetSum_le_mul_max (f : ℕ → R) {N : ℕ} (hN : 0 < N) :
    v (∑ i ∈ range N, f i) ≤
      2 * N * (range N).sup' (nonempty_range_iff.mpr hN.ne') fun i ↦ v (f i) := by
  have key (f : ℕ → R) (n : ℕ) : v (∑ i ∈ range (2 ^ n), f i) ≤
      2 ^ n * (range (2 ^ n)).sup' (nonempty_range_iff.mpr n.two_pow_pos.ne') fun i ↦ v (f i) := by
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      have H₁ : 2 ^ n ≤ 2 ^ (n + 1) := by grind
      rw [← sum_range_add_sum_Ico f H₁, sum_Ico_eq_sum_range,
        show 2 ^ (n + 1) - 2 ^ n = 2 ^ n by grind, pow_succ', mul_assoc]
      grw [ha]
      gcongr (2 * ?_)
      have hnr := nonempty_range_iff.mpr n.two_pow_pos.ne'
      have : (range (2 ^ (n + 1))).sup' (by grind) (fun i ↦ v (f i)) =
          max ((range (2 ^ n)).sup' hnr (fun i ↦ v (f i)))
            ((range (2 ^ n)).sup' hnr fun i ↦ v (f (2 ^ n + i))) := by
        have Hn : 2 ^ n ≠ 0 := NeZero.ne _
        convert sup'_range_eq_max Hn Hn (v ∘ f) using 3
        grind
      rw [this, mul_max_of_nonneg _ _ (mod_cast (2 ^ n).zero_le)]
      gcongr <;> exact ih _
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, 2 ^ m ≤ N ∧ N < 2 ^ (m + 1) :=
    ⟨N.log2, (Nat.log2_eq_iff <| Nat.ne_zero_of_lt hN).mp rfl⟩
  let g i := if i < N then f i else 0
  have hg : ∑ i ∈ range N, f i = ∑ i ∈ range (2 ^ (m + 1)), g i := by
    rw [eventually_constant_sum (by grind) hm₂.le]
    exact sum_congr rfl fun i hi ↦ by simp [g, mem_range.mp hi]
  rw [hg]
  grw [key]
  gcongr
  · exact le_sup'_of_le _ (by grind) <| hn (g 0)
  · rw [pow_succ']
    gcongr
    exact_mod_cast hm₁
  · refine sup'_le (by grind) _ fun i hi ↦ ?_
    simp only [g]
    split_ifs with h
    · exact le_sup' (fun i ↦ v (f i)) (mem_range.mpr h)
    · rw [(h₀ _).mpr rfl]
      exact le_sup'_of_le _ (mem_range.mpr hN) <| hn (f 0)

include hm

lemma abv_natCast_le (n : ℕ) : v n ≤ 2 * n := by
  rcases n.eq_zero_or_pos with rfl | hn₀
  · simp [(h₀ 0).mpr rfl]
  rw [show (n : R) = ∑ i ∈ Finset.range n, 1 by simp]
  refine (abv_finsetSum_le_mul_max hn h₀ ha _ hn₀).trans ?_
  simp only [Finset.sup'_const]
  grw [abv_one_le hm]
  exact (mul_one _).le

variable [Nontrivial R]

omit hn ha in
lemma abv_one : v 1 = 1 :=
  (eq_zero_or_one_of_sq_eq_self (abv_one_sq_eq hm)).resolve_left <| (h₀ 1).not.mpr one_ne_zero

omit hn ha in
lemma abv_pow (x : R) (n : ℕ) : v (x ^ n) = v x ^ n := by
  induction n with
  | zero => simp [abv_one hm h₀]
  | succ n ih => rw [pow_succ, hm, ih, ← pow_succ]

open Filter Topology Finset in
/-- The main result: a weak absolute value satisfies the triangle inequality. -/
lemma add_le_add_of_add_le_two_mul_max (x y : R) : v (x + y) ≤ v x + v y := by
  have hx : 0 ≤ v x := hn x
  have hy : 0 ≤ v y := hn y
  have key (N : ℕ) : v (x + y) ^ N ≤ 2 * (N + 1) * (2 * (v x + v y) ^ N) := by
    have hN : (range (N + 1)).Nonempty := by simp
    rw [← abv_pow hm h₀, add_pow x y]
    refine (abv_finsetSum_le_mul_max hn h₀ ha _ N.zero_lt_succ).trans ?_
    have H i (hi : i ∈ range (N + 1)) :
        v (x ^ i * y ^ (N - i) * N.choose i) ≤ 2 * (v x ^ i * v y ^ (N - i) * N.choose i) := by
      simp only [hm, abv_pow hm h₀]
      rw [mul_comm 2, mul_assoc (v x ^ i * v y ^ (N - i)), mul_comm _ 2]
      gcongr (_ * ?_)
      exact abv_natCast_le hm hn h₀ ha _
    push_cast
    gcongr
    refine (sup'_mono_fun (hs := hN) H).trans ?_
    rw [add_pow, mul_sum]
    refine sup'_le hN _ fun i hi ↦ ?_
    refine single_le_sum (f := fun i ↦ 2 * (v x ^ i * v y ^ (N - i) * ↑(N.choose i))) (fun a h ↦ ?_) hi
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    positivity
  refine Real.le_of_forall_pow_le_mul_pow zero_lt_four zero_le_four (hn _) (add_nonneg hx hy) ?_
  convert Eventually.of_forall key using 3 with N
  ring

/-- A "weak absolute value" (satisfying the weaker triangle inequality
`v (x + y) ≤ 2 * max (v x) (v y)`) is actually an absolute value. -/
def of_add_le_two_mul_max : AbsoluteValue R ℝ where
  toFun := v
  map_mul' := hm
  nonneg' := hn
  eq_zero' := h₀
  add_le' := add_le_add_of_add_le_two_mul_max hm hn h₀ ha

end weak
