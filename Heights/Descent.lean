import Mathlib.Algebra.GroupWithZero.Subgroup
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.CosetCover
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib
/-!
# Descent Theorem

We provide a proof of the following result.

Let `G` be a group and `f : G →* G` an endomorphism of `G` that maps every
subgroup of `G` into itself (e.g., `f = fun g ↦ g ^ n` when `G` is commutative).

If there is a finite subset `s : Finset G` and there exists a function `h : G → ℝ`
and constants `a, b, c : R` such that
* `s` surjects onto the quotient `G ⧸ f(G)`,
* for all `g ∈ s` and `x : G`, `h (x / g) ≤ a * h x + c`,
* for all `x : G`, `h (f x) ≥ b * h x - c`,
* for all `B : R`, there are only finitely many `x : G` such that `h x ≤ B`, and
* `0 ≤ a < b`,
then `G` is finitely generated.

This is one of the main ingredients of the standard proof of the **Mordell-Weil Theorem**.
It allows to reduce the statement to showing that `G / n • G` is finite (where `G`
is the Mordell-Weil group and `n ≥ 2`).
-/


/-
Replacing `ℝ` by an ordered field (`{R : Type*} [LinearOrder R] [Field R] [IsOrderedRing R]`)
works, but makes the type check quite slow (and `to_additive` needs some  help...).
-/

open scoped Pointwise

open Subgroup Finset in
/-- If `G` is a group and `f : G →* G` is an endomorphism sending subgroups into themselves,
and if there is a "height function" `h : G → ℝ` with respect to `f` and a finite subset `s`
of `G`, then `G` is finitely generated. -/
@[to_additive /-- If `G` is an additive group and `f : G →+ G` is an endomorphism sending
subgroups into themselves, and if there is a "height function" `h : G → ℝ` with respect
to `f` and a finite subset `s` of `G`, then `G` is finitely generated. -/]
theorem Group.FG_of_descent {G : Type*} [Group G]
    {f : G →* G} (hf : ∀ U : Subgroup G, U.map f ≤ U) {s : Finset G} {h : G → ℝ} {a b c : ℝ}
    (ha : 0 ≤ a) (H₀ : a < b) (H₁ : (s : Set G) * Set.range f = .univ)
    (H₂ : ∀ g ∈ s, ∀ x, h (g⁻¹ * x) ≤ a * h x + c) (H₃ : ∀ x, b * h x - c ≤ h (f x))
    (H₄ : ∀ B, {x : G | h x ≤ B}.Finite) :
    FG G := by
  set q := QuotientGroup.mk (s := map f ⊤)
  -- Main proof idea: `s` together with elements of sufficiently small "height" `h` generates `G`.
  let S : Set G := s ∪ {x : G | h x ≤ 2 * c / (b - a)}
  have hS : Finite S := s.finite_toSet.union <| H₄ _
  let U := closure S
  suffices U = ⊤ from fg_def.mpr <| (fg_iff_subgroup_fg ⊤).mp <| this ▸ closure_finite_fg S
  -- Assume this is false.
  by_contra! H
  -- Then we can find an element `x : G` not in `U` and of minimal height.
  have ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ U := by simpa using mt Subgroup.ext_iff.mpr H
  classical
  let T : Finset G := (H₄ (h x₀)).toFinset.filter (· ∉ U)
  have hx₀T : x₀ ∈ T := by simp [T, hx₀]
  have HT : T.Nonempty := ⟨_, hx₀T⟩
  obtain ⟨x, hx₁, hx₂⟩ := mem_image.mp <| (T.image h).min'_mem (HT.image h)
  -- Now we construct an element `y` of smaller height and not in `U`.
  obtain ⟨g, hg, z, hz, hy⟩ := Set.mem_mul.mp <| H₁ ▸ Set.mem_univ x
  obtain ⟨y, rfl⟩ := Set.mem_range.mp hz
  rw [← eq_inv_mul_iff_mul_eq] at hy
  have H' : h y < h x := by
    suffices a * h x + 2 * c < b * h x by nlinarith [hy ▸ H₂ g hg x, H₃ y]
    suffices 2 * c / (b - a) < h x by field_simp [sub_pos.mpr H₀] at this; grind
    suffices x ∉ S by grind
    exact notMem_of_notMem_closure <| by grind
  -- To obtain a contradiction, it is sufficient to show `y ∈ T`.
  refine (H'.trans_le <| hx₂ ▸ min'_le (T.image h) _ (mem_image_of_mem h ?_)).false
  simp only [mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, T]
  refine ⟨H'.le.trans <| hx₂ ▸ (T.image h).min'_le _ (mem_image.mpr ⟨_, hx₀T, rfl⟩), fun H ↦ ?_⟩
  have Hfy := U.mul_mem (mem_closure_of_mem <| by grind : g ∈ U) (hf U <| hy ▸ mem_map_of_mem f H)
  suffices x ∉ U by rw [mul_inv_cancel_left] at Hfy; exact this Hfy
  grind

open AddSubgroup DistribMulAction in
/--
If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` and `s : Finset G` satisfy
* `s` contains a set of representatives of `G / n • G`
* for all `g ∈ s` and `x : G`, `h (x - g) ≤ a * h x + c`,
* for all `x : G`, `h (n • x) ≥ b * h x - c`,
* for all `B : R`, there are only finitely many `x : G` such that `h x ≤ B`, and
* `0 ≤ a < b` and `c` are real numbers,
then `G` is finitely generated.
-/
theorem AddCommGroup.FG_of_descent' {G : Type*} [AddCommGroup G] {n : ℕ}
    {s : Finset G} {h : G → ℝ} {a b c : ℝ} (ha : 0 ≤ a) (H₀ : a < b)
    (H₁ : (s : Set G) + (n • (⊤ : AddSubgroup G) :) = .univ)
    (H₂ : ∀ g ∈ s, ∀ x, h (x - g) ≤ a * h x + c) (H₃ : ∀ x, b * h x - c ≤ h (n • x))
    (H₄ : ∀ B, {x : G | h x ≤ B}.Finite) :
    AddGroup.FG G := by
  let f := nsmulAddMonoidHom (α := G) n
  have H₁' : (s : Set G) + Set.range f = .univ := by
    convert H₁
    ext
    simp [f, Set.mem_smul_set]
  refine AddGroup.FG_of_descent (fun U u hu ↦ ?_) ha H₀ H₁' ?_ H₃ H₄
  · obtain ⟨u', hu₁, rfl⟩ := mem_map.mp hu
    exact AddSubgroup.nsmul_mem U hu₁ n
  · convert H₂ using 5
    exact neg_add_eq_sub ..

open AddSubgroup DistribMulAction Finset in
/--
If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / n • G` is finite
* for all `g x : G`, `h (x - g) ≤ a * h x + c g`,
* for all `x : G`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : R`, there are only finitely many `x : G` such that `h x ≤ B`, and
* `0 ≤ a < b` and `c₀` are real numbers, `c : G → ℝ`,
then `G` is finitely generated.
-/
theorem AddCommGroup.FG_of_descent {G : Type*} [AddCommGroup G] {n : ℕ}
    {h : G → ℝ} {a b c₀ : ℝ} {c : G → ℝ} (ha : 0 ≤ a) (H₀ : a < b)
    (H₁ : (n • (⊤ : AddSubgroup G)).FiniteIndex)
    (H₂ : ∀ g x, h (x - g) ≤ a * h x + c g) (H₃ : ∀ x, b * h x - c₀ ≤ h (n • x))
    (H₄ : ∀ B, {x : G | h x ≤ B}.Finite) :
    AddGroup.FG G := by
  let q := QuotientAddGroup.mk (s := n • (⊤ : AddSubgroup G))
  let qi : G ⧸ n • ⊤ → G := Function.surjInv QuotientAddGroup.mk_surjective
  classical
  let s : Finset G := ((Set.range q).toFinite.toFinset.image qi)
  have hs : s.Nonempty :=
    ((Set.range q).toFinite.toFinset_nonempty.mpr <| Set.range_nonempty q).image qi
  let c' : ℝ := max c₀ <| (s.image c).max' (image_nonempty.mpr hs)
  have H₃' x : b * h x - c' ≤ h (n • x) := by grind
  refine FG_of_descent' (s := s) ha H₀ ?_ (fun g hg x ↦ ?_) H₃' H₄
  · ext x
    simp only [Set.mem_add, Set.mem_univ, iff_true]
    refine ⟨qi (q x), by simp [s], ?_⟩
    simp only [eq_comm, ← sub_eq_iff_eq_add', exists_eq_right, SetLike.mem_coe,
      ← QuotientAddGroup.eq_iff_sub_mem]
    exact (Function.surjInv_eq QuotientAddGroup.mk_surjective _).symm
  · have hc : c g ≤ c' := le_sup_of_le_right <| le_max' _ _ <| mem_image_of_mem c hg
    grind
