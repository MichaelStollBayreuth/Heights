import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Descent Theorem

We provide a proof of the following result.

Let `G` be a group and `f : G →* G` an endomorphism of `G` that maps every
subgroup of `G` into itself (e.g., `f = fun g ↦ g ^ n` when `G` is commutative).

If there is a finite subset `s : Set G` and there exists a function `h : G → ℝ`
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

open Subgroup in
/-- If `G` is a group and `f : G →* G` is an endomorphism sending subgroups into themselves,
and if there is a "height function" `h : G → ℝ` with respect to `f` and a finite subset `s`
of `G`, then `G` is finitely generated. -/
@[to_additive /-- If `G` is an additive group and `f : G →+ G` is an endomorphism sending
subgroups into themselves, and if there is a "height function" `h : G → ℝ` with respect
to `f` and a finite subset `s` of `G`, then `G` is finitely generated. -/]
theorem Group.fg_of_descent {G : Type*} [Group G]
    {f : G →* G} (hf : ∀ U : Subgroup G, U.map f ≤ U) {s : Set G} {h : G → ℝ} {a b c : ℝ}
    (ha : 0 ≤ a) (H₀ : a < b) (hs : s.Finite) (H₁ : s * f.range = .univ)
    (H₂ : ∀ g ∈ s, ∀ x, h (g⁻¹ * x) ≤ a * h x + c) (H₃ : ∀ x, b * h x - c ≤ h (f x))
    (H₄ : ∀ B, {x : G | h x ≤ B}.Finite) :
    FG G := by
  set q := QuotientGroup.mk (s := map f ⊤)
  -- Main proof idea: `s` together with elements of sufficiently small "height" `h` generates `G`.
  let S : Set G := s ∪ {x : G | h x ≤ 2 * c / (b - a)}
  have hS : Finite S := (hs.union <| H₄ _).to_subtype
  let U := closure S
  suffices U = ⊤ from fg_def.mpr <| (fg_iff_subgroup_fg ⊤).mp <| this ▸ closure_finite_fg S
  -- Assume this is false.
  by_contra! H
  -- Then we can find an element `x : G` not in `U` and of minimal height.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ U := SetLike.exists_not_mem_of_ne_top U H rfl
  let T : Set G := {x | h x ≤ h x₀} ∩ {x | x ∉ U}
  have hx₀T : x₀ ∈ T := by simp [T, hx₀]
  obtain ⟨x, hx₁, hx₂⟩ := Set.exists_min_image _ h (H₄ (h x₀) |>.inter_of_left _) ⟨_, hx₀T⟩
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
  suffices y ∈ T from (H'.trans_le <| hx₂ y this).false
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T] at hx₁ ⊢
  refine ⟨H'.le.trans <| hx₂ _ hx₀T, fun H ↦ ?_⟩
  have Hfy := U.mul_mem (mem_closure_of_mem <| by grind : g ∈ U) (hf U <| hy ▸ mem_map_of_mem f H)
  exact hx₁.2 (mul_inv_cancel_left g x ▸ Hfy)

open AddSubgroup QuotientAddGroup in
/--
If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / n • G` is finite
* for all `g x : G`, `h (x - g) ≤ a * h x + c g`,
* for all `x : G`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : R`, there are only finitely many `x : G` such that `h x ≤ B`, and
* `0 ≤ a < b` and `c₀` are real numbers, `c : G → ℝ`,
then `G` is finitely generated.
-/
theorem AddCommGroup.fg_of_descent {G : Type*} [AddCommGroup G] {n : ℕ}
    {h : G → ℝ} {a b c₀ : ℝ} {c : G → ℝ} (ha : 0 ≤ a) (H₀ : a < b)
    (H₁ : (nsmulAddMonoidHom (α := G) n).range.FiniteIndex)
    (H₂ : ∀ g x, h (x - g) ≤ a * h x + c g) (H₃ : ∀ x, b * h x - c₀ ≤ h (n • x))
    (H₄ : ∀ B, {x : G | h x ≤ B}.Finite) :
    AddGroup.FG G := by
  let f : G →+ G := nsmulAddMonoidHom n
  let q := QuotientAddGroup.mk (s := f.range)
  let qi : G ⧸ f.range → G := Function.surjInv mk_surjective
  let s : Set G := (Set.range q).image qi
  obtain ⟨g, hg₁, hg₂⟩ := s.exists_max_image c s.toFinite <| (Set.range_nonempty q).image qi
  let c' : ℝ := max c₀ (c g)
  have H₁' : s + f.range = .univ := by
    ext x
    simp only [Set.mem_add, SetLike.mem_coe, Set.mem_univ, iff_true]
    refine ⟨qi (q x), by simp [s], ?_⟩
    conv => enter [1, y]; rw [eq_comm, ← sub_eq_iff_eq_add']
    simp only [↓existsAndEq, and_true]
    exact eq_iff_sub_mem.mp (Function.surjInv_eq mk_surjective _).symm
  have H₃' x : b * h x - c' ≤ h (f x) := by simp only [nsmulAddMonoidHom_apply, f]; grind
  refine AddGroup.fg_of_descent (fun U u hu ↦ ?_) ha H₀ s.toFinite H₁' (fun g' hg' x ↦ ?_) H₃' H₄
  · obtain ⟨u', hu₁, rfl⟩ := mem_map.mp hu
    exact U.nsmul_mem hu₁ n
  · rw [neg_add_eq_sub] -- `grind [neg_add_eq_sub]` solves the goal, but is slow
    grw [H₂]
    exact add_le_add_left (le_sup_of_le_right (hg₂ g' hg')) _
