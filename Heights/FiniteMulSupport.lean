import Mathlib

/-!
# Make fun_prop work for finite (mulitplicative) support

We define a new predicate `HasFiniteMulSupport` (and its additivized version) on functions
and provide the infrastructure so that `fun_prop` can prove it for functions that are
built from other functions with finite multiplicative support.
-/

namespace Function

variable {α M : Type*} [One M]

/-- The function `f` has finite multiplicative support. -/
@[to_additive (attr := fun_prop)]
def HasFiniteMulSupport (f : α → M) : Prop := f.mulSupport.Finite

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_one : HasFiniteMulSupport fun _ : α ↦ (1 : M) := by
  simp [HasFiniteMulSupport]

-- why do we need both versions?
@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_one' : HasFiniteMulSupport (1 : α → M) := by
  simp [HasFiniteMulSupport]

example : HasFiniteMulSupport (1 : ℕ → ℝ) := by fun_prop

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_fst {M' : Type*} [One M'] (f : α → M × M') (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).fst := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine hf.subset fun a ha ↦ ?_
  simp only [mem_mulSupport] at ha ⊢
  contrapose! ha
  exact ha ▸ Prod.fst_one

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_snd {M' : Type*} [One M'] (f : α → M × M') (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).snd := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine hf.subset fun a ha ↦ ?_
  simp only [mem_mulSupport] at ha ⊢
  contrapose! ha
  exact ha ▸ Prod.snd_one

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_prod_mk {M' : Type*} [One M'] (f : α → M) (g : α → M')
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ (f a, g a) := by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_mul {M : Type*} [MulOneClass M] (f g : α → M)
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a * g a :=
  (hf.union hg).subset <| mulSupport_mul ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_inv {M : Type*} [DivisionMonoid M] (f : α → M)
    (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a)⁻¹ := by
  simp only [HasFiniteMulSupport] at hf ⊢
  exact f.mulSupport_fun_inv ▸ hf

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_div {M : Type*} [DivisionMonoid M] (f g : α → M)
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a / g a :=
  (hf.union hg).subset <| mulSupport_div ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_pow {M : Type*} [Monoid M] (f : α → M) (hf : HasFiniteMulSupport f)
    (n : ℕ) :
    HasFiniteMulSupport fun a ↦ f a ^ n :=
  hf.subset <| f.mulSupport_pow n

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_max [LinearOrder M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ max (f a) (g a) :=
    (hf.union hg).subset <| mulSupport_max ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_min [LinearOrder M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ min (f a) (g a) :=
    (hf.union hg).subset <| mulSupport_min ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_sup [SemilatticeSup M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊔ g a :=
    (hf.union hg).subset <| mulSupport_sup ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_inf [SemilatticeInf M] (f g : α → M) (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊓ g a :=
    (hf.union hg).subset <| mulSupport_inf ..

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_iSup [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] (f : ι → α → M) (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨆ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iSup f

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] (f : ι → α → M) (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨅ i, f i a :=
  (Set.finite_iUnion hf).subset <| mulSupport_iInf f

@[to_additive (attr := fun_prop)]
lemma hasFiniteMulSupport_comp {N : Type*} [One N] (g : M → N) (f : α → M)
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport fun a ↦ g (f a) :=
  hf.subset <| mulSupport_comp_subset hg f

example {K : Type*} [Field K] {ι : Type*} {v : ι → AbsoluteValue K ℝ}
    (hv : ∀ x, HasFiniteMulSupport fun i ↦ v i x) (x : K) :
    HasFiniteMulSupport fun i ↦ max (v i x) 1 := by
  fun_prop

end Function
