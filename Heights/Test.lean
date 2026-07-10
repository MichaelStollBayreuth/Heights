#exit

import Heights.NumberField

namespace NumberField

open Height Finset Multiset Height.AdmissibleAbsValues IsDedekindDomain NumberField.HeightOneSpectrum

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] [NumberField K]

open Ideal in
lemma isFiniteRelIndex_span_singleton_span_pair {m : ℕ} (hm : m ≠ 0) (r : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.IsFiniteRelIndex (span {(m : 𝓞 K), r}).toAddSubgroup := by
  refine Submodule.isFiniteRelIndex_of_map_linearMapMulLeft_le hm (Submodule.fg_span (by simp)) <|
    (LinearMap.map_span_le ..).mpr fun a ha ↦ ?_
  rw [LinearMap.mulLeft_apply, mem_span_singleton]
  exact dvd_mul_right ..

open Ideal in
lemma relIndex_span_span_nat_mul {m n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(m * n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(m * n), n * a}).toAddSubgroup := by
  let f : 𝓞 K →ₗ[𝓞 K] 𝓞 K := LinearMap.mulLeft _ n
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun a ha ↦ by simp_all [f]
  have H₁ : span {(m * n : 𝓞 K)} = Submodule.map f (span {(m : 𝓞 K)}) := by
    simp [mul_comm, LinearMap.map_span, f]
  have H₂ : span {↑(m * n), n * a} = Submodule.map f (span {↑m, a}) := by
    simp [mul_comm, LinearMap.map_span, f, Set.image_pair]
  rw [H₁, H₂]
  simp_rw [Submodule.map_toAddSubgroup]
  convert AddSubgroup.relIndex_map_map_of_injective _ _ hf |>.symm

open Ideal in
lemma relIndex_span_span_eq_relIndex_span_span {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {a b : 𝓞 K}
    (h : n * a = m * b) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, b}).toAddSubgroup := by
  trans (span {(m * n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(m * n), n * a}).toAddSubgroup
  · exact relIndex_span_span_nat_mul hn a
  · rw [mul_comm, mul_comm m, h]
    exact (relIndex_span_span_nat_mul hm b).symm

open Ideal Module in
lemma absNorm_span_pair_eq_pow {n : ℕ} (hn : n ≠ 0) {a : 𝓞 K}
    (h : (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, a}).toAddSubgroup = n) :
    (span {↑n, a}).absNorm = n ^ (finrank ℚ K - 1) := by
  rw [show Ideal.absNorm _ = (Submodule.toAddSubgroup _).index from rfl,
    ← AddSubgroup.relIndex_top_right]
  refine mul_left_cancel₀ hn ?_
  rw [← pow_succ', show finrank ℚ K - 1 + 1 = finrank ℚ K by grind [finrank_pos]]
  have : (span {(n : 𝓞 K)}).toAddSubgroup.relIndex ⊤ = n ^ (finrank ℚ K) := by
    have : (span {(n : 𝓞 K)}).toAddSubgroup = AddSubgroup.map (nsmulAddMonoidHom n) ⊤ := by
      ext : 1
      simp [mem_span_singleton', mul_comm]
    rw [this]
    have : finrank ℚ K = finrank ℤ ↥(⊤ : AddSubgroup (𝓞 K)) :=
      RingOfIntegers.rank K ▸ (AddSubgroup.finrank_eq_of_finiteIndex ⊤).symm
    rw [this]
    have hfr : Free ℤ (⊤ : AddSubgroup (𝓞 K)).toIntSubmodule :=
      free_of_finite_type_torsion_free'
    have hfin : Module.Finite ℤ (⊤ : AddSubgroup (𝓞 K)).toIntSubmodule := IsNoetherian.finite ..
    exact AddSubgroup.relIndex_map_nsmul n _
  rw [← this]
  nth_rewrite 1 [← h]
  refine AddSubgroup.relIndex_mul_relIndex _ _ _ ?_ le_top
  exact Submodule.toAddSubgroup_mono <| span_mono <| by grind

open Ideal in
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow' (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (Ideal.span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ _ _ |>.mpr (.of_finite ℚ x)
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  let Im := span {(m : 𝓞 K)}
  let Imr := span {(m : 𝓞 K), r}
  have hI : Im.toAddSubgroup ≤ Imr.toAddSubgroup :=
    Submodule.toAddSubgroup_mono <| span_mono <| by grind
  let n := Im.toAddSubgroup.relIndex Imr.toAddSubgroup
  have hn : n ≠ 0 := isFiniteRelIndex_span_singleton_span_pair hm r |>.relIndex_ne_zero
  obtain ⟨a, ha'⟩ : ∃ a, m * a = n * r := by
    have : n • r ∈ span {(m : 𝓞 K)} :=
      Im.toAddSubgroup.nsmul_relIndex_mem <| Submodule.mem_span_of_mem <| by grind
    simpa [nsmul_eq_mul, mem_span_singleton', mul_comm] using this
  have ha : n * x = a := by
    apply_fun ((n : K) * ·) at hmr
    rw_mod_cast [← ha'] at hmr
    rw [nsmul_eq_mul, mul_left_comm] at hmr
    push_cast at hmr
    exact mul_left_cancel₀ (mod_cast hm) hmr
  refine ⟨n, hn, a, ha, absNorm_span_pair_eq_pow hn ?_⟩
  exact relIndex_span_span_eq_relIndex_span_span hn hm ha'


#exit
import Mathlib

variable {ι : Type*} {A B : ι → Type*} [∀ i, Monoid (A i)] [∀ i, Monoid (B i)]

/-- The product monoid homomorphism, defined component-wise. -/
@[to_additive]
def MonoidHom.pi (f : (i : ι) → (A i →* B i)) : ((i : ι) → A i) →* (i : ι) → B i :=
  Pi.monoidHom fun i ↦ (f i).comp <| Pi.evalMonoidHom A i
-- #find_home! MonoidHom.pi -- [Mathlib.Algebra.Group.Pi.Lemmas]

@[to_additive (attr := simp)]
lemma MonoidHom.pi_apply (f : (i : ι) → (A i →* B i)) (x : (i : ι) → A i) :
    pi f x = fun i ↦ f i (x i) :=
  rfl

variable (M : ι → Type*) [∀ i, CommMonoid (M i)]

@[to_additive]
lemma powMonoidHom_pi (n : ℕ) : MonoidHom.pi (fun i ↦ powMonoidHom (α := M i) n) = powMonoidHom n := by
  ext : 2
  simp
-- #find_home! powMonoidHom_pi -- not conclusive. Mathlib.GroupTheory.QuotientGroup.Basic ?

variable {G H : ι → Type*} [∀ i, CommGroup (G i)] [∀ i, CommGroup (H i)]

/-- The canonical isomorphism between the quotient modulo the range of a product homomorphism
and the product of the factors modulo the range of the individual homomorphisms. -/
@[to_additive]
noncomputable
def QuotientGroup.mulEquivPiModRange (f : (i : ι) → (G i →* H i)) :
    ((i : ι) → H i) ⧸ (MonoidHom.pi f).range ≃* ((i : ι) → H i ⧸ (f i).range) :=
  let φ : ((i : ι) → H i) →* (i : ι) → H i ⧸ (f i).range := {
    toFun x := (x ·)
    map_one' := by simp [Pi.one_def]
    map_mul' x y := by simp [Pi.mul_def]
  }
  QuotientGroup.liftEquiv (φ := φ) _ (fun y ↦ ⟨fun i ↦ Quotient.out (y i), by simp [φ]⟩) <| by
    ext x : 1
    simpa [φ, funext_iff] using (Classical.skolem (p := fun a b ↦ f a b = x a)).symm
-- #find_home! QuotientGroup.mulEquivPiModRange -- [Mathlib.GroupTheory.QuotientGroup.Defs], better .Basic

@[to_additive (attr := simp)]
lemma QuotientGroup.mulEquivPiModRange_apply (f : (i : ι) → (G i →* H i)) (x : (i : ι) → H i) :
    mulEquivPiModRange f ↑x = fun i ↦ ↑(x i) :=
  rfl


#exit
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
-- import Mathlib

variable {F : Type*} [Field F]

/-- The absolute value extending `v` on the completion of `F` with respect to `v`. -/
noncomputable
def Completion.absoluteValue (v : AbsoluteValue F ℝ) : AbsoluteValue v.Completion ℝ :=
  NormedField.toAbsoluteValue v.Completion

namespace AbsoluteValue

open WithAbs

variable {v : AbsoluteValue F ℝ}

-- set_option trace.Meta.synthInstance true
-- set_option trace.profiler true

lemma isometry_equiv_comap : Isometry (equiv (Completion.absoluteValue v)) := by
  -- without these, instance search times out below
  --have : CommRing v.Completion := inferInstance --UniformSpace.Completion.commRing (WithAbs v)
  --have : Ring v.Completion := inferInstance -- UniformSpace.Completion.ring
  -- the following leads to an error below
  /-
  failed to synthesize instance of type class
  AddMonoidHomClass (WithAbs (Completion.absoluteValue v) ≃+* v.Completion) (WithAbs (Completion.absoluteValue v))
    v.Completion
  -/
  -- have : SeminormedAddGroup (WithAbs (Completion.absoluteValue v)) := inferInstance
  exact (AddMonoidHomClass.isometry_iff_norm _).mpr (fun _ ↦ rfl)

#exit
import Mathlib.Algebra.MonoidAlgebra.Defs

#exit
noncomputable section

/-- `Polynomial R` is the type of univariate polynomials over `R`,
denoted as `R[X]` within the `Polynomial` namespace.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R

open AddMonoidAlgebra Finset
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

theorem forall_iff_forall_finsupp (P : R[X] → Prop) :
    (∀ p, P p) ↔ ∀ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

theorem exists_iff_exists_finsupp (P : R[X] → Prop) :
    (∃ p, P p) ↔ ∃ q : R[ℕ], P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

@[simp]
theorem eta (f : R[X]) : Polynomial.ofFinsupp f.toFinsupp = f := by cases f; rfl

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `R[ℕ]`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

private irreducible_def add : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg {R : Type u} [Ring R] : R[X] → R[X]
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : R[X] → R[X] → R[X]
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

instance zero : Zero R[X] :=
  ⟨⟨0⟩⟩

instance one : One R[X] :=
  ⟨⟨1⟩⟩

instance add' : Add R[X] :=
  ⟨add⟩

instance neg' {R : Type u} [Ring R] : Neg R[X] :=
  ⟨neg⟩

instance sub {R : Type u} [Ring R] : Sub R[X] :=
  ⟨fun a b => a + -b⟩

instance mul' : Mul R[X] :=
  ⟨mul⟩

-- If the private definitions are accidentally exposed, simplify them away.
@[simp] theorem add_eq_add : add p q = p + q := rfl
@[simp] theorem mul_eq_mul : mul p q = p * q := rfl

instance instNSMul : SMul ℕ R[X] where
  smul r p := ⟨r • p.toFinsupp⟩

instance smulZeroClass {S : Type*} [SMulZeroClass S R] : SMulZeroClass S R[X] where
  smul r p := ⟨r • p.toFinsupp⟩
  smul_zero a := congr_arg ofFinsupp (smul_zero a)

instance {S : Type*} [Zero S] [SMulZeroClass S R] [NoZeroSMulDivisors S R] :
    NoZeroSMulDivisors S R[X] where
  eq_zero_or_eq_zero_of_smul_eq_zero eq :=
    (eq_zero_or_eq_zero_of_smul_eq_zero <| congr_arg toFinsupp eq).imp id (congr_arg ofFinsupp)

-- to avoid a bug in the `ring` tactic
instance (priority := 1) pow : Pow R[X] ℕ where pow p n := npowRec n p

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : R[X]) = 0 :=
  rfl

@[simp]
theorem ofFinsupp_one : (⟨1⟩ : R[X]) = 1 :=
  rfl

@[simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add_def]

@[simp]
theorem ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ :=
  show _ = neg _ by rw [neg_def]

@[simp]
theorem ofFinsupp_sub {R : Type u} [Ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofFinsupp_add, ofFinsupp_neg]
  rfl

@[simp]
theorem ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ :=
  show _ = mul _ _ by rw [mul_def]

@[simp]
theorem ofFinsupp_nsmul (a : ℕ) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b) :
    (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) :=
  rfl

@[simp]
theorem ofFinsupp_pow (a) (n : ℕ) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n := by
  change _ = npowRec n _
  induction n with
  | zero        => simp [npowRec]
  | succ n n_ih => simp [npowRec, n_ih, pow_succ]

@[simp]
theorem toFinsupp_zero : (0 : R[X]).toFinsupp = 0 :=
  rfl

@[simp]
theorem toFinsupp_one : (1 : R[X]).toFinsupp = 1 :=
  rfl

@[simp]
theorem toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_add]

@[simp]
theorem toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFinsupp := by
  cases a
  rw [← ofFinsupp_neg]

@[simp]
theorem toFinsupp_sub {R : Type u} [Ring R] (a b : R[X]) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := by
  rw [sub_eq_add_neg, ← toFinsupp_neg, ← toFinsupp_add]
  rfl

@[simp]
theorem toFinsupp_mul (a b : R[X]) : (a * b).toFinsupp = a.toFinsupp * b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_mul]

@[simp]
theorem toFinsupp_nsmul (a : ℕ) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S R] (a : S) (b : R[X]) :
    (a • b).toFinsupp = a • b.toFinsupp :=
  rfl

@[simp]
theorem toFinsupp_pow (a : R[X]) (n : ℕ) : (a ^ n).toFinsupp = a.toFinsupp ^ n := by
  cases a
  rw [← ofFinsupp_pow]

theorem _root_.IsSMulRegular.polynomial {S : Type*} [SMulZeroClass S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X] a
  | ⟨_x⟩, ⟨_y⟩, h => congr_arg _ <| ha.finsupp (Polynomial.ofFinsupp.inj h)

theorem toFinsupp_injective : Function.Injective (toFinsupp : R[X] → AddMonoidAlgebra _ _) :=
  fun ⟨_x⟩ ⟨_y⟩ => congr_arg _

@[simp]
theorem toFinsupp_inj {a b : R[X]} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

@[simp]
theorem toFinsupp_eq_zero {a : R[X]} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero, toFinsupp_inj]

@[simp]
theorem toFinsupp_eq_one {a : R[X]} : a.toFinsupp = 1 ↔ a = 1 := by
  rw [← toFinsupp_one, toFinsupp_inj]

/-- A more convenient spelling of `Polynomial.ofFinsupp.injEq` in terms of `Iff`. -/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b :=
  iff_of_eq (ofFinsupp.injEq _ _)

@[simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero, ofFinsupp_inj]

@[simp]
theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 := by rw [← ofFinsupp_one, ofFinsupp_inj]

instance inhabited : Inhabited R[X] :=
  ⟨0⟩

instance instNatCast : NatCast R[X] where natCast n := ofFinsupp n

@[simp]
theorem ofFinsupp_natCast (n : ℕ) : (⟨n⟩ : R[X]) = n := rfl

@[simp]
theorem toFinsupp_natCast (n : ℕ) : (n : R[X]).toFinsupp = n := rfl

@[simp]
theorem ofFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (⟨ofNat(n)⟩ : R[X]) = ofNat(n) := rfl

@[simp]
theorem toFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]).toFinsupp = ofNat(n) := rfl

instance semiring : Semiring R[X] :=
  fast_instance% Function.Injective.semiring toFinsupp toFinsupp_injective toFinsupp_zero
    toFinsupp_one toFinsupp_add toFinsupp_mul (fun _ _ => toFinsupp_nsmul _ _) toFinsupp_pow
    fun _ => rfl

instance module {S} [Semiring S] [Module S R] : Module S R[X] :=
  fast_instance% Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩
    toFinsupp_injective toFinsupp_smul

end AddMonoidAlgebra

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] R[X] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by simp; rw [ofFinsupp_add]
  map_smul' r x := by simp; rw [← ofFinsupp_smul, smul_single']

/-- `X` is the polynomial variable (aka indeterminate). -/
def X : R[X] :=
  monomial 1 1

end Semiring

-----------------------------------------------------------------------------

#check Polynomial.X

class foo (F : Type) where

noncomputable
def Y {R : Type} [Semiring R] : Polynomial R := Polynomial.X

def baz (_ : Type) : Type := Unit -- sorry

def baz.of (F : Type) : baz F := () --sorry

def bar (F : Type) (_ : baz F) : foo F where

-- def ZZZ {F : Type} [Semiring F] (p : Polynomial F) : Type := Polynomial F --sorry

def ZZZ {α : Type} (a : α) : Type := α -- sorry

lemma abc {F : Type} [Semiring F] : True := by
  set_option trace.Meta.isDefEq true in
    let a := bar (ZZZ (.X + .X : Polynomial F)) <|
              baz.of (ZZZ (X + X : Polynomial F))
  trivial

/-
    let a := bar (ZZZ (X + .X : Polynomial F)) <|
              baz.of (ZZZ (.X + .X : Polynomial F))
    --> baz (ZZZ (X + ?m.50721)) =?= baz (ZZZ (?m.50798 + ?m.50801))

    let a := bar (ZZZ (X + X : Polynomial F)) <|
              baz.of (ZZZ (.X + .X : Polynomial F))
    --> baz (ZZZ (X + X)) =?= baz (ZZZ (?m.50847 + ?m.50850))

    let a := bar (ZZZ (.X + .X : Polynomial F)) <|
              baz.of (ZZZ (X + .X : Polynomial F))
    --> baz (ZZZ (X + X)) =?= baz (ZZZ (X + ?m.50789))

    let a := bar (ZZZ (.X + .X : Polynomial F)) <|
              baz.of (ZZZ (X + X : Polynomial F))
    --> baz (ZZZ (X + X)) =?= baz (ZZZ (X + X)), still with

[Meta.isDefEq] ✅️ baz (ZZZ (X + X)) =?= baz (ZZZ (X + X)) ▼
  [] ✅️ ZZZ (X + X) =?= ZZZ (X + X) ▼
    [] ✅️ X + X =?= X + X ▼
      -- @HAdd.hAdd F[X] F[X] F[X] instHAdd X X : F[X] =?= @HAdd.hAdd ?m.50761[X] ?m.50788[X] F[X] ?m.50991 X X : F[X]
      [] ❌️ instHAdd =?= instHAdd ▼
         -- @instHAdd F[X] add' : HAdd F[X] F[X] F[X] =?= @instHAdd ℕ instAddNat : HAdd ℕ ℕ ℕ
        [] ❌️ F[X] =?= ℕ ▼
          [onFailure] ❌️ F[X] =?= ℕ
        [] ❌️ { hAdd := fun a b ↦ Add.add a b } =?= { hAdd := fun a b ↦ Add.add a b } ▼
          [] ❌️ fun a b ↦ Add.add a b =?= fun a b ↦ Add.add a b ▶
          [onFailure] ❌️ { hAdd := fun a b ↦ Add.add a b } =?= { hAdd := fun a b ↦ Add.add a b }
          [onFailure] ❌️ { hAdd := fun a b ↦ Add.add a b } =?= { hAdd := fun a b ↦ Add.add a b }
      [] ✅️ instHAdd =?= ?m.50991 ▼
        [] instHAdd [nonassignable] =?= ?m.50991 [assignable]
        [] ✅️ HAdd ?m.50761[X] ?m.50788[X] F[X] =?= HAdd F[X] F[X] F[X] ▼
          [] ✅️ ?m.50761[X] =?= F[X] ▶
          [] ✅️ ?m.50788[X] =?= F[X] ▶
          [] ✅️ F[X] =?= F[X]
-/

variable {F : Type} [Semiring F]

#check (.X + .X : Polynomial F) -- Polynomial.X + Polynomial.X : Polynomial F
#check ZZZ (.X + .X : Polynomial F) -- ZZZ (Polynomial.X + Polynomial.X) : Type (where Polynomial.X : Polynomial F)
#check baz.of (ZZZ (.X + .X : Polynomial F)) -- baz.of (ZZZ (Polynomial.X + Polynomial.X)) : baz (ZZZ (Polynomial.X + Polynomial.X))
#check bar (ZZZ (.X + .X : Polynomial F))
/- bar
  (ZZZ
    (Polynomial.X + Polynomial.X)) : baz (ZZZ (Polynomial.X + Polynomial.X)) → foo (ZZZ (Polynomial.X + Polynomial.X))
 -/
#check bar (ZZZ (.X + .X : Polynomial F)) <| baz.of (ZZZ (.X + .X : Polynomial F))
/-
bar (ZZZ (Polynomial.X + Polynomial.X))
  (baz.of (ZZZ (Polynomial.X + Polynomial.X))) : foo (ZZZ (Polynomial.X + Polynomial.X))
-/

-- #min_imports

#exit
def baz.of' {F : Type*} (a : F) : baz F := sorry

def bar' {F : Type*} (a : F) (_ : baz F) : foo F := sorry

lemma abc {F : Type*} [Semiring F] : True := by
  set_option trace.Meta.isDefEq true in
    let a := bar' (.X + .C 1 : Polynomial F) <| baz.of' (.X + .C 1 : Polynomial F)
  trivial

inductive xyz (F : Type*) [CommRing F] where
| X
| A (a : F)
| w (p q : xyz F)

instance xyz.instCommRing {F : Type*} [CommRing F] : CommRing (xyz F) := sorry

def xyz.C {F : Type*} [CommRing F] : F →+* xyz F := sorry

def zzz {F : Type*} [CommRing F] (p : xyz F) : Type := sorry



#check Polynomial.X
#check Polynomial.C
#check xyz.X
#check xyz.C
#check Polynomial

lemma xyz₁ {F : Type*} [CommRing F] : True := by
  letI inst : baz (zzz (.X : xyz F)) := sorry
  -- OK
  let a := @bar (zzz .X) inst
  trivial

lemma xyz₂ {F : Type*} [CommRing F] : True := by
  letI inst : baz (zzz (.X + .C 1 : xyz F)) := sorry
  -- OK
  let a := @bar (zzz (.X + .C 1 : xyz F))
  trivial

lemma xyz₃ {F : Type*} [CommRing F] : True := by
  letI inst : baz (zzz (xyz.X (F := F) + .C 1)) := sorry
  -- OK
  let a := @bar (zzz (xyz.X + xyz.C 1)) inst
  trivial

lemma xyz₃' {F : Type*} [CommRing F] : True := by
  letI inst : baz (zzz (xyz.X + xyz.C (1 : F))) := sorry
  -- OK
  set_option trace.Meta.isDefEq true in
    let a := @bar (zzz (xyz.X + xyz.C 1)) inst
  trivial

lemma abc {F : Type*} [CommRing F] : True := by
  set_option trace.Meta.isDefEq true in
    let a := bar (zzz (.X + .C 1 : xyz F)) <| baz.of (zzz (.X + .C 1 : xyz F))
  trivial


#check AdjoinRoot

seal AdjoinRoot in
lemma xyz₅ {F : Type*} [CommRing F] : True := by
  letI inst : baz (AdjoinRoot (.X + .C 1 : Polynomial F)) := sorry
  -- (deterministic) timeout at `isDefEq`
  --set_option trace.profiler true in
  set_option trace.Meta.isDefEq true in
      let a := @bar (AdjoinRoot (.X + .C 1 : Polynomial F)) inst
  trivial
