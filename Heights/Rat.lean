import Heights.NumberField
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Ostrowski

/-!
### Heights over ℚ
-/

open NumberField

-- #38183

section API

open Height AdmissibleAbsValues

lemma Rat.prod_infinitePlace {M : Type*} [CommMonoid M] (f : InfinitePlace ℚ → M) :
    ∏ v : InfinitePlace ℚ, f v ^ v.mult = f infinitePlace := by
  have : infinitePlace.mult = 1 :=
    NumberField.InfinitePlace.mult_isReal ⟨infinitePlace, isReal_infinitePlace⟩
  simp [Subsingleton.elim default infinitePlace, this]
-- #find_home! Rat.prod_infinitePlace -- [Mathlib.NumberTheory.NumberField.InfinitePlace.Basic]

namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

instance : AddGroupSeminormClass (FinitePlace K) K ℝ where
  map_add_le_add v x y := by simpa [coe_apply] using IsAbsoluteValue.abv_add' x y
  map_zero v := by simp
  map_neg_eq_map v x := by simp [coe_apply]
-- [Mathlib.NumberTheory.NumberField.Completion.FinitePlace]

end NumberField.FinitePlace

lemma Finset.gcd_eq_sum_mul {α R : Type*} [DecidableEq α] [CommRing R] [IsBezout R] [IsDomain R]
    [NormalizedGCDMonoid R] (s : Finset α) (f : α → R) :
    ∃ g : α → R, s.gcd f = ∑ a ∈ s, f a * g a := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨x, y, hxy⟩ := exists_gcd_eq_mul_add_mul (f a) (s.gcd f)
    obtain ⟨g, hg⟩ := ih
    conv => enter [1, g]; rw [gcd_insert, sum_insert ha, hxy, hg]
    refine ⟨Function.update (g · * y) a x, ?_⟩
    simp only [Function.update_self, add_right_inj, sum_mul, mul_assoc]
    exact sum_congr rfl fun b hb ↦ congrArg (f b * ·) <|
      (Function.update_of_ne (show b ≠ a by grind) x (g · * y)).symm

-- #find_home! Finset.gcd_eq_sum_mul -- no good location

end API


namespace Rat

section tuples

/-- The term corresponding to a finite place in the definition of the multiplicative height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integers. -/
lemma iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace ℚ) {ι : Type*}
    [Fintype ι] [Nonempty ι] {x : ι → ℤ} (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v n ≤ 1 := IsNonarchimedean.apply_intCast_le_one_of_isNonarchimedean hv
  obtain ⟨f, hf⟩ := by classical exact Finset.gcd_eq_sum_mul .univ x
  rw [hx] at hf
  obtain ⟨j, hj⟩ : ∃ j, v (x j) = 1 := by
    have h' : v (∑ i, x i * f i) ≤ ⨆ i, v (x i * f i) := by
      convert IsNonarchimedean.apply_sum_le hv
      rw [← cbiSup_eq_of_forall (by grind)]
      simp [Finset.mem_univ, ciSup_unique]
    by_contra! h
    replace h i : v (x i) < 1 := lt_of_le_of_ne (H <| x i) (h i)
    rw [← map_one v, show (1 : ℚ) = (1 : ℤ) from rfl, hf] at h
    push_cast at h
    replace h i : v (x i * f i) < ⨆ i, v (x i * f i) := by
      rw [map_mul, ← mul_one (iSup _)]
      exact mul_lt_mul_of_nonneg_of_pos ((h i).trans_le h') (H _) (by positivity) zero_lt_one
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (x i * f i))
    exact (h i).ne hi
  exact le_antisymm (ciSup_le fun i ↦ H (x i)) <| Finite.le_ciSup_of_le j hj.symm.le

open Height

open AdmissibleAbsValues in
/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. -/
lemma mulHeight_eq_max_abs_of_gcd_eq_one {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ}
    (hx : Finset.univ.gcd x = 1) :
    mulHeight (((↑) : ℤ →  ℚ) ∘ x) = ⨆ i, |x i| := by
  have hx₀ : Int.cast ∘ x ≠ (0 : ι → ℚ) := by
    contrapose! hx
    replace hx : x = 0 := by ext i; simpa using funext_iff.mp hx i
    rw [hx, Finset.gcd_eq_zero_iff.mpr (by simp)]
    simp
  simp_rw [NumberField.mulHeight_eq hx₀, Function.comp_apply, infinitePlace_apply, ← Int.cast_abs,
    cast_intCast, prod_infinitePlace,
    finprod_eq_one_of_forall_eq_one (iSup_finitePlace_apply_eq_one_of_gcd_eq_one · hx), mul_one]
  exact (Monotone.map_ciSup_of_continuousAt continuous_of_discreteTopology.continuousAt
    Int.cast_mono (Finite.bddAbove_range _)).symm

/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. This version is in terms of a subtype. -/
lemma mulHeight_eq_max_abs_of_gcd_eq_one' {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : { x : ι → ℤ // Finset.univ.gcd x = 1 }) :
    mulHeight (((↑) : ℤ →  ℚ) ∘ x.val) = ⨆ i, |x.val i| :=
  mulHeight_eq_max_abs_of_gcd_eq_one x.prop

end tuples

section mulHeight₁

open Height

/-- The multiplicative height of a rational number is the maximum of the absolute values of
its numerator and denominator. -/
lemma mulHeight₁_eq_max (q : ℚ) : mulHeight₁ q = max q.num.natAbs q.den := by
  rw [mulHeight₁_eq_mulHeight]
  suffices mulHeight ![q, 1] = mulHeight ![(q.num : ℚ), q.den] by
    rw [this, ← intCast_natCast q.den]
    have : (Finset.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
      rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by grind]
      simpa [Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
        Int.isCoprime_iff_gcd_eq_one.mp <| isCoprime_num_den q
    convert mulHeight_eq_max_abs_of_gcd_eq_one this
    · ext i; fin_cases i <;> simp
    · rw [show (↑(max q.num.natAbs q.den) : ℝ) = (max q.num.natAbs q.den : ℤ) by norm_cast]
      norm_cast
      push_cast
      refine le_antisymm (max_le ?_ ?_) <| ciSup_le fun i ↦ ?_
      · exact Finite.le_ciSup_of_le 0 <| by simp
      · exact Finite.le_ciSup_of_le 1 <| by simp
      · fin_cases i <;> simp
  nth_rewrite 1 [← Rat.num_div_den q]
  have hq₀ : (q.den : ℚ) ≠ 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp [mul_div_cancel₀ _ hq₀]

open Real in
/-- The logarithmic height of a rational number is the logarithm of the maximum of the absolute
values of its numerator and denominator. -/
lemma logHeight₁_eq_log_max (q : ℚ) : logHeight₁ q = log (max q.num.natAbs q.den) := by
  norm_cast
  rw [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq_max]

/-- The multiplicative height of a positive natural number `n` cast to `ℚ` equals `n`. -/
theorem mulHeight₁_natCast (n : ℕ) [NeZero n] :
    mulHeight₁ (n : ℚ) = n := by
  simp [mulHeight₁_eq_max, show 1 ≤ n by grind [NeZero.ne n]]

end mulHeight₁

end Rat

-- end #38183

section projective

variable {ι : Type*} [Fintype ι]

private
lemma Int.ne_zero_of_gcd_eq_one {x : ι → ℤ} (hx : Finset.univ.gcd x = 1) :
    ((↑) : ℤ → ℚ) ∘ x ≠ 0 := by
  refine (Function.comp_ne_zero_iff _ Rat.intCast_injective rfl).mpr fun h ↦ ?_
  exact one_ne_zero (hx.symm.trans <| Finset.gcd_eq_zero_iff.mpr fun i _ ↦  congrFun h i)

/-- The map sending a coprime integer tuple to the corresponding point in `ℙⁿ(ℚ)`. -/
def Rat.coprimeIntToProjective :
    { x : ι → ℤ // Finset.univ.gcd x = 1 } → Projectivization ℚ (ι → ℚ) :=
  fun x ↦ .mk ℚ (((↑) : ℤ → ℚ) ∘ x.val) (Int.ne_zero_of_gcd_eq_one x.prop)

lemma Rat.exists_int_mul_eq_cast (r : ℚ) (n : ℕ) : (∃ z : ℤ, n * r = z) ↔ r.den ∣ n := by
  have hr₀ : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.pos.ne'
  nth_rewrite 1 [← Rat.num_div_den r, ← mul_div_assoc]
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨a * r.num, ?_⟩⟩
  · rw [div_eq_iff hr₀] at hz
    exact Int.ofNat_dvd.mp <| (isCoprime_num_den r).symm.dvd_of_dvd_mul_right
      ⟨_, mod_cast mul_comm (z : ℚ) _ ▸ hz⟩
  · rw [ha, Int.cast_mul, Nat.cast_mul, Int.cast_natCast, mul_assoc, mul_comm, mul_div_assoc,
      div_self hr₀, mul_one]

/-- Every point in `ℙⁿ(ℚ)` has a representative with coprime integral entries. -/
lemma Rat.coprimeIntToProjective_surjective [Nonempty ι] :
    Function.Surjective (coprimeIntToProjective (ι := ι)) := by
  intro x
  let r := x.rep
  let d := Finset.univ.lcm (Rat.den ∘ r)
  have hr : d • r ≠ 0 := by
    refine smul_ne_zero (fun hd ↦ ?_) x.rep_nonzero
    rw [Finset.lcm_eq_zero_iff] at hd
    simp at hd
  have ⟨R, hR⟩ : ∃ z : ι → ℤ, d • r = ((↑) : ℤ → ℚ) ∘ z := by
    have (i : ι) : ∃ y : ℤ, (d • r) i = y := by
      simp only [nsmul_eq_mul, Pi.natCast_def, Pi.mul_apply, d]
      exact (exists_int_mul_eq_cast ..).mpr <| Finset.dvd_lcm (Finset.mem_univ i)
    exact ⟨fun i ↦ (this i).choose, funext fun i ↦ (this i).choose_spec⟩
  have hR₀ : R ≠ 0 := by
    contrapose! hr
    simpa only [hr, Pi.comp_zero, Int.cast_zero, Function.const_zero] using hR
  have ⟨R', hR₁, hR₂⟩ := Finset.extract_gcd R Finset.univ_nonempty
  have hg : Finset.univ.gcd R ≠ 0 := by
    rw [ne_eq, Finset.gcd_eq_zero_iff]
    push Not
    simpa only [Finset.mem_univ, true_and] using Function.ne_iff.mp hR₀
  have hR₃ : ((↑) : ℤ → ℚ) ∘ R' = ((d : ℚ) / Finset.univ.gcd R) • r := by
    have : R = Finset.univ.gcd R • R' := by
      simp only [Finset.mem_univ, forall_const] at hR₁
      exact funext hR₁
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, eq_inv_smul_iff₀ <| mod_cast hg,
      Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, hR, this]
    ext1
    simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Pi.smul_apply, Function.comp_apply,
      Pi.mul_apply, Int.cast_mul]
    congr
    ext1
    simp only [Pi.mul_apply, Finset.mem_univ, hR₁]
  refine ⟨⟨R', hR₂⟩, ?_⟩
  simp only [coprimeIntToProjective]
  rw [← x.mk_rep]
  refine (Projectivization.mk_eq_mk_iff ℚ _ _ (Int.ne_zero_of_gcd_eq_one hR₂) x.rep_nonzero).mpr ?_
  have ha : (d : ℚ) / Finset.univ.gcd R ≠ 0 := by
    refine div_ne_zero (fun hd ↦ ?_) <| mod_cast hg
    norm_cast at hd
    rw [Finset.lcm_eq_zero_iff] at hd
    simp at hd
  exact ⟨ha.isUnit.unit, hR₃.symm⟩

open Height

lemma Rat.mulHeight_coprimeIntToProjective_eq (x : { x : ι → ℤ // Finset.univ.gcd x = 1 }) :
    mulHeight (((↑) : ℤ → ℚ) ∘ x.val) = (coprimeIntToProjective x).mulHeight := rfl

/-- The height on `ℙⁿ(ℚ)` satisfies the *Northcott Property*: there are only finitely many
points of bounded (multiplicative) height. -/
lemma Projectivization.Rat.finite_of_mulHeight_le (B : ℝ) :
    {x : Projectivization ℚ (ι → ℚ) | x.mulHeight ≤ B}.Finite := by
  rcases isEmpty_or_nonempty ι with H | H
  · exact Set.toFinite _
  let s := {x : { x : ι → ℤ  // Finset.univ.gcd x = 1 } |
    Height.mulHeight (((↑) : ℤ → ℚ) ∘  x.val) ≤ B}
  have hs : s.Finite := by
    simp only [s, Rat.mulHeight_eq_max_abs_of_gcd_eq_one']
    refine Set.Finite.of_finite_image ?_ Set.injOn_subtype_val
    refine Set.Finite.subset (s := {x | ∀ i, |x i| ≤ B}) ?_ fun x hx ↦ ?_
    · refine Set.forall_finite_image_eval_iff.mp fun i ↦ ?_
      simp only [Function.eval, Set.image]
      have : {z | ∃ a ∈ {x : ι → ℤ | ∀ (i : ι), |(x i : ℝ)| ≤ B}, a i = z} ⊆ {z | |(z : ℝ)| ≤ B} := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := Set.mem_setOf.mp hz
        exact ha i
      refine Set.Finite.subset ?_ this
      simpa only [abs_le, ← Int.ceil_le, ← Int.le_floor, Set.Icc_def] using Set.finite_Icc ..
    · simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right] at hx -- `↑(⨆ i, |x i|) ≤ B ∧ Finset.univ.gcd x = 1`
      have : ((⨆ i, |x i| :) : ℝ) = ⨆ i, (|x i| : ℝ) := by
        conv => enter [2, 1, i]; rw [← Int.cast_abs]
        -- this incantation looks a bit ridiculous, but I've found nothing simpler
        exact Monotone.map_ciSup_of_continuousAt continuous_of_discreteTopology.continuousAt
          Int.cast_mono (Finite.bddAbove_range _)
      exact (ciSup_le_iff <| Finite.bddAbove_range _).mp <| this ▸ hx.1
  refine Set.Finite.of_surjOn Rat.coprimeIntToProjective (fun x hx ↦ ?_) hs
  · rw [Set.mem_image, Subtype.exists]
    have ⟨y, hy⟩ := Rat.coprimeIntToProjective_surjective x
    exact ⟨y.val, y.prop,
      by simp [s, Rat.mulHeight_coprimeIntToProjective_eq, hy, Set.mem_setOf.mp hx], hy⟩

/-- The height on `ℙⁿ(ℚ)` satisfies the *Northcott Property*: there are only finitely many
points of bounded (logarithmic) height. -/
lemma Projectivization.Rat.finite_of_logHeight_le (B : ℝ) :
    {x : Projectivization ℚ (ι → ℚ) | x.logHeight ≤ B}.Finite := by
  have H (x : Projectivization ℚ (ι → ℚ)) : x.logHeight ≤ B ↔ x.mulHeight ≤ B.exp := by
    rw [x.logHeight_eq_log_mulHeight]
    exact Real.log_le_iff_le_exp x.mulHeight_pos
  simpa only [H] using finite_of_mulHeight_le (Real.exp B)

/-- The map from a field `K` to the projectivization of a two-dimensional `K`-vector space
given by sending `x` to `(x : 1)`. -/
-- better namespace than `_root_`?
def toProjectivization {K : Type*} [Field K] (x : K) : Projectivization K (Fin 2 → K) :=
  .mk K ![x, 1] <| by simp

lemma toProjectivization_injective {K : Type*} [Field K] :
    Function.Injective (toProjectivization (K := K)) := by
  intro x y h
  simp only [toProjectivization, Projectivization.mk_eq_mk_iff', Matrix.smul_cons, smul_eq_mul,
    mul_one, Matrix.smul_empty] at h
  have ⟨a, ha⟩ := h
  have ha₀ := congrFun ha 0
  have ha₁ := congrFun ha 1
  simp only [Fin.isValue, Matrix.cons_val_zero] at ha₀
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at ha₁
  simpa [ha₁] using ha₀.symm

/-- The height on `ℚ` satisfies the *Northcott Property*: there are only finitely many
points of bounded (multiplicative) height. -/
lemma Rat.finite_of_mulHeight_le (B : ℝ) : {x : ℚ | mulHeight₁ x ≤ B}.Finite := by
  refine Set.Finite.of_finite_image ?_ toProjectivization_injective.injOn
  simp_rw [Set.image, mulHeight₁_eq_mulHeight, Set.mem_setOf]
  have : {x | ∃ a : ℚ, mulHeight ![a, 1] ≤ B ∧ toProjectivization a = x} ⊆
      {x | x.mulHeight ≤ B} := by
    intro x hx
    simp only [Set.mem_setOf] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ha
  exact Set.Finite.subset (Projectivization.Rat.finite_of_mulHeight_le B) this

/-- The height on `ℚ` satisfies the *Northcott Property*: there are only finitely many
points of bounded (logarithmic) height. -/
lemma Rat.finite_of_logHeight_le (B : ℝ) : {x : ℚ | logHeight₁ x ≤ B}.Finite := by
  simpa only [logHeight₁, Real.log_le_iff_le_exp <| mulHeight₁_pos _]
    using finite_of_mulHeight_le (Real.exp B)

end projective
