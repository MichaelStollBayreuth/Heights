import Heights.NumberField
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Ostrowski

/-!
### Heights over ℚ
-/

open NumberField

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
  have hr₀ : (r.den : ℚ) ≠ 0 := mod_cast r.den_nz
  conv => enter [1, 1, z]; rw [← num_div_den r, ← mul_div_assoc, div_eq_iff hr₀, mul_comm (z : ℚ)]
  norm_cast
  exact ⟨fun ⟨z, hz⟩ ↦ Int.ofNat_dvd.mp <| (isCoprime_num_den r).symm.dvd_of_dvd_mul_right ⟨_, hz⟩,
    fun ⟨a, ha⟩ ↦ ⟨a * r.num, by rw [ha]; push_cast; ring⟩⟩

/-- Every point in `ℙⁿ(ℚ)` has a representative with coprime integral entries. -/
lemma Rat.coprimeIntToProjective_surjective [Nonempty ι] :
    Function.Surjective (coprimeIntToProjective (ι := ι)) := by
  intro x
  let d := Finset.univ.lcm (den ∘ x.rep)
  have hd₀ : d ≠ 0 := by simp [d, Finset.lcm_eq_zero_iff]
  have hr : d • x.rep ≠ 0 := smul_ne_zero hd₀ x.rep_nonzero
  obtain ⟨R, hR⟩ : ∃ z : ι → ℤ, d • x.rep = ((↑) : ℤ → ℚ) ∘ z := by
    have (i : ι) : ∃ y : ℤ, (d • x.rep) i = y := by
      simp only [nsmul_eq_mul, Pi.natCast_def, Pi.mul_apply, d]
      exact (exists_int_mul_eq_cast ..).mpr <| Finset.dvd_lcm (Finset.mem_univ i)
    exact ⟨fun i ↦ (this i).choose, funext fun i ↦ (this i).choose_spec⟩
  have hR₀ : R ≠ 0 := fun a ↦ (hR ▸ hr) (congrArg (Function.comp Int.cast) a)
  obtain ⟨R', hR₁, hR₂⟩ := Finset.extract_gcd R Finset.univ_nonempty
  refine ⟨⟨R', hR₂⟩, ?_⟩
  rw [coprimeIntToProjective, ← x.mk_rep]
  refine (Projectivization.mk_eq_mk_iff ℚ _ _ (Int.ne_zero_of_gcd_eq_one hR₂) x.rep_nonzero).mpr ?_
  have hg : Finset.univ.gcd R ≠ 0 := by
    contrapose! hR₀
    simp [funext_iff, Finset.gcd_eq_zero_iff.mp hR₀]
  have ha : (d : ℚ) / Finset.univ.gcd R ≠ 0 :=
    div_ne_zero (mod_cast (smul_ne_zero_iff.mp hr).1) <| mod_cast hg
  have hR₃ : ((↑) : ℤ → ℚ) ∘ R' = ((d : ℚ) / Finset.univ.gcd R) • x.rep := by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, eq_inv_smul_iff₀ <| mod_cast hg,
      Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, hR]
    ext : 1
    simp [hR₁]
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
    have H (x : { x : ι → ℤ // Finset.univ.gcd x = 1 }) :
        Height.mulHeight (((↑) : ℤ → ℚ) ∘  x.val) = ↑(⨆ (i : ι), |x.val i|) :=
        Rat.mulHeight_eq_max_abs_of_gcd_eq_one x.prop
    simp only [s, H]
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
        simp only [← Int.cast_abs]
        exact Finite.map_iSup_of_monotone _ Int.cast_mono
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
