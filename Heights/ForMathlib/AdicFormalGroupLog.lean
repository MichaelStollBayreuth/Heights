import Heights.ForMathlib.Chabauty.LogIso
import Heights.ForMathlib.AdicCompletionExtension

/-!
# The scaled formal logarithm of a formal group law

This file generalizes the `p`-scaling machinery of the vendored kit file
`Heights.ForMathlib.Chabauty.LogIso` from the natural number `p` to an arbitrary ring
element `c` (for the application: a power `π^e` of a uniformizer of `𝒪_v`, where `e` is
the absolute ramification index).  The `c`-scaled formal group law
`ChabautyColeman.FormalGroupLaw.scaledFC` is `F(cX, cY)/c`; the additivity identity of the
formal logarithm descends along an injective base-change map `f : O →+* K` to the
`c`-scaled integral logarithm (`ChabautyColeman.FormalGroupLaw.subst_scaledFC_descent`).

The second part specializes to the valuation ring `𝒪_v` of the completion of a global
field at a finite place: for `c = π^e` the scaled logarithm has integral coefficients
(`WeierstrassCurve` is not needed here; this works for any formal group law over `𝒪_v`),
with linear coefficient `1`, so it has an integral compositional inverse
(`ChabautyColeman.invSubst`), and evaluation at points of the maximal ideal produces a
group isomorphism onto `(𝔪, +)`.
-/

open MvPowerSeries IsLocalRing


namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The topology on `𝒪_v` is the `𝔪`-adic topology; this activates the vendored kit. -/
instance factIsAdic_adicCompletionIntegers :
    Fact (IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))) :=
  ⟨v.isAdic_maximalIdeal_adicCompletionIntegers⟩

end IsDedekindDomain.HeightOneSpectrum

namespace ChabautyColeman

section Helpers

variable {O : Type*} [CommRing O] {ι : Type*} {K : Type*} [CommRing K] {f : O →+* K} {c : O}

/-- General-scale version of `ChabautyColeman.map_eq_rescale`: scaling by an arbitrary
ring element `c` instead of a natural number `p`. -/
theorem map_eq_rescale_of_forall_coeff {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : ∀ d, f (coeff d H) = f c ^ d.degree * coeff d L) :
    MvPowerSeries.map f H = rescale (fun _ ↦ f c) L := by
  ext d
  rw [coeff_map, hH d, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]

end Helpers

namespace FormalGroupLaw

/-! ### The `c`-scaled formal group law -/

section ScaledFC

variable {O : Type*} [CommRing O] {ι : Type*} (Φ : FormalGroupLaw O ι) (c : O)

/-- The `c`-scaled formal group law: `F(cX, cY)/c`, integral because `F` has no constant
term. -/
noncomputable def scaledFC (j : ι) : MvPowerSeries (ι ⊕ ι) O :=
  fun d ↦ c ^ (d.degree - 1) * coeff d (Φ.F j)

@[simp]
theorem coeff_scaledFC (j : ι) (d : ι ⊕ ι →₀ ℕ) :
    coeff d (Φ.scaledFC c j) = c ^ (d.degree - 1) * coeff d (Φ.F j) := rfl

theorem constantCoeff_scaledFC (j : ι) : constantCoeff (Φ.scaledFC c j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_scaledFC, map_zero Finsupp.degree,
    coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff, mul_zero]

variable [Finite ι] in
theorem hasSubst_scaledFC : MvPowerSeries.HasSubst (Φ.scaledFC c) :=
  hasSubst_of_constantCoeff_zero fun j ↦ Φ.constantCoeff_scaledFC c j

end ScaledFC

/-! ### Descent of the logarithm additivity to the `c`-scaled level -/

section Descent

variable {O : Type*} [CommRing O] {ι : Type*} [Finite ι] {K : Type*} [Field K]
  {f : O →+* K} {c : O} (Φ : FormalGroupLaw O ι)

private lemma subst_smulX_subst_X_comp (e : ι → ι ⊕ ι) (L : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K))
        (MvPowerSeries.subst (fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L)
      = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have he : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcX2 : HasSubst fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  rw [subst_comp_subst_apply he hcX2]
  congr 1
  funext s
  rw [subst_X hcX2]

private lemma map_subst_X_comp (e : ι → ι ⊕ ι) {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : MvPowerSeries.map f H = rescale (fun _ ↦ f c) L) :
    MvPowerSeries.map f
        (MvPowerSeries.subst (fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) O)) H)
      = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (e s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have heO : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) O) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have heK : HasSubst fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcX : HasSubst fun j : ι ↦ f c • (X j : MvPowerSeries ι K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hXe : (fun s : ι ↦ MvPowerSeries.map f (X (e s) : MvPowerSeries (ι ⊕ ι) O))
      = fun s : ι ↦ (X (e s) : MvPowerSeries (ι ⊕ ι) K) :=
    funext fun s ↦ MvPowerSeries.map_X f (e s)
  rw [map_subst heO, hXe, hH, rescale_const_eq_subst, subst_comp_subst_apply hcX heK]
  congr 1
  funext s
  rw [subst_smul heK, subst_X heK]

/-- The `c`-scaled formal group law is the `c`-rescaling of `F`, over the fraction
field. -/
theorem map_scaledFC_smul (j : ι) :
    f c • MvPowerSeries.map f (Φ.scaledFC c j)
      = rescale (fun _ ↦ f c) ((Φ.map f).F j) := by
  ext d
  rw [MvPowerSeries.coeff_smul, coeff_map, coeff_scaledFC, coeff_rescale, map_mul, map_pow,
    Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
  have hF : (Φ.map f).F j = MvPowerSeries.map f (Φ.F j) := rfl
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, hF, coeff_map]

variable [Fintype ι] [DecidableEq ι] [CharZero K]

/-- The descended additivity identity: the `c`-scaled logarithm is additive for the
`c`-scaled formal group law, over `O`. -/
theorem subst_scaledFC_descent (hf : Function.Injective f)
    {HL : ι → MvPowerSeries ι O}
    (hHL : ∀ j, MvPowerSeries.map f (HL j)
      = rescale (fun _ ↦ f c) ((Φ.map f).log j)) (i : ι) :
    MvPowerSeries.subst (Φ.scaledFC c) (HL i)
      = MvPowerSeries.subst
          (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (HL i)
        + MvPowerSeries.subst
            (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (HL i) := by
  have hcX : HasSubst (fun j : ι ↦ f c • (X j : MvPowerSeries ι K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcX2 : HasSubst (fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hmsF : HasSubst fun j ↦ MvPowerSeries.map f (Φ.scaledFC c j) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        Φ.constantCoeff_scaledFC, map_zero]
  apply map_injective_of_injective hf
  rw [map_add, map_subst_X_comp Sum.inl (hHL i), map_subst_X_comp Sum.inr (hHL i)]
  calc MvPowerSeries.map f (MvPowerSeries.subst (Φ.scaledFC c) (HL i))
      = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledFC c j))
          (MvPowerSeries.map f (HL i)) := map_subst (Φ.hasSubst_scaledFC c) (HL i)
    _ = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledFC c j))
          (MvPowerSeries.subst (fun j ↦ f c • X j) ((Φ.map f).log i)) := by
        rw [hHL, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun j ↦ f c • MvPowerSeries.map f (Φ.scaledFC c j))
          ((Φ.map f).log i) := by
        rw [subst_comp_subst_apply hcX hmsF]
        congr 1
        funext j
        rw [subst_smul hmsF, subst_X hmsF]
    _ = MvPowerSeries.subst
          (fun j ↦ MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • X t) ((Φ.map f).F j))
          ((Φ.map f).log i) := by
        congr 1
        funext j
        rw [Φ.map_scaledFC_smul j, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • X t)
          (MvPowerSeries.subst (fun j ↦ (Φ.map f).F j) ((Φ.map f).log i)) :=
        (subst_comp_subst_apply (Φ.map f).hasSubst_F hcX2 _).symm
    _ = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
          ((Φ.map f).log i)
        + MvPowerSeries.subst
            (fun s : ι ↦ f c • (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
            ((Φ.map f).log i) := by
        rw [(Φ.map f).log_subst_F i, ← coe_substAlgHom hcX2, map_add, coe_substAlgHom hcX2,
          subst_smulX_subst_X_comp Sum.inl, subst_smulX_subst_X_comp Sum.inr]

end Descent

end FormalGroupLaw

end ChabautyColeman
