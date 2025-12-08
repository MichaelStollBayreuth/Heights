import Heights.Instances

/-!
### Heights over ℚ
-/

open NumberField

section API

-- The following should go into `Mathlib.NumberTheory.NumberField.Embeddings`

instance : TrivialStar (ℚ →+* ℂ) := { star_trivial r := by ext1; simp only [eq_ratCast] }

@[simp]
lemma Rat.prod_infinitePlace {M : Type*} [CommMonoid M] (f : InfinitePlace ℚ → M) :
    ∏ v, f v = f Rat.infinitePlace := by
  simp only [← Finset.singleton_eq_univ Rat.infinitePlace, Finset.prod_singleton]

-- (up to here)

-- The following are not needed, after all, but might be useful eventually.
/-
lemma ciSup_natCast {ι R : Type*} [Fintype ι] [Nonempty ι] [ConditionallyCompleteLinearOrder R]
    [TopologicalSpace R] [OrderClosedTopology R] [AddMonoidWithOne R] [AddLeftMono R]
    [ZeroLEOneClass R] (f : ι → ℕ) :
    ⨆ i, (f i : R) = (⨆ i, f i : ) := by
  -- not found by `apply?`
  refine (Monotone.map_ciSup_of_continuousAt ?_ Nat.mono_cast (Finite.bddAbove_range f)).symm
  exact continuous_of_discreteTopology.continuousAt -/

/-
lemma ciInf_natCast {ι R : Type*} [Fintype ι] [Nonempty ι] [ConditionallyCompleteLinearOrder R]
    [TopologicalSpace R] [OrderClosedTopology R] [AddMonoidWithOne R] [AddLeftMono R]
    [ZeroLEOneClass R] (f : ι → ℕ) :
    ⨅ i, (f i : R) = (⨅ i, f i : ) := by
  refine (Monotone.map_ciInf_of_continuousAt ?_ Nat.mono_cast (Finite.bddBelow_range f)).symm
  exact continuous_of_discreteTopology.continuousAt -/

/-
lemma Real.iSup_inv_eq_iInf {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → ℝ} (hf : ∀ i, 0 < f i) :
    ⨆ i, (f i)⁻¹ = (⨅ i, f i)⁻¹ := by
  have ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := f)
  have H₀ : 0 < ⨅ i, f i := hi ▸ hf i
  refine le_antisymm ?_ ?_
  · exact ciSup_le fun i ↦ (inv_le_inv₀ (hf i) H₀).mpr <| ciInf_le (Finite.bddBelow_range _) i
  · exact le_ciSup_of_le (Finite.bddAbove_range _) i <| by rw [← hi] -/

-- The following material could go into `Mathlib.RingTheory.DedekindDomain.Ideal`

open Ideal

lemma Int.heightOneSpectrum_aux₁ (I : IsDedekindDomain.HeightOneSpectrum ℤ) :
    span {((Submodule.IsPrincipal.principal I.asIdeal).choose.natAbs : ℤ)} = I.asIdeal := by
  have := (Submodule.IsPrincipal.principal I.asIdeal).choose_spec
  rw [submodule_span_eq] at this
  rw [this, span_natAbs]
  convert rfl

lemma Int.heightOneSpectrum_aux₂ (p : Nat.Primes) :
    (Submodule.IsPrincipal.principal <| span {(p.val : ℤ)}).choose.natAbs = p := by
  have := (Submodule.IsPrincipal.principal <| span {(p.val : ℤ)}).choose_spec
  rw [submodule_span_eq, span_singleton_eq_span_singleton, associated_iff_natAbs] at this
  rw [← this, natAbs_cast]

/-- The canonical bijection between the set of prime numbers and the height one spectrum of `ℤ` -/
noncomputable
def Int.natPrimesEquivHeightOneSpectrum : Nat.Primes ≃ IsDedekindDomain.HeightOneSpectrum ℤ where
  toFun p := .mk (span {(p.val : ℤ)})
    ((span_singleton_prime <| mod_cast p.prop.ne_zero).mpr <| Nat.prime_iff_prime_int.mp p.prop)
    (by simp only [ne_eq, span_singleton_eq_bot, Nat.cast_eq_zero]
        exact_mod_cast p.prop.ne_zero)
  invFun I :=
    ⟨(Submodule.IsPrincipal.principal I.asIdeal).choose.natAbs, by
      have := (Submodule.IsPrincipal.principal I.asIdeal).choose_spec
      have h : (Submodule.IsPrincipal.principal I.asIdeal).choose ≠ 0 := by
        intro hf
        rw [hf, submodule_span_eq, span_singleton_eq_bot.mpr rfl] at this
        exact I.ne_bot this
      rw [← Int.prime_iff_natAbs_prime, ← span_singleton_prime h, ← submodule_span_eq, ← this]
      exact I.isPrime⟩
  left_inv p := Subtype.ext <| heightOneSpectrum_aux₂ p
  right_inv I := IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr <| heightOneSpectrum_aux₁ I

/-- If `v` is an element of the height one spectrum of `ℤ`, then membership in the associated
ideal is equivalent to divisibility by the corresponding prime number. -/
lemma IsDedekindDomain.HeightOneSpectrum.mem_iff_dvd (v : HeightOneSpectrum ℤ) (x : ℤ) :
    x ∈ v.asIdeal ↔ (Int.natPrimesEquivHeightOneSpectrum.symm v : ℤ) ∣ x := by
  have : v.asIdeal = span {(Int.natPrimesEquivHeightOneSpectrum.symm v : ℤ)} := by
    simp only [Int.natPrimesEquivHeightOneSpectrum, submodule_span_eq, Equiv.coe_fn_symm_mk]
    have := (Submodule.IsPrincipal.principal v.asIdeal).choose_spec
    rw [submodule_span_eq] at this
    exact this.trans <| span_singleton_eq_span_singleton.mpr <| Int.associated_natAbs _
  simpa only [this] using mem_span_singleton

/-- A ring isomorphism `R → S` induces a map from the height one spectrum of `R` to that of `S`. -/
def RingEquiv.mapIsDedekindDomainHeightOneSpectrum {R S : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] (e : R ≃+* S) (v : IsDedekindDomain.HeightOneSpectrum R) :
    IsDedekindDomain.HeightOneSpectrum S :=
  .mk (map e v.asIdeal)
      (by have := v.isPrime
          exact map_isPrime_of_equiv e (I := v.asIdeal))
      (by have := v.ne_bot
          contrapose! this
          rwa [map_eq_bot_iff_of_injective <| RingEquiv.injective e] at this)

/-- A ring isomorphism (of Dedekind domains) induces an equivalence
between the height one spectra. -/
def RingEquiv.isDedekindDomainHeightOneSpectrumEquiv {R S : Type*} [CommRing R]
    [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] (e : R ≃+* S) :
    IsDedekindDomain.HeightOneSpectrum R ≃ IsDedekindDomain.HeightOneSpectrum S where
      toFun := e.mapIsDedekindDomainHeightOneSpectrum
      invFun := e.symm.mapIsDedekindDomainHeightOneSpectrum
      left_inv v := by
        simp only [mapIsDedekindDomainHeightOneSpectrum, map_symm]
        exact IsDedekindDomain.HeightOneSpectrum.ext <| comap_map_of_bijective e e.bijective
      right_inv v := by
        simp only [mapIsDedekindDomainHeightOneSpectrum, map_symm]
        exact IsDedekindDomain.HeightOneSpectrum.ext <|
          map_comap_of_surjective e e.surjective _

-- (up to here)

end API

section tuples

open Ideal

-- We need to increase the priority to avoid an instance mismatch below:
-- lemma test (v : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers ℚ)) (x : RingOfIntegers ℚ) :
--     ‖(embedding v) x‖ = 1 ↔ x ∉ v.asIdeal := by
--   convert NumberField.norm_eq_one_iff_not_mem v x
--   -- UniformSpace.Completion.instNorm ℚ = NormedField.toNorm
--   sorry
-- attribute [local instance 2000] NormedField.toNorm -- apparently no longer necessary

/-- The term corresponding to a finite place in the definition of the multiplicative height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integers. -/
lemma Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace ℚ) {ι : Type*}
    [Fintype ι] [Nonempty ι] {x : ι → ℤ} (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  let v' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := v.maximalIdeal
  have ⟨i, hi⟩ : ∃ i, ‖(FinitePlace.embedding v') (Rat.ringOfIntegersEquiv.symm (x i) : ℚ)‖ = 1 := by
    simp_rw [FinitePlace.norm_eq_one_iff_notMem]
    by_contra! H
    let pI := Rat.ringOfIntegersEquiv.isDedekindDomainHeightOneSpectrumEquiv v'
    let p := Int.natPrimesEquivHeightOneSpectrum.symm pI
    have h i : (p : ℤ) ∣ x i := by
      rw [← pI.mem_iff_dvd, show pI.asIdeal = .map Rat.ringOfIntegersEquiv v'.asIdeal from rfl,
        mem_map_of_equiv]
      exact ⟨_, H i, RingEquiv.apply_symm_apply ..⟩
    refine p.prop.not_dvd_one ?_
    rw [← Int.ofNat_dvd, Nat.cast_one, ← hx]
    exact Finset.dvd_gcd fun i _ ↦ h i
  have H i : (x i : ℚ) = Rat.ringOfIntegersEquiv.symm (x i) := by
    simp only [eq_intCast, map_intCast]
  simp_rw [H, ← FinitePlace.norm_embedding_eq]
  exact le_antisymm (Real.iSup_le (fun i ↦ FinitePlace.norm_le_one v' _) zero_le_one) <|
    le_ciSup_of_le (Finite.bddAbove_range _) i hi.symm.le

open Height

open AdmissibleAbsValues in
/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. -/
lemma Rat.mulHeight_eq_max_abs_of_gcd_eq_one {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ}
    (hx : Finset.univ.gcd x = 1) :
    mulHeight (((↑) : ℤ →  ℚ) ∘ x) = ⨆ i, |x i| := by
  simp only [mulHeight]
  conv_rhs => rw [← mul_one ((⨆ i, |x i| :) : ℝ)]
  congr 1
  · simp only [ArchAbsVal, archAbsVal, Function.comp_apply, weight, InfinitePlace.mult, pow_ite,
      pow_one, prod_infinitePlace, isReal_infinitePlace, ↓reduceIte]
    have (i : ι) : Rat.infinitePlace.val (x i) = Rat.infinitePlace (x i) := rfl
    conv => enter [1, 1, i]; rw [this, Rat.infinitePlace_apply]
    exact_mod_cast (Monotone.map_ciSup_of_continuousAt continuous_of_discreteTopology.continuousAt
      Int.cast_mono (Finite.bddAbove_range _)).symm
  · exact finprod_eq_one_of_forall_eq_one
      fun v ↦ Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one v hx

/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. This version is in terms of a subtype. -/
lemma Rat.mulHeight_eq_max_abs_of_gcd_eq_one' {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : { x : ι → ℤ // Finset.univ.gcd x = 1 }) :
    mulHeight (((↑) : ℤ →  ℚ) ∘ x.val) = ⨆ i, |x.val i| :=
  mulHeight_eq_max_abs_of_gcd_eq_one x.prop

end tuples

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
    push_neg
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
lemma Projectivization.Rat.finite_of_mulHeight_le [Nonempty ι] (B : ℝ) :
    {x : Projectivization ℚ (ι → ℚ) | x.mulHeight ≤ B}.Finite := by
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
lemma Projectivization.Rat.finite_of_logHeight_le [Nonempty ι] (B : ℝ) :
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
