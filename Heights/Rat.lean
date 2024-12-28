import Heights.Instances

/-!
### Heights over ℚ
-/

section rat

open NumberField

-- The following should go into `Mathlib.NumberTheory.NumberField.Embeddings`

instance : TrivialStar (ℚ →+* ℂ) := { star_trivial r := by ext1; simp only [eq_ratCast] }

@[simp]
lemma Rat.prod_infinitePlace {M : Type*} [CommMonoid M] (f : InfinitePlace ℚ → M) :
    ∏ v, f v = f Rat.infinitePlace := by
  simp only [← Finset.singleton_eq_univ Rat.infinitePlace, Finset.prod_singleton]

@[simp]
lemma Rat.isReal_infinitePlace : Rat.infinitePlace.IsReal :=
  InfinitePlace.isReal_iff.mpr <| IsSelfAdjoint.all Rat.infinitePlace.embedding

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

-- We need to increase the priority to avoid an instance mismatch below:
-- lemma test (v : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers ℚ)) (x : RingOfIntegers ℚ) :
--     ‖(embedding v) x‖ = 1 ↔ x ∉ v.asIdeal := by
--   convert NumberField.norm_eq_one_iff_not_mem v x
--   -- UniformSpace.Completion.instNorm ℚ = NormedField.toNorm
--   sorry
attribute [local instance 2000] NormedField.toNorm

/-- The term corresponding to a finite place in the definition of the multiplicative height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integers. -/
lemma Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace ℚ) {ι : Type*}
    [Fintype ι] [Nonempty ι] {x : ι → ℤ} (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  let v' : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers ℚ) := v.maximalIdeal
  have ⟨i, hi⟩ : ∃ i, ‖(embedding v') (Rat.ringOfIntegersEquiv.symm (x i))‖ = 1 := by
    simp_rw [NumberField.norm_eq_one_iff_not_mem]
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
  simp_rw [H, ← NumberField.FinitePlace.norm_embedding_eq]
  exact le_antisymm (Real.iSup_le (fun i ↦ NumberField.norm_le_one v' _) zero_le_one) <|
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



end rat
