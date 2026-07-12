import Mathlib
import Heights.ForMathlib.Basic
import Heights.EllipticCurve.WeakMordellWeil

/-!
# The 2-Selmer group of an elliptic curve

Let `E : y² = x³ + a₂x² + a₄x + a₆` be an elliptic curve over a field `K` (with `a₁ = a₃ = 0`),
let `A = K[X]/(f)` be its étale algebra and `μ : E(K) → Aˣ/(Aˣ)²` the `x - T` descent map of
`Heights.EllipticCurve.WeakMordellWeil`. For a field extension `L/K` (think: a completion of
`K`), everything base-changes, and we obtain a *local condition*
`W.localCondition L ≤ Units.modPow W.A 2`: the classes whose image in `Aₗˣ/(Aₗˣ)²` lies in the
image of the local descent map `μ_L`.

The **2-Selmer group** of `E` is the subgroup of `ker (norm : Aˣ/(Aˣ)² → Kˣ/(Kˣ)²)` cut out by
the local conditions at all completions of `K`. Here we define it relative to a Dedekind domain
`R` with fraction field `K` (giving the completions at the finite places) together with an
auxiliary family `Loc` of `K`-fields (giving the completions at the archimedean places in the
number field case): see `WeierstrassCurve.Affine.selmerGroup₂`. For a number field `F` the
2-Selmer group of `E/F` is `W.selmerGroup₂ (𝓞 F) (fun v : InfinitePlace F ↦ v.Completion)`.

## Main statements

* `range_μ_le_selmerGroup₂`: the image of `μ` is contained in the 2-Selmer group; since
  `ker μ = 2E(K)`, this bounds `E(K)/2E(K)` by the Selmer group.
* `card_range_μ`: `#(im μ) = 2 ^ rank E(K) · #E(K)[2]` for finitely generated `E(K)`, so
  together with the previous item the 2-Selmer group bounds the rank
  (`pow_rank_le_card_of_range_μ_le`).
* `selmerGroup₂_eq_badPrimes` (over a number field): the local conditions at the good finite
  places are subsumed by the `S`-unramifiedness condition `W.selmerGroupA`, so membership in
  the 2-Selmer group reduces to the *finitely many* local conditions at the bad places and the
  infinite places, inside the finite group `A(S,2) ⊓ ker N`. In particular the 2-Selmer group
  is finite (`finite_selmerGroup₂`). This rests on three `sorry`ed inputs: the two directions
  of the semilocal comparison between `A ⊗ F_v` and the completions of the field factors
  (`localRes_mem_selmerGroupA`, `mem_selmerGroupA_of_forall_localRes`) and the local statement
  that at a good place every unramified class with trivial norm is in the image of `μ_v`
  (`selmerGroupA_inf_ker_normM_le_range_μ`).
* `card_range_μ_adicCompletion`, `card_range_μ_completion_isReal`,
  `card_range_μ_completion_isComplex`: the size of the local image is
  `#E(K_v)[2] · ‖2‖_v⁻¹` — concretely `#E(K_v)[2] · (#𝔽_v)^(v(2))` at a finite place (so
  `#E(K_v)[2]` when the residue characteristic is odd), `#E(K_v)[2] / 2` at a real place, and
  `1` at a complex place. These formulas certify that a computed local image is the full one.
  The complex and odd-residue-characteristic cases are proved; the uniform finite-place formula
  and the real case are `sorry`ed.

## Towards explicit computations

The intended show-piece is a formal proof that the Mordell-Weil group of `y² = x³ - x + 1`
over `ℚ` is isomorphic to `ℤ`: here `f = x³ - x + 1` is irreducible with discriminant `-23`,
so `A` is the cubic field of discriminant `-23`, whose class group is trivial and whose unit
group has rank `1`; the 2-Selmer group turns out to have `𝔽₂`-dimension `1`, which together
with the point `(1, 1)` of infinite order and `E(ℚ)[2] = 0` pins down `E(ℚ) ≅ ℤ`. The
definitions below are therefore kept close to the objects one actually computes with
(`S`-Selmer groups of étale algebras, local images at finitely many places).
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

/-!
### Base change of the étale algebra and the local conditions

For a field extension `L/K`, the curve base-changes to `W⁄L` (Mathlib's
`WeierstrassCurve.baseChange`), the étale algebra to `(W⁄L).A = L[X]/(f)`, and the `x - T` map
to `μ : (W⁄L).Point → Units.modPow (W⁄L).A 2`. The local condition at `L` is the preimage in
`Units.modPow W.A 2` of the image of the local `x - T` map.
-/

section BaseChange

variable {L₀ : Type*} [Field L₀] (σ : K →+* L₀)

lemma map_f : (W.map σ).toAffine.f = W.f.map σ := by
  simp only [f, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, map_a₂, map_a₄, map_a₆]

instance [W.IsCharNeTwoNF] : (W.map σ).IsCharNeTwoNF where
  a₁ := by simp [map_a₁]
  a₃ := by simp [map_a₃]

lemma eval_map_f (x : K) : (W.map σ).toAffine.f.eval (σ x) = σ (W.f.eval x) := by
  rw [map_f, Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma map_fCofactor (x : K) :
    (W.fCofactor x).map σ = (W.map σ).toAffine.fCofactor (σ x) := by
  simp only [fCofactor, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, map_a₂, map_a₄, map_add, map_mul, map_pow]

variable (L : Type*) [Field L] [Algebra K L]

instance [W.IsCharNeTwoNF] : (W⁄L).IsCharNeTwoNF :=
  inferInstanceAs (W.map (algebraMap K L)).IsCharNeTwoNF

lemma eval_baseChange_f (x : K) :
    (W⁄L).toAffine.f.eval (algebraMap K L x) = algebraMap K L (W.f.eval x) :=
  W.eval_map_f (algebraMap K L) x

lemma baseChange_fCofactor (x : K) :
    (W.fCofactor x).map (algebraMap K L) = (W⁄L).toAffine.fCofactor (algebraMap K L x) :=
  W.map_fCofactor (algebraMap K L) x

/-- The base-change homomorphism `K[X]/(f) →+* L[X]/(f)` of étale algebras. -/
noncomputable def mapA : W.A →+* (W⁄L).toAffine.A :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (algebraMap K L)) (AdjoinRoot.root _) <| by
    rw [← Polynomial.eval₂_map, ← W.map_f (algebraMap K L)]
    exact AdjoinRoot.eval₂_root _

@[simp]
lemma mapA_mk (p : K[X]) :
    W.mapA L (AdjoinRoot.mk W.f p) = AdjoinRoot.mk (W⁄L).toAffine.f (p.map (algebraMap K L)) := by
  rw [mapA, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

/-- The base-change map on square classes of units of the étale algebra. -/
noncomputable def localRes : W.M →* Units.modPow (W⁄L).toAffine.A 2 :=
  Units.modPow.map (W.mapA L).toMonoidHom 2

lemma baseChange_f : (W⁄L).toAffine.f = W.f.map (algebraMap K L) :=
  W.map_f (algebraMap K L)

/-- The norm of the étale algebra is compatible with base change: the norm of `f` and `p` is
the resultant of the two polynomials, and resultants commute with ring homomorphisms. -/
lemma norm_mapA (a : W.A) :
    Algebra.norm L (W.mapA L a) = algebraMap K L (Algebra.norm K a) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [mapA_mk, AdjoinRoot.norm_mk_eq_resultant (W⁄L).toAffine.monic_f,
    AdjoinRoot.norm_mk_eq_resultant W.monic_f, W.baseChange_f,
    natDegree_map_eq_of_injective (algebraMap K L).injective,
    natDegree_map_eq_of_injective (algebraMap K L).injective, resultant_map_map]

/-- The norm map on square classes is compatible with base change. -/
lemma normM_localRes (m : W.M) :
    normM (W := (W⁄L).toAffine) (W.localRes L m) =
      Units.modPow.map (algebraMap K L).toMonoidHom 2 (W.normM m) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply, localRes, normM, Units.modPow.map_mk]
  exact congrArg _ (Units.ext (by simpa using W.norm_mapA L u))

variable [W.IsElliptic] [W.IsCharNeTwoNF]

instance : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic

open scoped Classical in
/-- The local `2`-descent condition at the extension field `L` of `K` (in the applications,
`L` is a completion of `K`): the subgroup of square classes in the étale algebra of `W`
whose image over `L` comes from an `L`-point of the curve. -/
noncomputable def localCondition : Subgroup W.M :=
  ((μ (W := (W⁄L).toAffine)).range).comap (W.localRes L)

open scoped Classical in
/-- Over an algebraically closed field extension, the image of the local descent map is
trivial: every unit of the étale algebra is a square. -/
theorem card_range_μ_of_isAlgClosed [IsAlgClosed L] :
    Nat.card (μ (W := (W⁄L).toAffine)).range = 1 := by
  -- every unit of a field factor of the étale algebra is a square
  have hfac (p : (W⁄L).toAffine.f.Factors) :
      Subsingleton (Units.modPow (AdjoinRoot (p : L[X])) 2) := by
    refine Units.modPow.subsingleton_of_forall_exists_pow fun u ↦ ?_
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := L) (K := AdjoinRoot (p : L[X]))).2 (u : AdjoinRoot (p : L[X]))
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hc, map_zero])
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c zero_lt_two
    have hd0 : d ≠ 0 := fun h0 ↦ hc0 (by rw [← hd, h0, zero_pow two_ne_zero])
    refine ⟨Units.mk0 (algebraMap _ _ d) (by simpa using hd0), Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hd, hc]
  -- hence the ambient group of square classes, and with it the image of `μ`, is trivial
  have hsub : Subsingleton (Units.modPow (W⁄L).toAffine.A 2) :=
    (AdjoinRoot.modPowEquivPiFactors (W⁄L).toAffine.f_ne_zero
      (W⁄L).toAffine.squarefree_f 2).toEquiv.subsingleton
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

variable [DecidableEq K]

open scoped Classical in
/-- The image of the global descent map `μ` satisfies the local condition at every extension
field: base change of points is compatible with the `x - T` maps. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  rintro _ ⟨P', rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [localCondition, Subgroup.mem_comap, μ_apply]
  match P with
  | 0 => rw [μ₀_zero, map_one]; exact one_mem _
  | .some x y hP =>
    have hP' : (W⁄L).toAffine.Nonsingular (algebraMap K L x) (algebraMap K L y) :=
      (W.map_nonsingular (algebraMap K L).injective x y).mpr hP
    rw [μ₀_some]
    refine ⟨.ofAdd (.some _ _ hP'), ?_⟩
    rw [μ_apply, μ₀_some]
    rcases eq_or_ne (W.f.eval x) 0 with hx | hx
    · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) = 0 := by
        rw [W.eval_baseChange_f, hx, map_zero]
      rw [μX_of_eval_f_eq_zero hxL, μX_of_eval_f_eq_zero hx, localRes, Units.modPow.map_unit]
      refine congrArg _ (Units.ext ?_)
      rw [IsUnit.unit_spec, IsUnit.unit_spec]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, W.baseChange_fCofactor]
    · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) ≠ 0 := by
        rw [W.eval_baseChange_f]
        exact fun h0 ↦ hx ((map_eq_zero _).mp h0)
      rw [μX_of_eval_f_ne_zero hxL, μX_of_eval_f_ne_zero hx, localRes, Units.modPow.map_unit]
      refine congrArg _ (Units.ext ?_)
      rw [IsUnit.unit_spec, IsUnit.unit_spec]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_sub,
        Polynomial.map_C, Polynomial.map_X]

end BaseChange

/-!
### The 2-Selmer group
-/

section SelmerGroup

variable [DecidableEq K] [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra K (Loc i)]

open scoped Classical in
/-- The **2-Selmer group** of `W`, relative to a Dedekind domain `R` with fraction field `K`
and an auxiliary family `Loc` of `K`-fields: the square classes in the étale algebra that are
in the kernel of the norm map and satisfy the local conditions at the completions of `K` at
all finite places of `R` and at all members of `Loc`.

For a number field `F` (with `R = 𝓞 F` and `Loc` the family of completions at the infinite
places), this is the classical 2-Selmer group of `W`, the group of everywhere locally solvable
2-coverings of `W`. -/
noncomputable def selmerGroup₂ : Subgroup W.M :=
  (normM (W := W)).ker ⊓ (⨅ v : HeightOneSpectrum R, W.localCondition (v.adicCompletion K))
    ⊓ ⨅ i, W.localCondition (Loc i)

-- the statement needs `DecidableEq K` (via `selmerGroup₂`), but it is erased from the proof
set_option linter.unusedSectionVars false in
open scoped Classical in
lemma mem_selmerGroup₂_iff {m : W.M} :
    m ∈ W.selmerGroup₂ R Loc ↔ W.normM m = 1 ∧
      (∀ v : HeightOneSpectrum R, m ∈ W.localCondition (v.adicCompletion K)) ∧
      ∀ i, m ∈ W.localCondition (Loc i) := by
  simp [selmerGroup₂, Subgroup.mem_iInf, and_assoc, MonoidHom.mem_ker]

/-- The image of the descent map `μ` is contained in the 2-Selmer group. Since
`ker μ = 2 • E(K)` (`ker_μ_eq`), this identifies `E(K)/2E(K)` with a subgroup of the
2-Selmer group. -/
theorem range_μ_le_selmerGroup₂ : (μ (W := W)).range ≤ W.selmerGroup₂ R Loc :=
  le_inf (le_inf range_μ_le_ker_normM <| le_iInf fun _ ↦ W.range_μ_le_localCondition _) <|
    le_iInf fun _ ↦ W.range_μ_le_localCondition _

/-- The size of the image of `μ` in terms of the rank and the rational 2-torsion:
`im μ ≅ E(K)/2E(K)`, which for a finitely generated `E(K)` has order
`2 ^ rank E(K) * #E(K)[2]`. -/
theorem card_range_μ [AddGroup.FG W.Point] :
    Nat.card (μ (W := W)).range =
      2 ^ Module.finrank ℤ W.Point * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (μ (W := W))).toEquiv, ker_μ_eq,
    ← Subgroup.index_eq_card, AddSubgroup.index_toSubgroup,
    AddSubgroup.index_range_nsmul_of_fg _ two_ne_zero]

/-- **The rank bound from a 2-Selmer group**: any subgroup of `Units.modPow W.A 2` that is
finite and contains the image of `μ` bounds the rank of `E(K)` from above, via
`2 ^ rank E(K) * #E(K)[2] ≤ #S`. Applies in particular to `S = W.selmerGroup₂ R Loc`
(`range_μ_le_selmerGroup₂`) once the latter is known to be finite. -/
theorem pow_rank_le_card_of_range_μ_le [AddGroup.FG W.Point] {S : Subgroup W.M} [Finite S]
    (h : (μ (W := W)).range ≤ S) :
    2 ^ Module.finrank ℤ W.Point * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker ≤
      Nat.card S := by
  rw [← W.card_range_μ]
  exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

end SelmerGroup

/-!
### Reduction to the bad places, and finiteness

Over a number field, the local condition at a *good* finite place `v` (odd residue
characteristic, good reduction — both guaranteed by `v ∉ W.badPrimes (𝓞 F)`) is implied by
`v`-unramifiedness together with the norm condition: the image of the local descent map is
exactly the subgroup of unramified classes in the kernel of the local norm. Consequently the
2-Selmer group equals the subgroup of the *finite* group `A(S,2) ⊓ ker N` cut out by the local
conditions at the bad and infinite places, which makes it computable and in particular finite.
-/

section NumberField

open NumberField

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
  [W.IsCharNeTwoNF]

/-!
The passage between the global and the local conditions rests on three inputs. The first two
form the *semilocal bridge*: for a square class `m` of the étale algebra `A = F[X]/(f)` and a
finite place `v`, being unramified at the primes of the field factors of `A` above `v` is
equivalent to the localization of `m` at `v` being unramified over the valuation ring of
`F_v`. Here "unramified over the valuation ring" is expressed by `selmerGroupA` of the
base-changed curve over `v.adicCompletionIntegers F` — for a good `v` the local set of bad
primes is empty, so this is precisely the subgroup of square classes with even valuations.
The underlying mathematical content is the decomposition `A ⊗ F_v ≅ ∏ (L_p)_w` of the
completed étale algebra into the completions of the field factors at the places above `v`,
compatibly with the valuations; this is not yet in Mathlib.

The third input is purely local: at a good place, every unramified square class with trivial
norm comes from a point (via a Hensel-lemma lifting or a counting argument against
`card_range_μ_adicCompletion`).
-/

open scoped Classical in
/-- Semilocal bridge, global to local: an `S`-unramified square class localizes to an
unramified class at every good finite place. -/
theorem localRes_mem_selmerGroupA {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ W.badPrimes (𝓞 F))
    {m : W.M} (hm : m ∈ W.selmerGroupA (𝓞 F)) :
    W.localRes (v.adicCompletion F) m ∈
      (W⁄(v.adicCompletion F)).toAffine.selmerGroupA (v.adicCompletionIntegers F) := by
  sorry

open scoped Classical in
/-- Semilocal bridge, local to global: a square class that localizes to an unramified class
at every finite place is `S`-unramified. -/
theorem mem_selmerGroupA_of_forall_localRes {m : W.M}
    (hm : ∀ v : HeightOneSpectrum (𝓞 F),
      W.localRes (v.adicCompletion F) m ∈
        (W⁄(v.adicCompletion F)).toAffine.selmerGroupA (v.adicCompletionIntegers F)) :
    m ∈ W.selmerGroupA (𝓞 F) := by
  sorry

open scoped Classical in
/-- The local Hensel input: at a good finite place, every unramified square class with
trivial norm is in the image of the local descent map. (Proof: Hensel lifting of points, or
counting against `card_range_μ_adicCompletion` — the two sides have the same, finite,
cardinality.) -/
theorem selmerGroupA_inf_ker_normM_le_range_μ {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    (W⁄(v.adicCompletion F)).toAffine.selmerGroupA (v.adicCompletionIntegers F)
        ⊓ (normM (W := (W⁄(v.adicCompletion F)).toAffine)).ker
      ≤ (μ (W := (W⁄(v.adicCompletion F)).toAffine)).range := by
  sorry

open scoped Classical in
/-- At a good finite place, the local condition follows from `S`-unramifiedness and the norm
condition: the image of the local descent map is the group of unramified square classes with
trivial norm. -/
theorem inf_le_localCondition_adicCompletion {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    W.selmerGroupA (𝓞 F) ⊓ (normM (W := W)).ker ≤ W.localCondition (v.adicCompletion F) := by
  intro m hm
  rw [Subgroup.mem_inf] at hm
  rw [localCondition, Subgroup.mem_comap]
  apply W.selmerGroupA_inf_ker_normM_le_range_μ hv
  rw [Subgroup.mem_inf]
  refine ⟨W.localRes_mem_selmerGroupA hv hm.1, ?_⟩
  rw [MonoidHom.mem_ker, W.normM_localRes, MonoidHom.mem_ker.mp hm.2, map_one]

open scoped Classical in
/-- **Reduction of the 2-Selmer group to the bad places**: over a number field, the 2-Selmer
group consists of the classes in `A(S,2) ∩ ker N` (a finite group computable from the class
groups and unit groups of the field factors, via `Heights.ForMathlib.SelmerGroup`) that
satisfy the local conditions at the places in `W.badPrimes (𝓞 F)` (which include the places
above `2` and the places of bad reduction) and at the infinite places. -/
theorem selmerGroup₂_eq_badPrimes :
    W.selmerGroup₂ (𝓞 F) (fun v : InfinitePlace F ↦ v.Completion) =
      W.selmerGroupA (𝓞 F) ⊓ (normM (W := W)).ker
        ⊓ (⨅ v : W.badPrimes (𝓞 F),
            W.localCondition ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))
        ⊓ ⨅ v : InfinitePlace F, W.localCondition v.Completion := by
  ext m
  simp only [mem_selmerGroup₂_iff, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨W.mem_selmerGroupA_of_forall_localRes fun v ↦ ?_, h1⟩, fun v ↦ h2 v⟩, h3⟩
    have h := h2 v
    rw [localCondition, Subgroup.mem_comap] at h
    exact (W⁄(v.adicCompletion F)).toAffine.range_μ_le_selmerGroupA
      (v.adicCompletionIntegers F) h
  · rintro ⟨⟨⟨hA, h1⟩, h2⟩, h3⟩
    refine ⟨h1, fun v ↦ ?_, h3⟩
    by_cases hv : v ∈ W.badPrimes (𝓞 F)
    · exact h2 ⟨v, hv⟩
    · exact W.inf_le_localCondition_adicCompletion hv <| Subgroup.mem_inf.mpr
        ⟨hA, MonoidHom.mem_ker.mpr h1⟩

open scoped Classical in
/-- The 2-Selmer group of an elliptic curve over a number field is finite. -/
theorem finite_selmerGroup₂
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor (𝓞 F) p))]
    [(p : W.f.Factors) → Group.FG (W.ringOfIntegersFactor (𝓞 F) p)ˣ] :
    Finite (W.selmerGroup₂ (𝓞 F) (fun v : InfinitePlace F ↦ v.Completion)) := by
  have hle : W.selmerGroup₂ (𝓞 F) (fun v : InfinitePlace F ↦ v.Completion) ≤
      W.selmerGroupA (𝓞 F) := by
    rw [selmerGroup₂_eq_badPrimes]
    exact inf_le_left.trans <| inf_le_left.trans inf_le_left
  have := W.finite_selmerGroupA (𝓞 F)
  exact Finite.of_injective _ (Subgroup.inclusion_injective hle)

/-!
### The size of the local images

For a completion `F_v`, the image of the local descent map
`μ_v : E(F_v)/2E(F_v) ↪ Units.modPow A_v 2` has order `#E(F_v)[2] · ‖2‖_v⁻¹`. This comes in
three flavors: at a finite place `‖2‖_v⁻¹ = (#𝔽_v)^(v(2))` (so the factor is `1` when the
residue characteristic is odd), at a real place `‖2‖_v⁻¹ = 1/2`, and at a complex place
`‖2‖_v⁻¹ = 1/4` (so the image is trivial). These formulas certify that a candidate list of
local points generates the full local image.
-/

open scoped Classical in
/-- The size of the local image at a finite place `v`:
`#(im μ_v) = #E(F_v)[2] · (#𝔽_v)^(v(2))`. For odd residue characteristic the second factor
is `1`; the general formula is `#E(F_v)[2] · ‖2‖_v⁻¹`.

The proof needs the structure of `E(F_v)` as a compact group: a finite-index subgroup is
isomorphic to `(𝒪_v, +)` via the formal group logarithm, and the quantity
`#(G/2G) / #G[2]` is multiplicative in extensions, equal to `1` for finite groups and to
`‖2‖_v⁻¹` for `(𝒪_v, +)`. This requires the formal group of an elliptic curve over a
complete DVR, which is a separate project. -/
theorem card_range_μ_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (μ (W := (W⁄(v.adicCompletion F)).toAffine)).range =
      Nat.card (nsmulAddMonoidHom (α := (W⁄(v.adicCompletion F)).toAffine.Point) 2).ker *
        Nat.card (𝓞 F ⧸ v.asIdeal) ^
          (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
  sorry

open scoped Classical in
/-- The size of the local image at a finite place of odd residue characteristic:
`#(im μ_v) = #E(F_v)[2]`. -/
theorem card_range_μ_adicCompletion_of_two_notMem {v : HeightOneSpectrum (𝓞 F)}
    (hv : (2 : 𝓞 F) ∉ v.asIdeal) :
    Nat.card (μ (W := (W⁄(v.adicCompletion F)).toAffine)).range =
      Nat.card (nsmulAddMonoidHom (α := (W⁄(v.adicCompletion F)).toAffine.Point) 2).ker := by
  have h0 : (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors = 0 := by
    by_contra h
    have h1 := (v.le_count_iff two_ne_zero 1).mp (Nat.one_le_iff_ne_zero.mpr h)
    rw [pow_one] at h1
    exact hv h1
  rw [W.card_range_μ_adicCompletion v, h0, pow_zero, mul_one]

open scoped Classical in
/-- The size of the local image at a real place: `#(im μ_v) = #E(ℝ)[2] / 2` (that is, `2` if
the cubic has three real roots, and `1` otherwise).

The proof is a sign analysis over the real closed field `v.Completion`: the étale algebra is
`ℝ × ℂ` or `ℝ³` according to the number of real roots, the square classes are the signs at
the real factors, and the image of `μ` consists of the sign patterns of `x - θᵢ` on the
region `f ≥ 0`, using the intermediate value theorem to realize them. -/
theorem card_range_μ_completion_isReal {v : InfinitePlace F} (hv : v.IsReal) :
    2 * Nat.card (μ (W := (W⁄v.Completion).toAffine)).range =
      Nat.card (nsmulAddMonoidHom (α := (W⁄v.Completion).toAffine.Point) 2).ker := by
  sorry

-- the statement lives with its number-field siblings; `NumberField F` and `DecidableEq F` are
-- part of the ambient section but the content is the general `card_range_μ_of_isAlgClosed`
set_option linter.unusedSectionVars false in
open scoped Classical in
/-- The local image at a complex place is trivial: over an algebraically closed field, every
unit of the étale algebra is a square, so the whole group of square classes is trivial. -/
theorem card_range_μ_completion_isComplex {v : InfinitePlace F} (hv : v.IsComplex) :
    Nat.card (μ (W := (W⁄v.Completion).toAffine)).range = 1 := by
  -- `v.Completion ≃+* ℂ` is algebraically closed
  have halg : IsAlgClosed v.Completion := by
    set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv with he
    refine IsAlgClosed.of_exists_root _ fun p hpm hpi ↦ ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (e : v.Completion →+* ℂ))
      (by rw [degree_map]; exact (Polynomial.degree_pos_of_irreducible hpi).ne')
    refine ⟨e.symm z, (map_eq_zero_iff (e : v.Completion →+* ℂ) e.injective).mp ?_⟩
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
      show ((e : v.Completion →+* ℂ) (e.symm z)) = z from e.apply_symm_apply z]
    exact hz
  exact W.card_range_μ_of_isAlgClosed v.Completion

end NumberField

end WeierstrassCurve.Affine
