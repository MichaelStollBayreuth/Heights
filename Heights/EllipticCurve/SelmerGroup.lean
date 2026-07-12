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

## Main statements (mostly `sorry`ed so far)

* `range_μ_le_selmerGroup₂`: the image of `μ` is contained in the 2-Selmer group; since
  `ker μ = 2E(K)`, this bounds `E(K)/2E(K)` by the Selmer group.
* `card_range_μ`: `#(im μ) = 2 ^ rank E(K) · #E(K)[2]` for finitely generated `E(K)`, so
  together with the previous item the 2-Selmer group bounds the rank
  (`pow_rank_le_card_of_range_μ_le`).
* `selmerGroup₂_eq_badPrimes` (over a number field): the local conditions at the good finite
  places are subsumed by the `S`-unramifiedness condition `W.selmerGroupA`, so membership in
  the 2-Selmer group reduces to the *finitely many* local conditions at the bad places and the
  infinite places, inside the finite group `A(S,2) ⊓ ker N`. In particular the 2-Selmer group
  is finite (`finite_selmerGroup₂`).
* `card_range_μ_adicCompletion`, `card_range_μ_completion_isReal`,
  `card_range_μ_completion_isComplex`: the size of the local image is
  `#E(K_v)[2] · ‖2‖_v⁻¹` — concretely `#E(K_v)[2] · (#𝔽_v)^(v(2))` at a finite place (so
  `#E(K_v)[2]` when the residue characteristic is odd), `#E(K_v)[2] / 2` at a real place, and
  `1` at a complex place. These formulas certify that a computed local image is the full one.

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

variable (L : Type*) [Field L] [Algebra K L]

instance [W.IsCharNeTwoNF] : (W⁄L).IsCharNeTwoNF :=
  inferInstanceAs (W.map (algebraMap K L)).IsCharNeTwoNF

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

variable [DecidableEq K] [W.IsElliptic] [W.IsCharNeTwoNF]

instance : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic

open scoped Classical in
/-- The local `2`-descent condition at the extension field `L` of `K` (in the applications,
`L` is a completion of `K`): the subgroup of square classes in the étale algebra of `W`
whose image over `L` comes from an `L`-point of the curve. -/
noncomputable def localCondition : Subgroup W.M :=
  ((μ (W := (W⁄L).toAffine)).range).comap (W.localRes L)

open scoped Classical in
/-- The image of the global descent map `μ` satisfies the local condition at every extension
field: base change of points is compatible with the `x - T` maps. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  sorry

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
  sorry

/-- **The rank bound from a 2-Selmer group**: any subgroup of `Units.modPow W.A 2` that is
finite and contains the image of `μ` bounds the rank of `E(K)` from above, via
`2 ^ rank E(K) * #E(K)[2] ≤ #S`. Applies in particular to `S = W.selmerGroup₂ R Loc`
(`range_μ_le_selmerGroup₂`) once the latter is known to be finite. -/
theorem pow_rank_le_card_of_range_μ_le [AddGroup.FG W.Point] {S : Subgroup W.M} [Finite S]
    (h : (μ (W := W)).range ≤ S) :
    2 ^ Module.finrank ℤ W.Point * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker ≤
      Nat.card S := by
  sorry

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

open scoped Classical in
/-- At a good finite place, the local condition follows from `S`-unramifiedness and the norm
condition: the image of the local descent map is the group of unramified square classes with
trivial norm. -/
theorem inf_le_localCondition_adicCompletion {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    W.selmerGroupA (𝓞 F) ⊓ (normM (W := W)).ker ≤ W.localCondition (v.adicCompletion F) := by
  sorry

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
  sorry

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
is `1`; the general formula is `#E(F_v)[2] · ‖2‖_v⁻¹`. -/
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
  sorry

open scoped Classical in
/-- The size of the local image at a real place: `#(im μ_v) = #E(ℝ)[2] / 2` (that is, `2` if
the cubic has three real roots, and `1` otherwise). -/
theorem card_range_μ_completion_isReal {v : InfinitePlace F} (hv : v.IsReal) :
    2 * Nat.card (μ (W := (W⁄v.Completion).toAffine)).range =
      Nat.card (nsmulAddMonoidHom (α := (W⁄v.Completion).toAffine.Point) 2).ker := by
  sorry

open scoped Classical in
/-- The local image at a complex place is trivial: `E(ℂ)` is 2-divisible. -/
theorem card_range_μ_completion_isComplex {v : InfinitePlace F} (hv : v.IsComplex) :
    Nat.card (μ (W := (W⁄v.Completion).toAffine)).range = 1 := by
  sorry

end NumberField

end WeierstrassCurve.Affine
