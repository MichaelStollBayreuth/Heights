import Mathlib
import Heights.ForMathlib.Basic
import Heights.ForMathlib.AdicCompletionExtension
import Heights.ForMathlib.FormalGroup
import Heights.ForMathlib.RealEtale
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
  is finite (`finite_selmerGroup₂`). Both directions of the semilocal comparison
  (`localRes_mem_selmerGroupA`, `mem_selmerGroupA_of_forall_localRes`) are proved, via
  contraction of primes along the embeddings of the field factors and their completions;
  the local statement that at a good place the image of `μ_v` is exactly the group of
  unramified classes with trivial norm (`selmerGroupA_inf_ker_normM_eq_range_μ`) is proved
  by counting. The
  whole reduction rests only on the `sorry`ed interface statements of
  `Heights.ForMathlib.FormalGroup`.
* `card_range_μ_adicCompletion`, `card_range_μ_completion_isReal`,
  `card_range_μ_completion_isComplex`: the size of the local image is
  `#E(K_v)[2] · ‖2‖_v⁻¹` — concretely `#E(K_v)[2] · (#𝔽_v)^(v(2))` at a finite place (so
  `#E(K_v)[2]` when the residue characteristic is odd), `#E(K_v)[2] / 2` at a real place, and
  `1` at a complex place. These formulas certify that a computed local image is the full one.
  The real and complex formulas are proved outright (the real case by a sign analysis over
  `ℝ`, transported along `v.Completion ≃+* ℝ`); the finite-place formula is proved modulo the
  interface statement of `Heights.ForMathlib.FormalGroup` (a finite-index subgroup of
  `E(F_v)` is isomorphic to `(𝒪_v, +)`, `sorry`ed there).

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

lemma baseChange_f : (W⁄L).toAffine.f = W.f.map (algebraMap K L) :=
  W.map_f (algebraMap K L)

/-- The base-change homomorphism `K[X]/(f) →+* L[X]/(f)` of étale algebras, as an instance of
`AdjoinRoot.map` (so that its API — `map_of`, `map_root`, `map_comp_map`, `mapRingEquiv` —
applies directly). -/
noncomputable def mapA : W.A →+* (W⁄L).toAffine.A :=
  AdjoinRoot.map (algebraMap K L) W.f (W⁄L).toAffine.f (W.baseChange_f L).dvd

@[simp]
lemma mapA_mk (p : K[X]) :
    W.mapA L (AdjoinRoot.mk W.f p) = AdjoinRoot.mk (W⁄L).toAffine.f (p.map (algebraMap K L)) :=
  AdjoinRoot.map_mk _ _ _

/-- The base-change map on square classes of units of the étale algebra. -/
noncomputable def localRes : W.M →* Units.modPow (W⁄L).toAffine.A 2 :=
  Units.modPow.map (W.mapA L).toMonoidHom 2

@[simp]
lemma localRes_mk (u : W.Aˣ) :
    W.localRes L (QuotientGroup.mk u) =
      QuotientGroup.mk (Units.map (W.mapA L).toMonoidHom u) :=
  rfl

@[simp]
lemma localRes_unit {a : W.A} (ha : IsUnit a) :
    W.localRes L (ha.unit : W.M) =
      ((ha.map (W.mapA L).toMonoidHom).unit : Units.modPow (W⁄L).toAffine.A 2) := by
  rw [localRes, Units.modPow.map_unit]

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
  simp only [QuotientGroup.mk'_apply, localRes_mk, normM, Units.modPow.map_mk]
  exact congrArg _ (Units.ext (by simpa using W.norm_mapA L u))

-- Base change of the étale algebra along an isomorphism of fields is an isomorphism:
-- `mapA` is (definitionally) `AdjoinRoot.map`, which `AdjoinRoot.mapRingEquiv` upgrades.
private lemma bijective_mapA_of_bijective_algebraMap (h : Function.Bijective (algebraMap K L)) :
    Function.Bijective (W.mapA L) :=
  (AdjoinRoot.mapRingEquiv (RingEquiv.ofBijective (algebraMap K L) h) W.f (W⁄L).toAffine.f
    (by rw [W.baseChange_f]; exact Associated.refl _)).bijective

lemma baseChange_self : (W⁄K).toAffine = W := by
  change W.map (algebraMap K K) = W
  rw [show algebraMap K K = RingHom.id K from Algebra.algebraMap_self]
  exact W.map_id

section PointMap

variable [DecidableEq K]

/-- Transport of points along an equality of Weierstrass curves. -/
def Point.congr {W₁ W₂ : Affine K} (h : W₁ = W₂) : W₁.Point ≃+ W₂.Point := by
  subst h; exact AddEquiv.refl _

lemma Point.congr_zero {W₁ W₂ : Affine K} (h : W₁ = W₂) :
    Point.congr h (0 : W₁.Point) = 0 := by subst h; rfl

lemma Point.congr_some {W₁ W₂ : Affine K} (h : W₁ = W₂) {x y : K}
    (hp : W₁.Nonsingular x y) :
    Point.congr h (Point.some x y hp) = Point.some x y (h ▸ hp) := by subst h; rfl

open scoped Classical in
/-- The base-change homomorphism on points, `E(K) →+ E(L)`: Mathlib's
`WeierstrassCurve.Affine.Point.map`, aligned with the plain base change `W⁄L` via
`baseChange_self`. -/
noncomputable def pointMap : W.Point →+ (W⁄L).toAffine.Point :=
  (Point.map (W' := W) (Algebra.ofId K L)).comp
    (Point.congr (W.baseChange_self).symm).toAddMonoidHom

open scoped Classical in
lemma pointMap_zero : W.pointMap L 0 = 0 := by
  simp [pointMap, Point.congr_zero]

open scoped Classical in
lemma pointMap_some {x y : K} (h : W.Nonsingular x y) :
    W.pointMap L (Point.some x y h) =
      Point.some (W' := (W⁄L).toAffine) (algebraMap K L x) (algebraMap K L y)
        ((W.map_nonsingular (algebraMap K L).injective x y).mpr h) := by
  rw [pointMap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Point.congr_some,
    Point.map_some]
  rfl

end PointMap

variable [W.IsElliptic] [W.IsCharNeTwoNF]

instance : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic

open scoped Classical in
/-- The local `2`-descent condition at the extension field `L` of `K` (in the applications,
`L` is a completion of `K`): the subgroup of square classes in the étale algebra of `W`
whose image over `L` comes from an `L`-point of the curve. -/
noncomputable def localCondition : Subgroup W.M :=
  ((μ (W := (W⁄L).toAffine)).range).comap (W.localRes L)

open scoped Classical in
lemma mem_localCondition_iff {m : W.M} :
    m ∈ W.localCondition L ↔ W.localRes L m ∈ (μ (W := (W⁄L).toAffine)).range :=
  Subgroup.mem_comap

open scoped Classical in
/-- Over an algebraically closed field extension, the image of the local descent map is
trivial: every unit of the étale algebra is a square. -/
theorem card_range_μ_of_isAlgClosed [IsAlgClosed L] :
    Nat.card (μ (W := (W⁄L).toAffine)).range = 1 := by
  -- every unit of a field factor of the étale algebra is a square
  have hfac (p : (W⁄L).toAffine.f.Factors) :
      Subsingleton (Units.modPow (AdjoinRoot (p : L[X])) 2) :=
    Units.modPow.subsingleton_of_isAlgClosed_of_isIntegral L _ two_ne_zero
  -- hence the ambient group of square classes, and with it the image of `μ`, is trivial
  have hsub : Subsingleton (Units.modPow (W⁄L).toAffine.A 2) :=
    (AdjoinRoot.modPowEquivPiFactors (W⁄L).toAffine.f_ne_zero
      (W⁄L).toAffine.squarefree_f 2).toEquiv.subsingleton
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

variable [DecidableEq K]

open scoped Classical in
/-- The local restriction map is compatible with the `x - T` maps: the square class of
`x - T` restricts to that of `σ(x) - T`, and likewise for the modified class at a
`2`-torsion `x`-coordinate. -/
theorem localRes_μX (x : K) :
    W.localRes L (W.μX x) = μX (W := (W⁄L).toAffine) (algebraMap K L x) := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) = 0 := by
      rw [W.eval_baseChange_f, hx, map_zero]
    rw [μX_of_eval_f_eq_zero hxL, μX_of_eval_f_eq_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, W.baseChange_fCofactor]
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) ≠ 0 := by
      rw [W.eval_baseChange_f]
      exact fun h0 ↦ hx ((map_eq_zero _).mp h0)
    rw [μX_of_eval_f_ne_zero hxL, μX_of_eval_f_ne_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X]

open scoped Classical in
/-- Naturality of the descent map under base change: restricting square classes after the
global `μ` is applying the local `μ` after the base change of points. -/
theorem localRes_comp_μ :
    (W.localRes L).comp (μ (W := W)) =
      (μ (W := (W⁄L).toAffine)).comp (AddMonoidHom.toMultiplicative (W.pointMap L)) := by
  refine MonoidHom.ext fun P' ↦ ?_
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    μ_apply]
  cases P with
  | zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, μ₀_zero, map_one, W.pointMap_zero L,
        μ₀_zero (W := (W⁄L).toAffine)]
  | some x y hP =>
      rw [μ₀_some, W.pointMap_some L hP, μ₀_some (W := (W⁄L).toAffine), W.localRes_μX L x]

open scoped Classical in
/-- The image of the global descent map `μ` satisfies the local condition at every extension
field: this is formal from the naturality `localRes_comp_μ`. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  rw [localCondition, ← Subgroup.map_le_iff_le_comap, MonoidHom.map_range, localRes_comp_μ]
  rintro _ ⟨P, rfl⟩
  exact ⟨_, rfl⟩

-- Under base change along an isomorphism, the descent image over `L` is the image of the
-- descent image over `K` under the local restriction of square classes.
open scoped Classical in
private lemma range_μ_of_bijective_algebraMap (h : Function.Bijective (algebraMap K L)) :
    (μ (W := (W⁄L).toAffine)).range = Subgroup.map (W.localRes L) (μ (W := W)).range := by
  -- along an isomorphism, base change of points is surjective; the rest is formal from
  -- the naturality `localRes_comp_μ`
  have hpm : Function.Surjective (W.pointMap L) := by
    rintro (_ | ⟨x, y, hP⟩)
    · exact ⟨0, W.pointMap_zero L⟩
    · obtain ⟨x', rfl⟩ := h.2 x
      obtain ⟨y', rfl⟩ := h.2 y
      exact ⟨Point.some x' y'
        ((W.map_nonsingular (algebraMap K L).injective _ _).mp hP), W.pointMap_some L _⟩
  have hsurj : Function.Surjective (AddMonoidHom.toMultiplicative (W.pointMap L)) :=
    fun P ↦ (hpm P.toAdd).imp fun _ hQ ↦ congrArg Multiplicative.ofAdd hQ
  rw [MonoidHom.map_range, localRes_comp_μ, ← MonoidHom.map_range,
    MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map]

open scoped Classical in
/-- If the base change is along an isomorphism, then the local descent map has the same
image size as the global one (via the induced isomorphism of the étale algebras). -/
theorem card_range_μ_of_bijective_algebraMap (h : Function.Bijective (algebraMap K L)) :
    Nat.card (μ (W := (W⁄L).toAffine)).range = Nat.card (μ (W := W)).range := by
  have hM := Units.modPow.bijective_map (φ := (W.mapA L).toMonoidHom)
    (W.bijective_mapA_of_bijective_algebraMap L h) 2
  rw [W.range_μ_of_bijective_algebraMap L h,
    Nat.card_congr (Subgroup.equivMapOfInjective (μ.range) (W.localRes L) hM.1).symm.toEquiv]

/-- If the base change is along an isomorphism, then the `2`-torsion of the group of points
has the same size over `L` as over `K` (the roots of `f` correspond). -/
theorem card_ker_nsmul_two_baseChange [DecidableEq L] (h : Function.Bijective (algebraMap K L)) :
    Nat.card (nsmulAddMonoidHom (α := (W⁄L).toAffine.Point) 2).ker =
      Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker := by
  rw [(W⁄L).toAffine.card_ker_nsmul_two, W.card_ker_nsmul_two]
  refine congrArg (· + 1) (Nat.card_congr (Equiv.ofBijective
    (fun x ↦ ⟨algebraMap K L x, by rw [W.eval_baseChange_f, x.2, map_zero]⟩) ⟨?_, ?_⟩)).symm
  · exact fun a b hab ↦ Subtype.ext (h.1 (Subtype.ext_iff.mp hab))
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h.2 y
    exact ⟨⟨x, h.1 (by rw [← W.eval_baseChange_f, hy, map_zero])⟩, rfl⟩

end BaseChange

/-!
### The local image at a real place

Over `ℝ` the étale algebra of the curve is `ℝ × ℂ` (when `f` has one real root) or `ℝ³` (when
`f` has three real roots). The image of the descent map consists of the sign patterns of the
`x - θᵢ` that occur on the region `{f ≥ 0}` — equivalently the classes of the `2`-torsion
points together with the trivial class — and this is a subgroup of index `2` in the full
`2`-torsion. The sign analysis is elementary (no completions or covers are involved), so we
carry it out over `ℝ` directly and transport it to a real completion by the isomorphism
`v.Completion ≃+* ℝ`.
-/

section RealPlace

/- The square-class sign layer lives in `Heights.ForMathlib.RealEtale`: for a nonzero squarefree
real polynomial `f`, the square class of a unit of `ℝ[X]/(f)` is trivial exactly when its value
at every real root of `f` is nonnegative (`Polynomial.mk_eq_one_iff_forall_eval_nonneg`, from the
sign decomposition `Polynomial.modPowEtaleEquiv`). The descent map below is one consumer. -/

variable (W' : Affine ℝ)

-- The real roots of `f`, as a type (`W'` is fixed throughout the section).
local notation "𝓡" => {x : ℝ // W'.f.eval x = 0}

-- The value of the torsion representative of `μX x` at a root `e` of `f` (instance-free); the
-- generic value `x - e` is `Polynomial.modPowEtaleEquiv_mk_C_sub_X_apply` (via `etaleEvalHom`).
private lemma eval_projFactor_torsion (x : ℝ) {e : ℝ} (he : W'.f.eval e = 0) :
    (etaleEvalHom W'.f (AdjoinRoot.mk W'.f (C x - X + W'.fCofactor x))).1 ⟨e, he⟩ =
      x - e + (W'.fCofactor x).eval e := by
  rw [etaleEvalHom_mk_fst]
  simp

-- At a root `e` distinct from the `2`-torsion `x`-coordinate, the cofactor `f / (X - x)`
-- vanishes (as `f e = 0` and `e ≠ x`), so the torsion value at `e` is just `x - e`.
private lemma eval_projFactor_torsion_ne {x e : ℝ} (hx : W'.f.eval x = 0)
    (he : W'.f.eval e = 0) (hxe : e ≠ x) :
    (etaleEvalHom W'.f (AdjoinRoot.mk W'.f (C x - X + W'.fCofactor x))).1 ⟨e, he⟩ = x - e := by
  rw [eval_projFactor_torsion]
  have h0 := congrArg (Polynomial.eval e) (W'.fCofactor_mul_eq x)
  simp only [eval_mul, eval_sub, eval_X, eval_C, hx, he, sub_zero] at h0
  rw [(mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hxe), add_zero]

/- The descent layer: the sign-class lemmas above are applied to `g = W'.f`, and combined with
the values of the `x - T` map `μX` at the real roots to compute the image of `μ` over `ℝ`. -/

-- Finiteness of the real roots and of the quadratic factors of `f`, available throughout.
instance : Finite 𝓡 := (finite_setOf_isRoot W'.f_ne_zero).to_subtype
noncomputable instance : Fintype 𝓡 := Fintype.ofFinite _
instance : Finite W'.f.Factors := Polynomial.Factors.finite W'.f_ne_zero
noncomputable instance : Fintype W'.f.Factors := Fintype.ofFinite _
noncomputable instance : Fintype {p : W'.f.Factors // (p : ℝ[X]).natDegree = 2} :=
  Fintype.ofFinite _

-- The real roots have a smallest element (`f` has at least one root).
private lemma exists_min_root (hpos : 0 < Nat.card 𝓡) :
    ∃ e₀ : 𝓡, ∀ e : 𝓡, (e₀ : ℝ) ≤ e := by
  have : Nonempty 𝓡 := (Nat.card_pos_iff.mp hpos).1
  exact ⟨Finset.univ.min' Finset.univ_nonempty,
    fun e ↦ Subtype.coe_le_coe.mpr (Finset.min'_le _ e (Finset.mem_univ e))⟩

variable [W'.IsElliptic] [W'.IsCharNeTwoNF]

instance : Finite W'.M :=
  Finite.of_equiv _ (modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f).symm.toEquiv

-- A real cubic has one or three real roots (`#roots + 2·#(quadratic factors) = 3`).
private lemma card_roots_eq_one_or_three :
    Nat.card 𝓡 = 1 ∨ Nat.card 𝓡 = 3 := by
  have h := Polynomial.card_realRoots_add_card_deg2 W'.f_ne_zero W'.squarefree_f
  rw [W'.natDegree_f, ← Nat.card_eq_fintype_card] at h
  lia

-- A negative value at some root obstructs triviality of the square class.
private lemma unit_class_ne_one_of_evalRoot_neg {a : W'.A} (ha : IsUnit a) {e : ℝ}
    (he : W'.f.eval e = 0) (hlt : (etaleEvalHom W'.f a).1 ⟨e, he⟩ < 0) :
    (QuotientGroup.mk ha.unit : W'.M) ≠ 1 := fun hone ↦
  absurd ((mk_eq_one_iff_forall_eval_nonneg W'.f_ne_zero W'.squarefree_f ha).mp hone ⟨e, he⟩)
    (not_le.mpr hlt)

-- Norm kernel: the product of the sign entries of any element of the descent image is trivial.
private lemma prod_modPowEtaleEquiv_μ_eq_one {t : W'.M} (ht : t ∈ (μ (W := W')).range) :
    (∏ e, modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f t e) = 1 := by
  rw [Polynomial.prod_modPowEtaleEquiv]
  exact (congrArg (Units.modPow.realEquivOfEven two_ne_zero even_two)
    (MonoidHom.mem_ker.mp (range_μ_le_ker_normM ht))).trans (map_one _)

-- Smallest-root kernel: the sign entry, at the smallest real root `e₀`, of the descent class of
-- any point is trivial. Otherwise the sign would be nontrivial at `e₀` and hence (the value being
-- monotone along the roots, via `eval_projFactor_torsion_ne`) at every root, contradicting the
-- trivial product over an odd number of roots.
private lemma modPowEtaleEquiv_μ₀_smallest_eq_one {e₀ : 𝓡} (hmin : ∀ e : 𝓡, (e₀ : ℝ) ≤ e)
    (hodd : Odd (Nat.card 𝓡)) (P : W'.Point) :
    modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f (W'.μ₀ P) e₀ = 1 := by
  set Φ := modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f with hΦ
  rcases P with _ | ⟨x, y, h⟩
  · change Φ (1 : W'.M) e₀ = 1; rw [map_one]; rfl
  have hprod : (∏ e, Φ (W'.μ₀ (.some x y h)) e) = 1 :=
    W'.prod_modPowEtaleEquiv_μ_eq_one ⟨.ofAdd (.some x y h), rfl⟩
  rw [Nat.card_eq_fintype_card] at hodd
  obtain ⟨e', he'⟩ := exists_eq_one_of_prod_eq_one_of_odd _ hodd hprod
  rw [μ₀_some, hΦ] at he' ⊢
  rcases eq_or_ne (W'.f.eval x) 0 with hx0 | hx0
  · rw [μX_of_eval_f_eq_zero hx0, modPowEtaleEquiv_mk_apply] at he' ⊢
    rcases eq_or_ne (e₀ : ℝ) x with he0 | he0
    · rcases eq_or_ne (e' : ℝ) x with he'x | he'x
      · rwa [show e₀ = e' from Subtype.ext (he0.trans he'x.symm)]
      · rw [W'.eval_projFactor_torsion_ne hx0 e'.2 he'x] at he'
        exact absurd (le_antisymm (by linarith) (he0 ▸ hmin e')) he'x
    · rw [W'.eval_projFactor_torsion_ne hx0 e₀.2 he0]
      linarith [hmin ⟨x, hx0⟩]
  · rw [μX_of_eval_f_ne_zero hx0, modPowEtaleEquiv_mk_C_sub_X_apply] at he' ⊢
    exact (hmin e').trans he'

-- Upper bound: every element of the descent image is, under the sign iso, both norm-trivial and
-- trivial at the smallest root — the intersection of the two kernels.
private lemma mem_kernels_of_mem_range {e₀ : 𝓡} (hmin : ∀ e : 𝓡, (e₀ : ℝ) ≤ e)
    (hodd : Odd (Nat.card 𝓡)) {t : W'.M} (ht : t ∈ (μ (W := W')).range) :
    (∏ e, modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f t e) = 1 ∧
      modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f t e₀ = 1 := by
  refine ⟨W'.prod_modPowEtaleEquiv_μ_eq_one ht, ?_⟩
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp ht
  exact W'.modPowEtaleEquiv_μ₀_smallest_eq_one hmin hodd g.toAdd

-- Transport the image by the sign iso and bound its size by the number of admissible patterns.
private lemma card_range_μ_le_card_patterns {e₀ : 𝓡} (hmin : ∀ e : 𝓡, (e₀ : ℝ) ≤ e)
    (hodd : Odd (Nat.card 𝓡)) :
    Nat.card (μ (W := W')).range ≤
      Nat.card {s : 𝓡 → Multiplicative (ZMod 2) // (∏ e, s e) = 1 ∧ s e₀ = 1} := by
  set Φ := modPowEtaleEquiv W'.f_ne_zero W'.squarefree_f
  set S : Subgroup (𝓡 → Multiplicative (ZMod 2)) :=
    (μ (W := W')).range.map (Φ : W'.M →* _) with hS
  set T : Set (𝓡 → Multiplicative (ZMod 2)) :=
    {s | (∏ e, s e) = 1 ∧ s e₀ = 1}
  have hcard : Nat.card (μ (W := W')).range = Nat.card S :=
    Nat.card_congr ((μ (W := W')).range.equivMapOfInjective _ Φ.injective).toEquiv
  have hST : (S : Set _) ⊆ T := by
    rintro s hs
    rw [SetLike.mem_coe, hS, Subgroup.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact W'.mem_kernels_of_mem_range hmin hodd ht
  rw [hcard]
  exact Nat.card_le_card_of_injective (Set.inclusion hST) (Set.inclusion_injective hST)

-- Lower bound: with three real roots the image is nontrivial — the class of the `2`-torsion point
-- `(e₀, 0)` (`e₀` the smallest root) is nontrivial, witnessed by its value `e₀ - e < 0` at any
-- other root `e`.
private lemma two_le_card_range_μ (hc : Nat.card 𝓡 = 3) :
    2 ≤ Nat.card (μ (W := W')).range := by
  obtain ⟨e₀, hmin⟩ := W'.exists_min_root (by rw [hc]; norm_num)
  obtain ⟨e, hne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [← Nat.card_eq_fintype_card, hc]; norm_num) e₀
  have hmem : W'.μX (e₀ : ℝ) ∈ (μ (W := W')).range :=
    MonoidHom.mem_range.mpr ⟨.ofAdd (.some _ 0 (W'.nonsingular_of_eval_f_eq_zero e₀.2)), rfl⟩
  have hne1 : W'.μX (e₀ : ℝ) ≠ 1 := by
    rw [μX_of_eval_f_eq_zero e₀.2]
    refine W'.unit_class_ne_one_of_evalRoot_neg _ e.2 ?_
    rw [W'.eval_projFactor_torsion_ne e₀.2 e.2 (fun heq ↦ hne (Subtype.ext heq))]
    have h1 : (e₀ : ℝ) ≤ e := hmin e
    have h2 : (e₀ : ℝ) ≠ e := fun heq ↦ hne (Subtype.ext heq.symm)
    linarith [lt_of_le_of_ne h1 h2]
  exact Finite.one_lt_card_iff_nontrivial.mpr
    ⟨⟨_, hmem⟩, 1, fun heq ↦ hne1 (congrArg Subtype.val heq)⟩

/-- The local descent identity at the real place: `2·#(im μ_ℝ) = #E(ℝ)[2]`. The étale algebra is
`ℝ × ℂ` (one real root) or `ℝ³` (three real roots), and under `modPowEtaleEquiv` the image is a
subgroup of the sign patterns that are norm-even and trivial at the smallest root; by
`card_range_μ_le_card_patterns` that subgroup has size `≤ 1` resp. `≤ 2`, and `two_le_card_range_μ`
gives `≥ 2` in the second case. -/
theorem two_mul_card_range_μ_real :
    2 * Nat.card (μ (W := W')).range =
      Nat.card (nsmulAddMonoidHom (α := W'.Point) 2).ker := by
  rw [W'.card_ker_nsmul_two]
  have hdich := W'.card_roots_eq_one_or_three
  obtain ⟨e₀, hmin⟩ := W'.exists_min_root (by rcases hdich with h | h <;> rw [h] <;> norm_num)
  have hodd : Odd (Nat.card 𝓡) := by
    rcases hdich with h | h <;> rw [h] <;> norm_num
  have hup := W'.card_range_μ_le_card_patterns hmin hodd
  rcases hdich with h | h
  · have him : Nat.card (μ (W := W')).range = 1 := le_antisymm
      (hup.trans_eq (card_prodEvalKer_one (by rw [← Nat.card_eq_fintype_card]; exact h) e₀))
      Nat.card_pos
    rw [h, him]
  · have him : Nat.card (μ (W := W')).range = 2 := le_antisymm
      (hup.trans_eq (card_prodEvalKer_three (by rw [← Nat.card_eq_fintype_card]; exact h) e₀))
      (W'.two_le_card_range_μ h)
    rw [h, him]

end RealPlace

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

variable {F : Type*} [Field F] [NumberField F] (W : Affine F)

/- Local notation: `F_[v]` and `𝒪_[v]` are the completion of `F` at the finite place `v` and
its valuation ring, `𝕎[v]` is the base change of `W` to `F_[v]` (as an affine curve), and
`𝕃 p` is the field factor `F[X]/(p)` of the étale algebra attached to a factor `p` of `f`. -/
local notation:max "F_[" v "]" => HeightOneSpectrum.adicCompletion F v
local notation:max "𝒪_[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v
local notation:max "𝕎[" v "]" =>
  WeierstrassCurve.toAffine (W⁄(HeightOneSpectrum.adicCompletion F v))
local notation:max "𝕃" p:max => AdjoinRoot (p : F[X])

instance instFiniteQuotientAsIdeal (v : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ v.asIdeal) :=
  v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

/-!
The passage between the global and the local conditions relates unramifiedness of a square
class `m` of the étale algebra `A = F[X]/(f)` at the primes of the field factors of `A` above
a finite place `v` to unramifiedness of the localization of `m` over the valuation ring of
`F_v`. Here "unramified over the valuation ring" is expressed by `selmerGroupA` of the
base-changed curve over `𝒪_[v]` — for a good `v` the local set of bad primes is empty, so
this is precisely the subgroup of square classes with even valuations.

Both directions are proved. Global to local (`localRes_mem_selmerGroupA`): every monic
irreducible factor `q` of `f` over `F_v` divides the image of a unique factor `p` of `f`
over `F`, the induced embedding `F[X]/(p) → F_v[X]/(q)` contracts the prime of the local
ring of integers to a prime `w ∣ v` of the ring of integers of `F[X]/(p)`, and valuations
transform by the ramification index along this embedding, which preserves evenness.

Local to global (`mem_selmerGroupA_of_forall_localRes`): conversely, every prime `w ∣ v`
of a field factor `F[X]/(p)` arises from a local factor `q`, namely the minimal polynomial
over `F_v` of the image of the root in the completion of `F[X]/(p)` at `w`
(`exists_localFactor`). The embedding `F_v[X]/(q) → (F[X]/(p))_w` transports evenness of the
valuation from the primes of the local ring of integers to the valuation of the completion,
which restricts to the `w`-adic valuation. This uses the extension `F_v →+* (F[X]/(p))_w` of
adic completions from `Heights.ForMathlib.AdicCompletionExtension` (adapted from the FLT
project) — but not the full decomposition `A ⊗ F_v ≅ ∏ (L_p)_w` of the completed étale
algebra: for parity of valuations, ramification is harmless in both directions.

The remaining local statement — at a good place, the image of `μ_v` is exactly the group of
unramified square classes with trivial norm (`selmerGroupA_inf_ker_normM_eq_range_μ`) — is
proved by counting both sides against `#E(F_v)[2]`. All in all, the reduction of the 2-Selmer
group to the bad places now rests only on the two `sorry`ed interface statements of
`Heights.ForMathlib.FormalGroup`.
-/

section Semilocal

open AdjoinRoot IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 F))

-- The instance found by unifying through the `ringOfIntegersFactor` abbreviation carries
-- mismatched `SMul` arguments; pin them to the `Algebra`-derived ones.
private instance instIsScalarTowerRingOfIntegersFactor (p : W.f.Factors) :
    @IsScalarTower (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq' rfl

-- Goodness transfers to the completion: over the valuation ring of a good place, the
-- base-changed curve has no bad primes.
private lemma badPrimes_adicCompletionIntegers {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    𝕎[v].badPrimes 𝒪_[v] = ∅ := by
  ext P
  simp only [Set.mem_empty_iff_false, iff_false]
  have hPval (z : F) : P.valuation F_[v] (algebraMap F F_[v] z) = v.valuation F z := by
    rw [P.eq_maximalIdeal, valuation_maximalIdeal_adicCompletionIntegers]
    exact v.valuedAdicCompletion_eq_valuation' z
  have hone {y : F} {c : F_[v]} (hc : c = algebraMap F F_[v] y)
      (h : P.valuation F_[v] c ≠ 1) : v.valuation F y ≠ 1 := by
    rwa [hc, hPval] at h
  have hsupp {y : F} {c : F_[v]} (hc : c = algebraMap F F_[v] y)
      (h : P ∈ HeightOneSpectrum.Support 𝒪_[v] c) : ¬ v.valuation F y ≤ 1 :=
    not_le.mpr <| by rwa [HeightOneSpectrum.Support, Set.mem_setOf_eq, hc, hPval] at h
  rintro ((((h | h) | h) | h) | h)
  · exact hone (by rw [map_ofNat]) h (W.valuation_two_eq_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hone (map_Δ ..) h (W.valuation_Δ_eq_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hsupp (map_a₂ ..) h (W.valuation_a₂_le_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hsupp (map_a₄ ..) h (W.valuation_a₄_le_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hsupp (map_a₆ ..) h (W.valuation_a₆_le_one_of_notMem_badPrimes (𝓞 F) hv)

-- At a good place, the residue characteristic is odd.
private lemma two_notMem_asIdeal_of_notMem_badPrimes {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) : (2 : 𝓞 F) ∉ v.asIdeal := by
  have h := W.valuation_two_eq_one_of_notMem_badPrimes (𝓞 F) hv
  rw [← map_ofNat (algebraMap (𝓞 F) F) 2] at h
  exact v.valuation_eq_one_iff_notMem.mp h

-- The base-change map on a field factor is integral on the ring of integers.
private lemma isIntegral_mapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (x : W.ringOfIntegersFactor (𝓞 F) p) :
    _root_.IsIntegral 𝒪_[v] (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (x : 𝕃 p)) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  refine ⟨P.map (algebraMap (𝓞 F) 𝒪_[v]), hPm.map _, ?_⟩
  have h2 := congrArg (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq) hPe
  rw [map_zero, Polynomial.hom_eval₂] at h2
  rw [Polynomial.eval₂_map]
  exact (congrArg (fun φ ↦ Polynomial.eval₂ φ
    (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (x : 𝕃 p)) P)
    (map_comp_algebraMap v hq)).symm.trans h2

-- The base-change map on the rings of integers of the field factors: the restriction of
-- `AdjoinRoot.map` to the integral closures.
private noncomputable def integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    W.ringOfIntegersFactor (𝓞 F) p →+* 𝕎[v].ringOfIntegersFactor 𝒪_[v] q :=
  ((AdjoinRoot.map (algebraMap F F_[v]) _ _ hq).comp
    (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p))).codRestrict
      (integralClosure 𝒪_[v] (AdjoinRoot (q : F_[v][X]))).toSubring
      fun x ↦ W.isIntegral_mapOfDvd v hq x

-- The square of ring homomorphisms defining `integerMapOfDvd`.
private lemma algebraMap_comp_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (algebraMap (𝕎[v].ringOfIntegersFactor 𝒪_[v] q) (AdjoinRoot (q : F_[v][X]))).comp
        (W.integerMapOfDvd v hq) =
      (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq).comp
        (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)) :=
  RingHom.ext fun _ ↦ rfl

-- The square `𝓞 F → 𝒪_v → B_q` versus `𝓞 F → B_p → B_q` on the rings of integers.
private lemma integerMapOfDvd_comp_algebraMap {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (W.integerMapOfDvd v hq).comp (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) =
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)).comp
        (algebraMap (𝓞 F) 𝒪_[v]) := by
  ext c
  exact RingHom.congr_fun (map_comp_algebraMap v hq) c

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/- The `F_v`-algebra structure on the completion of the field factor `F[X]/(p)` at a place
`w` above `v`, via `adicCompletionExtension`; a local instance for the constructions below. -/
@[implicit_reducible]
private noncomputable def algebraAdicCompletionFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    Algebra F_[v] (w.adicCompletion (𝕃 p)) :=
  (adicCompletionExtension F (𝕃 p) v w).toAlgebra

attribute [local instance] algebraAdicCompletionFactor

-- The square `F → F_v → (F[X]/(p))_w` = `F → F[X]/(p) → (F[X]/(p))_w` of coefficient maps.
private lemma algebraMap_adicCompletion_comp (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (algebraMap F_[v] (w.adicCompletion (𝕃 p))).comp (algebraMap F F_[v]) =
      (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))).comp (algebraMap F (𝕃 p)) := by
  ext c
  exact adicCompletionExtension_coe F (𝕃 p) v w c

-- Evaluating a base-changed polynomial at the image of the root in the completion.
private lemma aeval_root_adicCompletion (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (g : F[X]) :
    Polynomial.aeval (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X])))
        (g.map (algebraMap F F_[v])) =
      algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (AdjoinRoot.mk (p : F[X]) g) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← aeval_eq, Polynomial.aeval_def,
    Polynomial.hom_eval₂]
  exact congrArg (fun φ ↦ Polynomial.eval₂ φ
    (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) g)
    (W.algebraMap_adicCompletion_comp v p w)

-- The image of the root in the completion is integral over `F_v`.
private lemma isIntegral_root_adicCompletion (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    _root_.IsIntegral F_[v]
      (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) := by
  refine ⟨(p : F[X]).map (algebraMap F F_[v]), p.monic.map _, ?_⟩
  rw [← Polynomial.aeval_def, W.aeval_root_adicCompletion v p w, AdjoinRoot.mk_self, map_zero]

/- The local factor of `f` attached to a place `w` of the field factor `F[X]/(p)` above `v`:
the minimal polynomial over `F_v` of the image of the root in the completion at `w`. -/
private noncomputable def localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    𝕎[v].f.Factors :=
  ⟨minpoly F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))),
    minpoly.monic (W.isIntegral_root_adicCompletion v p w),
    minpoly.irreducible (W.isIntegral_root_adicCompletion v p w), by
      rw [baseChange_f]
      refine minpoly.dvd _ _ ?_
      rw [W.aeval_root_adicCompletion v p w, AdjoinRoot.mk_eq_zero.mpr p.dvd, map_zero]⟩

private lemma coe_localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (W.localFactor v p w : F_[v][X]) =
      minpoly F_[v] (algebraMap (𝕃 p)
        (w.adicCompletion (𝕃 p)) (root (p : F[X]))) :=
  rfl

/- The embedding of the local field factor into the completion, sending the root of the
local factor to the image of the global root. -/
private noncomputable def localFactorEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    AdjoinRoot (W.localFactor v p w : F_[v][X]) →+*
      w.adicCompletion (𝕃 p) :=
  AdjoinRoot.lift (algebraMap F_[v] (w.adicCompletion (𝕃 p)))
    (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) (by
      rw [W.coe_localFactor v p w]
      exact minpoly.aeval _ _)

private lemma localFactorEmb_of (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (c : F_[v]) :
    W.localFactorEmb v p w (AdjoinRoot.of _ c) =
      algebraMap F_[v] (w.adicCompletion (𝕃 p)) c :=
  AdjoinRoot.lift_of _

-- The square `𝒪_v → F_v[X]/(q) → (F[X]/(p))_w` = `𝒪_v → 𝒪_w → (F[X]/(p))_w`.
private lemma localFactorEmb_comp_algebraMap (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (W.localFactorEmb v p w).comp
        (algebraMap 𝒪_[v] (AdjoinRoot (W.localFactor v p w : F_[v][X]))) =
      (algebraMap (w.adicCompletionIntegers (𝕃 p)) (w.adicCompletion (𝕃 p))).comp
        (adicCompletionIntegersExtension F (𝕃 p) v w) := by
  ext c
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply 𝒪_[v] F_[v]
      (AdjoinRoot (W.localFactor v p w : F_[v][X])),
    AdjoinRoot.algebraMap_eq, W.localFactorEmb_of v p w]
  rfl

-- The embedding maps the local ring of integers into the integers of the completion.
private lemma localFactorEmb_mem_adicCompletionIntegers (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (x : 𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w)) :
    W.localFactorEmb v p w (x : AdjoinRoot (W.localFactor v p w : F_[v][X])) ∈
      w.adicCompletionIntegers (𝕃 p) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  have h2 := congrArg (W.localFactorEmb v p w) hPe
  rw [map_zero, Polynomial.hom_eval₂, W.localFactorEmb_comp_algebraMap v p w] at h2
  have hint2 : _root_.IsIntegral (w.adicCompletionIntegers (𝕃 p))
      (W.localFactorEmb v p w (x : AdjoinRoot (W.localFactor v p w : F_[v][X]))) := by
    refine ⟨P.map (adicCompletionIntegersExtension F (𝕃 p) v w), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h2
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint2
  rw [← hy]
  exact y.2

/- The restriction of `localFactorEmb` to the rings of integers. -/
private noncomputable def localFactorIntegerEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w) →+*
      w.adicCompletionIntegers (𝕃 p) :=
  ((W.localFactorEmb v p w).comp (algebraMap _ _)).codRestrict
    (w.adicCompletionIntegers (𝕃 p)).toSubring
    fun x ↦ W.localFactorEmb_mem_adicCompletionIntegers v p w x

private lemma algebraMap_comp_localFactorIntegerEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (algebraMap (w.adicCompletionIntegers (𝕃 p))
        (w.adicCompletion (𝕃 p))).comp (W.localFactorIntegerEmb v p w) =
      (W.localFactorEmb v p w).comp (algebraMap _ _) :=
  RingHom.ext fun _ ↦ rfl

-- The contraction of the maximal ideal of `𝒪_w` to the local ring of integers is nonzero.
private lemma comap_localFactorIntegerEmb_ne_bot (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p))).asIdeal.comap
      (W.localFactorIntegerEmb v p w) ≠ ⊥ := by
  intro h0
  have hsq0 : (W.localFactorIntegerEmb v p w).comp
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w))) =
      adicCompletionIntegersExtension F (𝕃 p) v w := by
    ext c
    exact RingHom.congr_fun (W.localFactorEmb_comp_algebraMap v p w) c
  have h1 := congrArg (Ideal.comap
    (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w)))) h0
  rw [Ideal.comap_comap, hsq0, IsDiscreteValuationRing.asIdeal_maximalIdeal,
    comap_maximalIdeal_adicCompletionIntegersExtension,
    ← RingHom.ker_eq_comap_bot] at h1
  have hinj : Function.Injective
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w))) := by
    have hinj' : Function.Injective
        (algebraMap 𝒪_[v] (AdjoinRoot (W.localFactor v p w : F_[v][X]))) := by
      rw [IsScalarTower.algebraMap_eq 𝒪_[v] F_[v]
        (AdjoinRoot (W.localFactor v p w : F_[v][X]))]
      exact (algebraMap F_[v] (AdjoinRoot (W.localFactor v p w : F_[v][X]))).injective.comp
        (IsFractionRing.injective _ _)
    exact fun a b hab ↦ hinj' (congrArg Subtype.val hab)
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj] at h1
  exact IsDiscreteValuationRing.not_a_field _ h1

-- The embedding of the local field factor is compatible with the CRT projections.
private lemma localFactorEmb_projFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (a : W.A) :
    W.localFactorEmb v p w (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w) (W.mapA F_[v] a)) =
      algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))
        (projFactor W.f_ne_zero W.squarefree_f p a) := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [mapA_mk, projFactor_mk, projFactor_mk, localFactorEmb, AdjoinRoot.lift_mk]
  exact W.aeval_root_adicCompletion v p w g

-- Unfolding of the local unramifiedness condition into per-factor divisibilities.
private lemma localRes_mem_selmerGroupA_iff (a : W.Aˣ) :
    W.localRes F_[v] (QuotientGroup.mk a) ∈ 𝕎[v].selmerGroupA 𝒪_[v] ↔
    ∀ (q : 𝕎[v].f.Factors)
      (w' : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)),
      w' ∉ HeightOneSpectrum.primesAbove 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)
        (𝕎[v].badPrimes 𝒪_[v]) →
      (2 : ℤ) ∣ Multiplicative.toAdd (w'.valuationOfNeZero
        (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toMonoidHom
          (Units.map (W.mapA F_[v]).toMonoidHom a))) := by
  rw [localRes_mk]
  exact 𝕎[v].mem_selmerGroupA_unit_iff 𝒪_[v] _

-- Transport of the divisibility from the contracted prime of the local factor to `w`.
private lemma dvd_toAdd_valuationOfNeZero_of_localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (a : W.Aˣ)
    (h : (2 : ℤ) ∣ Multiplicative.toAdd ((HeightOneSpectrum.comapOfNeBot
        (W.localFactorIntegerEmb v p w) (IsDiscreteValuationRing.maximalIdeal _)
        (W.comap_localFactorIntegerEmb_ne_bot v p w)).valuationOfNeZero
      (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w)).toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a)))) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
      (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a)) := by
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (W.localFactorEmb v p w) (W.localFactorIntegerEmb v p w)
    (W.algebraMap_comp_localFactorIntegerEmb v p w)
    (IsDiscreteValuationRing.maximalIdeal _)
    (W.comap_localFactorIntegerEmb_ne_bot v p w) _ h
  have hunits : Units.map (W.localFactorEmb v p w : _ →* _)
      (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w)).toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a)) =
      Units.map (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))).toMonoidHom
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a) :=
    Units.ext (W.localFactorEmb_projFactor v p w (a : W.A))
  rw [hunits,
    HeightOneSpectrum.valuationOfNeZero_maximalIdeal_adicCompletionIntegers] at hkey
  exact hkey

-- The double contraction of a prime of the local ring of integers is `v`.
private lemma comap_comap_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    (w.asIdeal.comap (W.integerMapOfDvd v hq)).comap
      (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) = v.asIdeal := by
  rw [Ideal.comap_comap, integerMapOfDvd_comp_algebraMap W v hq, ← Ideal.comap_comap]
  have h1 : w.asIdeal.comap (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) =
      IsLocalRing.maximalIdeal 𝒪_[v] :=
    IsLocalRing.eq_maximalIdeal (w.below 𝒪_[v]).isMaximal
  rw [h1, HeightOneSpectrum.comap_maximalIdeal_adicCompletionIntegers]

-- The contraction of a prime of the local ring of integers to the global one is nonzero.
private lemma comap_integerMapOfDvd_ne_bot {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    w.asIdeal.comap (W.integerMapOfDvd v hq) ≠ ⊥ := by
  intro h0
  have h1 := W.comap_comap_integerMapOfDvd v hq w
  rw [h0] at h1
  have hinj : Function.Injective (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) :=
    FaithfulSMul.algebraMap_injective _ _
  rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj] at h1
  exact v.ne_bot h1.symm

-- The contracted prime lies over `v`.
private lemma below_comapOfNeBot_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w
      (W.comap_integerMapOfDvd_ne_bot v hq w)).below (𝓞 F) = v :=
  HeightOneSpectrum.ext (W.comap_comap_integerMapOfDvd v hq w)

-- The base-change maps of the field factors are compatible with the CRT projections.
private lemma map_projFactor {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) (a : W.A) :
    AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (projFactor W.f_ne_zero W.squarefree_f p a) =
      projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q (W.mapA F_[v] a) := by
  obtain ⟨g, rfl⟩ := mk_surjective a
  rw [projFactor_mk, AdjoinRoot.map_mk, mapA_mk, projFactor_mk]

end Semilocal

variable [W.IsElliptic] [W.IsCharNeTwoNF]

open AdjoinRoot in
open scoped Classical in
/-- Semilocal comparison, global to local: an `S`-unramified square class localizes to an
unramified class at every good finite place.

Each monic irreducible factor `q` of `f` over `F_v` divides the image of a factor `p` of `f`;
the induced embedding `F[X]/(p) → F_v[X]/(q)` restricts to the rings of integers, the prime
of the local ring of integers contracts to a prime `w ∣ v`, and the local valuation is the
`w`-adic one raised to the ramification index, so evenness transfers. -/
theorem localRes_mem_selmerGroupA {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ W.badPrimes (𝓞 F))
    {m : W.M} (hm : m ∈ W.selmerGroupA (𝓞 F)) :
    W.localRes F_[v] m ∈ 𝕎[v].selmerGroupA 𝒪_[v] := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply] at hm ⊢
  rw [mem_selmerGroupA_unit_iff] at hm
  rw [W.localRes_mem_selmerGroupA_iff v a]
  intro q w hw
  -- find the global factor `p` below the local factor `q`
  obtain ⟨p, hq⟩ := Polynomial.Factors.exists_dvd_map (algebraMap F F_[v])
    W.f_ne_zero q.prime (q.dvd.trans (W.baseChange_f F_[v]).dvd)
  -- the prime of the global field factor below `w`
  have hne := W.comap_integerMapOfDvd_ne_bot v hq w
  have hbelow := W.below_comapOfNeBot_integerMapOfDvd v hq w
  -- the global unramifiedness hypothesis at that prime
  have hdvd := hm p (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w hne) fun hmem ↦
    hv (hbelow ▸ (HeightOneSpectrum.mem_primesAbove_iff (𝓞 F) _ _ _).mp hmem)
  -- transport along the embedding of field factors
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq) (W.integerMapOfDvd v hq)
    (W.algebraMap_comp_integerMapOfDvd v hq) w hne _ hdvd
  have hunits : Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a) =
      Units.map (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq : _ →* _)
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a) :=
    Units.ext (W.map_projFactor v hq (a : W.A)).symm
  rw [hunits]
  exact hkey

open AdjoinRoot in
open scoped Classical in
/-- Semilocal comparison, local to global: a square class that localizes to an unramified
class at every finite place is `S`-unramified.

Every prime `w` of a field factor `F[X]/(p)` above a good place `v` arises from a factor of
`f` over `F_v`: the minimal polynomial of the image of the root in the completion at `w`
(`localFactor`). Evenness of the valuation transports from the primes of the local ring of
integers through the completion `(F[X]/(p))_w` back to `w`. -/
theorem mem_selmerGroupA_of_forall_localRes {m : W.M}
    (hm : ∀ v : HeightOneSpectrum (𝓞 F),
      W.localRes F_[v] m ∈
        𝕎[v].selmerGroupA 𝒪_[v]) :
    m ∈ W.selmerGroupA (𝓞 F) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply]
  rw [mem_selmerGroupA_unit_iff]
  intro p w hw
  have hv : w.below (𝓞 F) ∉ W.badPrimes (𝓞 F) := W.below_notMem_badPrimes (𝓞 F) p hw
  refine W.dvd_toAdd_valuationOfNeZero_of_localFactor (w.below (𝓞 F)) p w a ?_
  refine (W.localRes_mem_selmerGroupA_iff (w.below (𝓞 F)) a).mp (hm (w.below (𝓞 F))) _ _ ?_
  rw [HeightOneSpectrum.mem_primesAbove_iff, W.badPrimes_adicCompletionIntegers hv]
  exact Set.notMem_empty _

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
-- `#(𝒪_v/2𝒪_v) = (#𝔽_v)^(v(2))`: reduce to `cardQuot` of the corresponding power of the
-- maximal ideal via the valuation of `2`, and compare the residue fields.
private lemma index_range_nsmul_two (v : HeightOneSpectrum (𝓞 F)) :
    (nsmulAddMonoidHom (α := 𝒪_[v]) 2).range.index =
      Nat.card (𝓞 F ⧸ v.asIdeal) ^
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
  have h2v : Valued.v (algebraMap 𝒪_[v] F_[v] (2 : 𝒪_[v])) =
      WithZero.exp (-((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors : ℤ)) := by
    rw [map_ofNat, ← map_ofNat (algebraMap F F_[v]) 2,
      show Valued.v (algebraMap F F_[v] (2 : F)) = v.valuation F 2 from
        v.valuedAdicCompletion_eq_valuation' 2,
      ← map_ofNat (algebraMap (𝓞 F) F) 2, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_if_neg v two_ne_zero]
  rw [AddMonoidHom.range_nsmulAddMonoidHom, Nat.cast_ofNat]
  calc (Ideal.span {(2 : 𝒪_[v])}).toAddSubgroup.index
      = Nat.card (𝒪_[v] ⧸ Ideal.span {(2 : 𝒪_[v])}) := rfl
    _ = Nat.card (𝒪_[v] ⧸ IsLocalRing.maximalIdeal 𝒪_[v] ^ (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors) :=
        Nat.card_congr (Ideal.quotEquivOfEq (v.span_singleton_eq_maximalIdeal_pow h2v)).toEquiv
    _ = Submodule.cardQuot (IsLocalRing.maximalIdeal 𝒪_[v] ^ (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors) :=
        (Submodule.cardQuot_apply _).symm
    _ = Submodule.cardQuot (IsLocalRing.maximalIdeal 𝒪_[v]) ^ (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors :=
        cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field _)
    _ = Nat.card (𝓞 F ⧸ v.asIdeal) ^ (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
        rw [Submodule.cardQuot_apply,
          ← Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv]

open scoped Classical in
/-- The size of the local image at a finite place `v`:
`#(im μ_v) = #E(F_v)[2] · (#𝔽_v)^(v(2))`. For odd residue characteristic the second factor
is `1`; the general formula is `#E(F_v)[2] · ‖2‖_v⁻¹`.

The formal-group input (`Heights.ForMathlib.FormalGroup`, still `sorry`ed) is that a
finite-index subgroup of `E(F_v)` is isomorphic to `(𝒪_v, +)`; the quantity
`#(G/2G) / #G[2]` is insensitive to passing to that subgroup
(`AddSubgroup.index_range_nsmul_mul_card_ker`), and for `(𝒪_v, +)` it is
`#(𝒪_v/2𝒪_v) = (#𝔽_v)^(v(2))`. -/
theorem card_range_μ_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (μ (W := 𝕎[v])).range =
      Nat.card (nsmulAddMonoidHom (α := 𝕎[v].Point) 2).ker *
        Nat.card (𝓞 F ⧸ v.asIdeal) ^
          (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors := by
  obtain ⟨U, hUfin, ⟨e⟩⟩ :=
    exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers v 𝕎[v]
  -- `#(im μ) = [E(F_v) : 2·E(F_v)]`
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (μ (W := 𝕎[v]))).toEquiv,
    ker_μ_eq, ← Subgroup.index_eq_card, AddSubgroup.index_toSubgroup]
  -- the multiplication-by-2 kernel of `U ≃+ 𝒪_v` is trivial, as `𝒪_v` is torsion-free
  have hczO : CharZero 𝒪_[v] :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (𝓞 F) 𝒪_[v])
  have hker : Nat.card ((nsmulAddMonoidHom (α := U) 2)).ker = 1 := by
    have : IsAddTorsionFree U := Function.Injective.isAddTorsionFree e.toAddMonoidHom e.injective
    rw [AddMonoidHom.ker_nsmulAddMonoidHom two_ne_zero]
    exact AddSubgroup.card_bot
  -- the Euler-characteristic identity for the finite-index subgroup `U`
  have hchi := AddSubgroup.index_range_nsmul_mul_card_ker U 2
  rw [hker, mul_one] at hchi
  rw [hchi]
  congr 1
  -- transport `[U : 2U]` to `𝒪_v` and count there
  rw [e.index_range_nsmulAddMonoidHom 2, index_range_nsmul_two v]

open scoped Classical in
/-- The size of the local image at a finite place of odd residue characteristic:
`#(im μ_v) = #E(F_v)[2]`. -/
theorem card_range_μ_adicCompletion_of_two_notMem {v : HeightOneSpectrum (𝓞 F)}
    (hv : (2 : 𝓞 F) ∉ v.asIdeal) :
    Nat.card (μ (W := 𝕎[v])).range =
      Nat.card (nsmulAddMonoidHom (α := 𝕎[v].Point) 2).ker := by
  have h0 : (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {(2 : 𝓞 F)})).factors = 0 := by
    by_contra h
    have h1 := (v.le_count_iff two_ne_zero 1).mp (Nat.one_le_iff_ne_zero.mpr h)
    rw [pow_one] at h1
    exact hv h1
  rw [W.card_range_μ_adicCompletion v, h0, pow_zero, mul_one]

-- `NumberField F` is needed by the statement (via `InfinitePlace F`) but erased from the proof
set_option linter.unusedSectionVars false in
open scoped Classical in
/-- The size of the local image at a real place: `#(im μ_v) = #E(ℝ)[2] / 2` (that is, `2` if
the cubic has three real roots, and `1` otherwise).

Proof by transport of the sign analysis over `ℝ` (`two_mul_card_range_μ_real`) along the
isomorphism `v.Completion ≃+* ℝ`: base change is along an isomorphism, so both the image of
the descent map (`card_range_μ_of_bijective_algebraMap`) and the `2`-torsion of the group of
points (`card_ker_nsmul_two_baseChange`) keep their size. -/
theorem card_range_μ_completion_isReal {v : InfinitePlace F} (hv : v.IsReal) :
    2 * Nat.card (μ (W := (W⁄v.Completion).toAffine)).range =
      Nat.card (nsmulAddMonoidHom (α := (W⁄v.Completion).toAffine.Point) 2).ker := by
  classical
  set W' := (W⁄v.Completion).toAffine
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  letI : Algebra v.Completion ℝ := (e : v.Completion →+* ℝ).toAlgebra
  have hbij : Function.Bijective (algebraMap v.Completion ℝ) := e.bijective
  rw [← W'.card_range_μ_of_bijective_algebraMap (L := ℝ) hbij,
    ← W'.card_ker_nsmul_two_baseChange (L := ℝ) hbij]
  exact (W'⁄ℝ).toAffine.two_mul_card_range_μ_real

-- the statement lives with its number-field siblings; `NumberField F` and `DecidableEq F` are
-- part of the ambient section but the content is the general `card_range_μ_of_isAlgClosed`
set_option linter.unusedSectionVars false in
open scoped Classical in
/-- The local image at a complex place is trivial: over an algebraically closed field, every
unit of the étale algebra is a square, so the whole group of square classes is trivial. -/
theorem card_range_μ_completion_isComplex {v : InfinitePlace F} (hv : v.IsComplex) :
    Nat.card (μ (W := (W⁄v.Completion).toAffine)).range = 1 := by
  have halg : IsAlgClosed v.Completion :=
    .of_ringEquiv' (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  exact W.card_range_μ_of_isAlgClosed v.Completion

section LocalCount

open AdjoinRoot IsDedekindDomain.HeightOneSpectrum

open scoped Classical

variable (v : HeightOneSpectrum (𝓞 F))

-- the instances are needed by the statement but are erased from the proof term
set_option linter.unusedSectionVars false in
-- The étale algebra of the base-changed curve has dimension `3`.
private lemma finrank_baseChange_A : Module.finrank F_[v] 𝕎[v].A = 3 := by
  have h := (AdjoinRoot.powerBasis' 𝕎[v].monic_f).finrank
  rw [AdjoinRoot.powerBasis'_dim, natDegree_f] at h
  exact h

/- The set of factors of the base-changed cubic is a finite type. -/
@[implicit_reducible]
private noncomputable def instFintypeFactorsBaseChange : Fintype 𝕎[v].f.Factors :=
  have : Finite 𝕎[v].f.Factors := Polynomial.Factors.finite 𝕎[v].f_ne_zero
  Fintype.ofFinite _

attribute [local instance] instFintypeFactorsBaseChange

-- the instances are needed by the statement but are erased from the proof term
set_option linter.unusedSectionVars false in
-- Degree counting for the squarefree cubic: `2 ^ (g - 1) ≤ r + 1` for `g` factors, `r` of them
-- linear — the pointwise bound `2 ≤ deg q + [deg q = 1]` sums to `2g ≤ 3 + r`, and `g ≤ 3`.
private lemma two_pow_le_card_linear_factors :
    2 ^ (Nat.card 𝕎[v].f.Factors - 1) ≤
      Nat.card {q : 𝕎[v].f.Factors // (q : F_[v][X]).natDegree = 1} + 1 := by
  have key (g r : ℕ) (hg : g ≤ 3) (h2g : 2 * g ≤ 3 + r) : 2 ^ (g - 1) ≤ r + 1 := by
    interval_cases g <;> lia
  have hdeg : ∑ q : 𝕎[v].f.Factors, (q : F_[v][X]).natDegree ≤ 3 :=
    natDegree_f 𝕎[v] ▸ Polynomial.Factors.sum_natDegree_le 𝕎[v].f_ne_zero
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype (fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1)]
  refine key _ _ ?_ ?_
  · rw [← Finset.card_univ, Finset.card_eq_sum_ones]
    exact (Finset.sum_le_sum fun q _ ↦ q.irreducible.natDegree_pos).trans hdeg
  · calc 2 * Fintype.card 𝕎[v].f.Factors
        = ∑ _q : 𝕎[v].f.Factors, 2 := by simp [mul_comm]
      _ ≤ ∑ q : 𝕎[v].f.Factors,
            ((q : F_[v][X]).natDegree + if (q : F_[v][X]).natDegree = 1 then 1 else 0) :=
        Finset.sum_le_sum fun q _ ↦ by have := q.irreducible.natDegree_pos; grind
      _ = (∑ q : 𝕎[v].f.Factors, (q : F_[v][X]).natDegree) +
            (Finset.univ.filter fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1).card := by
        rw [Finset.sum_add_distrib, Finset.card_filter]
      _ ≤ 3 + _ := Nat.add_le_add_right hdeg _

/-- The class of (the image of) a unit of `𝒪_v` in the square classes of the étale algebra
of the base-changed curve. -/
private noncomputable def scalarClass (c : 𝒪_[v]ˣ) : Units.modPow 𝕎[v].A 2 :=
  QuotientGroup.mk (Units.map (algebraMap F_[v] 𝕎[v].A).toMonoidHom
    (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c))

-- The projection of a scalar to a field factor is the scalar.
private lemma projFactor_algebraMap (q : 𝕎[v].f.Factors) (c : F_[v]) :
    projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q (algebraMap F_[v] 𝕎[v].A c) =
      algebraMap F_[v] (AdjoinRoot (q : F_[v][X])) c := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C (f := 𝕎[v].f) c, projFactor_mk,
    AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

-- The component of a scalar unit of `𝒪_v` in a field factor has valuation `1` everywhere:
-- it is the image of a unit of the factor's ring of integers.
private lemma valuation_projFactor_scalar (q : 𝕎[v].f.Factors)
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) (c : 𝒪_[v]ˣ) :
    w.valuation (AdjoinRoot (q : F_[v][X]))
      ((Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toMonoidHom
        (Units.map (algebraMap F_[v] 𝕎[v].A).toMonoidHom
          (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c)) :
        AdjoinRoot (q : F_[v][X]))) = 1 := by
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [W.projFactor_algebraMap v q,
    ← IsScalarTower.algebraMap_apply 𝒪_[v] F_[v] (AdjoinRoot (q : F_[v][X])),
    IsScalarTower.algebraMap_apply 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)
      (AdjoinRoot (q : F_[v][X])),
    valuation_of_algebraMap]
  refine (intValuation_eq_one_iff_mem_primeCompl _ _).mpr fun hmem ↦ ?_
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
    (c.isUnit.map (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q))))

-- The norm of a scalar class is the class of the scalar: the norm of a scalar is its cube.
private lemma normM_scalarClass (c : 𝒪_[v]ˣ) :
    normM (W := 𝕎[v]) (W.scalarClass v c) =
      QuotientGroup.mk (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c) := by
  rw [scalarClass, normM, Units.modPow.map_mk]
  have ha : Units.map (Algebra.norm F_[v])
      (Units.map (algebraMap F_[v] 𝕎[v].A).toMonoidHom
        (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c)) =
      (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c) ^ 3 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    exact (Algebra.norm_algebraMap _).trans (by rw [W.finrank_baseChange_A v])
  rw [ha]
  refine (QuotientGroup.eq).mpr ⟨(Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c)⁻¹, ?_⟩
  show (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c)⁻¹ ^ 2 = _
  group

-- For a non-square scalar, the norm of its class is nontrivial.
private lemma normM_scalarClass_ne_one {c : 𝒪_[v]ˣ}
    (hc : ¬ IsSquare (algebraMap 𝒪_[v] F_[v] (c : 𝒪_[v]))) :
    normM (W := 𝕎[v]) (W.scalarClass v c) ≠ 1 := by
  rw [W.normM_scalarClass v c]
  intro h
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp h
  rw [powMonoidHom_apply, sq] at hw
  refine hc ⟨(w : F_[v]ˣ), ?_⟩
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mul]
    using congrArg Units.val hw.symm

variable {v}

-- The class of a scalar unit of `𝒪_v` is unramified.
private lemma scalarClass_mem_selmerGroupA (c : 𝒪_[v]ˣ) :
    W.scalarClass v c ∈ 𝕎[v].selmerGroupA 𝒪_[v] := by
  rw [scalarClass, mem_selmerGroupA_unit_iff]
  intro q w hw
  have hdvd := w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1)
    (u := Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toMonoidHom
      (Units.map (algebraMap F_[v] 𝕎[v].A).toMonoidHom
        (Units.map (algebraMap 𝒪_[v] F_[v]).toMonoidHom c)))
    (by rw [W.valuation_projFactor_scalar v q w c]; simp)
  simpa using hdvd

-- The cardinality of `A(∅, 2)` is the product of the factor contributions.
private lemma card_selmerGroupA_eq_prod :
    Nat.card (𝕎[v].selmerGroupA 𝒪_[v]) =
      ∏ q : 𝕎[v].f.Factors, Nat.card (𝕎[v].selmerGroupFactor 𝒪_[v] q) := by
  calc Nat.card (𝕎[v].selmerGroupA 𝒪_[v])
      = Nat.card (𝕎[v].selmerGroupPi 𝒪_[v]) :=
        Nat.card_congr (Equiv.subtypeEquiv (AdjoinRoot.modPowEquivPiFactors
          𝕎[v].f_ne_zero 𝕎[v].squarefree_f 2).toEquiv fun _ ↦ Iff.rfl)
    _ = Nat.card ((q : 𝕎[v].f.Factors) → (𝕎[v].selmerGroupFactor 𝒪_[v] q)) := by
        refine Nat.card_congr ((Equiv.subtypeEquivRight fun x ↦ ?_).trans Equiv.subtypePiEquivPi)
        simp [selmerGroupPi, Subgroup.mem_pi]
    _ = ∏ q : 𝕎[v].f.Factors, Nat.card (𝕎[v].selmerGroupFactor 𝒪_[v] q) := Nat.card_pi

-- Each factor contributes exactly two square classes at a good place.
private lemma card_selmerGroupFactor (hv : v ∉ W.badPrimes (𝓞 F)) (q : 𝕎[v].f.Factors) :
    Nat.card (𝕎[v].selmerGroupFactor 𝒪_[v] q) = 2 := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := W.two_notMem_asIdeal_of_notMem_badPrimes hv
  -- instances for the interface statement
  have hFD : FiniteDimensional F_[v] (AdjoinRoot (q : F_[v][X])) :=
    (AdjoinRoot.powerBasis' q.monic).finite
  have hDed : IsDedekindDomain (integralClosure 𝒪_[v] (AdjoinRoot (q : F_[v][X]))) :=
    𝕎[v].isDedekindDomain_ringOfIntegersFactor 𝒪_[v] q
  have hFrac : IsFractionRing (integralClosure 𝒪_[v] (AdjoinRoot (q : F_[v][X])))
      (AdjoinRoot (q : F_[v][X])) :=
    isFractionRing_ringOfIntegersFactor (W := 𝕎[v]) 𝒪_[v] q
  -- identify the factor Selmer group with `L(∅, 2)` and count via the interface statement
  rw [selmerGroupFactor, W.badPrimes_adicCompletionIntegers hv,
    IsDedekindDomain.selmerGroupAbove_empty]
  exact HeightOneSpectrum.card_selmerGroup_integralClosure (K := F) v
    (AdjoinRoot (q : F_[v][X])) h2

-- The cardinality of `A(∅, 2)` is `2 ^ g`, for `g` the number of factors of `f` over `F_v`.
private lemma card_selmerGroupA_eq_two_pow (hv : v ∉ W.badPrimes (𝓞 F)) :
    Nat.card (𝕎[v].selmerGroupA 𝒪_[v]) = 2 ^ Nat.card 𝕎[v].f.Factors := by
  rw [W.card_selmerGroupA_eq_prod (v := v),
    Finset.prod_congr rfl fun q _ ↦ W.card_selmerGroupFactor hv q, Finset.prod_const,
    Finset.card_univ, Nat.card_eq_fintype_card]

-- In particular, `A(∅, 2)` is finite at a good place.
private lemma finite_selmerGroupA_adicCompletionIntegers (hv : v ∉ W.badPrimes (𝓞 F)) :
    Finite (𝕎[v].selmerGroupA 𝒪_[v]) := by
  refine (Nat.card_ne_zero.mp ?_).2
  rw [W.card_selmerGroupA_eq_two_pow hv]
  positivity

-- The norm condition cuts `A(∅, 2)` at least in half: the class of a non-square scalar
-- unit (which exists, `exists_unit_not_isSquare`) is unramified with nontrivial norm.
private lemma two_mul_card_inf_ker_le (hv : v ∉ W.badPrimes (𝓞 F)) :
    2 * Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2)) ≤ Nat.card (𝕎[v].selmerGroupA 𝒪_[v]) := by
  have hfinA := W.finite_selmerGroupA_adicCompletionIntegers hv
  -- the norm homomorphism restricted to `A(∅, 2)`
  set φ := (normM (W := 𝕎[v])).restrict (𝕎[v].selmerGroupA 𝒪_[v])
  have hT : Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2)) = Nat.card φ.ker := by
    change _ = Nat.card ((normM (W := 𝕎[v])).ker.subgroupOf (𝕎[v].selmerGroupA 𝒪_[v]))
    rw [← Subgroup.inf_subgroupOf_left]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  -- the image of the norm is nontrivial: a non-square scalar witnesses this
  obtain ⟨c, hc⟩ := v.exists_unit_not_isSquare (K := F)
    (W.two_notMem_asIdeal_of_notMem_badPrimes hv)
  have hfinR : Finite φ.range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hrange2 : 2 ≤ Nat.card φ.range :=
    Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨1, one_mem _⟩,
      ⟨normM (W := 𝕎[v]) (W.scalarClass v c),
        ⟨⟨W.scalarClass v c, W.scalarClass_mem_selmerGroupA (v := v) c⟩, rfl⟩⟩,
      fun h ↦ W.normM_scalarClass_ne_one v hc (Subtype.ext_iff.mp h).symm⟩
  calc 2 * Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2))
      = 2 * Nat.card φ.ker := by rw [hT]
    _ ≤ Nat.card φ.range * Nat.card φ.ker := Nat.mul_le_mul_right _ hrange2
    _ = Nat.card (𝕎[v].selmerGroupA 𝒪_[v]) := by
        rw [mul_comm]; exact φ.card_ker_mul_card_range

end LocalCount

attribute [local instance] instFintypeFactorsBaseChange

-- Counting at a good finite place: `#(A(∅,2) ⊓ ker N) ≤ 2^(g-1) ≤ #E(F_v)[2] = #(im μ)`.
open scoped Classical in
private lemma card_inf_ker_le_card_range_μ {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2)) ≤ Nat.card (μ (W := 𝕎[v])).range := by
  -- there is at least one factor
  have hg1 : 1 ≤ Nat.card 𝕎[v].f.Factors :=
    Nat.one_le_iff_ne_zero.mpr <| Nat.card_ne_zero.mpr
      ⟨Polynomial.Factors.nonempty <| Polynomial.not_isUnit_of_natDegree_pos _
        (by rw [natDegree_f]; lia), inferInstance⟩
  have h1 := W.two_mul_card_inf_ker_le hv
  rw [W.card_selmerGroupA_eq_two_pow hv, show 2 ^ Nat.card 𝕎[v].f.Factors =
    2 * 2 ^ (Nat.card 𝕎[v].f.Factors - 1) by
      rw [← pow_succ', Nat.sub_add_cancel hg1]] at h1
  calc Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2))
      ≤ 2 ^ (Nat.card 𝕎[v].f.Factors - 1) := by lia
    _ ≤ Nat.card {q : 𝕎[v].f.Factors // (q : F_[v][X]).natDegree = 1} + 1 :=
        W.two_pow_le_card_linear_factors (v := v)
    _ = Nat.card {x : F_[v] // 𝕎[v].f.eval x = 0} + 1 := by
        rw [Nat.card_congr Polynomial.Factors.linearEquivRoots]
    _ = Nat.card (nsmulAddMonoidHom (α := 𝕎[v].Point) 2).ker :=
        (𝕎[v].card_ker_nsmul_two).symm
    _ = Nat.card (μ (W := 𝕎[v])).range :=
        (W.card_range_μ_adicCompletion_of_two_notMem
          (W.two_notMem_asIdeal_of_notMem_badPrimes hv)).symm

open scoped Classical in
/-- **The image of the local descent map at a good finite place** consists exactly of the
unramified square classes with trivial norm. The inclusion `⊇` is the local Hensel input of
the reduction to the bad places: every unramified class with trivial norm comes from a point.

It is proved by counting: `#(A(∅,2) ⊓ ker N) ≤ #A(∅,2)/2 = 2^(g-1)` for `g` factors of `f`
over `F_v` (`card_selmerGroupA_eq_two_pow`, resting on the `𝔾ₘ`-interface statement of
`Heights.ForMathlib.FormalGroup`; the halving is by a non-square scalar class), while
`#(im μ) = #E(F_v)[2] ≥ 2^(g-1)` by counting `2`-torsion points coming from the linear
factors of `f`. -/
theorem selmerGroupA_inf_ker_normM_eq_range_μ {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker = (μ (W := 𝕎[v])).range := by
  have hle : (μ (W := 𝕎[v])).range ≤
      𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :=
    le_inf (𝕎[v].range_μ_le_selmerGroupA 𝒪_[v]) range_μ_le_ker_normM
  have hfinA := W.finite_selmerGroupA_adicCompletionIntegers hv
  have hfinT : Finite (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  exact (Subgroup.eq_of_le_of_card_ge hle (W.card_inf_ker_le_card_range_μ hv)).symm

open scoped Classical in
/-- At a good finite place, the local condition follows from `S`-unramifiedness and the norm
condition: the image of the local descent map is the group of unramified square classes with
trivial norm. -/
theorem inf_le_localCondition_adicCompletion {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) :
    W.selmerGroupA (𝓞 F) ⊓ (normM (W := W)).ker ≤ W.localCondition F_[v] := by
  intro m hm
  rw [Subgroup.mem_inf] at hm
  rw [mem_localCondition_iff]
  apply (W.selmerGroupA_inf_ker_normM_eq_range_μ hv).le
  rw [Subgroup.mem_inf]
  refine ⟨W.localRes_mem_selmerGroupA hv hm.1, ?_⟩
  rw [MonoidHom.mem_ker, W.normM_localRes, MonoidHom.mem_ker.mp hm.2, map_one]

variable [DecidableEq F]

open scoped Classical in
/-- **Reduction of the 2-Selmer group to the bad places**: over a number field, the 2-Selmer
group consists of the classes in `A(S,2) ∩ ker N` (a finite group computable from the class
groups and unit groups of the field factors, via `Heights.ForMathlib.SelmerGroup`) that
satisfy the local conditions at the places in `W.badPrimes (𝓞 F)` (which include the places
above `2` and the places of bad reduction) and at the infinite places. -/
theorem selmerGroup₂_eq_badPrimes :
    W.selmerGroup₂ (𝓞 F) (fun v : InfinitePlace F ↦ v.Completion) =
      W.selmerGroupA (𝓞 F) ⊓ (normM (W := W)).ker
        ⊓ (⨅ v : W.badPrimes (𝓞 F), W.localCondition F_[(v : HeightOneSpectrum (𝓞 F))])
        ⊓ ⨅ v : InfinitePlace F, W.localCondition v.Completion := by
  ext m
  simp only [mem_selmerGroup₂_iff, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨W.mem_selmerGroupA_of_forall_localRes fun v ↦ ?_, h1⟩, fun v ↦ h2 v⟩, h3⟩
    have h := h2 v
    rw [mem_localCondition_iff] at h
    exact 𝕎[v].range_μ_le_selmerGroupA
      𝒪_[v] h
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

end NumberField

end WeierstrassCurve.Affine
