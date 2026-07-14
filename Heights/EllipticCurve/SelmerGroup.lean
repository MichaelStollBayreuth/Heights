import Mathlib
import Heights.ForMathlib.Basic
import Heights.ForMathlib.AdicCompletionExtension
import Heights.ForMathlib.FormalGroup
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
  simp only [QuotientGroup.mk'_apply, localRes_mk, normM, Units.modPow.map_mk]
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
/-- The image of the global descent map `μ` satisfies the local condition at every extension
field: base change of points is compatible with the `x - T` maps. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  rintro _ ⟨P', rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [mem_localCondition_iff, μ_apply]
  match P with
  | 0 => rw [μ₀_zero, map_one]; exact one_mem _
  | .some x y hP =>
    have hP' : (W⁄L).toAffine.Nonsingular (algebraMap K L x) (algebraMap K L y) :=
      (W.map_nonsingular (algebraMap K L).injective x y).mpr hP
    rw [μ₀_some]
    exact ⟨.ofAdd (.some _ _ hP'), by rw [μ_apply, μ₀_some, W.localRes_μX L x]⟩

open scoped Classical in
/-- If the base change is along an isomorphism, then the local descent map has the same
image size as the global one (via the induced isomorphism of the étale algebras). -/
theorem card_range_μ_of_bijective_algebraMap (h : Function.Bijective (algebraMap K L)) :
    Nat.card (μ (W := (W⁄L).toAffine)).range = Nat.card (μ (W := W)).range := by
  set e := RingEquiv.ofBijective (algebraMap K L) h with he
  have hcomp : (algebraMap K L).comp (e.symm : L →+* K) = RingHom.id L :=
    RingHom.ext fun z ↦ e.apply_symm_apply z
  -- the induced map on square classes is bijective
  have hA : Function.Bijective (W.mapA L) := by
    constructor
    · intro a b hab
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨g', rfl⟩ := AdjoinRoot.mk_surjective b
      simp only [mapA_mk, AdjoinRoot.mk_eq_mk, baseChange_f, ← Polynomial.map_sub] at hab ⊢
      obtain ⟨c, hc⟩ := hab
      refine ⟨c.map (e.symm : L →+* K), Polynomial.map_injective _ h.1 ?_⟩
      rw [Polynomial.map_mul, hc, Polynomial.map_map, hcomp, Polynomial.map_id]
    · intro a
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
      refine ⟨AdjoinRoot.mk W.f (g.map (e.symm : L →+* K)), ?_⟩
      rw [mapA_mk, Polynomial.map_map, hcomp, Polynomial.map_id]
  have hM := Units.modPow.bijective_map (φ := (W.mapA L).toMonoidHom) hA 2
  -- the image of `im μ` under the isomorphism of square-class groups is `im μ_L`
  have hrange : (μ (W := (W⁄L).toAffine)).range = Subgroup.map (W.localRes L) (μ.range) := by
    refine le_antisymm ?_ (Subgroup.map_le_iff_le_comap.mpr (W.range_μ_le_localCondition L))
    rintro _ ⟨P', rfl⟩
    obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
    match P with
    | 0 => exact ⟨1, one_mem _, by rw [map_one]; rfl⟩
    | .some x y hP =>
      obtain ⟨x', rfl⟩ := h.2 x
      obtain ⟨y', rfl⟩ := h.2 y
      have hP' : W.Nonsingular x' y' := (W.map_nonsingular (algebraMap K L).injective _ _).mp hP
      exact ⟨μ (.ofAdd (.some _ _ hP')), ⟨_, rfl⟩, by
        simp only [μ_apply, μ₀_some]
        rw [W.localRes_μX L x']⟩
  rw [hrange,
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

open scoped Classical

variable (W' : Affine ℝ)

-- A monic irreducible real quadratic is positive definite (complete the square).
private lemma pos_of_monic_irreducible_quadratic {q : ℝ[X]} (hm : q.Monic)
    (hirr : Irreducible q) (hd : q.natDegree = 2) (x : ℝ) :
    0 < q.eval x := by
  have hlead : q.coeff 2 = 1 := by rw [← hd, ← Polynomial.leadingCoeff]; exact hm
  have heval (t : ℝ) : q.eval t = t ^ 2 + q.coeff 1 * t + q.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range, hd, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hlead]
    ring
  have hnoroot (t : ℝ) : q.eval t ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := dvd_iff_isRoot.mpr h0
    rcases hirr.isUnit_or_isUnit hc with h | h
    · exact Polynomial.not_isUnit_X_sub_C t h
    · obtain ⟨u, hu, rfl⟩ := Polynomial.isUnit_iff.mp h
      apply_fun natDegree at hc
      rw [hd, natDegree_mul (X_sub_C_ne_zero t) (by simpa using hu.ne_zero),
        natDegree_X_sub_C, natDegree_C] at hc
      lia
  by_contra! hle
  have hdisc : q.coeff 0 - q.coeff 1 ^ 2 / 4 ≤ 0 := by
    nlinarith [sq_nonneg (x + q.coeff 1 / 2), heval x]
  refine hnoroot (-q.coeff 1 / 2 + Real.sqrt (q.coeff 1 ^ 2 / 4 - q.coeff 0)) ?_
  have hs := Real.sq_sqrt (by linarith : (0:ℝ) ≤ q.coeff 1 ^ 2 / 4 - q.coeff 0)
  rw [heval]
  linear_combination hs

-- Every unit of `ℝ[X]/(q)` for a monic irreducible quadratic `q` is a square: the quotient
-- embeds into `ℂ` (with equality by dimension count), where every unit is a square.
private lemma subsingleton_modPow_of_quadratic {q : ℝ[X]} (hm : q.Monic)
    (hirr : Irreducible q) (hd : q.natDegree = 2) :
    Subsingleton (Units.modPow (AdjoinRoot q) 2) := by
  have hfact : Fact (Irreducible q) := ⟨hirr⟩
  have hfd : FiniteDimensional ℝ (AdjoinRoot q) := (AdjoinRoot.powerBasis' hm).finite
  -- an embedding into `ℂ`
  let φ : AdjoinRoot q →ₐ[ℝ] ℂ := IsAlgClosed.lift
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hsurj : Function.Surjective φ := by
    have hrank : Module.finrank ℝ (LinearMap.range φ.toLinearMap) = Module.finrank ℝ ℂ := by
      rw [LinearMap.finrank_range_of_inj hinj, Complex.finrank_real_complex,
        (AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim, hd]
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hrank)
  -- transport squares along the isomorphism
  refine Units.modPow.subsingleton_of_forall_exists_pow fun u ↦ ?_
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (φ (u : AdjoinRoot q)) zero_lt_two
  obtain ⟨w', rfl⟩ := hsurj w
  have hu : w' ^ 2 = (u : AdjoinRoot q) := hinj (by rw [map_pow, hw])
  have hw0 : w' ≠ 0 := fun h0 ↦ u.ne_zero (by rw [← hu, h0]; exact zero_pow two_ne_zero)
  exact ⟨Units.mk0 w' hw0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hu])⟩

-- The monic linear factor of `f` attached to a root.
private noncomputable def rootFactor {e : ℝ} (he : W'.f.eval e = 0) : W'.f.Factors :=
  ⟨X - C e, monic_X_sub_C _, irreducible_X_sub_C _, dvd_iff_isRoot.mpr he⟩

variable {W'}

-- Evaluation of the field factor attached to a root `e` at `e`, as a ring homomorphism.
private noncomputable def evalRoot {e : ℝ} (he : W'.f.eval e = 0) :
    AdjoinRoot ((W'.rootFactor he : W'.f.Factors) : ℝ[X]) →+* ℝ :=
  AdjoinRoot.lift (RingHom.id ℝ) e (by show Polynomial.eval₂ _ _ (X - C e) = 0; simp)

private lemma evalRoot_mk {e : ℝ} (he : W'.f.eval e = 0) (g : ℝ[X]) :
    evalRoot he (AdjoinRoot.mk _ g) = g.eval e := by
  rw [evalRoot, AdjoinRoot.lift_mk]
  simp [eval₂_id]

private lemma bijective_evalRoot {e : ℝ} (he : W'.f.eval e = 0) :
    Function.Bijective (evalRoot he) := by
  have : Fact (Irreducible ((W'.rootFactor he : W'.f.Factors) : ℝ[X])) :=
    ⟨(W'.rootFactor he).irreducible⟩
  refine ⟨(evalRoot he).injective, fun r ↦ ⟨AdjoinRoot.of _ r, ?_⟩⟩
  rw [evalRoot, AdjoinRoot.lift_of]
  rfl

private lemma isSquare_evalRoot_iff {e : ℝ} (he : W'.f.eval e = 0)
    (a : AdjoinRoot ((W'.rootFactor he : W'.f.Factors) : ℝ[X])) :
    IsSquare (evalRoot he a) ↔ IsSquare a := by
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun h ↦ h.map _⟩
  obtain ⟨s', rfl⟩ := (bijective_evalRoot he).2 s
  exact ⟨s', (bijective_evalRoot he).1 (by rw [map_mul]; exact hs)⟩

variable (W')

-- The number of real roots of `f`, from the two splittings (instance-free).
private lemma card_roots_split₃ {e₁ e₂ e₃ : ℝ} (h12 : e₁ < e₂) (h23 : e₂ < e₃)
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) :
    Nat.card {x : ℝ // W'.f.eval x = 0} = 3 := by
  have hset : {x : ℝ | W'.f.eval x = 0} = {e₁, e₂, e₃} := by
    ext x
    simp only [Set.mem_setOf_eq, hf, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero,
      sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  show Nat.card ↥{x : ℝ | W'.f.eval x = 0} = 3
  rw [Nat.card_coe_set_eq, hset]
  exact Set.ncard_eq_three.mpr ⟨e₁, e₂, e₃, h12.ne, (h12.trans h23).ne, h23.ne, rfl⟩

private lemma card_roots_split₁ {e : ℝ} {q : ℝ[X]} (hm : q.Monic) (hirr : Irreducible q)
    (hd : q.natDegree = 2) (hf : W'.f = (X - C e) * q) :
    Nat.card {x : ℝ // W'.f.eval x = 0} = 1 := by
  have hq (t : ℝ) : 0 < q.eval t := pos_of_monic_irreducible_quadratic hm hirr hd t
  have hset : {x : ℝ | W'.f.eval x = 0} = {e} := by
    ext x
    simp only [Set.mem_setOf_eq, hf, eval_mul, eval_sub, eval_X, eval_C, Set.mem_singleton_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; simp⟩
    rcases mul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' (hq x).ne'
  show Nat.card ↥{x : ℝ | W'.f.eval x = 0} = 1
  rw [Nat.card_coe_set_eq, hset, Set.ncard_singleton]

-- The evaluation of `f`, and the roots, in the three-real-roots case (instance-free setup).
private lemma eval_f_of_split₃ {e₁ e₂ e₃ : ℝ}
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) (t : ℝ) :
    W'.f.eval t = (t - e₁) * (t - e₂) * (t - e₃) := by rw [hf]; simp

private lemma root_eq_of_split₃ {e₁ e₂ e₃ t : ℝ}
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) (ht : W'.f.eval t = 0) :
    t = e₁ ∨ t = e₂ ∨ t = e₃ := by
  have h0 : (t - e₁) * (t - e₂) * (t - e₃) = 0 := by rw [← W'.eval_f_of_split₃ hf]; exact ht
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact .inl (sub_eq_zero.mp h')
    · exact .inr (.inl (sub_eq_zero.mp h'))
  · exact .inr (.inr (sub_eq_zero.mp h))

variable [W'.IsElliptic] [W'.IsCharNeTwoNF]

-- The value on `ha.unit` of the projection to a field factor `p` is `projFactor a`.
private lemma coe_map_projFactor_unit {a : W'.A} (ha : IsUnit a) (p : W'.f.Factors) :
    ((Units.map (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f p).toMonoidHom ha.unit :
        (AdjoinRoot (p : ℝ[X]))ˣ) : AdjoinRoot (p : ℝ[X])) =
      AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f p a := by
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec]

-- The square class of a unit of the étale algebra is trivial exactly when all its values at the
-- real roots of `f` are nonnegative: at a linear factor `X - e` triviality means `evalRoot` is a
-- square in `ℝ`, i.e. nonnegative, and the quadratic factors have no square classes at all.
private lemma mk_eq_one_iff_forall_evalRoot_nonneg {a : W'.A} (ha : IsUnit a) :
    (QuotientGroup.mk ha.unit : W'.M) = 1 ↔
      ∀ (e : ℝ) (he : W'.f.eval e = 0),
        0 ≤ evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f
          (W'.rootFactor he) a) := by
  rw [AdjoinRoot.modPow_mk_eq_one_iff_forall_factors W'.f_ne_zero W'.squarefree_f]
  refine ⟨fun hone e he ↦ ?_, fun h p ↦ ?_⟩
  · -- trivial class ⟹ the value at each root's linear factor is a square, hence nonnegative
    have hc := hone (W'.rootFactor he)
    rwa [Units.modPow.mk_eq_one_iff_isSquare, W'.coe_map_projFactor_unit ha (W'.rootFactor he),
      ← isSquare_evalRoot_iff he, Real.isSquare_iff] at hc
  rcases eq_or_ne ((p : ℝ[X]).natDegree) 1 with hd | hd
  · -- linear factor: `p = rootFactor he`
    obtain ⟨e, he, rfl⟩ : ∃ (e : ℝ) (he : W'.f.eval e = 0), p = W'.rootFactor he := by
      refine ⟨-(p : ℝ[X]).coeff 0, eval_eq_zero_of_dvd_of_eval_eq_zero p.dvd (by
          conv_lhs => rw [p.monic.eq_X_add_C hd]
          simp), Subtype.ext ?_⟩
      show (p : ℝ[X]) = X - C (-(p : ℝ[X]).coeff 0)
      conv_lhs => rw [p.monic.eq_X_add_C hd]
      rw [map_neg, sub_neg_eq_add]
    rw [Units.modPow.mk_eq_one_iff_isSquare, W'.coe_map_projFactor_unit ha (W'.rootFactor he),
      ← isSquare_evalRoot_iff he, Real.isSquare_iff]
    exact h e he
  · -- quadratic factor: the group of square classes of the factor is trivial
    have hd2 : (p : ℝ[X]).natDegree = 2 := by
      have h1 := p.irreducible.natDegree_pos
      have h2 := p.irreducible.natDegree_le_two
      lia
    have := subsingleton_modPow_of_quadratic p.monic p.irreducible hd2
    exact Subsingleton.elim _ _

-- The square class of a unit of the étale algebra is trivial when all its values at the
-- roots of `f` are nonnegative (the components at the quadratic factors are always trivial).
private lemma unit_class_eq_one {a : W'.A} (ha : IsUnit a)
    (h : ∀ (e : ℝ) (he : W'.f.eval e = 0),
      0 ≤ evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f
        (W'.rootFactor he) a)) :
    (QuotientGroup.mk ha.unit : W'.M) = 1 :=
  (W'.mk_eq_one_iff_forall_evalRoot_nonneg ha).mpr h

-- The square classes of two units agree when the products of their values at the roots
-- of `f` are all nonnegative.
private lemma unit_class_eq {a b : W'.A} (ha : IsUnit a) (hb : IsUnit b)
    (h : ∀ (e : ℝ) (he : W'.f.eval e = 0),
      0 ≤ evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f
          (W'.rootFactor he) a) *
        evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f
          (W'.rootFactor he) b)) :
    (QuotientGroup.mk ha.unit : W'.M) = QuotientGroup.mk hb.unit := by
  have hab := W'.unit_class_eq_one (ha.mul hb) (fun e he ↦ by rw [map_mul, map_mul]; exact h e he)
  have hmul : ((ha.mul hb).unit : W'.Aˣ) = ha.unit * hb.unit := Units.ext rfl
  rw [hmul, QuotientGroup.mk_mul] at hab
  rw [mul_eq_one_iff_eq_inv.mp hab, M.inv_eq_self]

-- The values of the representatives of `μX x` at a root `e` of `f`.
private lemma eval_projFactor_generic (x : ℝ) {e : ℝ} (he : W'.f.eval e = 0) :
    evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f (W'.rootFactor he)
      (AdjoinRoot.mk W'.f (C x - X))) = x - e := by
  rw [AdjoinRoot.projFactor_mk, evalRoot_mk]
  simp

private lemma eval_projFactor_torsion (x : ℝ) {e : ℝ} (he : W'.f.eval e = 0) :
    evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f (W'.rootFactor he)
      (AdjoinRoot.mk W'.f (C x - X + W'.fCofactor x))) =
      x - e + (W'.fCofactor x).eval e := by
  rw [AdjoinRoot.projFactor_mk, evalRoot_mk]
  simp

-- At a root `e` distinct from the `2`-torsion `x`-coordinate, the cofactor `f / (X - x)`
-- vanishes (as `f e = 0` and `e ≠ x`), so the torsion value at `e` is just `x - e`.
private lemma eval_projFactor_torsion_ne {x e : ℝ} (hx : W'.f.eval x = 0)
    (he : W'.f.eval e = 0) (hxe : e ≠ x) :
    evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f (W'.rootFactor he)
      (AdjoinRoot.mk W'.f (C x - X + W'.fCofactor x))) = x - e := by
  rw [eval_projFactor_torsion]
  have h0 := congrArg (Polynomial.eval e) (W'.fCofactor_mul_eq x)
  simp only [eval_mul, eval_sub, eval_X, eval_C, hx, he, sub_zero] at h0
  rw [(mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hxe), add_zero]

-- Three real roots, `x` a root: `μX x ∈ {1, μX e₁}`.
private lemma μX_root_mem_of_split₃ {e₁ e₂ e₃ : ℝ} (h12 : e₁ < e₂) (h23 : e₂ < e₃)
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) {x : ℝ} (hx : W'.f.eval x = 0) :
    W'.μX x = 1 ∨ W'.μX x = W'.μX e₁ := by
  have he₁ : W'.f.eval e₁ = 0 := by rw [W'.eval_f_of_split₃ hf]; ring
  obtain ⟨hcof₁, hcof₂, hcof₃⟩ := W'.fCofactor_eq_of_f_eq hf
  have s12 : (0:ℝ) < e₂ - e₁ := sub_pos.mpr h12
  have s23 : (0:ℝ) < e₃ - e₂ := sub_pos.mpr h23
  have s13 : (0:ℝ) < e₃ - e₁ := by linarith
  rcases W'.root_eq_of_split₃ hf hx with rfl | rfl | rfl
  · exact .inr rfl
  · -- `μX e₂ = μX e₁`: the products of the values at each root are positive
    refine .inr ?_
    rw [μX_of_eval_f_eq_zero hx, μX_of_eval_f_eq_zero he₁]
    refine W'.unit_class_eq _ _ (fun t ht ↦ ?_)
    rw [eval_projFactor_torsion, eval_projFactor_torsion, hcof₂, hcof₁]
    rcases W'.root_eq_of_split₃ hf ht with rfl | rfl | rfl <;>
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero,
        add_zero, zero_add] <;>
      nlinarith [mul_pos s12 s23, mul_pos s12 s13, mul_pos s23 s13]
  · -- `μX e₃ = 1`: all values are positive
    refine .inl ?_
    rw [μX_of_eval_f_eq_zero hx]
    refine W'.unit_class_eq_one _ (fun t ht ↦ ?_)
    rw [eval_projFactor_torsion, hcof₃]
    rcases W'.root_eq_of_split₃ hf ht with rfl | rfl | rfl <;>
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero,
        add_zero, zero_add] <;>
      nlinarith [mul_pos s13 s23]

-- Three real roots, `f x > 0`: `x` is in `(e₁, e₂)` or `(e₃, ∞)`, giving `μX x ∈ {1, μX e₁}`.
private lemma μX_generic_mem_of_split₃ {e₁ e₂ e₃ : ℝ} (h12 : e₁ < e₂) (h23 : e₂ < e₃)
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) {x : ℝ} (hx : 0 ≤ W'.f.eval x)
    (hx0 : W'.f.eval x ≠ 0) :
    W'.μX x = 1 ∨ W'.μX x = W'.μX e₁ := by
  have he₁ : W'.f.eval e₁ = 0 := by rw [W'.eval_f_of_split₃ hf]; ring
  have he₂ : W'.f.eval e₂ = 0 := by rw [W'.eval_f_of_split₃ hf]; ring
  have he₃ : W'.f.eval e₃ = 0 := by rw [W'.eval_f_of_split₃ hf]; ring
  obtain ⟨hcof₁, _, _⟩ := W'.fCofactor_eq_of_f_eq hf
  have hprod : 0 < (x - e₁) * (x - e₂) * (x - e₃) :=
    W'.eval_f_of_split₃ hf x ▸ lt_of_le_of_ne hx (Ne.symm hx0)
  have h1 : x ≠ e₁ := fun h ↦ hx0 (by rw [h]; exact he₁)
  have h2 : x ≠ e₂ := fun h ↦ hx0 (by rw [h]; exact he₂)
  have h3 : x ≠ e₃ := fun h ↦ hx0 (by rw [h]; exact he₃)
  rcases lt_or_gt_of_ne h1 with hx1 | hx1
  · nlinarith [mul_pos (mul_pos (sub_pos.mpr hx1) (show (0:ℝ) < e₂ - x by linarith))
      (show (0:ℝ) < e₃ - x by linarith)]
  rcases lt_or_gt_of_ne h3 with hx3 | hx3
  swap
  · -- `x > e₃`: all values positive, trivial class
    refine .inl ?_
    rw [μX_of_eval_f_ne_zero hx0]
    refine W'.unit_class_eq_one _ (fun t ht ↦ ?_)
    rw [eval_projFactor_generic]
    rcases W'.root_eq_of_split₃ hf ht with rfl | rfl | rfl <;> nlinarith
  rcases lt_or_gt_of_ne h2 with hx2 | hx2
  swap
  · nlinarith [mul_pos (mul_pos (show (0:ℝ) < x - e₁ by linarith) (sub_pos.mpr hx2))
      (sub_pos.mpr hx3)]
  · -- `e₁ < x < e₂`: same signs as for `(e₁, 0)`
    refine .inr ?_
    rw [μX_of_eval_f_ne_zero hx0, μX_of_eval_f_eq_zero he₁]
    refine W'.unit_class_eq _ _ (fun t ht ↦ ?_)
    rw [eval_projFactor_generic, eval_projFactor_torsion, hcof₁]
    have s12 : (0:ℝ) < e₂ - e₁ := sub_pos.mpr h12
    have s13 : (0:ℝ) < e₃ - e₁ := by linarith
    have sx1 : (0:ℝ) < x - e₁ := sub_pos.mpr hx1
    have sx2 : (0:ℝ) < e₂ - x := sub_pos.mpr hx2
    have sx3 : (0:ℝ) < e₃ - x := sub_pos.mpr hx3
    rcases W'.root_eq_of_split₃ hf ht with rfl | rfl | rfl <;>
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero,
        add_zero, zero_add] <;>
      nlinarith [mul_pos sx1 (mul_pos s12 s13), mul_pos sx2 s12, mul_pos sx3 s13]

-- Three real roots: the image of `μX` on `{f ≥ 0}` is `{1, μX e₁}`.
private lemma μX_mem_of_split₃ {e₁ e₂ e₃ : ℝ} (h12 : e₁ < e₂) (h23 : e₂ < e₃)
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) {x : ℝ} (hx : 0 ≤ W'.f.eval x) :
    W'.μX x = 1 ∨ W'.μX x = W'.μX e₁ := by
  rcases eq_or_ne (W'.f.eval x) 0 with hx0 | hx0
  · exact W'.μX_root_mem_of_split₃ h12 h23 hf hx0
  · exact W'.μX_generic_mem_of_split₃ h12 h23 hf hx hx0

-- Case of one real root: every point class is trivial.
private lemma μX_eq_one_of_split₁ {e : ℝ} {q : ℝ[X]} (hm : q.Monic) (hirr : Irreducible q)
    (hd : q.natDegree = 2) (hf : W'.f = (X - C e) * q) {x : ℝ} (hx : 0 ≤ W'.f.eval x) :
    W'.μX x = 1 := by
  have heval (t : ℝ) : W'.f.eval t = (t - e) * q.eval t := by rw [hf]; simp
  have he : W'.f.eval e = 0 := by rw [heval]; ring
  have hq (t : ℝ) : 0 < q.eval t := pos_of_monic_irreducible_quadratic hm hirr hd t
  have hroots {t : ℝ} (ht : W'.f.eval t = 0) : t = e := by
    have h0 : (t - e) * q.eval t = 0 := by rw [← heval]; exact ht
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (hq t).ne'
  have hcof : W'.fCofactor e = q :=
    mul_right_cancel₀ (X_sub_C_ne_zero e)
      (by rw [← W'.f_eq_mul_of_eval_eq_zero he, hf]; ring)
  rcases eq_or_ne (W'.f.eval x) 0 with hx0 | hx0
  · -- `x = e`: the value at `e` is `q e > 0`
    obtain rfl := hroots hx0
    rw [μX_of_eval_f_eq_zero hx0]
    refine W'.unit_class_eq_one _ (fun t ht ↦ ?_)
    obtain rfl := hroots ht
    rw [eval_projFactor_torsion, hcof]
    simpa using (hq t).le
  · -- `f x > 0` forces `x > e`
    rw [μX_of_eval_f_ne_zero hx0]
    refine W'.unit_class_eq_one _ (fun t ht ↦ ?_)
    obtain rfl := hroots ht
    rw [eval_projFactor_generic]
    nlinarith [heval x, hq x, lt_of_le_of_ne hx (Ne.symm hx0)]

-- Sorting three distinct reals in a triple product.
private lemma sort₃ {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {g : ℝ[X]}
    (hg : g = (X - C a) * (X - C b) * (X - C c)) :
    ∃ e₁ e₂ e₃ : ℝ, e₁ < e₂ ∧ e₂ < e₃ ∧ g = (X - C e₁) * (X - C e₂) * (X - C e₃) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact ⟨a, b, c, h1, h3, hg⟩
  · exact ⟨a, c, b, h2, h3, by rw [hg]; ring⟩
  · exact absurd (h2.trans h1) (lt_asymm h3)
  · exact ⟨c, a, b, h2, h1, by rw [hg]; ring⟩
  · exact ⟨b, a, c, h1, h2, by rw [hg]; ring⟩
  · exact absurd (h2.trans h3) (lt_asymm h1)
  · exact ⟨b, c, a, h3, h2, by rw [hg]; ring⟩
  · exact ⟨c, b, a, h3, h1, by rw [hg]; ring⟩

-- The splitting of the real cubic: three (distinct, sorted) real roots, or one real root
-- and a monic irreducible quadratic factor.
-- A monic reducible real quadratic splits into two monic linear factors.
private lemma exists_linear_split {g : ℝ[X]} (hgm : g.Monic) (hd2 : g.natDegree = 2)
    (hirr : ¬ Irreducible g) : ∃ a b : ℝ, g = (X - C a) * (X - C b) := by
  obtain ⟨p, hpm, hpi, d, hd⟩ := g.exists_monic_irreducible_factor
    (fun hu ↦ by simp [natDegree_eq_zero_of_isUnit hu] at hd2)
  have hdm : d.Monic := hpm.of_mul_monic_left (hd ▸ hgm)
  have hdeg := congrArg natDegree hd
  rw [hd2, natDegree_mul hpm.ne_zero hdm.ne_zero] at hdeg
  have hp1 : p.natDegree = 1 := by
    rcases Nat.lt_or_ge p.natDegree 2 with h | h
    · have := hpi.natDegree_pos; lia
    · -- `p` of degree `2` would make `g` irreducible
      rw [Polynomial.eq_one_of_monic_natDegree_zero hdm (by lia), mul_one] at hd
      exact absurd (hd ▸ hpi) hirr
  have hpe : p = X - C (-p.coeff 0) := by
    conv_lhs => rw [hpm.eq_X_add_C hp1]
    rw [map_neg, sub_neg_eq_add]
  have hde : d = X - C (-d.coeff 0) := by
    conv_lhs => rw [hdm.eq_X_add_C (by lia)]
    rw [map_neg, sub_neg_eq_add]
  exact ⟨-p.coeff 0, -d.coeff 0, by rw [hd, ← hpe, ← hde]⟩

private lemma f_split :
    (∃ e₁ e₂ e₃ : ℝ, e₁ < e₂ ∧ e₂ < e₃ ∧ W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) ∨
      ∃ (e : ℝ) (q : ℝ[X]), q.Monic ∧ Irreducible q ∧ q.natDegree = 2 ∧
        W'.f = (X - C e) * q := by
  -- peel off a monic quadratic factor `q`, leaving a monic linear factor `l = X - e`
  have hf3 : IsMonicOfDegree W'.f 3 := ⟨W'.natDegree_f, W'.monic_f⟩
  obtain ⟨q, l, hq, hl, hf⟩ := hf3.eq_isMonicOfDegree_two_mul_isMonicOfDegree (n := 1)
  obtain ⟨e, hle⟩ : ∃ e : ℝ, l = X - C e := by
    refine ⟨-l.coeff 0, ?_⟩
    conv_lhs => rw [hl.monic.eq_X_add_C hl.natDegree_eq]
    rw [map_neg, sub_neg_eq_add]
  by_cases hirr : Irreducible q
  · exact .inr ⟨e, q, hq.monic, hirr, hq.natDegree_eq, by rw [hf, hle, mul_comm]⟩
  · -- the quadratic factor splits into two linear factors `X - a`, `X - b`
    obtain ⟨a, b, hab⟩ := exists_linear_split hq.monic hq.natDegree_eq hirr
    have hsplit : W'.f = (X - C a) * (X - C b) * (X - C e) := by rw [hf, hle, hab]
    have hne (u v w : ℝ) (huvw : W'.f = (X - C u) * (X - C v) * (X - C w)) : u ≠ v := by
      rintro rfl
      exact Polynomial.not_isUnit_X_sub_C u (W'.squarefree_f (X - C u) ⟨X - C w, by rw [huvw]⟩)
    exact .inl (sort₃ (hne a b e hsplit) (hne a e b (by rw [hsplit]; ring))
      (hne b e a (by rw [hsplit]; ring)) hsplit)

-- A negative value at some root obstructs triviality of the square class.
private lemma unit_class_ne_one_of_evalRoot_neg {a : W'.A} (ha : IsUnit a) {e : ℝ}
    (he : W'.f.eval e = 0)
    (hlt : evalRoot he (AdjoinRoot.projFactor W'.f_ne_zero W'.squarefree_f
      (W'.rootFactor he) a) < 0) :
    (QuotientGroup.mk ha.unit : W'.M) ≠ 1 :=
  fun hone ↦ absurd ((W'.mk_eq_one_iff_forall_evalRoot_nonneg ha).mp hone e he) (not_le.mpr hlt)

-- The range of `μ` as a set equals the range of the underlying map `μ₀`.
private lemma range_μ_coe : (Set.range (μ (W := W'))) = Set.range (μ₀ (W := W')) := by
  ext m
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, rfl⟩ := Multiplicative.ofAdd.surjective P
    exact ⟨Q, (μ_apply Q).symm⟩
  · rintro ⟨Q, rfl⟩
    exact ⟨Multiplicative.ofAdd Q, μ_apply Q⟩

-- `IsCharNeTwoNF` is used by `equation_iff_eval_f_eq_sq` in the proof but erased from the term
set_option linter.unusedSectionVars false in
-- Over `ℝ`, `f x` is a square for a point `(x, y)`, hence `≥ 0`.
private lemma eval_f_nonneg_of_nonsingular {x y : ℝ} (h : W'.Nonsingular x y) :
    0 ≤ W'.f.eval x := by
  rw [(W'.equation_iff_eval_f_eq_sq x y).mp h.1]
  exact sq_nonneg y

-- The class of `(e₁, 0)` is nontrivial: its value at the factor `e₂` is `e₁ - e₂ < 0`.
private lemma μX_root_ne_one_of_split₃ {e₁ e₂ e₃ : ℝ} (h12 : e₁ < e₂)
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) :
    W'.μX e₁ ≠ 1 := by
  have he₁ : W'.f.eval e₁ = 0 := by rw [hf]; simp
  have he₂ : W'.f.eval e₂ = 0 := by rw [hf]; simp
  rw [μX_of_eval_f_eq_zero he₁]
  refine W'.unit_class_ne_one_of_evalRoot_neg _ he₂ ?_
  rw [W'.eval_projFactor_torsion_ne he₁ he₂ h12.ne']
  linarith

-- With three real roots, the image of `μ` is `{1, class of (e₁, 0)}`.
private lemma range_μ₀_split₃ {e₁ e₂ e₃ : ℝ} (h12 : e₁ < e₂) (h23 : e₂ < e₃)
    (hf : W'.f = (X - C e₁) * (X - C e₂) * (X - C e₃)) :
    Set.range (μ₀ (W := W')) = {1, W'.μX e₁} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨(_ | ⟨x, y, h⟩), rfl⟩
    · exact Set.mem_insert _ _
    · rw [μ₀_some]
      rcases W'.μX_mem_of_split₃ h12 h23 hf (W'.eval_f_nonneg_of_nonsingular h) with h' | h'
      · exact h' ▸ Set.mem_insert _ _
      · exact h' ▸ Set.mem_insert_of_mem _ rfl
  · rintro _ (rfl | rfl)
    · exact ⟨0, rfl⟩
    · have he₁ : W'.f.eval e₁ = 0 := by rw [hf]; simp
      exact ⟨.some e₁ 0 (W'.nonsingular_of_eval_f_eq_zero he₁), rfl⟩

-- With one real root, the image of `μ` is trivial.
private lemma range_μ₀_split₁ {e : ℝ} {q : ℝ[X]} (hm : q.Monic) (hirr : Irreducible q)
    (hd : q.natDegree = 2) (hf : W'.f = (X - C e) * q) :
    Set.range (μ₀ (W := W')) = {1} := by
  refine Set.eq_of_subset_of_subset ?_ (by rintro _ rfl; exact ⟨0, rfl⟩)
  rintro _ ⟨(_ | ⟨x, y, h⟩), rfl⟩
  · exact Set.mem_singleton _
  · rw [μ₀_some, W'.μX_eq_one_of_split₁ hm hirr hd hf (W'.eval_f_nonneg_of_nonsingular h)]
    exact Set.mem_singleton _

/-- Over `ℝ`, the image of the descent map has index `2` in the `2`-torsion: `2·#(im μ_ℝ)`
equals `#E(ℝ)[2]`. The étale algebra is `ℝ × ℂ` (one real root) or `ℝ³` (three real roots);
the image consists of the sign patterns of `x - θᵢ` on the region `f ≥ 0`. -/
theorem two_mul_card_range_μ_real :
    2 * Nat.card (μ (W := W')).range =
      Nat.card (nsmulAddMonoidHom (α := W'.Point) 2).ker := by
  rw [W'.card_ker_nsmul_two,
    show Nat.card (μ (W := W')).range = (Set.range (μ₀ (W := W'))).ncard by
      rw [← W'.range_μ_coe, ← MonoidHom.coe_range]; exact Nat.card_coe_set_eq _]
  rcases W'.f_split with ⟨e₁, e₂, e₃, h12, h23, hf⟩ | ⟨e, q, hm, hirr, hd, hf⟩
  · rw [W'.range_μ₀_split₃ h12 h23 hf, W'.card_roots_split₃ h12 h23 hf,
      Set.ncard_pair (Ne.symm (W'.μX_root_ne_one_of_split₃ h12 hf))]
  · rw [W'.range_μ₀_split₁ hm hirr hd hf, W'.card_roots_split₁ hm hirr hd hf,
      Set.ncard_singleton]

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
    _root_.IsIntegral 𝒪_[v] (mapOfDvd (algebraMap F F_[v]) hq (x : 𝕃 p)) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  refine ⟨P.map (algebraMap (𝓞 F) 𝒪_[v]), hPm.map _, ?_⟩
  have h2 := congrArg (mapOfDvd (algebraMap F F_[v]) hq) hPe
  rw [map_zero, Polynomial.hom_eval₂] at h2
  rw [Polynomial.eval₂_map]
  exact (congrArg (fun φ ↦ Polynomial.eval₂ φ
    (mapOfDvd (algebraMap F F_[v]) hq (x : 𝕃 p)) P)
    (mapOfDvd_comp_algebraMap v hq)).symm.trans h2

-- The base-change map on the rings of integers of the field factors: the restriction of
-- `mapOfDvd` to the integral closures.
private noncomputable def integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    W.ringOfIntegersFactor (𝓞 F) p →+* 𝕎[v].ringOfIntegersFactor 𝒪_[v] q :=
  ((mapOfDvd (algebraMap F F_[v]) hq).comp
    (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p))).codRestrict
      (integralClosure 𝒪_[v] (AdjoinRoot (q : F_[v][X]))).toSubring
      fun x ↦ W.isIntegral_mapOfDvd v hq x

-- The square of ring homomorphisms defining `integerMapOfDvd`.
private lemma algebraMap_comp_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (algebraMap (𝕎[v].ringOfIntegersFactor 𝒪_[v] q) (AdjoinRoot (q : F_[v][X]))).comp
        (W.integerMapOfDvd v hq) =
      (mapOfDvd (algebraMap F F_[v]) hq).comp
        (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)) :=
  RingHom.ext fun _ ↦ rfl

-- The square `𝓞 F → 𝒪_v → B_q` versus `𝓞 F → B_p → B_q` on the rings of integers.
private lemma integerMapOfDvd_comp_algebraMap {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (W.integerMapOfDvd v hq).comp (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) =
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)).comp
        (algebraMap (𝓞 F) 𝒪_[v]) := by
  ext c
  exact RingHom.congr_fun (mapOfDvd_comp_algebraMap v hq) c

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
  rw [mem_selmerGroupA_iff]
  simp only [localRes_mk]
  refine forall_congr' fun q ↦ ?_
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]

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
  have hinj : Function.Injective (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) := by
    have hinj' : Function.Injective (algebraMap (𝓞 F) (𝕃 p)) := by
      rw [IsScalarTower.algebraMap_eq (𝓞 F) F (𝕃 p)]
      exact (algebraMap F (𝕃 p)).injective.comp (IsFractionRing.injective (𝓞 F) F)
    exact fun a b hab ↦ hinj' (congrArg Subtype.val hab)
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
private lemma mapOfDvd_projFactor {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) (a : W.A) :
    mapOfDvd (algebraMap F F_[v]) hq (projFactor W.f_ne_zero W.squarefree_f p a) =
      projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q (W.mapA F_[v] a) := by
  obtain ⟨g, rfl⟩ := mk_surjective a
  rw [projFactor_mk, mapOfDvd_mk, mapA_mk, projFactor_mk]

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
  rw [mem_selmerGroupA_iff] at hm ⊢
  intro q
  -- find the global factor `p` below the local factor `q`
  obtain ⟨p, hq⟩ := Polynomial.Factors.exists_dvd_map (algebraMap F F_[v])
    W.f_ne_zero q.prime (q.dvd.trans (W.baseChange_f F_[v]).dvd)
  -- reduce to a valuation-divisibility statement for the `q`-component
  simp only [QuotientGroup.mk'_apply, localRes_mk] at hm ⊢
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]
  intro w hw
  -- the prime of the global field factor below `w`
  have hne := W.comap_integerMapOfDvd_ne_bot v hq w
  have hbelow := W.below_comapOfNeBot_integerMapOfDvd v hq w
  -- the global unramifiedness hypothesis at that prime
  have hp := hm p
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff] at hp
  have hdvd := hp (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w hne) fun hmem ↦
    hv (hbelow ▸ (HeightOneSpectrum.mem_primesAbove_iff (𝓞 F) _ _ _).mp hmem)
  -- transport along the embedding of field factors
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (mapOfDvd (algebraMap F F_[v]) hq) (W.integerMapOfDvd v hq)
    (W.algebraMap_comp_integerMapOfDvd v hq) w hne _ hdvd
  have hunits : Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a) =
      Units.map (mapOfDvd (algebraMap F F_[v]) hq : _ →* _)
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a) :=
    Units.ext (W.mapOfDvd_projFactor v hq (a : W.A)).symm
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
  rw [mem_selmerGroupA_iff]
  intro p
  simp only [QuotientGroup.mk'_apply]
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]
  intro w hw
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
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  obtain ⟨U, hUfin, ⟨e⟩⟩ :=
    exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers v 𝕎[v]
  -- `#(im μ) = [E(F_v) : 2·E(F_v)]`
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (μ (W := 𝕎[v]))).toEquiv,
    ker_μ_eq, ← Subgroup.index_eq_card, AddSubgroup.index_toSubgroup]
  -- the multiplication-by-2 kernel of `U ≃+ 𝒪_v` is trivial, as `𝒪_v` is torsion-free
  have hczO : CharZero 𝒪_[v] :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (𝓞 F) 𝒪_[v])
  have hker : Nat.card ((nsmulAddMonoidHom (α := U) 2)).ker = 1 := by
    rw [AddMonoidHom.ker_eq_bot _ fun a b hab ↦ e.injective <| nsmul_right_injective
      two_ne_zero (by simpa only [nsmulAddMonoidHom_apply, map_nsmul] using congrArg e hab)]
    exact AddSubgroup.card_bot
  -- the Euler-characteristic identity for the finite-index subgroup `U`
  have hchi := AddSubgroup.index_range_nsmul_mul_card_ker U 2
  rw [hker, mul_one] at hchi
  rw [hchi]
  congr 1
  -- transport `[U : 2U]` to `𝒪_v` and count there
  rw [show (nsmulAddMonoidHom (α := U) 2).range.index =
      (nsmulAddMonoidHom (α := 𝒪_[v]) 2).range.index by
        simpa [AddEquiv.map_range_nsmulAddMonoidHom]
          using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := U) 2).range e).symm,
    index_range_nsmul_two v]

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
  -- `v.Completion ≃+* ℂ` is algebraically closed
  have halg : IsAlgClosed v.Completion := by
    set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    refine IsAlgClosed.of_exists_root _ fun p hpm hpi ↦ ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (e : v.Completion →+* ℂ))
      (by rw [degree_map]; exact (Polynomial.degree_pos_of_irreducible hpi).ne')
    refine ⟨e.symm z, (map_eq_zero_iff (e : v.Completion →+* ℂ) e.injective).mp ?_⟩
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
      show ((e : v.Completion →+* ℂ) (e.symm z)) = z from e.apply_symm_apply z]
    exact hz
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
-- Degree counting for the squarefree cubic: `2 ^ (g - 1) ≤ r + 1` for `g` factors,
-- `r` of them linear.
private lemma two_pow_le_card_linear_factors :
    2 ^ (Nat.card 𝕎[v].f.Factors - 1) ≤
      Nat.card {q : 𝕎[v].f.Factors // (q : F_[v][X]).natDegree = 1} + 1 := by
  have hdeg : ∑ q : 𝕎[v].f.Factors, (q : F_[v][X]).natDegree ≤ 3 :=
    natDegree_f 𝕎[v] ▸ Polynomial.Factors.sum_natDegree_le 𝕎[v].f_ne_zero
  -- split the sum into the contributions of the linear and the higher-degree factors
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1)] at hdeg
  have h1 : ∑ q ∈ Finset.univ.filter
      (fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1), (q : F_[v][X]).natDegree =
      (Finset.univ.filter fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1).card := by
    rw [Finset.sum_congr rfl fun q hq ↦ (Finset.mem_filter.mp hq).2]
    simp
  have h2 : 2 * (Finset.univ.filter fun q : 𝕎[v].f.Factors ↦
      ¬ (q : F_[v][X]).natDegree = 1).card ≤
      ∑ q ∈ Finset.univ.filter
        (fun q : 𝕎[v].f.Factors ↦ ¬ (q : F_[v][X]).natDegree = 1),
        (q : F_[v][X]).natDegree := by
    rw [mul_comm, ← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun q hq ↦ ?_
    have hpos := q.irreducible.natDegree_pos
    have hne1 := (Finset.mem_filter.mp hq).2
    lia
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset 𝕎[v].f.Factors))
    (p := fun q ↦ (q : F_[v][X]).natDegree = 1)
  -- translate the cardinalities and case out
  rw [show Nat.card {q : 𝕎[v].f.Factors // (q : F_[v][X]).natDegree = 1} =
      (Finset.univ.filter fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1).card by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype],
    show Nat.card 𝕎[v].f.Factors = (Finset.univ : Finset 𝕎[v].f.Factors).card by
        rw [Nat.card_eq_fintype_card, Finset.card_univ],
    ← hcards]
  set a := (Finset.univ.filter fun q : 𝕎[v].f.Factors ↦ (q : F_[v][X]).natDegree = 1).card
  set b := (Finset.univ.filter fun q : 𝕎[v].f.Factors ↦ ¬ (q : F_[v][X]).natDegree = 1).card
  have hab : a + 2 * b ≤ 3 := by lia
  have hb1 : b ≤ 1 := by lia
  have ha3 : a ≤ 3 := by lia
  interval_cases b <;> interval_cases a <;> lia

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
  rw [scalarClass, mem_selmerGroupA_iff]
  intro q
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]
  intro w hw
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
    _ = Nat.card ((q : 𝕎[v].f.Factors) → (𝕎[v].selmerGroupFactor 𝒪_[v] q)) :=
        Nat.card_congr
          ⟨fun x q ↦ ⟨x.1 q, x.2 q (Set.mem_univ q)⟩,
            fun y ↦ ⟨fun q ↦ (y q : Units.modPow (AdjoinRoot (q : F_[v][X])) 2),
              fun q _ ↦ (y q).2⟩,
            fun _ ↦ rfl, fun _ ↦ rfl⟩
    _ = ∏ q : 𝕎[v].f.Factors, Nat.card (𝕎[v].selmerGroupFactor 𝒪_[v] q) := Nat.card_pi

-- Each factor contributes exactly two square classes at a good place.
private lemma card_selmerGroupFactor (hv : v ∉ W.badPrimes (𝓞 F)) (q : 𝕎[v].f.Factors) :
    Nat.card (𝕎[v].selmerGroupFactor 𝒪_[v] q) = 2 := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := W.two_notMem_asIdeal_of_notMem_badPrimes hv
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
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
  have hfinq : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  have hfinA := W.finite_selmerGroupA_adicCompletionIntegers hv
  -- the norm homomorphism restricted to `A(∅, 2)`
  set φ := (normM (W := 𝕎[v])).comp (𝕎[v].selmerGroupA 𝒪_[v]).subtype
  have hT : Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2)) = Nat.card φ.ker :=
    Nat.card_congr ⟨fun x ↦ ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, (Subgroup.mem_inf.mp x.2).2⟩,
      fun y ↦ ⟨y.1.1, Subgroup.mem_inf.mpr ⟨y.1.2, y.2⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
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
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
          ← Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]

end LocalCount

attribute [local instance] instFintypeFactorsBaseChange

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
  -- there is at least one factor
  have hg1 : 1 ≤ Nat.card 𝕎[v].f.Factors :=
    Nat.one_le_iff_ne_zero.mpr <| Nat.card_ne_zero.mpr
      ⟨Polynomial.Factors.nonempty <| Polynomial.not_isUnit_of_natDegree_pos _
        (by rw [natDegree_f]; lia), inferInstance⟩
  -- counting: `#(A(∅,2) ⊓ ker N) ≤ 2^(g-1) ≤ #E(F_v)[2] = #(im μ)`
  have hchain : Nat.card (𝕎[v].selmerGroupA 𝒪_[v] ⊓ (normM (W := 𝕎[v])).ker :
      Subgroup (Units.modPow 𝕎[v].A 2)) ≤ Nat.card (μ (W := 𝕎[v])).range := by
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
  exact (Subgroup.eq_of_le_of_card_ge hle hchain).symm

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
