import Mathlib
import Heights.ForMathlib.Chabauty.FormalGroupLaw
import Heights.ForMathlib.FormalGroup

/-!
# The formal group of a Weierstrass curve (skeleton)

This file connects the elliptic-curve side of `Heights.ForMathlib.FormalGroup` to the
formal-group-law kit vendored from the Chabauty project
(`Heights.ForMathlib.Chabauty.FormalGroupLaw`): the plan is to construct the formal group
of a Weierstrass curve as a one-dimensional `ChabautyColeman.FormalGroupLaw` (with index
type `Unit`) and to identify its `𝔪`-points with the kernel of reduction
`E₁(K_v) = filtration hW 0`.

Everything substantial is `sorry`ed for now; the file records the interface
(Silverman, *Arithmetic of Elliptic Curves*, IV.1 and VII.2):

* `WeierstrassCurve.wSeries`: the power series `w(t) ∈ O⟦t⟧` describing the curve near the
  origin in the coordinates `t = -x/y`, `w = -1/y`, as the solution of the fixed-point
  equation `w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³`;
* `WeierstrassCurve.formalGroupLaw`: the formal group law `F(t₁, t₂)` obtained from the
  chord construction on the curve `(t, w(t))`;
* `WeierstrassCurve.exists_points_equiv_filtration`: over `𝒪_v`, the `𝔪`-points of the
  formal group law of an integral model are the kernel of reduction, compatibly with the
  filtrations on both sides.

The `Fact (IsAdic (maximalIdeal 𝒪_v))` instance registered here activates the kit's
standing hypotheses for `O = 𝒪_v` (the remaining ones — completeness, Hausdorffness,
uniform add group, topological ring — are instances from
`Heights.ForMathlib.AdicCompletionExtension`).
-/

open ChabautyColeman PowerSeries IsDedekindDomain

namespace WeierstrassCurve

section wSeries

variable {O : Type*} [CommRing O]

/-- The power series `w(t) ∈ O⟦t⟧` describing a Weierstrass curve near the origin in the
coordinates `t = -x/y`, `w = -1/y`: the unique solution with `w ≡ t³ mod t⁴` of the
fixed-point equation `wSeries_eq` (Silverman, IV.1.1). -/
noncomputable def wSeries (_W : WeierstrassCurve O) : PowerSeries O :=
  sorry

/-- The defining fixed-point equation of `wSeries`, i.e. the Weierstrass equation in the
coordinates `(t, w)`. -/
theorem wSeries_eq (W : WeierstrassCurve O) :
    W.wSeries = X ^ 3 + PowerSeries.C W.a₁ * X * W.wSeries +
      PowerSeries.C W.a₂ * X ^ 2 * W.wSeries + PowerSeries.C W.a₃ * W.wSeries ^ 2 +
      PowerSeries.C W.a₄ * X * W.wSeries ^ 2 + PowerSeries.C W.a₆ * W.wSeries ^ 3 :=
  sorry

/-- The formal group law of a Weierstrass curve: the power series `F(t₁, t₂)` giving the
`t`-coordinate of the sum of the points with parameters `t₁`, `t₂` on the curve
`(t, w(t))`, via the chord construction (Silverman, IV.1.1). One-dimensional, so the index
type is `Unit`. -/
noncomputable def formalGroupLaw (_W : WeierstrassCurve O) : FormalGroupLaw O Unit :=
  sorry

end wSeries

end WeierstrassCurve

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

instance factIsAdic_adicCompletionIntegers :
    Fact (IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))) :=
  ⟨v.isAdic_maximalIdeal_adicCompletionIntegers⟩

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} [DecidableEq (v.adicCompletion K)] [CharZero K]
  [Finite (R ⧸ v.asIdeal)] {W : Affine (v.adicCompletion K)} [W.IsElliptic]
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}

/-- The `𝔪`-points of the formal group law of an integral model `W₀` of `W` are the kernel
of reduction `E₁(K_v) = filtration hW 0`, via `z ↦ (x, y)` with `x = z/w(z)`,
`y = -1/w(z)`; the equivalence matches the filtration by valuation on both sides
(Silverman, VII.2.2). -/
theorem exists_points_equiv_filtration (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) :
    ∃ θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0,
      ∀ (z : W₀.formalGroupLaw.Points) (n : ℕ),
        ((z () : v.adicCompletionIntegers K) ∈
            IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
          ((θ z : filtration hW 0) : W.Point) ∈ filtration hW n) :=
  sorry

end WeierstrassCurve.Affine
