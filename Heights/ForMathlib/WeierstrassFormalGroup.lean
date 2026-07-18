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

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O)

/-- One step of the fixed-point iteration defining `wSeries`: the right-hand side of the
Weierstrass equation in the coordinates `(t, w)`. -/
private noncomputable def wStep (w : PowerSeries O) : PowerSeries O :=
  X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2 +
    C W.a₆ * w ^ 3

private lemma X_dvd_wStep {w : PowerSeries O} (hw : X ∣ w) : X ∣ W.wStep w := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨X ^ 2 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * (X * u ^ 2) +
    C W.a₄ * X * (X * u ^ 2) + C W.a₆ * (X ^ 2 * u ^ 3), ?_⟩
  simp only [wStep]
  ring

private lemma wStep_contract {u v : PowerSeries O} (hu : X ∣ u) (hv : X ∣ v) {k : ℕ}
    (h : X ^ k ∣ u - v) : X ^ (k + 1) ∣ W.wStep u - W.wStep v := by
  have h2 : X ^ (k + 1) ∣ u ^ 2 - v ^ 2 := by
    have : u ^ 2 - v ^ 2 = (u + v) * (u - v) := by ring
    rw [this, pow_succ, mul_comm (X ^ k)]
    exact mul_dvd_mul (dvd_add hu hv) h
  have h3 : X ^ (k + 1) ∣ u ^ 3 - v ^ 3 := by
    have : u ^ 3 - v ^ 3 = (u ^ 2 + u * v + v ^ 2) * (u - v) := by ring
    rw [this, pow_succ, mul_comm (X ^ k)]
    refine mul_dvd_mul ?_ h
    exact dvd_add (dvd_add ((hu.mul_right u).trans (by rw [pow_two])) (hu.mul_right v))
      ((hv.mul_right v).trans (by rw [pow_two]))
  have hXk : (X : PowerSeries O) ^ (k + 1) ∣ X * (u - v) := by
    rw [pow_succ, mul_comm (X ^ k)]
    exact mul_dvd_mul_left X h
  have hstep : W.wStep u - W.wStep v = C W.a₁ * (X * (u - v)) + C W.a₂ * X * (X * (u - v)) +
      C W.a₃ * (u ^ 2 - v ^ 2) + C W.a₄ * X * (u ^ 2 - v ^ 2) + C W.a₆ * (u ^ 3 - v ^ 3) := by
    simp only [wStep]
    ring
  rw [hstep]
  exact dvd_add (dvd_add (dvd_add (dvd_add (hXk.mul_left _) ((hXk.mul_left _)))
    (h2.mul_left _)) (h2.mul_left _)) (h3.mul_left _)

private lemma X_dvd_iterate (m : ℕ) : X ∣ (W.wStep)^[m] (0 : PowerSeries O) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply']; exact W.X_dvd_wStep ih

private lemma iterate_congr (m d : ℕ) :
    X ^ m ∣ (W.wStep)^[m + d] (0 : PowerSeries O) - (W.wStep)^[m] (0 : PowerSeries O) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + d = (m + d) + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact W.wStep_contract (W.X_dvd_iterate _) (W.X_dvd_iterate _) ih

/-- The power series `w(t) ∈ O⟦t⟧` describing a Weierstrass curve near the origin in the
coordinates `t = -x/y`, `w = -1/y`: the unique solution with `w ≡ t³ mod t⁴` of the
fixed-point equation `wSeries_eq` (Silverman, IV.1.1), obtained as the `t`-adic limit of
the iteration of the right-hand side starting at `0`. -/
noncomputable def wSeries : PowerSeries O :=
  PowerSeries.mk fun n ↦ coeff n ((W.wStep)^[n + 1] 0)

private lemma coeff_wSeries (n : ℕ) :
    coeff n W.wSeries = coeff n ((W.wStep)^[n + 1] 0) :=
  coeff_mk _ _

private lemma X_pow_dvd_wSeries_sub_iterate (m : ℕ) :
    X ^ m ∣ W.wSeries - (W.wStep)^[m] (0 : PowerSeries O) := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [map_sub, W.coeff_wSeries, sub_eq_zero]
  have h1 := W.iterate_congr (k + 1) (m - (k + 1))
  rw [show k + 1 + (m - (k + 1)) = m by lia] at h1
  have h2 := X_pow_dvd_iff.mp h1 k (by lia)
  rw [map_sub, sub_eq_zero] at h2
  exact h2.symm

private lemma X_dvd_wSeries : (X : PowerSeries O) ∣ W.wSeries := by
  have h := W.X_pow_dvd_wSeries_sub_iterate 1
  rw [pow_one] at h
  have h2 := dvd_add h (W.X_dvd_iterate 1)
  rwa [sub_add_cancel] at h2

private theorem wSeries_eq_wStep : W.wSeries = W.wStep W.wSeries := by
  have hX : (X : PowerSeries O) ∣ W.wSeries := W.X_dvd_wSeries
  have key (m : ℕ) : X ^ (m + 1) ∣ W.wSeries - W.wStep W.wSeries := by
    have h1 := W.X_pow_dvd_wSeries_sub_iterate (m + 1)
    have h2 : X ^ (m + 1) ∣ (W.wStep)^[m + 1] (0 : PowerSeries O) - W.wStep W.wSeries := by
      rw [Function.iterate_succ_apply']
      exact W.wStep_contract (W.X_dvd_iterate m) hX
        (dvd_sub_comm.mp (W.X_pow_dvd_wSeries_sub_iterate m))
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this
  ext n
  have h := X_pow_dvd_iff.mp (key n) n (by lia)
  rwa [map_sub, sub_eq_zero] at h

private lemma X_pow_three_dvd_wStep {w : PowerSeries O} (hw : X ^ 3 ∣ w) :
    X ^ 3 ∣ W.wStep w := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨1 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * (X ^ 3 * u ^ 2) +
    C W.a₄ * (X ^ 4 * u ^ 2) + C W.a₆ * (X ^ 6 * u ^ 3), ?_⟩
  simp only [wStep]
  ring

theorem X_pow_three_dvd_wSeries : (X : PowerSeries O) ^ 3 ∣ W.wSeries := by
  have h3 : X ^ 3 ∣ (W.wStep)^[3] (0 : PowerSeries O) := by
    have h0 : (X : PowerSeries O) ^ 3 ∣ 0 := dvd_zero _
    exact W.X_pow_three_dvd_wStep (W.X_pow_three_dvd_wStep (W.X_pow_three_dvd_wStep h0))
  have h := dvd_add (W.X_pow_dvd_wSeries_sub_iterate 3) h3
  rwa [sub_add_cancel] at h

@[simp]
theorem constantCoeff_wSeries : constantCoeff W.wSeries = 0 :=
  X_dvd_iff.mp (dvd_trans (dvd_pow_self X three_ne_zero) W.X_pow_three_dvd_wSeries)

theorem coeff_wSeries_of_lt {k : ℕ} (hk : k < 3) : coeff k W.wSeries = 0 :=
  X_pow_dvd_iff.mp W.X_pow_three_dvd_wSeries k hk

@[simp]
theorem coeff_wSeries_three : coeff 3 W.wSeries = 1 := by
  have h4 : X ^ 4 ∣ W.wStep W.wSeries - X ^ 3 := by
    obtain ⟨u, hu⟩ := W.X_pow_three_dvd_wSeries
    refine ⟨C W.a₁ * u + C W.a₂ * (X * u) + C W.a₃ * (X ^ 2 * u ^ 2) +
      C W.a₄ * (X ^ 3 * u ^ 2) + C W.a₆ * (X ^ 5 * u ^ 3), ?_⟩
    rw [hu]
    simp only [wStep]
    ring
  have h0 : coeff 3 (W.wStep W.wSeries - X ^ 3) = 0 := X_pow_dvd_iff.mp h4 3 (by lia)
  rw [map_sub, coeff_X_pow, if_pos rfl, sub_eq_zero] at h0
  rw [W.wSeries_eq_wStep, h0]

/-- The defining fixed-point equation of `wSeries`, i.e. the Weierstrass equation in the
coordinates `(t, w)`. -/
theorem wSeries_eq :
    W.wSeries = X ^ 3 + PowerSeries.C W.a₁ * X * W.wSeries +
      PowerSeries.C W.a₂ * X ^ 2 * W.wSeries + PowerSeries.C W.a₃ * W.wSeries ^ 2 +
      PowerSeries.C W.a₄ * X * W.wSeries ^ 2 + PowerSeries.C W.a₆ * W.wSeries ^ 3 :=
  W.wSeries_eq_wStep

/-!
### The chord construction

The slope and intercept of the chord through the points with parameters `t₁`, `t₂` on the
curve `(t, w(t))`, as power series in `O⟦t₁, t₂⟧` (variables indexed by `Unit ⊕ Unit`, as
in the formal-group-law kit).
-/

section Chord

open MvPowerSeries

-- coefficients of a one-variable series renamed into a single variable `s`
private lemma coeff_rename_single {τ : Type*} [DecidableEq τ] (s : τ) (w : PowerSeries O)
    (d : τ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.rename (fun _ : Unit ↦ s) w) =
      if d = Finsupp.single s (d s) then PowerSeries.coeff (d s) w else 0 := by
  split_ifs with h
  · have hd : d = Finsupp.embDomain (⟨fun _ ↦ s, fun _ _ _ ↦ rfl⟩ : Unit ↪ τ)
        (Finsupp.single () (d s)) := by
      rw [Finsupp.embDomain_single]
      exact h
    have h1 := coeff_embDomain_rename (⟨fun _ ↦ s, fun _ _ _ ↦ rfl⟩ : Unit ↪ τ) w
      (Finsupp.single () (d s))
    rw [← hd] at h1
    exact h1
  · refine coeff_rename_eq_zero _ _ fun ⟨y, hy⟩ ↦ h ?_
    rw [← hy, Finsupp.unique_single y, Finsupp.mapDomain_single]
    simp

variable (W : WeierstrassCurve O)

/-- The slope (divided difference) series `λ(t₁, t₂) = (w(t₂) - w(t₁))/(t₂ - t₁)`,
defined directly by its coefficients: the coefficient of `t₁ⁱt₂ʲ` is the coefficient of
`t^(i+j+1)` in `wSeries`. -/
noncomputable def slopeSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  fun d ↦ PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) W.wSeries

lemma coeff_slopeSeries (d : Unit ⊕ Unit →₀ ℕ) :
    MvPowerSeries.coeff d W.slopeSeries =
      PowerSeries.coeff (d (Sum.inl ()) + d (Sum.inr ()) + 1) W.wSeries :=
  rfl

private lemma eq_single_iff (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inr ()) (d (Sum.inr ())) ↔ d (Sum.inl ()) = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext t
    match t with
    | .inl () => simpa using h
    | .inr () => simp

private lemma eq_single_iff' (d : Unit ⊕ Unit →₀ ℕ) :
    d = Finsupp.single (Sum.inl ()) (d (Sum.inl ())) ↔ d (Sum.inr ()) = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext t
    match t with
    | .inl () => simp
    | .inr () => simpa using h

/-- The defining property of the slope series:
`λ(t₁, t₂) · (t₂ - t₁) = w(t₂) - w(t₁)`. -/
theorem slopeSeries_mul_sub :
    W.slopeSeries * (MvPowerSeries.X (Sum.inr ()) - MvPowerSeries.X (Sum.inl ())) =
      MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries -
        MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries := by
  ext d
  set i := d (Sum.inl ()) with hi
  set j := d (Sum.inr ()) with hj
  rw [mul_sub, map_sub, map_sub,
    show (MvPowerSeries.X (Sum.inr ()) : MvPowerSeries (Unit ⊕ Unit) O) =
      MvPowerSeries.monomial (Finsupp.single (Sum.inr ()) 1) 1 from rfl,
    show (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O) =
      MvPowerSeries.monomial (Finsupp.single (Sum.inl ()) 1) 1 from rfl,
    MvPowerSeries.coeff_mul_monomial, MvPowerSeries.coeff_mul_monomial,
    coeff_rename_single, coeff_rename_single]
  have hsubr : 1 ≤ j → (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    lia
  have hsubl : 1 ≤ i → (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) +
      (d - Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) (Sum.inr ()) + 1 = i + j := by
    intro h
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    simp
    lia
  simp only [mul_one, eq_single_iff, eq_single_iff', Finsupp.single_le_iff, coeff_slopeSeries]
  split_ifs with h1 h2 h3 h4 <;>
    grind

/-- The intercept series `ν(t₁, t₂) = w(t₁) - λ(t₁, t₂)·t₁` of the chord through the
points with parameters `t₁`, `t₂` on the curve `(t, w(t))`. -/
noncomputable def interceptSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries -
    W.slopeSeries * MvPowerSeries.X (Sum.inl ())

/-- The intercept series is symmetric in the two parameters. -/
theorem interceptSeries_eq :
    W.interceptSeries = MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries -
      W.slopeSeries * MvPowerSeries.X (Sum.inr ()) := by
  have h := W.slopeSeries_mul_sub
  simp only [interceptSeries]
  linear_combination h

end Chord

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
