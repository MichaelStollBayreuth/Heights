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

/-- The right-hand side of the Weierstrass equation in the coordinates `(t, w)`, with the
parameter series `q` in place of `t` and the unknown `v` in place of `w`. -/
private noncomputable def wStepAt (q v : PowerSeries O) : PowerSeries O :=
  q ^ 3 + C W.a₁ * q * v + C W.a₂ * q ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * q * v ^ 2 +
    C W.a₆ * v ^ 3

/-- One step of the fixed-point iteration defining `wSeries`: the right-hand side of the
Weierstrass equation in the coordinates `(t, w)`. -/
private noncomputable def wStep (w : PowerSeries O) : PowerSeries O :=
  W.wStepAt X w

private lemma wStepAt_contract {q u v : PowerSeries O} (hq : X ∣ q) (hu : X ∣ u) (hv : X ∣ v)
    {k : ℕ} (h : X ^ k ∣ u - v) : X ^ (k + 1) ∣ W.wStepAt q u - W.wStepAt q v := by
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
  have hXk : X ^ (k + 1) ∣ q * (u - v) := by
    rw [pow_succ, mul_comm (X ^ k)]
    exact mul_dvd_mul hq h
  have hstep : W.wStepAt q u - W.wStepAt q v = C W.a₁ * (q * (u - v)) +
      C W.a₂ * q * (q * (u - v)) + C W.a₃ * (u ^ 2 - v ^ 2) + C W.a₄ * q * (u ^ 2 - v ^ 2) +
      C W.a₆ * (u ^ 3 - v ^ 3) := by
    simp only [wStepAt]
    ring
  rw [hstep]
  exact dvd_add (dvd_add (dvd_add (dvd_add (hXk.mul_left _) ((hXk.mul_left _)))
    (h2.mul_left _)) (h2.mul_left _)) (h3.mul_left _)

/-- Two solutions of the Weierstrass equation at the same parameter series that both have
vanishing constant term agree. -/
private lemma eq_of_wStepAt_fixed {q v v' : PowerSeries O} (hq : X ∣ q) (hv : X ∣ v)
    (hv' : X ∣ v') (h : v = W.wStepAt q v) (h' : v' = W.wStepAt q v') : v = v' := by
  have key (k : ℕ) : X ^ k ∣ v - v' := by
    induction k with
    | zero => simp
    | succ k ih =>
      have := W.wStepAt_contract hq hv hv' ih
      rwa [← h, ← h'] at this
  ext n
  have h0 := X_pow_dvd_iff.mp (key (n + 1)) n (by lia)
  rwa [map_sub, sub_eq_zero] at h0

private lemma X_dvd_wStep {w : PowerSeries O} (hw : X ∣ w) : X ∣ W.wStep w := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨X ^ 2 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * (X * u ^ 2) +
    C W.a₄ * X * (X * u ^ 2) + C W.a₆ * (X ^ 2 * u ^ 3), ?_⟩
  simp only [wStep, wStepAt]
  ring

private lemma wStep_contract {u v : PowerSeries O} (hu : X ∣ u) (hv : X ∣ v) {k : ℕ}
    (h : X ^ k ∣ u - v) : X ^ (k + 1) ∣ W.wStep u - W.wStep v :=
  W.wStepAt_contract dvd_rfl hu hv h

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
  simp only [wStep, wStepAt]
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
    simp only [wStep, wStepAt]
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

/-- The unit part of `wSeries`: `w = t³·v` with `v(0) = 1`. -/
noncomputable def vSeries : PowerSeries O :=
  (W.X_pow_three_dvd_wSeries).choose

lemma wSeries_eq_X_pow_three_mul : W.wSeries = X ^ 3 * W.vSeries :=
  (W.X_pow_three_dvd_wSeries).choose_spec

@[simp]
lemma constantCoeff_vSeries : constantCoeff W.vSeries = 1 := by
  have h := congrArg (coeff 3) W.wSeries_eq_X_pow_three_mul
  rw [W.coeff_wSeries_three, show (3 : ℕ) = 0 + 3 from rfl,
    PowerSeries.coeff_X_pow_mul] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact h.symm

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

@[simp]
lemma constantCoeff_slopeSeries : constantCoeff W.slopeSeries = 0 := by
  have h : constantCoeff W.slopeSeries =
      PowerSeries.coeff ((0 : Unit ⊕ Unit →₀ ℕ) (Sum.inl ()) + (0 : Unit ⊕ Unit →₀ ℕ)
        (Sum.inr ()) + 1) W.wSeries :=
    W.coeff_slopeSeries 0
  rw [h]
  exact W.coeff_wSeries_of_lt (by simp)

lemma constantCoeff_wSeries_mv : MvPowerSeries.constantCoeff W.wSeries = 0 :=
  W.constantCoeff_wSeries

@[simp]
lemma constantCoeff_interceptSeries : constantCoeff W.interceptSeries = 0 := by
  simp [interceptSeries, constantCoeff_rename, W.constantCoeff_wSeries_mv]

/-- The third-root series: the parameter `t₃(t₁, t₂)` of the third intersection point of
the chord through the points with parameters `t₁`, `t₂` with the curve `(t, w(t))`.
By Vieta applied to the cubic in `t` obtained by substituting `w = λt + ν` into the
Weierstrass equation,
`t₃ = -t₁ - t₂ - (a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν)/(1 + a₂λ + a₄λ² + a₆λ³)`. -/
noncomputable def thirdRootSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  -MvPowerSeries.X (Sum.inl ()) - MvPowerSeries.X (Sum.inr ()) -
    (MvPowerSeries.C W.a₁ * W.slopeSeries + MvPowerSeries.C W.a₂ * W.interceptSeries +
        MvPowerSeries.C W.a₃ * W.slopeSeries ^ 2 +
        2 * MvPowerSeries.C W.a₄ * W.slopeSeries * W.interceptSeries +
        3 * MvPowerSeries.C W.a₆ * W.slopeSeries ^ 2 * W.interceptSeries) *
      MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
        MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1

@[simp]
lemma constantCoeff_thirdRootSeries : constantCoeff W.thirdRootSeries = 0 := by
  simp [thirdRootSeries]

/-- The series `u(t) = 1 - a₁t - a₃w(t)`: minus the denominator `y` of the coordinates
`x = t/w`, `y = -1/w` of the negative of the point with parameter `t`, rescaled by `w`. -/
noncomputable def uSeries : PowerSeries O :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.wSeries

@[simp]
lemma constantCoeff_uSeries : PowerSeries.constantCoeff W.uSeries = 1 := by
  simp [uSeries]

lemma mul_invOfUnit_uSeries : W.uSeries * PowerSeries.invOfUnit W.uSeries 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

lemma isUnit_uSeries : IsUnit W.uSeries :=
  IsUnit.of_mul_eq_one _ W.mul_invOfUnit_uSeries

/-- The formal inverse parameter series: the parameter `ι(t) = -t/(1 - a₁t - a₃w(t))` of
the negative of the point with parameter `t` on the curve `(t, w(t))`. -/
noncomputable def inverseSeries : PowerSeries O :=
  -(PowerSeries.X * PowerSeries.invOfUnit W.uSeries 1)

@[simp]
lemma constantCoeff_inverseSeries : PowerSeries.constantCoeff W.inverseSeries = 0 := by
  simp [inverseSeries]

lemma hasSubst_inverseSeries : PowerSeries.HasSubst (W.inverseSeries : PowerSeries O) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_inverseSeries

private lemma subst_one_eq (a : PowerSeries O) (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 : PowerSeries O) = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

-- substitution along `ι` maps `invOfUnit` to `invOfUnit` of the image
private lemma subst_inverseSeries_invOfUnit {D : PowerSeries O}
    (hD : PowerSeries.constantCoeff D = 1)
    (hD' : PowerSeries.constantCoeff (PowerSeries.subst W.inverseSeries D) = 1) :
    PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1) =
      PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 := by
  have h1 : PowerSeries.subst W.inverseSeries D *
      PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1) = 1 := by
    rw [← PowerSeries.subst_mul W.hasSubst_inverseSeries,
      PowerSeries.mul_invOfUnit _ 1 (by rw [hD]; rfl), subst_one_eq _ W.hasSubst_inverseSeries]
  have h2 : PowerSeries.subst W.inverseSeries D *
      PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by rw [hD']; rfl)
  calc PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1)
      = PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1) *
        (PowerSeries.subst W.inverseSeries D *
          PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1) := by
        rw [h2, mul_one]
    _ = (PowerSeries.subst W.inverseSeries D *
          PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit D 1)) *
        PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 := by ring
    _ = PowerSeries.invOfUnit (PowerSeries.subst W.inverseSeries D) 1 := by rw [h1, one_mul]

private lemma subst_inverseSeries_wStepAt (v : PowerSeries O) :
    PowerSeries.subst W.inverseSeries (W.wStepAt X v) =
      W.wStepAt W.inverseSeries (PowerSeries.subst W.inverseSeries v) := by
  simp only [wStepAt, PowerSeries.subst_add W.hasSubst_inverseSeries,
    PowerSeries.subst_mul W.hasSubst_inverseSeries,
    PowerSeries.subst_pow W.hasSubst_inverseSeries, PowerSeries.subst_C,
    PowerSeries.subst_X W.hasSubst_inverseSeries]
  rfl

/-- Composition with the formal inverse maps `w` to `-w/u` (the `w`-coordinate of the
negative of a point). -/
theorem subst_inverseSeries_wSeries :
    PowerSeries.subst W.inverseSeries W.wSeries =
      -(W.wSeries * PowerSeries.invOfUnit W.uSeries 1) := by
  refine W.eq_of_wStepAt_fixed (q := W.inverseSeries)
    ⟨-(PowerSeries.invOfUnit W.uSeries 1), by rw [inverseSeries]; ring⟩ ?_ ?_ ?_ ?_
  · -- `X ∣ subst ι w`
    rw [PowerSeries.X_dvd_iff]
    exact MvPowerSeries.constantCoeff_subst_eq_zero W.hasSubst_inverseSeries.const
      (fun _ ↦ W.constantCoeff_inverseSeries) W.constantCoeff_wSeries
  · exact ((PowerSeries.X_dvd_iff.mpr W.constantCoeff_wSeries).mul_right _).neg_right
  · -- `w ∘ ι` solves the Weierstrass equation at `ι`
    conv_lhs => rw [W.wSeries_eq_wStep]
    rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl,
      W.subst_inverseSeries_wStepAt]
  · -- `-w/u` solves the Weierstrass equation at `ι`
    refine (W.isUnit_uSeries.pow 3).mul_left_cancel ?_
    have h1 := W.mul_invOfUnit_uSeries
    have h2 := W.wSeries_eq_wStep
    rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl, wStepAt] at h2
    simp only [wStepAt, inverseSeries, uSeries] at h1 h2 ⊢
    grobner

/-- Composition with the formal inverse maps `u` to its inverse. -/
theorem subst_inverseSeries_uSeries :
    PowerSeries.subst W.inverseSeries W.uSeries = PowerSeries.invOfUnit W.uSeries 1 := by
  refine W.isUnit_uSeries.mul_left_cancel ?_
  rw [W.mul_invOfUnit_uSeries]
  simp only [uSeries, PowerSeries.subst_sub W.hasSubst_inverseSeries,
    PowerSeries.subst_mul W.hasSubst_inverseSeries, PowerSeries.subst_C,
    PowerSeries.subst_X W.hasSubst_inverseSeries, subst_one_eq _ W.hasSubst_inverseSeries,
    W.subst_inverseSeries_wSeries]
  have h1 := W.mul_invOfUnit_uSeries
  simp only [uSeries, inverseSeries,
    show (MvPowerSeries.C : O →+* MvPowerSeries Unit O) = PowerSeries.C from rfl] at h1 ⊢
  grobner

/-- The formal inverse is an involution. -/
theorem subst_inverseSeries_self :
    PowerSeries.subst W.inverseSeries W.inverseSeries = PowerSeries.X := by
  have hinv := W.subst_inverseSeries_invOfUnit (D := W.uSeries) (by simp)
    (by rw [W.subst_inverseSeries_uSeries]
        simp [PowerSeries.constantCoeff_invOfUnit])
  have hdouble : PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1 = W.uSeries := by
    have h1 : PowerSeries.invOfUnit W.uSeries 1 * W.uSeries = 1 := by
      rw [mul_comm]
      exact W.mul_invOfUnit_uSeries
    have h2 : PowerSeries.invOfUnit W.uSeries 1 *
        PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1 = 1 :=
      PowerSeries.mul_invOfUnit _ 1 (by simp [PowerSeries.constantCoeff_invOfUnit])
    calc PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1
        = (PowerSeries.invOfUnit W.uSeries 1 * W.uSeries) *
          PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1 := by rw [h1, one_mul]
      _ = W.uSeries * (PowerSeries.invOfUnit W.uSeries 1 *
          PowerSeries.invOfUnit (PowerSeries.invOfUnit W.uSeries 1) 1) := by ring
      _ = W.uSeries := by rw [h2, mul_one]
  have hexp : PowerSeries.subst W.inverseSeries (-(PowerSeries.X *
      PowerSeries.invOfUnit W.uSeries 1)) = -(W.inverseSeries *
      PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit W.uSeries 1)) := by
    rw [← PowerSeries.coe_substAlgHom W.hasSubst_inverseSeries, map_neg, map_mul,
      PowerSeries.coe_substAlgHom W.hasSubst_inverseSeries,
      PowerSeries.subst_X W.hasSubst_inverseSeries]
  rw [show PowerSeries.subst W.inverseSeries W.inverseSeries = -(W.inverseSeries *
      PowerSeries.subst W.inverseSeries (PowerSeries.invOfUnit W.uSeries 1)) from hexp,
    hinv, W.subst_inverseSeries_uSeries, hdouble, inverseSeries]
  linear_combination (PowerSeries.X : PowerSeries O) * W.mul_invOfUnit_uSeries

/-- The addition series of the chord construction: `F(t₁, t₂) = ι(t₃(t₁, t₂))`, the
parameter of the sum of the points with parameters `t₁`, `t₂`. -/
noncomputable def addSeries : MvPowerSeries (Unit ⊕ Unit) O :=
  MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.inverseSeries

lemma hasSubst_thirdRootSeries :
    MvPowerSeries.HasSubst (fun _ : Unit ↦ W.thirdRootSeries) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ W.constantCoeff_thirdRootSeries

@[simp]
lemma constantCoeff_addSeries :
    MvPowerSeries.constantCoeff W.addSeries = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero W.hasSubst_thirdRootSeries
    (fun _ ↦ W.constantCoeff_thirdRootSeries) W.constantCoeff_inverseSeries

/-! Swap-invariance of the chord data, giving commutativity of the formal group law. -/

lemma rename_swap_slopeSeries :
    MvPowerSeries.rename Sum.swap W.slopeSeries = W.slopeSeries := by
  ext d
  have hd : d = Finsupp.embDomain (Equiv.sumComm Unit Unit).toEmbedding
      (Finsupp.mapDomain Sum.swap d) := by
    ext t
    rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
    have : (⇑(Equiv.sumComm Unit Unit).toEmbedding ∘ Sum.swap) = id := by
      ext s
      match s with
      | .inl () => rfl
      | .inr () => rfl
    rw [this, Finsupp.mapDomain_id]
  calc MvPowerSeries.coeff d (MvPowerSeries.rename Sum.swap W.slopeSeries)
      = MvPowerSeries.coeff (Finsupp.mapDomain Sum.swap d) W.slopeSeries := by
        conv_lhs => rw [hd]
        exact coeff_embDomain_rename _ _ _
    _ = MvPowerSeries.coeff d W.slopeSeries := by
        rw [W.coeff_slopeSeries, W.coeff_slopeSeries]
        have h1 : Finsupp.mapDomain Sum.swap d (Sum.inl ()) = d (Sum.inr ()) := by
          rw [show (Sum.inl () : Unit ⊕ Unit) = (Equiv.sumComm Unit Unit) (Sum.inr ()) from rfl]
          exact Finsupp.mapDomain_equiv_apply (f := Equiv.sumComm Unit Unit) d _ |>.trans (by rfl)
        have h2 : Finsupp.mapDomain Sum.swap d (Sum.inr ()) = d (Sum.inl ()) := by
          rw [show (Sum.inr () : Unit ⊕ Unit) = (Equiv.sumComm Unit Unit) (Sum.inl ()) from rfl]
          exact Finsupp.mapDomain_equiv_apply (f := Equiv.sumComm Unit Unit) d _ |>.trans (by rfl)
        rw [h1, h2, add_comm (d (Sum.inr ()))]

lemma rename_swap_interceptSeries :
    MvPowerSeries.rename Sum.swap W.interceptSeries = W.interceptSeries := by
  rw [interceptSeries, map_sub, map_mul, W.rename_swap_slopeSeries, rename_X, rename_rename]
  exact W.interceptSeries_eq.symm

private lemma rename_swap_invOfUnit {D : MvPowerSeries (Unit ⊕ Unit) O}
    (hD : MvPowerSeries.constantCoeff D = 1) :
    MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1) =
      MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 := by
  have h1 : MvPowerSeries.rename Sum.swap D *
      MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : MvPowerSeries.rename Sum.swap D *
      MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 =
      1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by rw [constantCoeff_rename, hD]; rfl)
  calc MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1)
      = MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1) *
        (MvPowerSeries.rename Sum.swap D *
          MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1) := by rw [h2, mul_one]
    _ = (MvPowerSeries.rename Sum.swap D *
          MvPowerSeries.rename Sum.swap (MvPowerSeries.invOfUnit D 1)) *
        MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 := by ring
    _ = MvPowerSeries.invOfUnit (MvPowerSeries.rename Sum.swap D) 1 := by rw [h1, one_mul]

lemma rename_swap_thirdRootSeries :
    MvPowerSeries.rename Sum.swap W.thirdRootSeries = W.thirdRootSeries := by
  have hD : MvPowerSeries.constantCoeff (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
      MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) =
      1 := by
    simp
  rw [thirdRootSeries]
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat, rename_X,
    MvPowerSeries.rename_C, W.rename_swap_slopeSeries, W.rename_swap_interceptSeries,
    rename_swap_invOfUnit hD]
  simp only [show Sum.swap (Sum.inl () : Unit ⊕ Unit) = Sum.inr () from rfl,
    show Sum.swap (Sum.inr () : Unit ⊕ Unit) = Sum.inl () from rfl]
  ring

lemma rename_swap_addSeries :
    MvPowerSeries.rename Sum.swap W.addSeries = W.addSeries := by
  rw [addSeries, rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply W.hasSubst_thirdRootSeries (HasSubst.X_comp _)]
  congr 1
  funext u
  rw [← rename_eq_subst, W.rename_swap_thirdRootSeries]

section AddZero

/-! Specialization of the chord data at `t₂ = 0`: the slope becomes `w(t)/t`, the intercept
vanishes, and the third root becomes the formal inverse `ι(t)`. -/

private lemma hasSubst_unitR :
    MvPowerSeries.HasSubst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

private lemma subst_unitR_renameL :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries) = W.wSeries := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hasSubst_unitR]
  have hX : (fun u : Unit ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((MvPowerSeries.X ∘ fun _ ↦ Sum.inl () : Unit → MvPowerSeries (Unit ⊕ Unit) O) u)) =
      MvPowerSeries.X := by
    funext u
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_unitR]
    rfl
  rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
  have : algebraMap O O = RingHom.id O := rfl
  rw [this]
  exact congrFun (congrArg _ (MvPowerSeries.map_id)) W.wSeries

private lemma subst_unitR_renameR :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries) = 0 := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hasSubst_unitR]
  have hX : (fun u : Unit ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((MvPowerSeries.X ∘ fun _ ↦ Sum.inr () : Unit → MvPowerSeries (Unit ⊕ Unit) O) u)) =
      fun _ ↦ 0 := by
    funext u
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_unitR]
    rfl
  rw [hX]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_wSeries

private lemma X_mul_subst_unitR_slopeSeries :
    (PowerSeries.X : PowerSeries O) *
      MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0) W.slopeSeries = W.wSeries := by
  have h := congrArg (MvPowerSeries.subst
    (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O))
    W.slopeSeries_mul_sub
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_unitR] at h
  simp only [map_mul, map_sub] at h
  simp only [MvPowerSeries.coe_substAlgHom hasSubst_unitR, W.subst_unitR_renameL,
    W.subst_unitR_renameR, MvPowerSeries.subst_X hasSubst_unitR] at h
  have h1 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (Sum.inr ()) = 0 := rfl
  have h2 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [h1, h2] at h
  linear_combination -h

private lemma subst_unitR_interceptSeries :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.interceptSeries = 0 := by
  rw [interceptSeries, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR, map_sub, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom hasSubst_unitR, W.subst_unitR_renameL,
    MvPowerSeries.subst_X hasSubst_unitR]
  have h2 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (Sum.inl ()) = PowerSeries.X := rfl
  rw [h2]
  linear_combination -W.X_mul_subst_unitR_slopeSeries

-- transport of `invOfUnit` along a ring homomorphism fixing the constant coefficient
private lemma ringHom_invOfUnit {O' : Type*} [CommRing O'] {σ' τ' : Type*} {F : Type*}
    [FunLike F (MvPowerSeries σ' O) (MvPowerSeries τ' O')]
    [RingHomClass F (MvPowerSeries σ' O) (MvPowerSeries τ' O')] (φ : F)
    {D : MvPowerSeries σ' O} (hD : MvPowerSeries.constantCoeff D = 1)
    (hD' : MvPowerSeries.constantCoeff (φ D) = 1) :
    φ (MvPowerSeries.invOfUnit D 1) = MvPowerSeries.invOfUnit (φ D) 1 := by
  have h1 : φ D * φ (MvPowerSeries.invOfUnit D 1) = 1 := by
    rw [← map_mul, MvPowerSeries.mul_invOfUnit D 1 (by rw [hD]; rfl), map_one]
  have h2 : φ D * MvPowerSeries.invOfUnit (φ D) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by rw [hD']; rfl)
  calc φ (MvPowerSeries.invOfUnit D 1)
      = φ (MvPowerSeries.invOfUnit D 1) * (φ D * MvPowerSeries.invOfUnit (φ D) 1) := by
        rw [h2, mul_one]
    _ = (φ D * φ (MvPowerSeries.invOfUnit D 1)) * MvPowerSeries.invOfUnit (φ D) 1 := by ring
    _ = MvPowerSeries.invOfUnit (φ D) 1 := by rw [h1, one_mul]

/-- Specializing the third-root series at `t₂ = 0` gives the formal inverse. -/
theorem subst_unitR_thirdRootSeries :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.thirdRootSeries = W.inverseSeries := by
  set L : PowerSeries O :=
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.slopeSeries with hL
  have hXL : PowerSeries.X * L = W.wSeries := W.X_mul_subst_unitR_slopeSeries
  -- the specialized slope satisfies the `X`-cancelled Weierstrass equation
  have hLfix : L = PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * PowerSeries.X * L +
      PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * L + PowerSeries.C W.a₃ * PowerSeries.X * L ^ 2 +
      PowerSeries.C W.a₄ * PowerSeries.X ^ 2 * L ^ 2 +
      PowerSeries.C W.a₆ * PowerSeries.X ^ 2 * L ^ 3 := by
    refine PowerSeries.X_mul_cancel ?_
    rw [hXL]
    conv_lhs => rw [W.wSeries_eq]
    rw [← hXL]
    ring
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    have := congrArg PowerSeries.constantCoeff hLfix
    simpa [pow_two] using this
  -- push the substitution through the definition of the third root
  set D : MvPowerSeries (Unit ⊕ Unit) O := 1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
    MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3 with hD
  have hDsub : MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O) D =
      1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3 := by
    rw [hD, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [map_add, map_mul, map_pow, map_one]
    rw [MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [MvPowerSeries.subst_C,
      show (MvPowerSeries.C : O →+* MvPowerSeries Unit O) = PowerSeries.C from rfl]
    rfl
  have hD1 : MvPowerSeries.constantCoeff D = 1 := by simp [hD]
  have hD1' : PowerSeries.constantCoeff
      (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) = 1 := by
    simp [hL0]
  have hInv : MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      (MvPowerSeries.invOfUnit D 1) =
      MvPowerSeries.invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
        PowerSeries.C W.a₆ * L ^ 3) 1 := by
    have h := ringHom_invOfUnit (O' := O) (MvPowerSeries.substAlgHom hasSubst_unitR) hD1
      (by rw [MvPowerSeries.coe_substAlgHom, hDsub]; exact hD1')
    rwa [MvPowerSeries.coe_substAlgHom, hDsub] at h
  -- expand the substituted third root
  have hexp : MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.thirdRootSeries = -PowerSeries.X -
      (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2) *
        MvPowerSeries.invOfUnit (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
          PowerSeries.C W.a₆ * L ^ 3) 1 := by
    rw [thirdRootSeries, ← hD, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat]
    rw [MvPowerSeries.coe_substAlgHom hasSubst_unitR]
    simp only [MvPowerSeries.subst_C, MvPowerSeries.subst_X hasSubst_unitR, hInv,
      W.subst_unitR_interceptSeries,
      show (MvPowerSeries.C : O →+* MvPowerSeries Unit O) = PowerSeries.C from rfl]
    have h1 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
        (Sum.inr ()) = 0 := rfl
    have h2 : (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
        (Sum.inl ()) = PowerSeries.X := rfl
    rw [h1, h2]
    ring
  rw [hexp]
  -- compare with `ι = -X·u⁻¹` after multiplying by the units `u` and `D̃`
  set d : PowerSeries O := MvPowerSeries.invOfUnit (1 + PowerSeries.C W.a₂ * L +
    PowerSeries.C W.a₄ * L ^ 2 + PowerSeries.C W.a₆ * L ^ 3) 1 with hd
  have hUnit2 : (1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * d = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by exact_mod_cast hD1')
  have hUnit1 := W.mul_invOfUnit_uSeries
  clear_value L d
  refine (W.isUnit_uSeries.mul (IsUnit.of_mul_eq_one _ hUnit2)).mul_left_cancel ?_
  rw [inverseSeries]
  simp only [uSeries] at hUnit1 ⊢
  rw [← hXL] at hUnit1 ⊢
  linear_combination ((1 + PowerSeries.C W.a₂ * L + PowerSeries.C W.a₄ * L ^ 2 +
      PowerSeries.C W.a₆ * L ^ 3) * PowerSeries.X) * hUnit1 -
    ((1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * (PowerSeries.X * L)) *
      (PowerSeries.C W.a₁ * L + PowerSeries.C W.a₃ * L ^ 2)) * hUnit2 -
    (PowerSeries.C W.a₁ + PowerSeries.C W.a₃ * L) * hLfix

/-- Adding the zero point does nothing: specialization of the addition series at `t₂ = 0`
is the identity. -/
theorem subst_unitR_addSeries :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.addSeries = PowerSeries.X := by
  rw [addSeries, MvPowerSeries.subst_comp_subst_apply W.hasSubst_thirdRootSeries hasSubst_unitR]
  have h : (fun _ : Unit ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.thirdRootSeries) = fun _ : Unit ↦ (W.inverseSeries : MvPowerSeries Unit O) := by
    funext u
    exact W.subst_unitR_thirdRootSeries
  rw [h]
  exact W.subst_inverseSeries_self

private lemma hasSubst_unitL :
    MvPowerSeries.HasSubst
      (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)

/-- Adding the zero point on the left does nothing either, by commutativity. -/
theorem subst_unitL_addSeries :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O)
      W.addSeries = PowerSeries.X := by
  conv_lhs => rw [← W.rename_swap_addSeries]
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hasSubst_unitL]
  have h : (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst
      (Sum.elim (fun _ ↦ 0) MvPowerSeries.X : Unit ⊕ Unit → MvPowerSeries Unit O)
      ((MvPowerSeries.X ∘ Sum.swap : Unit ⊕ Unit → MvPowerSeries (Unit ⊕ Unit) O) s)) =
      (Sum.elim MvPowerSeries.X fun _ ↦ 0 : Unit ⊕ Unit → MvPowerSeries Unit O) := by
    funext s
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_unitL]
    match s with
    | .inl () => rfl
    | .inr () => rfl
  rw [h]
  exact W.subst_unitR_addSeries

end AddZero

section Naturality

/-! ### Naturality of the chord construction under coefficient ring maps

Every ingredient of the chord construction commutes with base change along a ring
homomorphism `φ : O →+* O'`. This is the reduction engine for associativity: it transports
identities from the universal Weierstrass curve over `ℤ[A₁, …, A₆]` to any curve.
-/

variable {O' : Type*} [CommRing O'] (φ : O →+* O')

theorem map_wSeries : PowerSeries.map φ W.wSeries = (W.map φ).wSeries := by
  refine (W.map φ).eq_of_wStepAt_fixed (q := X) dvd_rfl ?_ ?_ ?_ ((W.map φ).wSeries_eq_wStep)
  · rw [PowerSeries.X_dvd_iff, show PowerSeries.constantCoeff (PowerSeries.map φ W.wSeries) =
      φ (PowerSeries.constantCoeff W.wSeries) from rfl, W.constantCoeff_wSeries, map_zero]
  · exact PowerSeries.X_dvd_iff.mpr (W.map φ).constantCoeff_wSeries
  · conv_lhs => rw [W.wSeries_eq_wStep]
    simp only [wStep, wStepAt, map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem map_slopeSeries :
    MvPowerSeries.map φ W.slopeSeries = (W.map φ).slopeSeries := by
  ext d
  rw [MvPowerSeries.coeff_map, W.coeff_slopeSeries, (W.map φ).coeff_slopeSeries,
    ← W.map_wSeries φ, PowerSeries.coeff_map]

theorem map_interceptSeries :
    MvPowerSeries.map φ W.interceptSeries = (W.map φ).interceptSeries := by
  simp only [interceptSeries, map_sub, map_mul, ← MvPowerSeries.rename_map,
    MvPowerSeries.map_X, W.map_slopeSeries φ]
  rw [show MvPowerSeries.map φ (W.wSeries : MvPowerSeries Unit O) =
    ((W.map φ).wSeries : MvPowerSeries Unit O') from W.map_wSeries φ]

theorem map_uSeries : PowerSeries.map φ W.uSeries = (W.map φ).uSeries := by
  simp only [uSeries, map_sub, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X,
    W.map_wSeries φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

theorem map_thirdRootSeries :
    MvPowerSeries.map φ W.thirdRootSeries = (W.map φ).thirdRootSeries := by
  have hinv : MvPowerSeries.map φ (MvPowerSeries.invOfUnit
      (1 + MvPowerSeries.C W.a₂ * W.slopeSeries + MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1) =
      MvPowerSeries.invOfUnit
      (1 + MvPowerSeries.C (W.map φ).a₂ * (W.map φ).slopeSeries +
        MvPowerSeries.C (W.map φ).a₄ * (W.map φ).slopeSeries ^ 2 +
        MvPowerSeries.C (W.map φ).a₆ * (W.map φ).slopeSeries ^ 3) 1 := by
    have h := ringHom_invOfUnit (MvPowerSeries.map φ)
      (D := 1 + MvPowerSeries.C W.a₂ * W.slopeSeries + MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) (by simp) (by simp)
    rw [h]
    congr 1
    simp only [map_add, map_one, map_mul, map_pow, MvPowerSeries.map_C, W.map_slopeSeries φ,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  simp only [thirdRootSeries, map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat,
    MvPowerSeries.map_X, MvPowerSeries.map_C, W.map_slopeSeries φ, W.map_interceptSeries φ,
    hinv, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem map_inverseSeries :
    PowerSeries.map φ W.inverseSeries = (W.map φ).inverseSeries := by
  simp only [inverseSeries, PowerSeries.invOfUnit]
  have hD' : MvPowerSeries.constantCoeff (PowerSeries.map φ W.uSeries) = 1 := by
    rw [show (PowerSeries.map φ W.uSeries : PowerSeries O') = (W.map φ).uSeries
      from W.map_uSeries φ]
    exact (W.map φ).constantCoeff_uSeries
  have h := ringHom_invOfUnit (PowerSeries.map φ) (σ' := Unit) (τ' := Unit) (D := W.uSeries)
    (by exact W.constantCoeff_uSeries) hD'
  rw [map_neg, map_mul, PowerSeries.map_X, h, W.map_uSeries φ]

theorem map_addSeries :
    MvPowerSeries.map φ W.addSeries = (W.map φ).addSeries := by
  rw [addSeries, MvPowerSeries.map_subst W.hasSubst_thirdRootSeries, addSeries]
  congr 1
  · funext u
    exact W.map_thirdRootSeries φ
  · exact W.map_inverseSeries φ

end Naturality

private lemma hasSubst_assocLeftFam_addSeries :
    MvPowerSeries.HasSubst (assocLeftFam (fun _ : Unit ↦ W.addSeries)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · exact MvPowerSeries.constantCoeff_subst_eq_zero (FormalGroupLaw.hasSubst_emb12 (O := O))
      (by rintro (j | j) <;> simp) W.constantCoeff_addSeries
  · simp [assocLeftFam]

private lemma hasSubst_assocRightFam_addSeries :
    MvPowerSeries.HasSubst (assocRightFam (fun _ : Unit ↦ W.addSeries)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · simp [assocRightFam]
  · exact MvPowerSeries.constantCoeff_subst_eq_zero (FormalGroupLaw.hasSubst_emb23 (O := O))
      (by rintro (j | j) <;> simp) W.constantCoeff_addSeries

section Naturality

variable {O' : Type*} [CommRing O'] (φ : O →+* O')

private lemma map_assocLeftFam_addSeries :
    (fun s ↦ MvPowerSeries.map φ (assocLeftFam (fun _ : Unit ↦ W.addSeries) s)) =
      assocLeftFam (fun _ : Unit ↦ (W.map φ).addSeries) := by
  funext s
  match s with
  | .inl j =>
    simp only [assocLeftFam, Sum.elim_inl,
      MvPowerSeries.map_subst (FormalGroupLaw.hasSubst_emb12 (O := O)), W.map_addSeries φ]
    congr 1
    funext t
    rcases t with t | t <;> simp [MvPowerSeries.map_X]
  | .inr j => simp [assocLeftFam, MvPowerSeries.map_X]

private lemma map_assocRightFam_addSeries :
    (fun s ↦ MvPowerSeries.map φ (assocRightFam (fun _ : Unit ↦ W.addSeries) s)) =
      assocRightFam (fun _ : Unit ↦ (W.map φ).addSeries) := by
  funext s
  match s with
  | .inl j => simp [assocRightFam, MvPowerSeries.map_X]
  | .inr j =>
    simp only [assocRightFam, Sum.elim_inr,
      MvPowerSeries.map_subst (FormalGroupLaw.hasSubst_emb23 (O := O)), W.map_addSeries φ]
    congr 1
    funext t
    rcases t with t | t <;> simp [MvPowerSeries.map_X]

end Naturality

section FieldChord

/-! ### The chord construction computes the group law, at the level of field identities -/

variable {F : Type*} [Field F] [DecidableEq F] (WF : WeierstrassCurve F)

private lemma chord_x_ne {q₁ q₂ w₁ w₂ : F} (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0)
    (hx : q₁ * w₂ - q₂ * w₁ ≠ 0) : q₁ / w₁ ≠ q₂ / w₂ := by
  intro h
  apply hx
  field_simp at h
  linear_combination h

private lemma chord_addX_addY {q₁ q₂ w₁ w₂ Λ N T₃ wT : F}
    (hw₁ : w₁ = q₁ ^ 3 + WF.a₁ * q₁ * w₁ + WF.a₂ * q₁ ^ 2 * w₁ + WF.a₃ * w₁ ^ 2 +
      WF.a₄ * q₁ * w₁ ^ 2 + WF.a₆ * w₁ ^ 3)
    (hw₂ : w₂ = q₂ ^ 3 + WF.a₁ * q₂ * w₂ + WF.a₂ * q₂ ^ 2 * w₂ + WF.a₃ * w₂ ^ 2 +
      WF.a₄ * q₂ * w₂ ^ 2 + WF.a₆ * w₂ ^ 3)
    (hslope : Λ * (q₂ - q₁) = w₂ - w₁)
    (hN : N = w₁ - Λ * q₁)
    (hT₃ : (1 + WF.a₂ * Λ + WF.a₄ * Λ ^ 2 + WF.a₆ * Λ ^ 3) * (T₃ + q₁ + q₂) =
      -(WF.a₁ * Λ + WF.a₂ * N + WF.a₃ * Λ ^ 2 + 2 * WF.a₄ * Λ * N + 3 * WF.a₆ * Λ ^ 2 * N))
    (hwT : wT = Λ * T₃ + N)
    (hA : (1 + WF.a₂ * Λ + WF.a₄ * Λ ^ 2 + WF.a₆ * Λ ^ 3) ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hwT0 : wT ≠ 0)
    (hx : q₁ * w₂ - q₂ * w₁ ≠ 0) :
    T₃ / wT = WF.toAffine.addX (q₁ / w₁) (q₂ / w₂)
        (WF.toAffine.slope (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (-1 / w₂)) ∧
      (1 - WF.a₁ * T₃ - WF.a₃ * wT) / wT =
        WF.toAffine.addY (q₁ / w₁) (q₂ / w₂) (-1 / w₁)
          (WF.toAffine.slope (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (-1 / w₂)) := by
  have hxq := chord_x_ne hw₁0 hw₂0 hx
  have hne : q₁ / w₁ - q₂ / w₂ ≠ 0 := sub_ne_zero.mpr hxq
  have hline₁ : w₁ = Λ * q₁ + N := by linear_combination -hN
  have hline₂ : w₂ = Λ * q₂ + N := by linear_combination -hN - hslope
  have hqw : q₁ * w₂ - q₂ * w₁ = N * (q₁ - q₂) := by
    linear_combination q₁ * hline₂ - q₂ * hline₁
  have hN0 : N ≠ 0 := fun h ↦ hx (by rw [hqw, h, zero_mul])
  have hℓ : WF.toAffine.slope (q₁ / w₁) (q₂ / w₂) (-1 / w₁) (-1 / w₂) = Λ / N := by
    rw [Affine.slope_of_X_ne hxq, div_eq_div_iff (sub_ne_zero.mpr hxq) hN0]
    field_simp
    linear_combination (w₂ - Λ * q₂) * hline₁ - w₁ * hline₂ + Λ * q₂ * hline₁
  have hq12 : q₁ - q₂ ≠ 0 := by
    intro h
    apply hx
    rw [hqw, h, mul_zero]
  rw [hℓ]
  set AA := 1 + WF.a₂ * Λ + WF.a₄ * Λ ^ 2 + WF.a₆ * Λ ^ 3 with hAA2
  have hCub₁ : -N + AA*q₁^3 + WF.a₃*N^2 + WF.a₆*N^3 - Λ*q₁ + Λ*WF.a₁*q₁^2 + N*WF.a₁*q₁
    + N*WF.a₂*q₁^2 + WF.a₃*Λ^2*q₁^2 + WF.a₄*q₁*N^2 + 2*Λ*N*WF.a₃*q₁ + 2*Λ*N*WF.a₄*q₁^2
    + 3*Λ*WF.a₆*q₁*N^2 + 3*N*WF.a₆*Λ^2*q₁^2 = 0 := by
    linear_combination -hw₁ + (1 + w₁*(-WF.a₃ - N*WF.a₆ - WF.a₄*q₁ - Λ*WF.a₆*q₁) - N*WF.a₃
      - WF.a₁*q₁ - WF.a₂*q₁^2 - WF.a₆*N^2 - WF.a₆*w₁^2 - Λ*WF.a₃*q₁ - Λ*WF.a₄*q₁^2 - N*WF.a₄*q₁
      - WF.a₆*Λ^2*q₁^2 - 2*Λ*N*WF.a₆*q₁) * hline₁ + (q₁^3) * hAA2
  have hCub₂ : -N + AA*q₂^3 + WF.a₃*N^2 + WF.a₆*N^3 - Λ*q₂ + Λ*WF.a₁*q₂^2 + N*WF.a₁*q₂
    + N*WF.a₂*q₂^2 + WF.a₃*Λ^2*q₂^2 + WF.a₄*q₂*N^2 + 2*Λ*N*WF.a₃*q₂ + 2*Λ*N*WF.a₄*q₂^2
    + 3*Λ*WF.a₆*q₂*N^2 + 3*N*WF.a₆*Λ^2*q₂^2 = 0 := by
    linear_combination -hw₂ + (1 + w₂*(-WF.a₃ - N*WF.a₆ - WF.a₄*q₂ - Λ*WF.a₆*q₂) - N*WF.a₃
      - WF.a₁*q₂ - WF.a₂*q₂^2 - WF.a₆*N^2 - WF.a₆*w₂^2 - Λ*WF.a₃*q₂ - Λ*WF.a₄*q₂^2 - N*WF.a₄*q₂
      - WF.a₆*Λ^2*q₂^2 - 2*Λ*N*WF.a₆*q₂) * hline₂ + (q₂^3) * hAA2
  clear_value AA
  constructor
  · rw [Affine.addX]
    field_simp
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hA) hq12) ?_
    linear_combination (AA^3*(w₂*N^2*q₁^2 - w₁*N^2*q₂^2 + q₁*q₂*w₁*N^2 + q₂*w₁*w₂*Λ^2
      - q₁*q₂*w₂*N^2 - q₁*w₁*w₂*Λ^2 + WF.a₂*q₁*w₁*w₂*N^2 - WF.a₂*q₂*w₁*w₂*N^2
      + Λ*N*WF.a₁*q₂*w₁*w₂ - Λ*N*WF.a₁*q₁*w₁*w₂)) * hwT +
    (AA^3*(-N^3*q₂^2 + q₁*q₂*N^3 + N*q₂*w₂*Λ^2 + T₃*q₁*w₂*N^2 + T₃*q₂*w₂*Λ^3 + WF.a₂*q₁*w₂*N^3
      - Λ*T₃*N^2*q₂^2 - N*q₁*w₂*Λ^2 - T₃*q₁*w₂*Λ^3 - T₃*q₂*w₂*N^2 - WF.a₂*q₂*w₂*N^3
      + Λ*T₃*q₁*q₂*N^2 + Λ*WF.a₁*q₂*w₂*N^2 - Λ*WF.a₁*q₁*w₂*N^2 + Λ*T₃*WF.a₂*q₁*w₂*N^2
      + N*T₃*WF.a₁*q₂*w₂*Λ^2 - Λ*T₃*WF.a₂*q₂*w₂*N^2 - N*T₃*WF.a₁*q₁*w₂*Λ^2)) * hline₁ +
    (AA^3*(N^3*q₁^2 + T₃*q₁*N^3 + WF.a₂*q₁*N^4 + q₂*Λ^2*N^2 - N*Λ^3*q₁^2 - T₃*q₂*N^3
      - T₃*Λ^4*q₁^2 - WF.a₂*q₂*N^4 - q₁*q₂*N^3 - q₁*Λ^2*N^2 + Λ*WF.a₁*q₂*N^3 + Λ*WF.a₂*N^3*q₁^2
      + N*T₃*q₂*Λ^3 + N*q₁*q₂*Λ^3 + T₃*q₁*q₂*Λ^4 - Λ*WF.a₁*q₁*N^3 - N*T₃*q₁*Λ^3
      - WF.a₁*Λ^2*N^2*q₁^2 + 2*Λ*T₃*N^2*q₁^2 + Λ*T₃*WF.a₂*q₁*N^3 + T₃*WF.a₁*q₂*Λ^2*N^2
      + T₃*WF.a₂*Λ^2*N^2*q₁^2 + WF.a₁*q₁*q₂*Λ^2*N^2 - Λ*T₃*WF.a₂*q₂*N^3 - Λ*WF.a₂*q₁*q₂*N^3
      - N*T₃*WF.a₁*Λ^3*q₁^2 - T₃*WF.a₁*q₁*Λ^2*N^2 - 2*Λ*T₃*q₁*q₂*N^2 + N*T₃*WF.a₁*q₁*q₂*Λ^3
      - T₃*WF.a₂*q₁*q₂*Λ^2*N^2)) * hline₂ +
    (AA^2*(q₁*N^4 - q₂*N^4 + N*Λ^4*q₂^2 + q₁*Λ^5*q₂^2 + q₂*Λ^3*N^2 - N*Λ^4*q₁^2 - q₁*Λ^3*N^2
      - q₂*Λ^5*q₁^2 - 2*Λ*N^3*q₂^2 + 2*Λ*N^3*q₁^2 + Λ*WF.a₂*q₁*N^4 + WF.a₁*q₂*Λ^2*N^3
      + WF.a₁*Λ^3*N^2*q₂^2 + WF.a₂*Λ^2*N^3*q₁^2 - Λ*WF.a₂*q₂*N^4 - WF.a₁*q₁*Λ^2*N^3
      - WF.a₁*Λ^3*N^2*q₁^2 - WF.a₂*Λ^2*N^3*q₂^2 - 3*q₁*Λ^2*N^2*q₂^2 + 3*q₂*Λ^2*N^2*q₁^2
      + N*WF.a₁*q₁*Λ^4*q₂^2 + WF.a₂*q₂*Λ^3*N^2*q₁^2 - N*WF.a₁*q₂*Λ^4*q₁^2
      - WF.a₂*q₁*Λ^3*N^2*q₂^2)) * hT₃ +
    (AA*(AA*N*Λ^4 + AA*q₂*Λ^5 - 2*AA*Λ*N^3 + AA*WF.a₁*Λ^3*N^2 - AA*WF.a₂*Λ^2*N^3
      - 3*AA*q₂*Λ^2*N^2 + AA*N*WF.a₁*q₂*Λ^4 - AA*WF.a₂*q₂*Λ^3*N^2)) * hCub₁ +
    (-N*AA^2*Λ^4 - q₁*AA^2*Λ^5 + 2*Λ*AA^2*N^3 + WF.a₂*AA^2*Λ^2*N^3 - WF.a₁*AA^2*Λ^3*N^2
      + 3*q₁*AA^2*Λ^2*N^2 + WF.a₂*q₁*AA^2*Λ^3*N^2 - N*WF.a₁*q₁*AA^2*Λ^4) * hCub₂ +
    (AA^2*(WF.a₂*q₁*N^5 + q₂*Λ^2*N^3 - WF.a₂*q₂*N^5 - q₁*Λ^2*N^3 + Λ*WF.a₁*q₂*N^4
      - Λ*WF.a₁*q₁*N^4)) * hAA2
  · rw [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
    field_simp
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hA) hq12) ?_
    linear_combination (AA^3*(q₂*w₂*N^3 - q₁*w₂*N^3 + Λ*w₁*N^2*q₂^2 + WF.a₁*w₁*N^3*q₂^2
      + q₁*w₁*w₂*Λ^3 - WF.a₁*w₂*N^3*q₁^2 - q₂*w₁*w₂*Λ^3 - 2*Λ*w₂*N^2*q₁^2 + WF.a₁*q₁*q₂*w₂*N^3
      - Λ*q₁*q₂*w₁*N^2 - WF.a₁*q₁*q₂*w₁*N^3 + 2*Λ*q₁*q₂*w₂*N^2 + Λ*WF.a₂*q₂*w₁*w₂*N^2
      + Λ*q₁*w₁*w₂*N^2*WF.a₁^2 + WF.a₁*WF.a₂*q₂*w₁*w₂*N^3 - Λ*WF.a₂*q₁*w₁*w₂*N^2
      - Λ*q₂*w₁*w₂*N^2*WF.a₁^2 - WF.a₁*WF.a₂*q₁*w₁*w₂*N^3 - 2*N*WF.a₁*q₂*w₁*w₂*Λ^2
      + 2*N*WF.a₁*q₁*w₁*w₂*Λ^2)) * hwT +
    (AA^3*(Λ*N^3*q₂^2 + WF.a₁*N^4*q₂^2 + q₁*w₂*N^3 - q₂*w₂*N^3 + N*q₁*w₂*Λ^3 + T₃*q₁*w₂*Λ^4
      + T₃*Λ^2*N^2*q₂^2 - Λ*q₁*q₂*N^3 - N*q₂*w₂*Λ^3 - T₃*q₂*w₂*Λ^4 - WF.a₁*q₁*q₂*N^4
      + Λ*T₃*WF.a₁*N^3*q₂^2 + Λ*WF.a₂*q₂*w₂*N^3 + Λ*q₁*w₂*N^3*WF.a₁^2 + T₃*WF.a₁*q₂*w₂*N^3
      + WF.a₁*WF.a₂*q₂*w₂*N^4 - Λ*WF.a₂*q₁*w₂*N^3 - Λ*q₂*w₂*N^3*WF.a₁^2 - T₃*WF.a₁*q₁*w₂*N^3
      - T₃*q₁*q₂*Λ^2*N^2 - WF.a₁*WF.a₂*q₁*w₂*N^4 - 2*WF.a₁*q₂*w₂*Λ^2*N^2 + 2*WF.a₁*q₁*w₂*Λ^2*N^2
      + T₃*WF.a₂*q₂*w₂*Λ^2*N^2 + T₃*q₁*w₂*Λ^2*N^2*WF.a₁^2 - Λ*T₃*WF.a₁*q₁*q₂*N^3
      - T₃*WF.a₂*q₁*w₂*Λ^2*N^2 - T₃*q₂*w₂*Λ^2*N^2*WF.a₁^2 - 2*N*T₃*WF.a₁*q₂*w₂*Λ^3
      + 2*N*T₃*WF.a₁*q₁*w₂*Λ^3 + Λ*T₃*WF.a₁*WF.a₂*q₂*w₂*N^3
      - Λ*T₃*WF.a₁*WF.a₂*q₁*w₂*N^3)) * hline₁ +
    (AA^3*(N*Λ^4*q₁^2 + T₃*Λ^5*q₁^2 + q₁*Λ^3*N^2 - Λ*N^3*q₁^2 - WF.a₁*N^4*q₁^2 - q₂*Λ^3*N^2
      + Λ*T₃*q₂*N^3 + Λ*WF.a₂*q₂*N^4 + Λ*q₁*q₂*N^3 + Λ*q₁*N^4*WF.a₁^2 + N*T₃*q₁*Λ^4
      + T₃*WF.a₁*q₂*N^4 + WF.a₁*WF.a₂*q₂*N^5 + WF.a₁*q₁*q₂*N^4 + Λ^2*N^3*WF.a₁^2*q₁^2
      - Λ*T₃*q₁*N^3 - Λ*WF.a₂*q₁*N^4 - Λ*q₂*N^4*WF.a₁^2 - N*T₃*q₂*Λ^4 - N*q₁*q₂*Λ^4
      - T₃*WF.a₁*q₁*N^4 - T₃*q₁*q₂*Λ^5 - WF.a₁*WF.a₂*q₁*N^5 - WF.a₂*Λ^2*N^3*q₁^2
      - 2*T₃*Λ^2*N^2*q₁^2 - 2*WF.a₁*q₂*Λ^2*N^3 + 2*WF.a₁*q₁*Λ^2*N^3 + 2*WF.a₁*Λ^3*N^2*q₁^2
      + T₃*WF.a₂*q₂*Λ^2*N^3 + T₃*q₁*Λ^2*N^3*WF.a₁^2 + T₃*Λ^3*N^2*WF.a₁^2*q₁^2
      + WF.a₂*q₁*q₂*Λ^2*N^3 - Λ*WF.a₁*WF.a₂*N^4*q₁^2 - T₃*WF.a₂*q₁*Λ^2*N^3
      - T₃*WF.a₂*Λ^3*N^2*q₁^2 - T₃*q₂*Λ^2*N^3*WF.a₁^2 - q₁*q₂*Λ^2*N^3*WF.a₁^2
      - 2*Λ*T₃*WF.a₁*N^3*q₁^2 - 2*T₃*WF.a₁*q₂*Λ^3*N^2 - 2*WF.a₁*q₁*q₂*Λ^3*N^2
      + 2*N*T₃*WF.a₁*Λ^4*q₁^2 + 2*T₃*WF.a₁*q₁*Λ^3*N^2 + 2*T₃*q₁*q₂*Λ^2*N^2
      + Λ*T₃*WF.a₁*WF.a₂*q₂*N^4 + Λ*WF.a₁*WF.a₂*q₁*q₂*N^4 + T₃*WF.a₂*q₁*q₂*Λ^3*N^2
      - Λ*T₃*WF.a₁*WF.a₂*q₁*N^4 - T₃*WF.a₁*WF.a₂*Λ^2*N^3*q₁^2 - T₃*q₁*q₂*Λ^3*N^2*WF.a₁^2
      - 2*N*T₃*WF.a₁*q₁*q₂*Λ^4 + 2*Λ*T₃*WF.a₁*q₁*q₂*N^3 + T₃*WF.a₁*WF.a₂*q₁*q₂*Λ^2*N^3)) * hline₂ +
    (AA^2*(Λ*q₂*N^4 + N*Λ^5*q₁^2 + WF.a₁*q₂*N^5 + q₁*Λ^4*N^2 + q₂*Λ^6*q₁^2 - Λ*q₁*N^4
      - N*Λ^5*q₂^2 - WF.a₁*q₁*N^5 - q₁*Λ^6*q₂^2 - q₂*Λ^4*N^2 - 2*Λ^2*N^3*q₁^2 + 2*Λ^2*N^3*q₂^2
      + WF.a₂*q₂*Λ^2*N^4 + WF.a₂*Λ^3*N^3*q₂^2 + q₁*Λ^2*N^4*WF.a₁^2 + Λ^3*N^3*WF.a₁^2*q₁^2
      - WF.a₂*q₁*Λ^2*N^4 - WF.a₂*Λ^3*N^3*q₁^2 - q₂*Λ^2*N^4*WF.a₁^2 - Λ^3*N^3*WF.a₁^2*q₂^2
      - 3*q₂*Λ^3*N^2*q₁^2 - 2*Λ*WF.a₁*N^4*q₁^2 - 2*WF.a₁*q₂*Λ^3*N^3 - 2*WF.a₁*Λ^4*N^2*q₂^2
      + 2*Λ*WF.a₁*N^4*q₂^2 + 2*WF.a₁*q₁*Λ^3*N^3 + 2*WF.a₁*Λ^4*N^2*q₁^2 + 3*q₁*Λ^3*N^2*q₂^2
      + Λ*WF.a₁*WF.a₂*q₂*N^5 + WF.a₁*WF.a₂*Λ^2*N^4*q₂^2 + WF.a₂*q₁*Λ^4*N^2*q₂^2
      + q₂*Λ^4*N^2*WF.a₁^2*q₁^2 - Λ*WF.a₁*WF.a₂*q₁*N^5 - WF.a₁*WF.a₂*Λ^2*N^4*q₁^2
      - WF.a₂*q₂*Λ^4*N^2*q₁^2 - q₁*Λ^4*N^2*WF.a₁^2*q₂^2 - 3*WF.a₁*q₂*Λ^2*N^3*q₁^2
      - 2*N*WF.a₁*q₁*Λ^5*q₂^2 + 2*N*WF.a₁*q₂*Λ^5*q₁^2 + 3*WF.a₁*q₁*Λ^2*N^3*q₂^2
      + WF.a₁*WF.a₂*q₁*Λ^3*N^3*q₂^2 - WF.a₁*WF.a₂*q₂*Λ^3*N^3*q₁^2)) * hT₃ +
    (AA*(-AA*N*Λ^5 - AA*q₂*Λ^6 + 2*AA*Λ^2*N^3 + AA*WF.a₂*Λ^3*N^3 - AA*Λ^3*N^3*WF.a₁^2
      - 2*AA*WF.a₁*Λ^4*N^2 + 2*AA*Λ*WF.a₁*N^4 + 3*AA*q₂*Λ^3*N^2 + AA*WF.a₁*WF.a₂*Λ^2*N^4
      + AA*WF.a₂*q₂*Λ^4*N^2 - AA*q₂*Λ^4*N^2*WF.a₁^2 - 2*AA*N*WF.a₁*q₂*Λ^5
      + 3*AA*WF.a₁*q₂*Λ^2*N^3 + AA*WF.a₁*WF.a₂*q₂*Λ^3*N^3)) * hCub₁ +
    (N*AA^2*Λ^5 + q₁*AA^2*Λ^6 - 2*AA^2*Λ^2*N^3 + AA^2*Λ^3*N^3*WF.a₁^2 - WF.a₂*AA^2*Λ^3*N^3
      - 3*q₁*AA^2*Λ^3*N^2 - 2*Λ*WF.a₁*AA^2*N^4 + 2*WF.a₁*AA^2*Λ^4*N^2 + q₁*AA^2*Λ^4*N^2*WF.a₁^2
      - WF.a₁*WF.a₂*AA^2*Λ^2*N^4 - WF.a₂*q₁*AA^2*Λ^4*N^2 - 3*WF.a₁*q₁*AA^2*Λ^2*N^3
      + 2*N*WF.a₁*q₁*AA^2*Λ^5 - WF.a₁*WF.a₂*q₁*AA^2*Λ^3*N^3) * hCub₂ +
    (AA^2*(q₁*Λ^3*N^3 - q₂*Λ^3*N^3 + Λ*WF.a₂*q₂*N^5 + Λ*q₁*N^5*WF.a₁^2 + WF.a₁*WF.a₂*q₂*N^6
      - Λ*WF.a₂*q₁*N^5 - Λ*q₂*N^5*WF.a₁^2 - WF.a₁*WF.a₂*q₁*N^6 - 2*WF.a₁*q₂*Λ^2*N^4
      + 2*WF.a₁*q₁*Λ^2*N^4)) * hAA2

/-- The chord construction computes the group law, at the level of nonsingular points. -/
private lemma chord_point_add {q₁ q₂ w₁ w₂ Λ N T₃ wT : F}
    (hw₁ : w₁ = q₁ ^ 3 + WF.a₁ * q₁ * w₁ + WF.a₂ * q₁ ^ 2 * w₁ + WF.a₃ * w₁ ^ 2 +
      WF.a₄ * q₁ * w₁ ^ 2 + WF.a₆ * w₁ ^ 3)
    (hw₂ : w₂ = q₂ ^ 3 + WF.a₁ * q₂ * w₂ + WF.a₂ * q₂ ^ 2 * w₂ + WF.a₃ * w₂ ^ 2 +
      WF.a₄ * q₂ * w₂ ^ 2 + WF.a₆ * w₂ ^ 3)
    (hslope : Λ * (q₂ - q₁) = w₂ - w₁)
    (hN : N = w₁ - Λ * q₁)
    (hT₃ : (1 + WF.a₂ * Λ + WF.a₄ * Λ ^ 2 + WF.a₆ * Λ ^ 3) * (T₃ + q₁ + q₂) =
      -(WF.a₁ * Λ + WF.a₂ * N + WF.a₃ * Λ ^ 2 + 2 * WF.a₄ * Λ * N + 3 * WF.a₆ * Λ ^ 2 * N))
    (hwT : wT = Λ * T₃ + N)
    (hA : (1 + WF.a₂ * Λ + WF.a₄ * Λ ^ 2 + WF.a₆ * Λ ^ 3) ≠ 0)
    (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0) (hwT0 : wT ≠ 0)
    (hx : q₁ * w₂ - q₂ * w₁ ≠ 0)
    (h₁ : WF.toAffine.Nonsingular (q₁ / w₁) (-1 / w₁))
    (h₂ : WF.toAffine.Nonsingular (q₂ / w₂) (-1 / w₂)) :
    ∃ h₃ : WF.toAffine.Nonsingular (T₃ / wT) ((1 - WF.a₁ * T₃ - WF.a₃ * wT) / wT),
      Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂ = Affine.Point.some _ _ h₃ := by
  obtain ⟨hX, hY⟩ := chord_addX_addY WF hw₁ hw₂ hslope hN hT₃ hwT hA hw₁0 hw₂0 hwT0 hx
  have hxq := chord_x_ne hw₁0 hw₂0 hx
  have hxy : ¬(q₁ / w₁ = q₂ / w₂ ∧ -1 / w₁ = WF.toAffine.negY (q₂ / w₂) (-1 / w₂)) :=
    fun h ↦ hxq h.1
  refine ⟨hX ▸ hY ▸ Affine.nonsingular_add h₁ h₂ hxy, ?_⟩
  rw [Affine.Point.add_some hxy]
  simp only [Affine.Point.some.injEq]
  exact ⟨hX.symm, hY.symm⟩

/-- The parametrized point `(q/w, -1/w)` is nonsingular whenever `(q, w)` satisfies the
Weierstrass equation in the `(t, w)`-chart and the discriminant does not vanish. -/
private lemma chord_point_nonsingular {q w : F}
    (hw : w = q ^ 3 + WF.a₁ * q * w + WF.a₂ * q ^ 2 * w + WF.a₃ * w ^ 2 +
      WF.a₄ * q * w ^ 2 + WF.a₆ * w ^ 3)
    (hw0 : w ≠ 0) (hΔ : WF.Δ ≠ 0) :
    WF.toAffine.Nonsingular (q / w) (-1 / w) := by
  refine (WF.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_
  rw [Affine.equation_iff]
  field_simp
  linear_combination hw

end FieldChord

section Universal

/-- The universal Weierstrass curve, over `ℤ[A₁, A₂, A₃, A₄, A₆]`. -/
noncomputable def universal : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

/-- Every Weierstrass curve is a base change of the universal one. -/
theorem exists_map_universal (W : WeierstrassCurve O) :
    ∃ φ : MvPolynomial (Fin 5) ℤ →+* O, universal.map φ = W := by
  refine ⟨(MvPolynomial.aeval ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]).toRingHom, ?_⟩
  ext <;> simp [universal, WeierstrassCurve.map]

/-- Associativity of the addition series for the universal Weierstrass curve.

This is the remaining core: it is proved by identifying the addition series with the group
law of the (elliptic, since `Δ ≠ 0`) curve over the fraction field of
`ℤ[A₁, …, A₆]⟦t₁, t₂, t₃⟧`. -/
theorem assoc_addSeries_universal (i : Unit) :
    MvPowerSeries.subst (assocLeftFam (fun _ : Unit ↦ universal.addSeries))
      universal.addSeries =
    MvPowerSeries.subst (assocRightFam (fun _ : Unit ↦ universal.addSeries))
      universal.addSeries :=
  sorry

/-- Associativity of the addition series, for any Weierstrass curve, by reduction to the
universal one. -/
theorem assoc_addSeries (W : WeierstrassCurve O) :
    MvPowerSeries.subst (assocLeftFam (fun _ : Unit ↦ W.addSeries)) W.addSeries =
      MvPowerSeries.subst (assocRightFam (fun _ : Unit ↦ W.addSeries)) W.addSeries := by
  obtain ⟨φ, rfl⟩ := exists_map_universal W
  have h := congrArg (MvPowerSeries.map φ) (assoc_addSeries_universal ())
  rw [MvPowerSeries.map_subst universal.hasSubst_assocLeftFam_addSeries,
    MvPowerSeries.map_subst universal.hasSubst_assocRightFam_addSeries,
    universal.map_assocLeftFam_addSeries φ, universal.map_assocRightFam_addSeries φ,
    universal.map_addSeries φ] at h
  exact h

end Universal


section OnLine

/-! ### The third intersection point lies on the chord

`w(t₃(t₁, t₂)) = λ(t₁, t₂)·t₃(t₁, t₂) + ν(t₁, t₂)`, proved via a multivariate version of
the fixed-point uniqueness engine (filtration by total degree) and the Vieta argument:
the cubic obtained by substituting the chord into the Weierstrass equation has roots
`t₁`, `t₂`, and its third root is `t₃` by construction, so the line value at `t₃` solves
the Weierstrass equation there; so does `w ∘ t₃`, and solutions are unique.
-/

-- vanishing of all coefficients of total degree `< k`
private def LowVanish {σ : Type*} (k : ℕ) (f : MvPowerSeries σ O) : Prop :=
  ∀ d : σ →₀ ℕ, Finsupp.degree d < k → MvPowerSeries.coeff d f = 0

private lemma lowVanish_zero {σ : Type*} (f : MvPowerSeries σ O) : LowVanish 0 f :=
  fun _ hd ↦ absurd hd (by lia)

private lemma LowVanish.of_eq {σ : Type*} {k l : ℕ} {f : MvPowerSeries σ O}
    (hf : LowVanish k f) (h : k = l) : LowVanish l f := h ▸ hf

private lemma LowVanish.mono {σ : Type*} {k l : ℕ} {f : MvPowerSeries σ O}
    (hf : LowVanish l f) (h : k ≤ l) : LowVanish k f :=
  fun d hd ↦ hf d (lt_of_lt_of_le hd h)

private lemma LowVanish.add {σ : Type*} {k : ℕ} {f g : MvPowerSeries σ O}
    (hf : LowVanish k f) (hg : LowVanish k g) : LowVanish k (f + g) := fun d hd ↦ by
  rw [map_add, hf d hd, hg d hd, add_zero]

private lemma LowVanish.sub {σ : Type*} {k : ℕ} {f g : MvPowerSeries σ O}
    (hf : LowVanish k f) (hg : LowVanish k g) : LowVanish k (f - g) := fun d hd ↦ by
  rw [map_sub, hf d hd, hg d hd, sub_zero]

private lemma LowVanish.mul {σ : Type*} {k l : ℕ} {f g : MvPowerSeries σ O}
    (hf : LowVanish k f) (hg : LowVanish l g) : LowVanish (k + l) (f * g) := by
  intro d hd
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  rcases lt_or_ge (Finsupp.degree p.1) k with h1 | h1
  · rw [hf _ h1, zero_mul]
  · have hpd : p.1 + p.2 = d := by simpa using hp
    have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree d := by
      rw [← hpd, map_add]
    rw [hg _ (by lia), mul_zero]

private lemma lowVanish_one {σ : Type*} {f : MvPowerSeries σ O}
    (hf : MvPowerSeries.constantCoeff f = 0) : LowVanish 1 f := by
  intro d hd
  have hd0 : d = 0 := by
    ext s
    have := Finsupp.le_degree s d
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    lia
  rw [hd0]
  exact hf

private lemma eq_of_lowVanish {σ : Type*} {f g : MvPowerSeries σ O}
    (h : ∀ k, LowVanish k (f - g)) : f = g := by
  ext d
  have := h (Finsupp.degree d + 1) d (by lia)
  rwa [map_sub, sub_eq_zero] at this

variable {σ : Type*}

/-- The Weierstrass right-hand side with parameter `q` and unknown `v`, in a multivariate
power series ring. -/
private noncomputable def mvWStepAt (q v : MvPowerSeries σ O) : MvPowerSeries σ O :=
  q ^ 3 + MvPowerSeries.C W.a₁ * q * v + MvPowerSeries.C W.a₂ * q ^ 2 * v +
    MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * q * v ^ 2 +
    MvPowerSeries.C W.a₆ * v ^ 3

private lemma mvWStepAt_contract {q u v : MvPowerSeries σ O} (hq : LowVanish 1 q)
    (hu : LowVanish 1 u) (hv : LowVanish 1 v) {k : ℕ} (h : LowVanish k (u - v)) :
    LowVanish (k + 1) (W.mvWStepAt q u - W.mvWStepAt q v) := by
  have hC : ∀ a : O, LowVanish 0 (MvPowerSeries.C a : MvPowerSeries σ O) := fun a ↦
    lowVanish_zero _
  have h2 : LowVanish (k + 1) (u ^ 2 - v ^ 2) := by
    have he : u ^ 2 - v ^ 2 = (u + v) * (u - v) := by ring
    rw [he]
    exact ((hu.add hv).mul h).of_eq (by lia)
  have h3 : LowVanish (k + 1) (u ^ 3 - v ^ 3) := by
    have he : u ^ 3 - v ^ 3 = (u * u + u * v + v * v) * (u - v) := by ring
    rw [he]
    exact ((((hu.mul hu).mono one_le_two).add ((hu.mul hv).mono one_le_two)).add
      ((hv.mul hv).mono one_le_two)).mul h |>.of_eq (by lia)
  have hq1 : LowVanish (k + 1) (q * (u - v)) := (hq.mul h).of_eq (by lia)
  have hstep : W.mvWStepAt q u - W.mvWStepAt q v = MvPowerSeries.C W.a₁ * (q * (u - v)) +
      MvPowerSeries.C W.a₂ * q * (q * (u - v)) + MvPowerSeries.C W.a₃ * (u ^ 2 - v ^ 2) +
      MvPowerSeries.C W.a₄ * q * (u ^ 2 - v ^ 2) + MvPowerSeries.C W.a₆ * (u ^ 3 - v ^ 3) := by
    simp only [mvWStepAt]
    ring
  rw [hstep]
  refine ((((((hC W.a₁).mul hq1).of_eq (by lia)).add ?_).add ?_).add ?_).add ?_
  · exact (((hC W.a₂).mul hq).mul hq1).mono (by lia)
  · exact ((hC W.a₃).mul h2).of_eq (by lia)
  · exact (((hC W.a₄).mul hq).mul h2).mono (by lia)
  · exact ((hC W.a₆).mul h3).of_eq (by lia)

private lemma eq_of_mvWStepAt_fixed {q v v' : MvPowerSeries σ O} (hq : LowVanish 1 q)
    (hv : LowVanish 1 v) (hv' : LowVanish 1 v') (h : v = W.mvWStepAt q v)
    (h' : v' = W.mvWStepAt q v') : v = v' := by
  refine eq_of_lowVanish fun k ↦ ?_
  induction k with
  | zero => exact lowVanish_zero _
  | succ k ih =>
    have := W.mvWStepAt_contract hq hv hv' ih
    rwa [← h, ← h'] at this

section Pair

/-! Specialization of the chord data along a pair of parameter series `(q₁, q₂)` in a
multivariate power series ring: the substitution plumbing feeding the identification of
the addition series with the group law over the fraction field. -/

variable {σ' : Type*} [Finite σ'] {q₁ q₂ : MvPowerSeries σ' O}

private lemma hasSubst_pair (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.HasSubst
      (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) : Unit ⊕ Unit → MvPowerSeries σ' O) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simpa)

private lemma hasSubst_single {q : MvPowerSeries σ' O}
    (hq : MvPowerSeries.constantCoeff q = 0) :
    MvPowerSeries.HasSubst (fun _ : Unit ↦ q) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ hq

private lemma subst_pair_rename (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) (c : Unit → Unit ⊕ Unit) (f : PowerSeries O) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) (MvPowerSeries.rename c f) =
      MvPowerSeries.subst (fun _ : Unit ↦ Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂) (c ())) f := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _)
      (hasSubst_pair h₁ h₂)]
  congr 1
  funext u
  rw [Function.comp_apply, MvPowerSeries.subst_X (hasSubst_pair h₁ h₂)]

/-- The Weierstrass equation holds for `w` composed with any parameter series. -/
private lemma subst_wSeries_fix {q : MvPowerSeries σ' O}
    (hq : MvPowerSeries.constantCoeff q = 0) :
    MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries =
      W.mvWStepAt q (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) := by
  conv_lhs => rw [W.wSeries_eq_wStep]
  rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl]
  rw [wStepAt, ← MvPowerSeries.coe_substAlgHom (hasSubst_single hq)]
  simp only [map_add, map_mul, map_pow]
  rw [MvPowerSeries.coe_substAlgHom (hasSubst_single hq)]
  simp only [show (PowerSeries.C : O →+* O⟦X⟧) = MvPowerSeries.C from rfl,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
    MvPowerSeries.subst_C, MvPowerSeries.subst_X (hasSubst_single hq), mvWStepAt]

private lemma pair_slope_identity (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.slopeSeries * (q₂ - q₁) =
      MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries -
        MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries := by
  have h := congrArg (MvPowerSeries.substAlgHom (hasSubst_pair h₁ h₂)) W.slopeSeries_mul_sub
  simp only [map_mul, map_sub] at h
  simp only [MvPowerSeries.coe_substAlgHom (hasSubst_pair h₁ h₂),
    subst_pair_rename h₁ h₂, MvPowerSeries.subst_X (hasSubst_pair h₁ h₂),
    Sum.elim_inl, Sum.elim_inr] at h
  exact h

private lemma pair_intercept_identity₁ (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.interceptSeries =
      MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries -
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.slopeSeries * q₁ := by
  have h := congrArg (MvPowerSeries.substAlgHom (hasSubst_pair h₁ h₂))
    (show W.interceptSeries = MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries -
      W.slopeSeries * MvPowerSeries.X (Sum.inl ()) from rfl)
  simp only [map_sub, map_mul] at h
  simp only [MvPowerSeries.coe_substAlgHom (hasSubst_pair h₁ h₂),
    subst_pair_rename h₁ h₂, MvPowerSeries.subst_X (hasSubst_pair h₁ h₂),
    Sum.elim_inl, Sum.elim_inr] at h
  exact h

private lemma pair_intercept_identity₂ (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.interceptSeries =
      MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries -
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.slopeSeries * q₂ := by
  have h := congrArg (MvPowerSeries.substAlgHom (hasSubst_pair h₁ h₂)) W.interceptSeries_eq
  simp only [map_sub, map_mul] at h
  simp only [MvPowerSeries.coe_substAlgHom (hasSubst_pair h₁ h₂),
    subst_pair_rename h₁ h₂, MvPowerSeries.subst_X (hasSubst_pair h₁ h₂),
    Sum.elim_inl, Sum.elim_inr] at h
  exact h

private lemma pair_thirdRoot_constantCoeff (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair h₁ h₂)
    (by rintro (j | j) <;> simpa) W.constantCoeff_thirdRootSeries

private lemma pair_F_comp (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries =
      MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
        W.inverseSeries := by
  rw [addSeries, MvPowerSeries.subst_comp_subst_apply W.hasSubst_thirdRootSeries
    (hasSubst_pair h₁ h₂)]

private lemma pair_u_mul (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
        W.uSeries *
      MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
        (PowerSeries.invOfUnit W.uSeries 1) = 1 := by
  have h := congrArg (MvPowerSeries.substAlgHom
    (hasSubst_single (W.pair_thirdRoot_constantCoeff h₁ h₂))) W.mul_invOfUnit_uSeries
  simp only [map_mul, map_one] at h
  simpa only [MvPowerSeries.coe_substAlgHom
    (hasSubst_single (W.pair_thirdRoot_constantCoeff h₁ h₂))] using h

private lemma pair_F_eq (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries =
      -(MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries *
        MvPowerSeries.subst (fun _ : Unit ↦
          MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
          (PowerSeries.invOfUnit W.uSeries 1)) := by
  rw [W.pair_F_comp h₁ h₂,
    show W.inverseSeries = -(PowerSeries.X * PowerSeries.invOfUnit W.uSeries 1) from rfl,
    ← MvPowerSeries.coe_substAlgHom (hasSubst_single (W.pair_thirdRoot_constantCoeff h₁ h₂))]
  simp only [map_neg, map_mul]
  rw [MvPowerSeries.coe_substAlgHom (hasSubst_single (W.pair_thirdRoot_constantCoeff h₁ h₂)),
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
    MvPowerSeries.subst_X (hasSubst_single (W.pair_thirdRoot_constantCoeff h₁ h₂))]

private lemma pair_wF (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries) W.wSeries =
      -(MvPowerSeries.subst (fun _ : Unit ↦
          MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
          W.wSeries *
        MvPowerSeries.subst (fun _ : Unit ↦
          MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
          (PowerSeries.invOfUnit W.uSeries 1)) := by
  have hT := W.pair_thirdRoot_constantCoeff h₁ h₂
  have hcomp : MvPowerSeries.subst (fun _ : Unit ↦
      MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries) W.wSeries =
      MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
        (MvPowerSeries.subst (fun _ : Unit ↦ W.inverseSeries) W.wSeries) := by
    rw [MvPowerSeries.subst_comp_subst_apply
      (hasSubst_single W.constantCoeff_inverseSeries) (hasSubst_single hT),
      show (fun _ : Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂))
          W.addSeries) = fun _ : Unit ↦ MvPowerSeries.subst (fun _ : Unit ↦
          MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
          W.inverseSeries
        from funext fun _ ↦ W.pair_F_comp h₁ h₂]
  rw [hcomp, show MvPowerSeries.subst (fun _ : Unit ↦ W.inverseSeries) W.wSeries =
      PowerSeries.subst W.inverseSeries W.wSeries from rfl, W.subst_inverseSeries_wSeries,
    ← MvPowerSeries.coe_substAlgHom (hasSubst_single hT)]
  simp only [map_neg, map_mul]

private lemma pair_u_eq (h₁ : MvPowerSeries.constantCoeff q₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
        W.uSeries =
      1 - MvPowerSeries.C W.a₁ *
          MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries -
        MvPowerSeries.C W.a₃ * MvPowerSeries.subst (fun _ : Unit ↦
          MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
          W.wSeries := by
  have hT := W.pair_thirdRoot_constantCoeff h₁ h₂
  rw [uSeries, ← MvPowerSeries.coe_substAlgHom (hasSubst_single hT)]
  simp only [map_sub, map_one, map_mul]
  rw [MvPowerSeries.coe_substAlgHom (hasSubst_single hT)]
  simp only [show (PowerSeries.C : O →+* O⟦X⟧) = MvPowerSeries.C from rfl,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
    MvPowerSeries.subst_C, MvPowerSeries.subst_X (hasSubst_single hT)]

end Pair

section Domain

variable [IsDomain O]

private lemma X_inl_ne_X_inr :
    (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O) ≠
      MvPowerSeries.X (Sum.inr ()) := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl ()) 1)) h
  simp [MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff] at h1

private lemma line_left :
    W.slopeSeries * MvPowerSeries.X (Sum.inl ()) + W.interceptSeries =
      MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries := by
  rw [interceptSeries]
  ring

private lemma line_right :
    W.slopeSeries * MvPowerSeries.X (Sum.inr ()) + W.interceptSeries =
      MvPowerSeries.rename (fun _ ↦ Sum.inr ()) W.wSeries := by
  rw [interceptSeries_eq]
  ring

private lemma wsAt_rename (c : Unit → Unit ⊕ Unit) :
    MvPowerSeries.rename c W.wSeries =
      W.mvWStepAt (MvPowerSeries.X (c ())) (MvPowerSeries.rename c W.wSeries) := by
  conv_lhs => rw [W.wSeries_eq_wStep]
  simp only [wStep, wStepAt, mvWStepAt, map_add, map_mul, map_pow,
    show (PowerSeries.C : O →+* O⟦X⟧) = MvPowerSeries.C from rfl, MvPowerSeries.rename_C,
    show MvPowerSeries.rename c (PowerSeries.X : PowerSeries O) =
      MvPowerSeries.X (c ()) from MvPowerSeries.rename_X c ()]

set_option maxRecDepth 4000 in
/-- Vieta: the chord value at the third root satisfies the Weierstrass equation there. -/
private lemma line_at_thirdRoot :
    W.slopeSeries * W.thirdRootSeries + W.interceptSeries =
      W.mvWStepAt W.thirdRootSeries
        (W.slopeSeries * W.thirdRootSeries + W.interceptSeries) := by
  have hC1 : W.slopeSeries * MvPowerSeries.X (Sum.inl ()) + W.interceptSeries =
      W.mvWStepAt (MvPowerSeries.X (Sum.inl ()))
        (W.slopeSeries * MvPowerSeries.X (Sum.inl ()) + W.interceptSeries) := by
    rw [W.line_left]
    exact W.wsAt_rename _
  have hC2 : W.slopeSeries * MvPowerSeries.X (Sum.inr ()) + W.interceptSeries =
      W.mvWStepAt (MvPowerSeries.X (Sum.inr ()))
        (W.slopeSeries * MvPowerSeries.X (Sum.inr ()) + W.interceptSeries) := by
    rw [W.line_right]
    exact W.wsAt_rename _
  have hAd : (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
      MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) *
      MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
        MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by simp)
  simp only [mvWStepAt, thirdRootSeries] at hC1 ⊢
  set Λ := W.slopeSeries
  set N := W.interceptSeries
  set t₁ := (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O)
  set t₂ := (MvPowerSeries.X (Sum.inr ()) : MvPowerSeries (Unit ⊕ Unit) O)
  set d := MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * Λ +
    MvPowerSeries.C W.a₄ * Λ ^ 2 + MvPowerSeries.C W.a₆ * Λ ^ 3) 1
  -- extract the linear coefficient of the chord cubic by cancelling `t₁ - t₂`
  have hsub : (t₁ - t₂) * (-(1 + MvPowerSeries.C W.a₂ * Λ + MvPowerSeries.C W.a₄ * Λ ^ 2 +
      MvPowerSeries.C W.a₆ * Λ ^ 3) * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
      (MvPowerSeries.C W.a₁ * Λ + MvPowerSeries.C W.a₂ * N + MvPowerSeries.C W.a₃ * Λ ^ 2 +
        2 * MvPowerSeries.C W.a₄ * Λ * N + 3 * MvPowerSeries.C W.a₆ * Λ ^ 2 * N) *
        (t₁ + t₂) +
      (Λ - (MvPowerSeries.C W.a₁ * N + 2 * MvPowerSeries.C W.a₃ * Λ * N +
        MvPowerSeries.C W.a₄ * N ^ 2 + 3 * MvPowerSeries.C W.a₆ * Λ * N ^ 2))) = 0 := by
    simp only [mvWStepAt] at hC1 hC2
    linear_combination hC1 - hC2
  have hE1 := (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr X_inl_ne_X_inr)
  clear_value Λ N t₁ t₂ d
  set B := MvPowerSeries.C W.a₁ * Λ + MvPowerSeries.C W.a₂ * N + MvPowerSeries.C W.a₃ * Λ ^ 2 +
    2 * MvPowerSeries.C W.a₄ * Λ * N + 3 * MvPowerSeries.C W.a₆ * Λ ^ 2 * N with hB
  set T := -t₁ - t₂ - B * d with hT
  clear_value B T
  linear_combination hC1 + (T - t₁) * hE1 + ((T - t₁) * (T - t₂) * B) * hAd -
    ((T - t₁) * (T - t₂) * (1 + MvPowerSeries.C W.a₂ * Λ + MvPowerSeries.C W.a₄ * Λ ^ 2 +
      MvPowerSeries.C W.a₆ * Λ ^ 3)) * hT + (T ^ 2 - t₁ ^ 2) * hB

/-- The third intersection point lies on the chord:
`w(t₃(t₁, t₂)) = λ(t₁, t₂)·t₃(t₁, t₂) + ν(t₁, t₂)`. -/
theorem subst_thirdRootSeries_wSeries :
    MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.wSeries =
      W.slopeSeries * W.thirdRootSeries + W.interceptSeries := by
  have hfix : MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.wSeries =
      W.mvWStepAt W.thirdRootSeries
        (MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.wSeries) := by
    conv_lhs => rw [W.wSeries_eq_wStep]
    rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl]
    rw [wStepAt, ← MvPowerSeries.coe_substAlgHom W.hasSubst_thirdRootSeries]
    simp only [map_add, map_mul, map_pow]
    rw [MvPowerSeries.coe_substAlgHom W.hasSubst_thirdRootSeries]
    simp only [show (PowerSeries.C : O →+* O⟦X⟧) = MvPowerSeries.C from rfl,
      show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
      MvPowerSeries.subst_C, MvPowerSeries.subst_X W.hasSubst_thirdRootSeries, mvWStepAt]
  refine W.eq_of_mvWStepAt_fixed (q := W.thirdRootSeries)
    (lowVanish_one W.constantCoeff_thirdRootSeries) ?_ ?_ hfix W.line_at_thirdRoot
  · exact lowVanish_one (MvPowerSeries.constantCoeff_subst_eq_zero W.hasSubst_thirdRootSeries
      (fun _ ↦ W.constantCoeff_thirdRootSeries) W.constantCoeff_wSeries)
  · exact lowVanish_one (by simp)

variable {σ' : Type*} [Finite σ']

/-- `w` composed with a nonzero parameter is nonzero (over a domain). -/
private lemma subst_wSeries_ne_zero {q : MvPowerSeries σ' O}
    (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries ≠ 0 := by
  have hs := hasSubst_single hq
  have hexp : MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries =
      q ^ 3 * MvPowerSeries.subst (fun _ : Unit ↦ q) W.vSeries := by
    conv_lhs => rw [W.wSeries_eq_X_pow_three_mul]
    rw [← MvPowerSeries.coe_substAlgHom hs, map_mul, map_pow,
      MvPowerSeries.coe_substAlgHom hs,
      show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
      MvPowerSeries.subst_X hs]
  rw [hexp]
  refine mul_ne_zero (pow_ne_zero 3 hq0) fun h ↦ ?_
  have hc := congrArg MvPowerSeries.constantCoeff h
  rw [map_zero, MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ (0 : Unit →₀ ℕ)
    (fun d hd ↦ ?_)] at hc
  · rw [show MvPowerSeries.coeff (0 : Unit →₀ ℕ) W.vSeries =
      PowerSeries.constantCoeff W.vSeries from rfl, W.constantCoeff_vSeries] at hc
    simpa using hc
  · rcases Finsupp.ne_iff.mp hd with ⟨u, hu⟩
    have hu' : d u ≠ 0 := by simpa using hu
    rw [smul_eq_mul, Finsupp.prod, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hu') ?_)
    rw [map_pow, hq, zero_pow hu']

/-- The intercept series does not vanish: its coefficient at `t₁²t₂` is `-1`. -/
private lemma interceptSeries_ne_zero : W.interceptSeries ≠ 0 := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff
    (Finsupp.single (Sum.inl ()) 2 + Finsupp.single (Sum.inr ()) 1)) h
  rw [map_zero, interceptSeries, map_sub, coeff_rename_single,
    if_neg (by rw [eq_single_iff']; simp),
    show (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O) =
      MvPowerSeries.monomial (Finsupp.single (Sum.inl ()) 1) 1 from rfl,
    MvPowerSeries.coeff_mul_monomial, if_pos (by
      refine Finsupp.le_def.mpr fun s ↦ ?_
      rcases s with u | u <;> simp [Finsupp.single_apply]),
    W.coeff_slopeSeries] at h1
  have h2 : ((Finsupp.single (Sum.inl ()) 2 + Finsupp.single (Sum.inr ()) 1 -
      Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ)) (Sum.inl ()) = 1 := by
    simp [Finsupp.single_apply]
  have h3 : ((Finsupp.single (Sum.inl ()) 2 + Finsupp.single (Sum.inr ()) 1 -
      Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ)) (Sum.inr ()) = 1 := by
    simp [Finsupp.single_apply]
  rw [h2, h3, W.coeff_wSeries_three, mul_one] at h1
  simpa using h1

end Domain

end OnLine

end Chord

/-- The formal group law of a Weierstrass curve: the power series `F(t₁, t₂)` giving the
`t`-coordinate of the sum of the points with parameters `t₁`, `t₂` on the curve
`(t, w(t))`, via the chord construction (Silverman, IV.1.1). One-dimensional, so the index
type is `Unit`. The group-law axioms are `sorry`ed for now. -/
noncomputable def formalGroupLaw (W : WeierstrassCurve O) : FormalGroupLaw O Unit where
  F := fun _ ↦ W.addSeries
  zero_constantCoeff := fun _ ↦ W.constantCoeff_addSeries
  add_zero' := fun _ ↦ W.subst_unitR_addSeries
  zero_add' := fun _ ↦ W.subst_unitL_addSeries
  assoc' := fun _ ↦ W.assoc_addSeries
  comm' := fun _ ↦ by
    rw [show (fun s : Unit ⊕ Unit ↦ (MvPowerSeries.X s.swap : MvPowerSeries (Unit ⊕ Unit) O))
        = (MvPowerSeries.X ∘ Sum.swap) from rfl, ← MvPowerSeries.rename_eq_subst]
    exact W.rename_swap_addSeries



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
