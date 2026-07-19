import Heights.ForMathlib.WeierstrassFormalGroup

/-!
# The 𝔪-points of the formal group of a Weierstrass curve and the kernel of reduction

For a Weierstrass curve `W` over a complete adic local ring `O` (the standing setting of
the vendored `p`-adic kit), the fixed-point series `w` and the chord data evaluate at
parameters `t` in the maximal ideal via `ChabautyColeman.MvPSeries.eval`.  The first part
of this file provides that evaluation layer: the value `W.wEval t`, its defining
Weierstrass fixed-point equation, the factorization `w(t) = t³·v(t)` with `v(t) ≡ 1 mod 𝔪`,
the uniqueness of solutions of the fixed-point equation in `𝔪`, the evaluated chord data
(`W.slopeEval`, `W.interceptEval`, `W.thirdRootEval`, `W.addEval`), and the formal inverse
`W.negPoint` on the `𝔪`-points.

The second part specializes to `O = 𝒪_v` and proves the identification of the `𝔪`-points
of the formal group of an integral model with the kernel of reduction (Silverman,
*Arithmetic of Elliptic Curves*, VII.2.2).

## Main definitions and statements

* `WeierstrassCurve.Affine.formalPoint`: the point `(t/w(t), -1/w(t))` of `E(K_v)`
  attached to an `𝔪`-point with parameter `t` (the point at infinity for `t = 0`).
* `WeierstrassCurve.Affine.formalPoint_add`: the parametrization is additive.  The chord
  case evaluates the formal chord identities; doubling uses an auxiliary parameter of very
  small valuation to reduce to chord cases.
* `WeierstrassCurve.Affine.filtration`: the subgroup `E_{n+1}(K_v)` of points whose
  `x`-coordinate has a pole of order at least `2(n+1)`; closure under addition comes from
  the formal group.
* `WeierstrassCurve.Affine.exists_points_equiv_filtration`: the additive equivalence
  `Ê(𝔪) ≃+ E₁(K_v)` matching `𝔪`-power levels with filtration steps.
* `WeierstrassCurve.Affine.exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers`:
  the structure theorem — `E(K_v)` has a finite-index subgroup isomorphic to `(𝒪_v, +)`;
  it rests on the two remaining `sorry`s `filtration_finiteIndex` (openness/compactness)
  and `exists_filtration_equiv` (the formal logarithm).
-/

open ChabautyColeman IsLocalRing MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- An element of `1 + 𝔪` in a local ring is a unit. -/
theorem _root_.IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal {u : O}
    (h : u - 1 ∈ maximalIdeal O) : IsUnit u :=
  sub_sub_cancel 1 u ▸ isUnit_one_sub_self_of_mem_nonunits _ (by simpa using neg_mem h)

variable (W : WeierstrassCurve O)

/-- The Weierstrass fixed-point polynomial: the right-hand side of the equation
`w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³` satisfied by `w = w(t)`. -/
def wPoly (t r : O) : O :=
  t ^ 3 + W.a₁ * t * r + W.a₂ * t ^ 2 * r + W.a₃ * r ^ 2 + W.a₄ * t * r ^ 2 + W.a₆ * r ^ 3

/-- Solutions in `𝔪` of the Weierstrass fixed-point equation at a parameter `t ∈ 𝔪` are
unique: the difference of two solutions is contracted by a factor in `𝔪`. -/
theorem eq_of_wPoly_fixed {t r r' : O} (ht : t ∈ maximalIdeal O) (hr : r ∈ maximalIdeal O)
    (hr' : r' ∈ maximalIdeal O) (h : r = W.wPoly t r) (h' : r' = W.wPoly t r') : r = r' := by
  have hm : W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (r + r') + W.a₄ * t * (r + r') +
      W.a₆ * (r ^ 2 + r * r' + r' ^ 2) ∈ maximalIdeal O := by
    refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact Ideal.mul_mem_left _ _ ht
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ht 2 two_pos)
    · exact Ideal.mul_mem_left _ _ (add_mem hr hr')
    · exact Ideal.mul_mem_left _ _ (add_mem hr hr')
    · exact Ideal.mul_mem_left _ _ (add_mem (add_mem (Ideal.pow_mem_of_mem _ hr 2 two_pos)
        (Ideal.mul_mem_right _ _ hr)) (Ideal.pow_mem_of_mem _ hr' 2 two_pos))
  have hkey : (1 - (W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (r + r') +
      W.a₄ * t * (r + r') + W.a₆ * (r ^ 2 + r * r' + r' ^ 2))) * (r - r') = 0 := by
    simp only [wPoly] at h h'
    linear_combination h - h'
  have hu : IsUnit (1 - (W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * (r + r') +
      W.a₄ * t * (r + r') + W.a₆ * (r ^ 2 + r * r' + r' ^ 2))) :=
    IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal (by simpa using neg_mem hm)
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hkey)

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]

omit W in
private lemma hasEval_pairElim {t₁ t₂ : O} (h₁ : t₁ ∈ maximalIdeal O)
    (h₂ : t₂ ∈ maximalIdeal O) :
    MvPowerSeries.HasEval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂ : Unit ⊕ Unit → O) :=
  MvPSeries.hasEval_of_mem (by rintro (j | j) <;> assumption)

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

omit W in
/-- The value at points of `𝔪^k` of a series whose constant coefficient lies in `𝔪^k`
lies in `𝔪^k`. -/
theorem _root_.ChabautyColeman.MvPSeries.eval_mem_maximalIdeal_pow
    {σ : Type*} [Finite σ] {z₀ : σ → O} (hz₀ : MvPowerSeries.HasEval z₀) {k : ℕ}
    (hmem : ∀ i, z₀ i ∈ maximalIdeal O ^ k) (h : MvPowerSeries σ O)
    (hcc : MvPowerSeries.constantCoeff h ∈ maximalIdeal O ^ k) :
    MvPSeries.eval z₀ h ∈ maximalIdeal O ^ k := by
  classical
  have htot := MvPSeries.hasSum_eval hz₀ h
  have hval : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d h * d.prod (fun s e ↦ z₀ s ^ e) ∈ maximalIdeal O ^ k := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simpa using hcc
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hi]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (hmem i) _
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))))
  have hsum := tsum_mem (IsAdic.isClosed_pow (I := maximalIdeal O) Fact.out k) hval
  rwa [htot.tsum_eq] at hsum

omit W in
/-- The value at points of `𝔪^j` of a series whose coefficients vanish below total degree
`c` lies in `𝔪^(c·j)`. -/
theorem _root_.ChabautyColeman.MvPSeries.eval_mem_maximalIdeal_pow_mul
    {σ : Type*} [Finite σ] {z₀ : σ → O} (hz₀ : MvPowerSeries.HasEval z₀) {j c : ℕ}
    (hmem : ∀ i, z₀ i ∈ maximalIdeal O ^ j) (h : MvPowerSeries σ O)
    (hcoeff : ∀ d : σ →₀ ℕ, d.degree < c → MvPowerSeries.coeff d h = 0) :
    MvPSeries.eval z₀ h ∈ maximalIdeal O ^ (c * j) := by
  classical
  have htot := MvPSeries.hasSum_eval hz₀ h
  have hval : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d h * d.prod (fun s e ↦ z₀ s ^ e) ∈ maximalIdeal O ^ (c * j) := by
    intro d
    rcases lt_or_ge d.degree c with hlt | hge
    · rw [hcoeff d hlt, zero_mul]
      exact zero_mem _
    -- the monomial value lies in `𝔪^(j·degree d)`
    have key : ∀ t : Finset σ, (∏ s ∈ t, z₀ s ^ d s) ∈ maximalIdeal O ^ (j * ∑ s ∈ t, d s) := by
      intro t
      induction t using Finset.induction with
      | empty => simp
      | insert s t hs ih =>
        rw [Finset.prod_insert hs, Finset.sum_insert hs, Nat.mul_add, pow_add]
        exact Ideal.mul_mem_mul (pow_mul (maximalIdeal O) j (d s) ▸
          Ideal.pow_mem_pow (hmem s) (d s)) ih
    refine Ideal.mul_mem_left _ _ (SetLike.le_def.mp
      (Ideal.pow_le_pow_right (by calc c * j ≤ d.degree * j := by gcongr
        _ = j * d.degree := mul_comm _ _)) ?_)
    have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
    rw [Finsupp.prod, hdeg]
    exact key d.support
  have hsum := tsum_mem (IsAdic.isClosed_pow (I := maximalIdeal O) Fact.out (c * j)) hval
  rwa [htot.tsum_eq] at hsum

/-- The value of the fixed-point series `w` at a parameter `t`. -/
noncomputable def wEval (t : O) : O := MvPSeries.eval (fun _ : Unit ↦ t) W.wSeries

/-- The value of the unit-part series `v` (with `w = t³·v`) at a parameter `t`. -/
noncomputable def vEval (t : O) : O := MvPSeries.eval (fun _ : Unit ↦ t) W.vSeries

variable {t : O} (ht : t ∈ maximalIdeal O)

include ht

theorem wEval_mem : W.wEval t ∈ maximalIdeal O :=
  MvPSeries.eval_mem_maximalIdeal (MvPSeries.hasEval_of_mem fun _ ↦ ht) (fun _ ↦ ht)
    W.wSeries (by rw [W.constantCoeff_wSeries_mv]; exact zero_mem _)

/-- The value of `w` satisfies the Weierstrass fixed-point equation. -/
theorem wEval_eq : W.wEval t = W.wPoly t (W.wEval t) := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.wSeries_eq
  simp only [map_add, map_mul, map_pow, MvPSeries.evalRingHom_apply] at h
  rw [show (PowerSeries.C : O →+* PowerSeries O) = MvPowerSeries.C from rfl,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl] at h
  simp only [MvPSeries.eval_C, MvPSeries.eval_X] at h
  exact h.trans (by rw [wPoly, wEval])

/-- The factorization `w(t) = t³ · v(t)` of the value of `w`. -/
theorem wEval_eq_cube_mul : W.wEval t = t ^ 3 * W.vEval t := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.wSeries_eq_X_pow_three_mul
  simp only [map_mul, map_pow, MvPSeries.evalRingHom_apply,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
    MvPSeries.eval_X] at h
  exact h

theorem vEval_sub_one_mem : W.vEval t - 1 ∈ maximalIdeal O := by
  have h := MvPSeries.eval_sub_constantCoeff_mem (MvPSeries.hasEval_of_mem fun _ ↦ ht)
    (fun _ ↦ ht) W.vSeries
  rwa [show MvPowerSeries.constantCoeff W.vSeries = PowerSeries.constantCoeff W.vSeries
    from rfl, W.constantCoeff_vSeries] at h

theorem isUnit_vEval : IsUnit (W.vEval t) :=
  IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal (W.vEval_sub_one_mem ht)

omit ht in
theorem wEval_ne_zero [IsDomain O] (ht : t ∈ maximalIdeal O) (ht0 : t ≠ 0) :
    W.wEval t ≠ 0 := by
  rw [W.wEval_eq_cube_mul ht]
  exact mul_ne_zero (pow_ne_zero 3 ht0) (W.isUnit_vEval ht).ne_zero

omit ht

/-!
### Evaluation of the chord data

The values of `u`, its inverse, the formal inverse `ι`, and the two-parameter chord data
(slope, intercept, third root, addition series) at parameters in the maximal ideal, with
the evaluated forms of their defining identities.
-/

/-- The value of the series `u = 1 - a₁t - a₃w(t)` at a parameter `t`. -/
noncomputable def uEval (t : O) : O := MvPSeries.eval (fun _ : Unit ↦ t) W.uSeries

/-- The value of the inverse of the series `u` at a parameter `t`. -/
noncomputable def duEval (t : O) : O :=
  MvPSeries.eval (fun _ : Unit ↦ t) (PowerSeries.invOfUnit W.uSeries 1)

/-- The value of the formal inverse series `ι` at a parameter `t`. -/
noncomputable def iotaEval (t : O) : O := MvPSeries.eval (fun _ : Unit ↦ t) W.inverseSeries

include ht

theorem uEval_eq : W.uEval t = 1 - W.a₁ * t - W.a₃ * W.wEval t := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) (show W.uSeries =
    1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.wSeries from rfl)
  simp only [map_sub, map_one, map_mul, MvPSeries.evalRingHom_apply] at h
  rw [show (PowerSeries.C : O →+* PowerSeries O) = MvPowerSeries.C from rfl,
    show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl] at h
  simp only [MvPSeries.eval_C, MvPSeries.eval_X] at h
  exact h

theorem uEval_mul_duEval : W.uEval t * W.duEval t = 1 := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.mul_invOfUnit_uSeries
  simp only [map_mul, map_one, MvPSeries.evalRingHom_apply] at h
  exact h

theorem isUnit_uEval : IsUnit (W.uEval t) :=
  IsUnit.of_mul_eq_one _ (W.uEval_mul_duEval ht)

theorem isUnit_duEval : IsUnit (W.duEval t) :=
  IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact W.uEval_mul_duEval ht)

theorem iotaEval_eq : W.iotaEval t = -(t * W.duEval t) := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) (show W.inverseSeries =
    -(PowerSeries.X * PowerSeries.invOfUnit W.uSeries 1) from rfl)
  simp only [map_neg, map_mul, MvPSeries.evalRingHom_apply] at h
  rw [show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl] at h
  simp only [MvPSeries.eval_X] at h
  exact h

theorem iotaEval_mem : W.iotaEval t ∈ maximalIdeal O :=
  MvPSeries.eval_mem_maximalIdeal (MvPSeries.hasEval_of_mem fun _ ↦ ht) (fun _ ↦ ht)
    W.inverseSeries (by
      rw [show MvPowerSeries.constantCoeff W.inverseSeries =
        PowerSeries.constantCoeff W.inverseSeries from rfl, W.constantCoeff_inverseSeries]
      exact zero_mem _)

omit W in
/-- Evaluation of a one-variable substitution is evaluation at the value. -/
theorem eval_subst_single {f : PowerSeries O} (hf : PowerSeries.constantCoeff f = 0)
    (g : PowerSeries O) :
    MvPSeries.eval (fun _ : Unit ↦ t) (PowerSeries.subst f g) =
      MvPSeries.eval (fun _ : Unit ↦ MvPSeries.eval (fun _ : Unit ↦ t) f) g :=
  MvPSeries.eval_subst (MvPSeries.hasEval_of_mem fun _ ↦ ht)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ hf) g

theorem wEval_iotaEval : W.wEval (W.iotaEval t) = -(W.wEval t * W.duEval t) := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.subst_inverseSeries_wSeries
  rw [map_neg, map_mul] at h
  simp only [MvPSeries.evalRingHom_apply] at h
  rw [eval_subst_single ht W.constantCoeff_inverseSeries] at h
  exact h

theorem iotaEval_iotaEval : W.iotaEval (W.iotaEval t) = t := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t := MvPSeries.hasEval_of_mem fun _ ↦ ht
  have h := congrArg (MvPSeries.evalRingHom hE) W.subst_inverseSeries_self
  simp only [MvPSeries.evalRingHom_apply] at h
  rw [eval_subst_single ht W.constantCoeff_inverseSeries] at h
  rw [show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
    MvPSeries.eval_X] at h
  exact h

omit ht

/-- The value of the slope series at a pair of parameters. -/
noncomputable def slopeEval (t₁ t₂ : O) : O :=
  MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.slopeSeries

/-- The value of the intercept series at a pair of parameters. -/
noncomputable def interceptEval (t₁ t₂ : O) : O :=
  MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.interceptSeries

/-- The value of the third-root series at a pair of parameters. -/
noncomputable def thirdRootEval (t₁ t₂ : O) : O :=
  MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.thirdRootSeries

/-- The value of the addition series at a pair of parameters. -/
noncomputable def addEval (t₁ t₂ : O) : O :=
  MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.addSeries

variable {t₁ t₂ : O} (h₁ : t₁ ∈ maximalIdeal O) (h₂ : t₂ ∈ maximalIdeal O)

include h₁ h₂

omit W in
/-- Evaluating a substituted one-variable series at a pair is evaluation at the value. -/
private lemma eval_pair_subst_single {q : MvPowerSeries (Unit ⊕ Unit) O}
    (hq : MvPowerSeries.constantCoeff q = 0) (g : PowerSeries O) :
    MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        (MvPowerSeries.subst (fun _ : Unit ↦ q) g) =
      MvPSeries.eval (fun _ : Unit ↦
        MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) q) g :=
  MvPSeries.eval_subst (hasEval_pairElim h₁ h₂)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ hq) g

omit W in
/-- Evaluating a renamed one-variable series at a pair evaluates at the matching entry. -/
private lemma eval_pair_rename (c : Unit → Unit ⊕ Unit) (g : PowerSeries O) :
    MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) (MvPowerSeries.rename c g) =
      MvPSeries.eval (fun _ : Unit ↦ Sum.elim (fun _ ↦ t₁) (fun _ ↦ t₂) (c ())) g := by
  rw [MvPowerSeries.rename_eq_subst]
  rw [MvPSeries.eval_subst (hasEval_pairElim h₁ h₂) (MvPowerSeries.HasSubst.X_comp c) g]
  congr 1
  funext s
  rw [Function.comp_apply, MvPSeries.eval_X]

/-- The evaluated slope identity: `λ̂·(t₂ - t₁) = w(t₂) - w(t₁)`. -/
theorem slopeEval_mul_sub :
    W.slopeEval t₁ t₂ * (t₂ - t₁) = W.wEval t₂ - W.wEval t₁ := by
  have h := congrArg (MvPSeries.evalRingHom (hasEval_pairElim h₁ h₂)) W.slopeSeries_mul_sub
  simp only [map_mul, map_sub, MvPSeries.evalRingHom_apply, MvPSeries.eval_X] at h
  rw [eval_pair_rename h₁ h₂, eval_pair_rename h₁ h₂] at h
  simp only [Sum.elim_inl, Sum.elim_inr] at h
  exact h

/-- The evaluated intercept identity: `ν̂ = w(t₁) - λ̂·t₁`. -/
theorem interceptEval_eq :
    W.interceptEval t₁ t₂ = W.wEval t₁ - W.slopeEval t₁ t₂ * t₁ := by
  have h := congrArg (MvPSeries.evalRingHom (hasEval_pairElim h₁ h₂))
    (show W.interceptSeries = MvPowerSeries.rename (fun _ ↦ Sum.inl ()) W.wSeries -
      W.slopeSeries * MvPowerSeries.X (Sum.inl ()) from rfl)
  simp only [map_sub, map_mul, MvPSeries.evalRingHom_apply, MvPSeries.eval_X] at h
  rw [eval_pair_rename h₁ h₂] at h
  simp only [Sum.elim_inl] at h
  exact h

theorem slopeEval_mem : W.slopeEval t₁ t₂ ∈ maximalIdeal O :=
  MvPSeries.eval_mem_maximalIdeal (hasEval_pairElim h₁ h₂)
    (by rintro (j | j) <;> assumption) W.slopeSeries
    (by rw [show MvPowerSeries.constantCoeff W.slopeSeries = 0 from
      W.constantCoeff_slopeSeries]; exact zero_mem _)

theorem thirdRootEval_mem : W.thirdRootEval t₁ t₂ ∈ maximalIdeal O :=
  MvPSeries.eval_mem_maximalIdeal (hasEval_pairElim h₁ h₂)
    (by rintro (j | j) <;> assumption) W.thirdRootSeries
    (by rw [W.constantCoeff_thirdRootSeries]; exact zero_mem _)

/-- The evaluated third-root relation, with the inverse of the cubic's leading
coefficient eliminated. -/
theorem thirdRootEval_relation :
    (1 + W.a₂ * W.slopeEval t₁ t₂ + W.a₄ * W.slopeEval t₁ t₂ ^ 2 +
        W.a₆ * W.slopeEval t₁ t₂ ^ 3) * (W.thirdRootEval t₁ t₂ + t₁ + t₂) =
      -(W.a₁ * W.slopeEval t₁ t₂ + W.a₂ * W.interceptEval t₁ t₂ +
        W.a₃ * W.slopeEval t₁ t₂ ^ 2 +
        2 * W.a₄ * W.slopeEval t₁ t₂ * W.interceptEval t₁ t₂ +
        3 * W.a₆ * W.slopeEval t₁ t₂ ^ 2 * W.interceptEval t₁ t₂) := by
  have hE := hasEval_pairElim (t₁ := t₁) (t₂ := t₂) h₁ h₂
  have hT := congrArg (MvPSeries.evalRingHom hE) (show W.thirdRootSeries =
    -MvPowerSeries.X (Sum.inl ()) - MvPowerSeries.X (Sum.inr ()) -
      (MvPowerSeries.C W.a₁ * W.slopeSeries + MvPowerSeries.C W.a₂ * W.interceptSeries +
        MvPowerSeries.C W.a₃ * W.slopeSeries ^ 2 +
        2 * MvPowerSeries.C W.a₄ * W.slopeSeries * W.interceptSeries +
        3 * MvPowerSeries.C W.a₆ * W.slopeSeries ^ 2 * W.interceptSeries) *
      MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
        MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1 from rfl)
  have hD := congrArg (MvPSeries.evalRingHom hE)
    (MvPowerSeries.mul_invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
      MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
      MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1
      (by simp [show MvPowerSeries.constantCoeff W.slopeSeries = 0 from
        W.constantCoeff_slopeSeries]))
  simp only [map_sub, map_neg, map_add, map_mul, map_pow, map_one, map_ofNat,
    MvPSeries.evalRingHom_apply, MvPSeries.eval_X, MvPSeries.eval_C, Sum.elim_inl,
    Sum.elim_inr] at hT hD
  simp only [show MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.slopeSeries =
      W.slopeEval t₁ t₂ from rfl,
    show MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.interceptSeries =
      W.interceptEval t₁ t₂ from rfl,
    show MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.thirdRootSeries =
      W.thirdRootEval t₁ t₂ from rfl] at hT hD
  set Λ := W.slopeEval t₁ t₂
  set N := W.interceptEval t₁ t₂
  set T := W.thirdRootEval t₁ t₂
  set d := MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
    (MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
      MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
      MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1)
  clear_value Λ N T d
  linear_combination (1 + W.a₂ * Λ + W.a₄ * Λ ^ 2 + W.a₆ * Λ ^ 3) * hT -
    (W.a₁ * Λ + W.a₂ * N + W.a₃ * Λ ^ 2 + 2 * W.a₄ * Λ * N + 3 * W.a₆ * Λ ^ 2 * N) * hD

/-- The evaluated on-line identity: `w(t̂₃) = λ̂·t̂₃ + ν̂`. -/
theorem wEval_thirdRootEval [IsDomain O] :
    W.wEval (W.thirdRootEval t₁ t₂) =
      W.slopeEval t₁ t₂ * W.thirdRootEval t₁ t₂ + W.interceptEval t₁ t₂ := by
  have h := congrArg (MvPSeries.evalRingHom (hasEval_pairElim h₁ h₂))
    W.subst_thirdRootSeries_wSeries
  simp only [map_add, map_mul, MvPSeries.evalRingHom_apply] at h
  rw [eval_pair_subst_single h₁ h₂ W.constantCoeff_thirdRootSeries] at h
  exact h

/-- The evaluated addition series is the formal inverse of the evaluated third root. -/
theorem addEval_eq : W.addEval t₁ t₂ = W.iotaEval (W.thirdRootEval t₁ t₂) := by
  have h := congrArg (MvPSeries.evalRingHom (hasEval_pairElim h₁ h₂))
    (show W.addSeries =
      MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.inverseSeries from rfl)
  simp only [MvPSeries.evalRingHom_apply] at h
  rw [eval_pair_subst_single h₁ h₂ W.constantCoeff_thirdRootSeries] at h
  exact h

omit h₁ h₂ in
/-- The addition series deviates from `t₁ + t₂` by `𝔪^(2j)` when both parameters lie in
`𝔪^j`: the formal group law is `t₁ + t₂` to first order. -/
theorem addEval_sub_add_mem {j : ℕ} (hj : j ≠ 0) (h₁ : t₁ ∈ maximalIdeal O ^ j)
    (h₂ : t₂ ∈ maximalIdeal O ^ j) :
    W.addEval t₁ t₂ - (t₁ + t₂) ∈ maximalIdeal O ^ (2 * j) := by
  have h₁' : t₁ ∈ maximalIdeal O := Ideal.pow_le_self hj h₁
  have h₂' : t₂ ∈ maximalIdeal O := Ideal.pow_le_self hj h₂
  have hE := hasEval_pairElim h₁' h₂'
  have heval : W.addEval t₁ t₂ - t₁ - t₂ =
      MvPSeries.eval (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂)
        (W.addSeries - MvPowerSeries.X (Sum.inl ()) - MvPowerSeries.X (Sum.inr ())) := by
    rw [MvPSeries.eval_sub hE, MvPSeries.eval_sub hE, MvPSeries.eval_X, MvPSeries.eval_X]
    rfl
  rw [show W.addEval t₁ t₂ - (t₁ + t₂) = W.addEval t₁ t₂ - t₁ - t₂ by ring, heval]
  exact MvPSeries.eval_mem_maximalIdeal_pow_mul hE (by rintro (u | u) <;> assumption) _
    (fun d hd ↦ W.coeff_addSeries_sub_of_degree_lt hd)

/-- The symmetric evaluated intercept identity: `ν̂ = w(t₂) - λ̂·t₂`. -/
theorem interceptEval_eq' :
    W.interceptEval t₁ t₂ = W.wEval t₂ - W.slopeEval t₁ t₂ * t₂ := by
  have h := congrArg (MvPSeries.evalRingHom (hasEval_pairElim h₁ h₂)) W.interceptSeries_eq
  simp only [map_sub, map_mul, MvPSeries.evalRingHom_apply, MvPSeries.eval_X] at h
  rw [eval_pair_rename h₁ h₂] at h
  simp only [Sum.elim_inr] at h
  exact h

omit h₁ h₂ in
@[simp]
theorem wEval_zero : W.wEval 0 = 0 := by
  rw [W.wEval_eq_cube_mul (zero_mem _)]
  ring

omit h₁ h₂ in
@[simp]
theorem iotaEval_zero : W.iotaEval 0 = 0 := by
  rw [W.iotaEval_eq (zero_mem _)]
  ring

omit h₂ in
/-- The evaluated formal inverse identity: `F(t, ι(t)) = 0`. -/
theorem addEval_iotaEval : W.addEval t₁ (W.iotaEval t₁) = 0 := by
  have hE : MvPowerSeries.HasEval fun _ : Unit ↦ t₁ := MvPSeries.hasEval_of_mem fun _ ↦ h₁
  have h := congrArg (MvPSeries.evalRingHom hE) W.subst_inverseSeries_addSeries
  rw [map_zero] at h
  simp only [MvPSeries.evalRingHom_apply] at h
  rw [MvPSeries.eval_subst hE (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (j | j)
    · exact MvPowerSeries.constantCoeff_X ()
    · exact W.constantCoeff_inverseSeries))] at h
  rw [show (fun s ↦ MvPSeries.eval (fun _ : Unit ↦ t₁)
      ((Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O))
        fun _ ↦ W.inverseSeries) s)) =
      (Sum.elim (fun _ ↦ t₁) fun _ ↦ W.iotaEval t₁) from funext fun s ↦ by
    rcases s with u | u
    · exact MvPSeries.eval_X _ _
    · rfl] at h
  exact h

omit h₁ h₂

/-- The formal inverse on the `𝔪`-points of the formal group of a Weierstrass curve. -/
noncomputable def negPoint (z : W.formalGroupLaw.Points) : W.formalGroupLaw.Points :=
  fun _ ↦ ⟨W.iotaEval (z ()), W.iotaEval_mem (z ()).2⟩

@[simp]
theorem negPoint_apply_coe (z : W.formalGroupLaw.Points) :
    ((W.negPoint z) () : O) = W.iotaEval (z ()) := rfl

/-- The coordinate of a sum of `𝔪`-points is the evaluated addition series. -/
theorem add_apply_coe_eq_addEval (z z' : W.formalGroupLaw.Points) :
    ((z + z') () : O) = W.addEval (z ()) (z' ()) := rfl

/-- The formal inverse is a right inverse for the addition of `𝔪`-points. -/
theorem add_negPoint (z : W.formalGroupLaw.Points) : z + W.negPoint z = 0 := by
  funext i
  refine Subtype.ext ?_
  rw [show ((z + W.negPoint z) i : O) = W.addEval (z ()) (W.iotaEval (z ())) from rfl,
    W.addEval_iotaEval (z ()).2]
  rfl

end WeierstrassCurve

/-!
### The kernel of reduction as the image of the `𝔪`-points of the formal group

Over `𝒪_v`, the parameter `t ∈ 𝔪` of a point of the formal group gives the affine point
`(t/w(t), -1/w(t))` of `E(K_v)`, with `v(x) = v(t)⁻²`, so `t ∈ 𝔪^(n+1)` corresponds to
the filtration step `E_{n+1}(K_v)`.
-/

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
  {t : v.adicCompletionIntegers K}

private lemma algebraMap_eq_coe (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x =
      (x : v.adicCompletion K) := rfl

private lemma valued_coe_le_one (x : v.adicCompletionIntegers K) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 := x.2

/-- The valuation of (the coercion of) a unit of `𝒪_v` is `1`. -/
private lemma valued_coe_isUnit {a : v.adicCompletionIntegers K} (ha : IsUnit a) :
    Valued.v ((a : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
  (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp ha

/-- Membership in the maximal ideal of `𝒪_v` is the valuation bound `exp (-1)`. -/
private lemma mem_maximalIdeal_iff {x : v.adicCompletionIntegers K} :
    x ∈ maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ exp (-1 : ℤ) := by
  have h := mem_maximalIdeal_pow_iff (K := K) (x := x) (n := 1)
  rwa [pow_one] at h

private lemma coe_iotaEval_eq {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.iotaEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      -((t : v.adicCompletion K) *
        ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.iotaEval_eq hm)
  push_cast at h
  exact h

private lemma coe_wEval_iotaEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.wEval (W₀.iotaEval t) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      -(((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_iotaEval hm)
  push_cast at h
  exact h

private lemma coe_uEval_mul_duEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.uEval t : v.adicCompletionIntegers K) : v.adicCompletion K) *
      ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.uEval_mul_duEval hm)
  push_cast at h
  exact h

section

include hW

private lemma coe_a₁ : ((W₀.a₁ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₁ := by
  rw [← hW, WeierstrassCurve.map_a₁, algebraMap_eq_coe]

private lemma coe_a₂ : ((W₀.a₂ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₂ := by
  rw [← hW, WeierstrassCurve.map_a₂, algebraMap_eq_coe]

private lemma coe_a₃ : ((W₀.a₃ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₃ := by
  rw [← hW, WeierstrassCurve.map_a₃, algebraMap_eq_coe]

private lemma coe_a₄ : ((W₀.a₄ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₄ := by
  rw [← hW, WeierstrassCurve.map_a₄, algebraMap_eq_coe]

private lemma coe_a₆ : ((W₀.a₆ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₆ := by
  rw [← hW, WeierstrassCurve.map_a₆, algebraMap_eq_coe]

/-- On an affine point of the kernel of reduction, `v(y)² = v(x)³`; in particular `y ≠ 0`,
and the parameter `-x/y` and the value `-1/y` lie in the maximal ideal. -/
private lemma valued_of_mem {x y : v.adicCompletion K} (hxy : W.Equation x y)
    (hx : exp (2 : ℤ) ≤ Valued.v x) :
    y ≠ 0 ∧ Valued.v (-x / y) ≤ exp (-1 : ℤ) ∧ Valued.v (-1 / y) ≤ exp (-1 : ℤ) := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := coe_a₁ hW ▸ valued_coe_le_one W₀.a₁
  have ha₂ : Valued.v W.a₂ ≤ 1 := coe_a₂ hW ▸ valued_coe_le_one W₀.a₂
  have ha₃ : Valued.v W.a₃ ≤ 1 := coe_a₃ hW ▸ valued_coe_le_one W₀.a₃
  have ha₄ : Valued.v W.a₄ ≤ 1 := coe_a₄ hW ▸ valued_coe_le_one W₀.a₄
  have ha₆ : Valued.v W.a₆ ≤ 1 := coe_a₆ hW ▸ valued_coe_le_one W₀.a₆
  set A := Valued.v x with hA
  have hA1 : (1 : ℤᵐ⁰) < A :=
    lt_of_lt_of_le (by rw [← exp_zero]; exact exp_lt_exp.mpr (by lia)) hx
  have hA0 : A ≠ 0 := (zero_lt_one.trans hA1).ne'
  set B := Valued.v y with hB
  have heq' : y ^ 2 + (W.a₁ * x * y + W.a₃ * y) =
      x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) := by
    linear_combination (W.equation_iff x y).mp hxy
  have hval := congrArg Valued.v heq'
  have hApow : A ^ 2 < A ^ 3 := pow_lt_pow_right₀ hA1 (by lia)
  -- the right-hand side has valuation `A³`
  have hRHS : Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = A ^ 3 := by
    have h1 : Valued.v (W.a₂ * x ^ 2) ≤ A ^ 2 := by
      rw [map_mul, map_pow]
      exact (mul_le_mul' ha₂ le_rfl).trans_eq (one_mul _)
    have h2 : Valued.v (W.a₄ * x) ≤ A ^ 2 := by
      rw [map_mul]
      exact ((mul_le_mul' ha₄ le_rfl).trans_eq (one_mul _)).trans
        (le_self_pow hA1.le (by lia))
    have h3 : Valued.v W.a₆ ≤ A ^ 2 := ha₆.trans (hA1.le.trans (le_self_pow hA1.le (by lia)))
    have hlow : Valued.v (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) < A ^ 3 :=
      lt_of_le_of_lt ((Valued.v.map_add _ _).trans
        (max_le h1 ((Valued.v.map_add _ _).trans (max_le h2 h3)))) hApow
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hlow), map_pow]
  -- `B ≤ A` is impossible: the left-hand side would be too small
  have hBA : A < B := by
    by_contra hle
    push Not at hle
    have h1 : Valued.v (y ^ 2) ≤ A ^ 2 := by
      rw [map_pow]
      exact pow_le_pow_left' hle 2
    have h2 : Valued.v (W.a₁ * x * y) ≤ A ^ 2 := by
      rw [map_mul, map_mul]
      calc Valued.v W.a₁ * A * B ≤ 1 * A * A := mul_le_mul' (mul_le_mul' ha₁ le_rfl) hle
        _ = A ^ 2 := by rw [one_mul, sq]
    have h3 : Valued.v (W.a₃ * y) ≤ A ^ 2 := by
      rw [map_mul]
      exact ((mul_le_mul' ha₃ hle).trans_eq (one_mul _)).trans (le_self_pow hA1.le (by lia))
    have hLHS_le : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) ≤ A ^ 2 :=
      (Valued.v.map_add _ _).trans
        (max_le h1 ((Valued.v.map_add _ _).trans (max_le h2 h3)))
    rw [hval, hRHS] at hLHS_le
    exact absurd hLHS_le (not_le.mpr hApow)
  have hB1 : (1 : ℤᵐ⁰) < B := hA1.trans hBA
  have hB0 : B ≠ 0 := (zero_lt_one.trans hB1).ne'
  have hy0 : y ≠ 0 := by
    intro h
    rw [hB, h, map_zero] at hBA
    simp at hBA
  -- the left-hand side has valuation `B²`, so `B² = A³`
  have hBA3 : B ^ 2 = A ^ 3 := by
    have h2 : Valued.v (W.a₁ * x * y) < B ^ 2 := by
      rw [map_mul, map_mul]
      calc Valued.v W.a₁ * A * B ≤ 1 * A * B := mul_le_mul' (mul_le_mul' ha₁ le_rfl) le_rfl
        _ = A * B := by rw [one_mul]
        _ < B * B := mul_lt_mul_of_pos_right hBA (zero_lt_one.trans hB1)
        _ = B ^ 2 := (sq B).symm
    have h3 : Valued.v (W.a₃ * y) < B ^ 2 := by
      rw [map_mul]
      calc Valued.v W.a₃ * B ≤ 1 * B := mul_le_mul' ha₃ le_rfl
        _ = B := one_mul B
        _ < B ^ 2 := by
          calc B = B ^ 1 := (pow_one B).symm
            _ < B ^ 2 := pow_lt_pow_right₀ hB1 (by lia)
    have hsum : Valued.v (W.a₁ * x * y + W.a₃ * y) < B ^ 2 :=
      lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt h2 h3)
    have hLHS : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = B ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hsum), map_pow]
    rw [← hLHS, hval, hRHS]
  -- pass to exponents
  obtain ⟨a, ha⟩ : ∃ a : ℤ, A = exp a := ⟨log A, (exp_log hA0).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, B = exp b := ⟨log B, (exp_log hB0).symm⟩
  have h2a : (2 : ℤ) ≤ a := by rwa [ha, exp_le_exp] at hx
  have h23 : 2 * b = 3 * a := by
    have h := hBA3
    rw [ha, hb, ← exp_nsmul, ← exp_nsmul, exp_inj] at h
    push_cast [nsmul_eq_mul] at h
    exact h
  refine ⟨hy0, ?_, ?_⟩
  · rw [map_div₀, Valuation.map_neg, ← hA, ← hB, ha, hb, ← exp_sub, exp_le_exp]
    lia
  · rw [map_div₀, Valuation.map_neg, map_one, ← hB, hb, ← exp_zero, ← exp_sub, exp_le_exp]
    lia

/-- An affine point outside the kernel of reduction has integral coordinates: the only
poles on a Weierstrass curve with integral coefficients have even order at `x`. -/
private lemma integral_of_not_mem {x y : v.adicCompletion K} (hxy : W.Equation x y)
    (hx : ¬ exp (2 : ℤ) ≤ Valued.v x) :
    Valued.v x ≤ 1 ∧ Valued.v y ≤ 1 := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := coe_a₁ hW ▸ valued_coe_le_one W₀.a₁
  have ha₂ : Valued.v W.a₂ ≤ 1 := coe_a₂ hW ▸ valued_coe_le_one W₀.a₂
  have ha₃ : Valued.v W.a₃ ≤ 1 := coe_a₃ hW ▸ valued_coe_le_one W₀.a₃
  have ha₄ : Valued.v W.a₄ ≤ 1 := coe_a₄ hW ▸ valued_coe_le_one W₀.a₄
  have ha₆ : Valued.v W.a₆ ≤ 1 := coe_a₆ hW ▸ valued_coe_le_one W₀.a₆
  have heq' : y ^ 2 + (W.a₁ * x * y + W.a₃ * y) =
      x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) := by
    linear_combination (W.equation_iff x y).mp hxy
  have hval := congrArg Valued.v heq'
  have hcase : (Valued.v x) ≤ 1 ∨ (Valued.v x) = exp 1 := by
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact .inl (h0 ▸ zero_le)
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, (Valued.v x) = exp a := ⟨log (Valued.v x), (exp_log h0).symm⟩
      have ha1 : a ≤ 1 := by
        by_contra hlt
        exact hx (ha ▸ exp_le_exp.mpr (by lia))
      rcases eq_or_lt_of_le ha1 with h1 | h1
      · exact .inr (by rw [ha, h1])
      · exact .inl (by rw [ha, ← exp_zero, exp_le_exp]; lia)
  rcases hcase with hA1 | hA1
  · -- `x` integral forces `y` integral
    refine ⟨hA1, ?_⟩
    by_contra hB1
    push Not at hB1
    have hB0 : (Valued.v y) ≠ 0 := fun h ↦ by simp [h] at hB1
    have h1 : Valued.v (W.a₁ * x * y + W.a₃ * y) < (Valued.v y) ^ 2 := by
      refine lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul, map_mul]
        calc Valued.v W.a₁ * Valued.v x * Valued.v y ≤ 1 * 1 * Valued.v y :=
            mul_le_mul' (mul_le_mul' ha₁ hA1) le_rfl
          _ = 1 * (Valued.v y) := by rw [one_mul]
          _ < (Valued.v y) * (Valued.v y) := mul_lt_mul_of_pos_right hB1 (zero_lt_iff.mpr hB0)
          _ = (Valued.v y) ^ 2 := (sq (Valued.v y)).symm
      · rw [map_mul]
        calc Valued.v W.a₃ * (Valued.v y) ≤ 1 * (Valued.v y) := mul_le_mul' ha₃ le_rfl
          _ = (Valued.v y) ^ 1 := by rw [one_mul, pow_one]
          _ < (Valued.v y) ^ 2 := pow_lt_pow_right₀ hB1 (by lia)
    have hLHS : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = (Valued.v y) ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact h1), map_pow]
    have hRHS : Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) ≤ 1 := by
      refine le_trans (Valued.v.map_add _ _) (max_le ?_ (le_trans (Valued.v.map_add _ _)
        (max_le ?_ (le_trans (Valued.v.map_add _ _) (max_le ?_ ha₆)))))
      · rw [map_pow]
        exact pow_le_one' hA1 3
      · rw [map_mul, map_pow]
        exact mul_le_one' ha₂ (pow_le_one' hA1 2)
      · rw [map_mul]
        exact mul_le_one' ha₄ hA1
    rw [← hval, hLHS] at hRHS
    exact absurd hRHS (not_le.mpr (one_lt_pow₀ hB1 (by lia)))
  · -- `v(x) = exp 1` is impossible
    exfalso
    have hRHS : Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = exp (3 : ℤ) := by
      have hlow : Valued.v (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) < exp (3 : ℤ) := by
        refine lt_of_le_of_lt (le_trans (Valued.v.map_add _ _) (max_le ?_
          (le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)))) (?_ : exp (2 : ℤ) < _)
        · rw [map_mul, map_pow, hA1]
          calc Valued.v W.a₂ * exp 1 ^ 2 ≤ 1 * exp 1 ^ 2 := mul_le_mul' ha₂ le_rfl
            _ = exp (2 : ℤ) := by rw [one_mul, ← exp_nsmul, nsmul_eq_mul]; norm_num
        · rw [map_mul, hA1]
          calc Valued.v W.a₄ * exp 1 ≤ 1 * exp 1 := mul_le_mul' ha₄ le_rfl
            _ ≤ exp (2 : ℤ) := by rw [one_mul, exp_le_exp]; lia
        · exact ha₆.trans (by rw [← exp_zero, exp_le_exp]; lia)
        · rw [exp_lt_exp]
          lia
      rw [show x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) = x ^ 3 +
        (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) from rfl,
        Valuation.map_add_eq_of_lt_left _ (by
          rw [map_pow, hA1, ← exp_nsmul, nsmul_eq_mul]
          norm_num at hlow ⊢
          exact hlow),
        map_pow, hA1, ← exp_nsmul, nsmul_eq_mul]
      norm_num
    rcases le_or_gt (Valued.v y) (exp 1) with hB1 | hB1
    · have hLHS_le : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) ≤ exp (2 : ℤ) := by
        refine le_trans (Valued.v.map_add _ _) (max_le ?_ (le_trans (Valued.v.map_add _ _)
          (max_le ?_ ?_)))
        · rw [map_pow]
          calc (Valued.v y) ^ 2 ≤ exp 1 ^ 2 := pow_le_pow_left' hB1 2
            _ = exp (2 : ℤ) := by rw [← exp_nsmul, nsmul_eq_mul]; norm_num
        · rw [map_mul, map_mul, hA1]
          calc Valued.v W.a₁ * exp 1 * (Valued.v y) ≤ 1 * exp 1 * exp 1 :=
              mul_le_mul' (mul_le_mul' ha₁ le_rfl) hB1
            _ = exp (2 : ℤ) := by rw [one_mul, ← exp_add]; norm_num
        · rw [map_mul]
          calc Valued.v W.a₃ * (Valued.v y) ≤ 1 * exp 1 := mul_le_mul' ha₃ hB1
            _ ≤ exp (2 : ℤ) := by rw [one_mul, exp_le_exp]; lia
      rw [hval, hRHS] at hLHS_le
      rw [exp_le_exp] at hLHS_le
      lia
    · have hB0 : (Valued.v y) ≠ 0 := fun h ↦ by
        rw [h] at hB1
        exact absurd hB1 (by simp)
      have h1 : Valued.v (W.a₁ * x * y + W.a₃ * y) < (Valued.v y) ^ 2 := by
        refine lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt ?_ ?_)
        · rw [map_mul, map_mul, hA1]
          calc Valued.v W.a₁ * exp 1 * (Valued.v y) ≤ 1 * exp 1 * (Valued.v y) :=
              mul_le_mul' (mul_le_mul' ha₁ le_rfl) le_rfl
            _ = exp 1 * (Valued.v y) := by rw [one_mul]
            _ < (Valued.v y) * (Valued.v y) := mul_lt_mul_of_pos_right hB1 (zero_lt_iff.mpr hB0)
            _ = (Valued.v y) ^ 2 := (sq (Valued.v y)).symm
        · rw [map_mul]
          calc Valued.v W.a₃ * (Valued.v y) ≤ 1 * (Valued.v y) := mul_le_mul' ha₃ le_rfl
            _ = (Valued.v y) ^ 1 := by rw [one_mul, pow_one]
            _ < (Valued.v y) ^ 2 := pow_lt_pow_right₀
              (lt_trans (by rw [← exp_zero, exp_lt_exp]; lia) hB1) (by lia)
      have hLHS : Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = (Valued.v y) ^ 2 := by
        rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact h1), map_pow]
      have hB3 : (Valued.v y) ^ 2 = exp (3 : ℤ) := by rw [← hLHS, hval, hRHS]
      obtain ⟨b, hb⟩ : ∃ b : ℤ, (Valued.v y) = exp b := ⟨log (Valued.v y), (exp_log hB0).symm⟩
      rw [hb, ← exp_nsmul, exp_inj, nsmul_eq_mul] at hB3
      push_cast at hB3
      lia

/-- The coerced Weierstrass fixed-point equation for the value of `w`. -/
private lemma coe_wEval_eq {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (t : v.adicCompletion K) ^ 3 +
        W.a₁ * t * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) +
        W.a₂ * (t : v.adicCompletion K) ^ 2 *
          ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) +
        W.a₃ * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 +
        W.a₄ * t * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 +
        W.a₆ * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 3 := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_eq hm)
  rw [wPoly] at h
  push_cast at h
  rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW] at h
  exact h

/-- The coerced form of the evaluated `u`-series. -/
private lemma coe_uEval_eq {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.uEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      1 - W.a₁ * t - W.a₃ *
        ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.uEval_eq hm)
  push_cast at h
  rw [coe_a₁ hW, coe_a₃ hW] at h
  exact h

end

/-- The formal inverse preserves the valuation of the parameter. -/
private lemma valued_iotaEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((W₀.iotaEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      Valued.v (t : v.adicCompletion K) := by
  rw [coe_iotaEval_eq hm, Valuation.map_neg, map_mul,
    valued_coe_isUnit (W₀.isUnit_duEval hm), mul_one]

private lemma ne_of_valued_lt {a b : v.adicCompletionIntegers K}
    (h : Valued.v (a : v.adicCompletion K) < Valued.v (b : v.adicCompletion K)) : a ≠ b :=
  fun he ↦ h.ne (by rw [he])

/-- A parameter of valuation smaller than that of `2` is not its own formal inverse. -/
private lemma ne_iotaEval_self {s : v.adicCompletionIntegers K}
    (hsm : s ∈ maximalIdeal (v.adicCompletionIntegers K)) (hs0 : s ≠ 0)
    (h2 : Valued.v (s : v.adicCompletion K) <
      Valued.v ((2 : v.adicCompletionIntegers K) : v.adicCompletion K)) :
    s ≠ W₀.iotaEval s := by
  intro h
  have hd := W₀.iotaEval_eq hsm
  rw [← h] at hd
  have hdu : W₀.duEval s = -1 := by
    have hkey : s * (1 + W₀.duEval s) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact absurd h' hs0
    · linear_combination h'
  have h2eq : W₀.a₁ * s + W₀.a₃ * W₀.wEval s = 2 := by
    have hu1 : W₀.uEval s = -1 := by
      have h' := W₀.uEval_mul_duEval hsm
      rw [hdu] at h'
      linear_combination -h'
    have h' := W₀.uEval_eq hsm
    rw [hu1] at h'
    linear_combination h'
  have hws_le : Valued.v ((W₀.wEval s : v.adicCompletionIntegers K) : v.adicCompletion K) ≤
      Valued.v (s : v.adicCompletion K) := by
    have h' := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
      (W₀.wEval_eq_cube_mul hsm)
    push_cast at h'
    rw [h', map_mul, map_pow, valued_coe_isUnit (W₀.isUnit_vEval hsm), mul_one]
    calc Valued.v (s : v.adicCompletion K) ^ 3
        = Valued.v (s : v.adicCompletion K) * Valued.v (s : v.adicCompletion K) ^ 2 :=
          pow_succ' _ 2
      _ ≤ Valued.v (s : v.adicCompletion K) * 1 :=
          mul_le_mul' le_rfl (pow_le_one' (valued_coe_le_one s) 2)
      _ = Valued.v (s : v.adicCompletion K) := mul_one _
  have hcoe2 := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K)) h2eq
  push_cast at hcoe2
  have hval2 : Valued.v ((2 : v.adicCompletionIntegers K) : v.adicCompletion K) ≤
      Valued.v (s : v.adicCompletion K) := by
    rw [← hcoe2]
    refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)
    · rw [map_mul]
      exact (mul_le_mul' (valued_coe_le_one _) le_rfl).trans_eq (one_mul _)
    · rw [map_mul]
      calc Valued.v (W₀.a₃ : v.adicCompletion K) *
            Valued.v ((W₀.wEval s : v.adicCompletionIntegers K) : v.adicCompletion K)
          ≤ 1 * Valued.v (s : v.adicCompletion K) :=
            mul_le_mul' (valued_coe_le_one _) hws_le
        _ = Valued.v (s : v.adicCompletion K) := one_mul _
  exact absurd (lt_of_le_of_lt hval2 h2) (lt_irrefl _)

/-- An auxiliary parameter in `𝔪` avoiding a given nonzero parameter, its formal inverse,
and its own formal inverse: any high enough power of a uniformizer works. -/
private lemma exists_aux_param [CharZero K] {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (h0 : t ≠ 0) :
    ∃ s : v.adicCompletionIntegers K, s ∈ maximalIdeal (v.adicCompletionIntegers K) ∧
      s ≠ 0 ∧ s ≠ t ∧ s ≠ W₀.iotaEval t ∧ s ≠ W₀.iotaEval s := by
  have hchar : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have h20 : ((2 : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    exact_mod_cast (two_ne_zero : (2 : v.adicCompletion K) ≠ 0)
  -- an auxiliary parameter `s = π^k` of very small valuation
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπv : Valued.v ((π : v.adicCompletionIntegers K) : v.adicCompletion K) = exp (-1) := by
    have h := v.valued_irreducible_adicCompletionIntegers hπ
    rwa [algebraMap_eq_coe] at h
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact h0
  obtain ⟨m, htv⟩ : ∃ m : ℤ, Valued.v (t :
      v.adicCompletion K) = exp m := ⟨_, (exp_log ht0').symm⟩
  have hm1 : m ≤ -1 := by
    have h := mem_maximalIdeal_iff.mp hm
    rwa [htv, exp_le_exp] at h
  obtain ⟨c, h2v⟩ : ∃ c : ℤ, Valued.v ((2 : v.adicCompletionIntegers K) :
      v.adicCompletion K) = exp c := ⟨_, (exp_log (by simp [h20])).symm⟩
  have hc0 : c ≤ 0 := by
    have h := valued_coe_le_one (2 : v.adicCompletionIntegers K)
    rwa [h2v, ← exp_zero, exp_le_exp] at h
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, (k : ℤ) = max (-m) (-c) + 1 :=
    ⟨(max (-m) (-c) + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨s, hsdef⟩ : ∃ s : v.adicCompletionIntegers K, s = π ^ k := ⟨_, rfl⟩
  have hsv : Valued.v ((s : v.adicCompletionIntegers K) : v.adicCompletion K) =
      exp (-(k : ℤ)) := by
    rw [hsdef]
    push_cast
    rw [map_pow, hπv, ← exp_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have hks : -(k : ℤ) < m := by omega
  have hkc : -(k : ℤ) < c := by omega
  have hsm : s ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    mem_maximalIdeal_iff.mpr (by rw [hsv, exp_le_exp]; lia)
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    exact pow_ne_zero _ hπ.ne_zero
  refine ⟨s, hsm, hs0, ?_, ?_, ?_⟩
  · exact ne_of_valued_lt (by rw [hsv, htv, exp_lt_exp]; exact hks)
  · refine ne_of_valued_lt ?_
    rw [valued_iotaEval hm, hsv, htv, exp_lt_exp]
    exact hks
  · exact ne_iotaEval_self hsm hs0 (by rw [hsv, h2v, exp_lt_exp]; exact hkc)

/-- The valuation of the `x`-coordinate `t/w(t)` is `v(t)⁻²`. -/
theorem valued_formalPoint_x
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (ht0 : t ≠ 0) :
    Valued.v ((t : v.adicCompletion K) / (W₀.wEval t : v.adicCompletion K)) =
      (Valued.v (t : v.adicCompletion K))⁻¹ ^ 2 := by
  have hvE : Valued.v ((W₀.vEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
    valued_coe_isUnit (W₀.isUnit_vEval ht)
  have hw : ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (t : v.adicCompletion K) ^ 3 * ((W₀.vEval t : v.adicCompletionIntegers K) :
        v.adicCompletion K) := by
    rw [W₀.wEval_eq_cube_mul ht]
    push_cast
    rfl
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact ht0
  rw [map_div₀, hw, map_mul, map_pow, hvE, mul_one, inv_pow, pow_succ',
    div_mul_eq_div_div, div_self ht0', one_div]

/-- The parameter of a sum of `𝔪`-points lies in every `𝔪`-power containing both
parameters (evaluation of the addition series preserves the level). -/
private lemma add_param_mem_pow {z z' : W₀.formalGroupLaw.Points} {n : ℕ}
    (hz : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1))
    (hz' : (z' () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1)) :
    ((z + z') () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) := by
  rw [W₀.add_apply_coe_eq_addEval]
  refine MvPSeries.eval_mem_maximalIdeal_pow (hasEval_pairElim (z ()).2 (z' ()).2)
    (by rintro (j | j) <;> assumption) W₀.addSeries ?_
  rw [W₀.constantCoeff_addSeries]
  exact zero_mem _

/-- For a nonzero parameter `t ∈ 𝔪`, membership in `𝔪^(n+1)` is the pole condition on
the `x`-coordinate of the associated point. -/
private lemma param_pow_iff {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (h0 : t ≠ 0) (n : ℕ) :
    t ∈ maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
      exp (2 * (n + 1) : ℤ) ≤ Valued.v ((t : v.adicCompletion K) /
        ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
  rw [valued_formalPoint_x hm h0, mem_maximalIdeal_pow_iff]
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact h0
  obtain ⟨m, hmv⟩ : ∃ m : ℤ, Valued.v (t : v.adicCompletion K) = exp m :=
    ⟨_, (exp_log ht0').symm⟩
  rw [hmv, ← exp_neg, ← exp_nsmul, exp_le_exp, exp_le_exp, nsmul_eq_mul]
  push_cast
  constructor <;> intro h <;> lia

/-- The parameter map modulo `𝔪^(k+2)` is additive on parameters in `𝔪^(k+1)`. -/
private lemma mk_add_param {k : ℕ} {z z' : W₀.formalGroupLaw.Points}
    (hz : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1))
    (hz' : (z' () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1)) :
    Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
        (((z + z') ()) : v.adicCompletionIntegers K) =
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)) (z ()) +
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)) (z' ()) := by
  rw [← map_add (Ideal.Quotient.mk _)]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [W₀.add_apply_coe_eq_addEval]
  refine SetLike.le_def.mp
    (Ideal.pow_le_pow_right (m := k + 2) (n := 2 * (k + 1)) (by lia)) ?_
  exact W₀.addEval_sub_add_mem (Nat.succ_ne_zero k) hz hz'

private lemma finite_quotient_pow [Finite (R ⧸ v.asIdeal)] (m : ℕ) :
    Finite (v.adicCompletionIntegers K ⧸
      (maximalIdeal (v.adicCompletionIntegers K) ^ m)) := by
  have hfin : Finite (v.adicCompletionIntegers K ⧸
      maximalIdeal (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m

/-- Closed balls (with nonzero radius) in the completion are open. -/
private lemma isOpen_le_ball (a : v.adicCompletion K) (m : ℤ) :
    IsOpen {b : v.adicCompletion K | Valued.v (b - a) ≤ exp m} := by
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp m)
  have hr0 : Valued.v.restrict z ≠ 0 := fun h0 ↦ exp_ne_zero (hz ▸ (by
    rw [← Valuation.embedding_restrict, h0, map_zero] : Valued.v z = 0))
  have hset : {b : v.adicCompletion K | Valued.v (b - a) ≤ exp m} = (fun b ↦ b - a) ⁻¹'
      {y | Valued.v.restrict y ≤ Valued.v.restrict z} := by
    ext b
    rw [Set.mem_preimage, Set.mem_setOf, Set.mem_setOf,
      Valuation.restrict_le_iff_le_embedding, Valuation.embedding_restrict, hz]
  rw [hset]
  exact (Valued.isOpen_closedBall _ hr0).preimage (continuous_id.sub continuous_const)

/-- The valuation ring inside the completion is a compact subset: it is closed, and totally
bounded because the quotients `𝒪_v/𝔪^n` are finite. -/
private lemma isCompact_integerSet [Finite (R ⧸ v.asIdeal)] :
    IsCompact {a : v.adicCompletion K | Valued.v a ≤ 1} := by
  rw [isCompact_iff_totallyBounded_isComplete]
  constructor
  · -- totally bounded: cover by cosets of `𝔪^n`
    rw [(Valued.hasBasis_uniformity _ _).totallyBounded_iff]
    intro γ _
    obtain ⟨m, hm⟩ : ∃ m : ℤ,
        exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
      obtain ⟨a, ha⟩ :=
        WithZero.ne_zero_iff_exists.mp (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
      refine ⟨Multiplicative.toAdd a - 1, ?_⟩
      rw [← ha, show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl]
      exact exp_lt_exp.mpr (by lia)
    set n : ℕ := (-m).toNat with hn
    have hfq : Finite (v.adicCompletionIntegers K ⧸
        (maximalIdeal (v.adicCompletionIntegers K) ^ n)) := finite_quotient_pow n
    refine ⟨Set.range (fun c : v.adicCompletionIntegers K ⧸
        (maximalIdeal (v.adicCompletionIntegers K) ^ n) ↦
        ((Quotient.out c : v.adicCompletionIntegers K) : v.adicCompletion K)),
      Set.finite_range _, fun x hx ↦ ?_⟩
    have hxm : Valued.v x ≤ 1 := hx
    obtain ⟨c, hc⟩ : ∃ c, c = Ideal.Quotient.mk
        (maximalIdeal (v.adicCompletionIntegers K) ^ n) ⟨x, hxm⟩ := ⟨_, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨((Quotient.out c : v.adicCompletionIntegers K) :
      v.adicCompletion K), Set.mem_range_self c, ?_⟩
    have hsub : (⟨x, hxm⟩ - Quotient.out c : v.adicCompletionIntegers K) ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ n := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hc]
      exact (Quotient.out_eq c).symm
    have hval : Valued.v (((Quotient.out c : v.adicCompletionIntegers K) :
        v.adicCompletion K) - x) ≤ exp (-(n : ℤ)) := by
      have h1 := (v.mem_maximalIdeal_pow_iff (K := K)).mp hsub
      rw [show ((⟨x, hxm⟩ - Quotient.out c : v.adicCompletionIntegers K) :
        v.adicCompletion K) = x - ((Quotient.out c : v.adicCompletionIntegers K) :
          v.adicCompletion K) from rfl] at h1
      rwa [← Valuation.map_sub_swap] at h1
    refine Set.mem_setOf.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
      (lt_of_le_of_lt hval ?_))
    refine lt_of_le_of_lt (exp_le_exp.mpr ?_) hm
    rw [hn]
    lia
  · -- complete: the valuation ring is closed in the complete field
    have hset : {a : v.adicCompletion K | Valued.v a ≤ 1} =
        (((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring :
          ValuationSubring (v.adicCompletion K)) : Set (v.adicCompletion K)) := rfl
    rw [hset]
    exact (Valued.isClosed_valuationSubring _).isComplete


variable [W.IsElliptic]

include hW in
/-- The parametrized point of the kernel of reduction attached to a parameter `t ∈ 𝔪`,
`t ≠ 0`, is nonsingular. -/
theorem formalPoint_nonsingular
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (ht0 : t ≠ 0) :
    W.Nonsingular ((t : v.adicCompletion K) / (W₀.wEval t : v.adicCompletion K))
      (-1 / (W₀.wEval t : v.adicCompletion K)) := by
  refine W.chord_point_nonsingular (coe_wEval_eq hW ht) ?_ W.isUnit_Δ.ne_zero
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact W₀.wEval_ne_zero ht ht0

variable [DecidableEq (v.adicCompletion K)]

/-- The point of the kernel of reduction attached to an `𝔪`-point of the formal group of
the integral model `W₀`: the parameter `t` gives the affine point `(t/w(t), -1/w(t))`,
and `t = 0` gives the point at infinity. -/
noncomputable def formalPoint (z : W₀.formalGroupLaw.Points) : W.Point :=
  if h0 : (z () : v.adicCompletionIntegers K) = 0 then 0
  else .some _ _ (formalPoint_nonsingular hW (z ()).2 h0)

@[simp]
lemma formalPoint_of_param_eq_zero {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) = 0) : formalPoint hW z = 0 :=
  dif_pos h0

lemma formalPoint_of_param_ne_zero {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0) :
    formalPoint hW z = .some _ _ (formalPoint_nonsingular hW (z ()).2 h0) :=
  dif_neg h0

/-- The parametrization of the kernel of reduction is injective. -/
theorem formalPoint_injective : Function.Injective (formalPoint hW) := by
  intro z z' h
  have key : (z () : v.adicCompletionIntegers K) = z' () := by
    rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0 <;>
      rcases eq_or_ne (z' () : v.adicCompletionIntegers K) 0 with h0' | h0'
    · rw [h0, h0']
    · rw [formalPoint_of_param_eq_zero hW h0, formalPoint_of_param_ne_zero hW h0'] at h
      exact absurd h.symm (by simp)
    · rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_eq_zero hW h0'] at h
      exact absurd h (by simp)
    · rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_ne_zero hW h0'] at h
      simp only [Point.some.injEq] at h
      obtain ⟨hX, hY⟩ := h
      have hw0 : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := by
        simp only [ne_eq, ZeroMemClass.coe_eq_zero]
        exact W₀.wEval_ne_zero (z ()).2 h0
      have hw0' : ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := by
        simp only [ne_eq, ZeroMemClass.coe_eq_zero]
        exact W₀.wEval_ne_zero (z' ()).2 h0'
      have hw : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
          ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        field_simp at hY
        exact (neg_injective hY).symm
      rw [hw, div_eq_div_iff hw0' hw0'] at hX
      exact_mod_cast mul_right_cancel₀ hw0' hX
  funext i
  exact Subtype.ext key

/-- Every affine point with a pole of order at least `2` at `x` comes from a parameter
in `𝔪`. -/
theorem exists_formalPoint_eq_some {x y : v.adicCompletion K} (h : W.Nonsingular x y)
    (hx : exp (2 : ℤ) ≤ Valued.v x) :
    ∃ z : W₀.formalGroupLaw.Points, formalPoint hW z = .some x y h := by
  obtain ⟨hy0, hs, hr⟩ := valued_of_mem hW h.left hx
  have hexp1 : (exp (-1 : ℤ) : ℤᵐ⁰) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]
    lia
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    simp at hx
  set t : v.adicCompletionIntegers K :=
    ⟨-x / y, by rw [mem_adicCompletionIntegers]; exact hs.trans hexp1⟩ with htdef
  set r : v.adicCompletionIntegers K :=
    ⟨-1 / y, by rw [mem_adicCompletionIntegers]; exact hr.trans hexp1⟩ with hrdef
  have htm : t ∈ maximalIdeal (v.adicCompletionIntegers K) := mem_maximalIdeal_iff.mpr hs
  have hrm : r ∈ maximalIdeal (v.adicCompletionIntegers K) := mem_maximalIdeal_iff.mpr hr
  have ht0 : t ≠ 0 := by
    intro hteq
    have h0 : (-x / y : v.adicCompletion K) = 0 := congrArg Subtype.val hteq
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    exact h0.elim hx0 hy0
  -- `-1/y` satisfies the Weierstrass fixed-point equation at the parameter `-x/y`
  have hfixK : (-1 / y : v.adicCompletion K) =
      (-x / y) ^ 3 + W.a₁ * (-x / y) * (-1 / y) + W.a₂ * (-x / y) ^ 2 * (-1 / y) +
        W.a₃ * (-1 / y) ^ 2 + W.a₄ * (-x / y) * (-1 / y) ^ 2 + W.a₆ * (-1 / y) ^ 3 := by
    have heq := (W.equation_iff x y).mp h.left
    field_simp
    linear_combination -heq
  have hfixO : r = W₀.wPoly t r := by
    refine Subtype.coe_injective ?_
    rw [wPoly]
    push_cast
    rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW]
    exact hfixK
  have huniq : W₀.wEval t = r :=
    W₀.eq_of_wPoly_fixed htm (W₀.wEval_mem htm) hrm (W₀.wEval_eq htm) hfixO
  refine ⟨fun _ ↦ ⟨t, htm⟩, ?_⟩
  rw [formalPoint_of_param_ne_zero hW ht0]
  simp only [Point.some.injEq]
  have hrcoe : ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = -1 / y := by
    rw [huniq]
  constructor
  · rw [hrcoe]
    show (-x / y) / (-1 / y) = x
    field_simp
  · rw [hrcoe]
    show -1 / (-1 / y) = y
    field_simp

theorem formalPoint_eq_zero_iff {z : W₀.formalGroupLaw.Points} :
    formalPoint hW z = 0 ↔ (z () : v.adicCompletionIntegers K) = 0 := by
  refine ⟨fun h ↦ ?_, formalPoint_of_param_eq_zero hW⟩
  by_contra h0
  rw [formalPoint_of_param_ne_zero hW h0] at h
  exact absurd h (by simp)

include hW in
/-- The parametrization intertwines the formal inverse with negation of points. -/
theorem formalPoint_negPoint (z : W₀.formalGroupLaw.Points) :
    formalPoint hW (W₀.negPoint z) = -formalPoint hW z := by
  rcases eq_or_ne ((z ()) : v.adicCompletionIntegers K) 0 with h0 | h0
  · rw [formalPoint_of_param_eq_zero hW h0, formalPoint_of_param_eq_zero hW
      (by rw [W₀.negPoint_apply_coe, h0, W₀.iotaEval_zero]), neg_zero]
  · have hm := (z ()).2
    have hι0 : W₀.iotaEval (z () : v.adicCompletionIntegers K) ≠ 0 := by
      rw [W₀.iotaEval_eq hm]
      exact neg_ne_zero.mpr (mul_ne_zero h0 (W₀.isUnit_duEval hm).ne_zero)
    rw [formalPoint_of_param_ne_zero hW h0,
      formalPoint_of_param_ne_zero hW (by rw [W₀.negPoint_apply_coe]; exact hι0),
      Point.neg_some]
    simp only [Point.some.injEq, W₀.negPoint_apply_coe]
    have hWT0 : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
      simp only [ne_eq, ZeroMemClass.coe_eq_zero]
      exact W₀.wEval_ne_zero hm h0
    have hDU0 : ((W₀.duEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
      simp only [ne_eq, ZeroMemClass.coe_eq_zero]
      exact (W₀.isUnit_duEval hm).ne_zero
    constructor
    · rw [coe_iotaEval_eq hm, coe_wEval_iotaEval hm]
      field_simp
    · rw [coe_wEval_iotaEval hm, Affine.negY]
      field_simp
      linear_combination -coe_uEval_mul_duEval hm +
        ((W₀.duEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) *
          coe_uEval_eq hW hm

include hW in
/-- The chord addition at the level of parameters: for `t₁, t₂ ∈ 𝔪` nonzero with distinct
`x`-coordinates and nonvanishing third root `T`, the sum of the parametrized points is the
point with parameter `ι̂(T)`. -/
private lemma paramPoint_add {t₁ t₂ : v.adicCompletionIntegers K}
    (hm : t₁ ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hm' : t₂ ∈ maximalIdeal (v.adicCompletionIntegers K))
    (h0 : t₁ ≠ 0) (h0' : t₂ ≠ 0)
    (hx : ((t₁ : v.adicCompletion K)) *
        ((W₀.wEval t₂ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠
      ((t₂ : v.adicCompletion K)) *
        ((W₀.wEval t₁ : v.adicCompletionIntegers K) : v.adicCompletion K))
    (hT0 : W₀.thirdRootEval t₁ t₂ ≠ 0)
    (hιm : W₀.iotaEval (W₀.thirdRootEval t₁ t₂) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hι0 : W₀.iotaEval (W₀.thirdRootEval t₁ t₂) ≠ 0) :
    (.some _ _ (formalPoint_nonsingular hW hm h0) : W.Point) +
        .some _ _ (formalPoint_nonsingular hW hm' h0') =
      .some _ _ (formalPoint_nonsingular hW hιm hι0) := by
  have hTm : W₀.thirdRootEval t₁ t₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    W₀.thirdRootEval_mem hm hm'
  have hΛm : W₀.slopeEval t₁ t₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    W₀.slopeEval_mem hm hm'
  -- the leading coefficient of the chord cubic is a unit
  have hA : IsUnit (1 + W₀.a₂ * W₀.slopeEval t₁ t₂ + W₀.a₄ * W₀.slopeEval t₁ t₂ ^ 2 +
      W₀.a₆ * W₀.slopeEval t₁ t₂ ^ 3) := by
    refine IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal ?_
    have h2 : (1 + W₀.a₂ * W₀.slopeEval t₁ t₂ + W₀.a₄ * W₀.slopeEval t₁ t₂ ^ 2 +
        W₀.a₆ * W₀.slopeEval t₁ t₂ ^ 3) - 1 = W₀.a₂ * W₀.slopeEval t₁ t₂ +
        W₀.a₄ * W₀.slopeEval t₁ t₂ ^ 2 + W₀.a₆ * W₀.slopeEval t₁ t₂ ^ 3 := by ring
    rw [h2]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ hΛm)
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hΛm 2 two_pos)))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hΛm 3 (by lia)))
  -- coerced hypotheses for the field-level chord lemma
  have hslope := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.slopeEval_mul_sub hm hm')
  have hNc := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.interceptEval_eq hm hm')
  have hT₃c := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.thirdRootEval_relation hm hm')
  have hwTc := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_thirdRootEval hm hm')
  push_cast at hslope hNc hT₃c hwTc
  rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW] at hT₃c
  have hAc : ((1 : v.adicCompletion K) + W.a₂ *
      ((W₀.slopeEval t₁ t₂ : v.adicCompletionIntegers K) : v.adicCompletion K) +
      W.a₄ * ((W₀.slopeEval t₁ t₂ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 +
      W.a₆ * ((W₀.slopeEval t₁ t₂ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 3)
      ≠ 0 := by
    intro hc
    apply hA.ne_zero
    refine Subtype.coe_injective ?_
    push_cast
    rw [coe_a₂ hW, coe_a₄ hW, coe_a₆ hW]
    exact hc
  have hw₁0 : ((W₀.wEval t₁ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact W₀.wEval_ne_zero hm h0
  have hw₂0 : ((W₀.wEval t₂ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact W₀.wEval_ne_zero hm' h0'
  have hwT0 : ((W₀.wEval (W₀.thirdRootEval t₁ t₂) : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact W₀.wEval_ne_zero hTm hT0
  obtain ⟨h₃, hsum⟩ := W.chord_point_add (coe_wEval_eq hW hm) (coe_wEval_eq hW hm')
    hslope hNc hT₃c hwTc hAc hw₁0 hw₂0 hwT0 (sub_ne_zero.mpr hx)
    (formalPoint_nonsingular hW hm h0) (formalPoint_nonsingular hW hm' h0')
  rw [hsum]
  simp only [Point.some.injEq]
  -- identify the chord point with the parametrized point at `ι̂(T)`
  have hDU0 : ((W₀.duEval (W₀.thirdRootEval t₁ t₂) : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact (W₀.isUnit_duEval hTm).ne_zero
  constructor
  · rw [coe_iotaEval_eq hTm, coe_wEval_iotaEval hTm]
    field_simp
  · rw [coe_wEval_iotaEval hTm]
    field_simp
    linear_combination coe_uEval_mul_duEval hTm -
      ((W₀.duEval (W₀.thirdRootEval t₁ t₂) : v.adicCompletionIntegers K) :
        v.adicCompletion K) * coe_uEval_eq hW hTm

include hW in
/-- The chord case of additivity: two nonzero parameters whose points have distinct
`x`-coordinates. -/
private lemma formalPoint_add_of_x_ne {z z' : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h0' : (z' () : v.adicCompletionIntegers K) ≠ 0)
    (hx : ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) ≠
      ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K)) :
    formalPoint hW (z + z') = formalPoint hW z + formalPoint hW z' := by
  have hm := (z ()).2
  have hm' := (z' ()).2
  -- the third root does not vanish (else the chord would be vertical)
  have hT0 : W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
      (z' () : v.adicCompletionIntegers K) ≠ 0 := by
    intro h
    have honl := W₀.wEval_thirdRootEval hm hm'
    rw [h, mul_zero, zero_add, W₀.wEval_zero] at honl
    have hν : W₀.interceptEval (z () : v.adicCompletionIntegers K)
        (z' () : v.adicCompletionIntegers K) *
          ((z' () : v.adicCompletionIntegers K) - (z () : v.adicCompletionIntegers K)) =
        (z' () : v.adicCompletionIntegers K) * W₀.wEval (z ()) -
          (z () : v.adicCompletionIntegers K) * W₀.wEval (z' ()) := by
      linear_combination ((z' () : v.adicCompletionIntegers K)) *
          W₀.interceptEval_eq hm hm' -
        ((z () : v.adicCompletionIntegers K)) * W₀.interceptEval_eq' hm hm'
    rw [← honl, zero_mul] at hν
    apply hx
    have hc := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K)) hν
    push_cast at hc
    linear_combination hc
  have hTm := W₀.thirdRootEval_mem hm hm'
  have hιm : W₀.iotaEval (W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
      (z' () : v.adicCompletionIntegers K)) ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    W₀.iotaEval_mem hTm
  have hι0 : W₀.iotaEval (W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
      (z' () : v.adicCompletionIntegers K)) ≠ 0 := by
    rw [W₀.iotaEval_eq hTm]
    exact neg_ne_zero.mpr (mul_ne_zero hT0 (W₀.isUnit_duEval hTm).ne_zero)
  have hpcoe : ((z + z') () : v.adicCompletionIntegers K) =
      W₀.iotaEval (W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
        (z' () : v.adicCompletionIntegers K)) := by
    rw [W₀.add_apply_coe_eq_addEval, W₀.addEval_eq hm hm']
  have hp0 : ((z + z') () : v.adicCompletionIntegers K) ≠ 0 := by
    rw [hpcoe]
    exact hι0
  rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_ne_zero hW h0',
    formalPoint_of_param_ne_zero hW hp0,
    paramPoint_add hW hm hm' h0 h0' hx hT0 hιm hι0]
  simp only [hpcoe]

include hW in
/-- Two nonzero parameters whose points share their `x`-coordinate agree up to the formal
inverse. -/
private lemma eq_or_eq_negPoint_of_x_cond {z z' : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h0' : (z' () : v.adicCompletionIntegers K) ≠ 0)
    (hx : ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K)) :
    z' = z ∨ z' = W₀.negPoint z := by
  have hm := (z ()).2
  have hm' := (z' ()).2
  have hWT0 : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact W₀.wEval_ne_zero hm h0
  have hWT0' : ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact W₀.wEval_ne_zero hm' h0'
  have hns := formalPoint_nonsingular hW hm h0
  have hns' := formalPoint_nonsingular hW hm' h0'
  have hxeq : ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) /
      ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) /
        ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    rw [div_eq_div_iff hWT0' hWT0]
    linear_combination -hx
  rcases W.Y_eq_of_X_eq hns'.left hns.left hxeq with hy | hy
  · left
    refine formalPoint_injective hW ?_
    rw [formalPoint_of_param_ne_zero hW h0', formalPoint_of_param_ne_zero hW h0]
    simp only [Point.some.injEq]
    exact ⟨hxeq, hy⟩
  · right
    refine formalPoint_injective hW ?_
    rw [formalPoint_negPoint hW, formalPoint_of_param_ne_zero hW h0',
      formalPoint_of_param_ne_zero hW h0, Point.neg_some]
    simp only [Point.some.injEq]
    exact ⟨hxeq, hy⟩

include hW in
/-- Additivity of the parametrization when the parameters are distinct and not related by
the formal inverse. -/
private lemma formalPoint_add_of_ne {z z' : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h0' : (z' () : v.adicCompletionIntegers K) ≠ 0)
    (hne : z' ≠ z) (hnneg : z' ≠ W₀.negPoint z) :
    formalPoint hW (z + z') = formalPoint hW z + formalPoint hW z' := by
  refine formalPoint_add_of_x_ne hW h0 h0' fun hx ↦ ?_
  rcases eq_or_eq_negPoint_of_x_cond hW h0 h0' hx with h | h
  · exact hne h
  · exact hnneg h

variable [CharZero K]

include hW in
/-- The doubling case of additivity, via an auxiliary point of very small valuation
(which turns all needed additions into chord cases). -/
private lemma formalPoint_add_self {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h2t : (z () : v.adicCompletionIntegers K) ≠ W₀.iotaEval (z ())) :
    formalPoint hW (z + z) = formalPoint hW z + formalPoint hW z := by
  have hm := (z ()).2
  obtain ⟨s, hsm, hs0, hst, hsιt, hsιs⟩ := exists_aux_param hm h0
  -- the auxiliary point and the three chord additions
  obtain ⟨u, hudef⟩ : ∃ u : W₀.formalGroupLaw.Points, u = fun _ ↦ ⟨s, hsm⟩ := ⟨_, rfl⟩
  have hus : (u () : v.adicCompletionIntegers K) = s := by rw [hudef]
  have hu0 : (u () : v.adicCompletionIntegers K) ≠ 0 := by rw [hus]; exact hs0
  have hune : u ≠ z := by
    intro h
    apply hst
    rw [← hus]
    exact congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h
  have hunneg : u ≠ W₀.negPoint z := by
    intro h
    apply hsιt
    rw [← hus]
    exact congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h
  have husm : (u () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) := (u ()).2
  have hnu0 : ((W₀.negPoint u) () : v.adicCompletionIntegers K) ≠ 0 := by
    rw [W₀.negPoint_apply_coe, hus, W₀.iotaEval_eq hsm]
    exact neg_ne_zero.mpr (mul_ne_zero hs0 (W₀.isUnit_duEval hsm).ne_zero)
  have hnune : W₀.negPoint u ≠ z := by
    intro h
    apply hsιt
    have h' := congrArg (fun w ↦ W₀.iotaEval (w () : v.adicCompletionIntegers K)) h
    simp only [W₀.negPoint_apply_coe, hus] at h'
    rw [W₀.iotaEval_iotaEval hsm] at h'
    rw [← h']
  have hnunneg : W₀.negPoint u ≠ W₀.negPoint z := by
    intro h
    apply hst
    have h' := congrArg (fun w ↦ W₀.iotaEval (w () : v.adicCompletionIntegers K)) h
    simp only [W₀.negPoint_apply_coe, hus] at h'
    rw [W₀.iotaEval_iotaEval hsm, W₀.iotaEval_iotaEval hm] at h'
    exact h'
  have c1 : formalPoint hW (z + u) = formalPoint hW z + formalPoint hW u :=
    formalPoint_add_of_ne hW h0 hu0 hune hunneg
  have c2 : formalPoint hW (z + W₀.negPoint u) =
      formalPoint hW z + formalPoint hW (W₀.negPoint u) :=
    formalPoint_add_of_ne hW h0 hnu0 hnune hnunneg
  have hpu : ((z + u) () : v.adicCompletionIntegers K) ≠ 0 := by
    intro h
    have hz : formalPoint hW z + formalPoint hW u = 0 := by
      rw [← c1, formalPoint_of_param_eq_zero hW h]
    have h1 : formalPoint hW u = formalPoint hW (W₀.negPoint z) := by
      rw [formalPoint_negPoint hW]
      exact eq_neg_of_add_eq_zero_right hz
    exact hunneg (formalPoint_injective hW h1)
  have hpnu : ((z + W₀.negPoint u) () : v.adicCompletionIntegers K) ≠ 0 := by
    intro h
    have hz : formalPoint hW z + formalPoint hW (W₀.negPoint u) = 0 := by
      rw [← c2, formalPoint_of_param_eq_zero hW h]
    have h1 : formalPoint hW u = formalPoint hW z := by
      have h2 : formalPoint hW (W₀.negPoint u) = -formalPoint hW z :=
        eq_neg_of_add_eq_zero_right hz
      rw [formalPoint_negPoint hW, neg_inj] at h2
      exact h2
    exact hune (formalPoint_injective hW h1)
  have hcne : z + W₀.negPoint u ≠ z + u := by
    intro h
    have h' := congrArg (formalPoint hW) h
    rw [c1, c2] at h'
    have h'' := add_left_cancel h'
    have h3 := congrArg (fun w ↦ (w () : v.adicCompletionIntegers K))
      (formalPoint_injective hW h'')
    simp only [W₀.negPoint_apply_coe, hus] at h3
    exact hsιs h3.symm
  have hcnneg : z + W₀.negPoint u ≠ W₀.negPoint (z + u) := by
    intro h
    have h' := congrArg (formalPoint hW) h
    simp only [c1, c2, formalPoint_negPoint hW, neg_add] at h'
    have h'' := add_right_cancel h'
    rw [← formalPoint_negPoint hW] at h''
    exact h2t (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K))
      (formalPoint_injective hW h''))
  have c3 : formalPoint hW ((z + u) + (z + W₀.negPoint u)) =
      formalPoint hW (z + u) + formalPoint hW (z + W₀.negPoint u) :=
    formalPoint_add_of_ne hW hpu hpnu hcne hcnneg
  have hkey : (z + u) + (z + W₀.negPoint u) = z + z := by
    rw [add_add_add_comm, W₀.add_negPoint, add_zero]
  calc formalPoint hW (z + z)
      = formalPoint hW ((z + u) + (z + W₀.negPoint u)) :=
        (congrArg (formalPoint hW) hkey).symm
    _ = formalPoint hW (z + u) + formalPoint hW (z + W₀.negPoint u) := c3
    _ = (formalPoint hW z + formalPoint hW u) +
        (formalPoint hW z + formalPoint hW (W₀.negPoint u)) := by rw [c1, c2]
    _ = formalPoint hW z + formalPoint hW z := by
      rw [formalPoint_negPoint hW]
      abel

include hW in
/-- The parametrization of the kernel of reduction is additive. -/
theorem formalPoint_add (z z' : W₀.formalGroupLaw.Points) :
    formalPoint hW (z + z') = formalPoint hW z + formalPoint hW z' := by
  rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0
  · have hz : z = 0 := funext fun _ ↦ Subtype.ext h0
    rw [hz, zero_add, formalPoint_of_param_eq_zero hW (z := 0) (by simp), zero_add]
  rcases eq_or_ne (z' () : v.adicCompletionIntegers K) 0 with h0' | h0'
  · have hz' : z' = 0 := funext fun _ ↦ Subtype.ext h0'
    rw [hz', add_zero, formalPoint_of_param_eq_zero hW (z := 0) (by simp), add_zero]
  rcases eq_or_ne (z' () : v.adicCompletionIntegers K) (W₀.iotaEval (z ())) with hinv | hinv
  · have hz' : z' = W₀.negPoint z := funext fun _ ↦ Subtype.ext hinv
    rw [hz', W₀.add_negPoint, formalPoint_of_param_eq_zero hW (z := 0) (by simp),
      formalPoint_negPoint hW, add_neg_cancel]
  rcases eq_or_ne (z' () : v.adicCompletionIntegers K) (z () : v.adicCompletionIntegers K)
    with heqp | hnep
  · have hz' : z' = z := funext fun _ ↦ Subtype.ext heqp
    rw [hz']
    exact formalPoint_add_self hW h0 fun h ↦ hinv (heqp.trans h)
  · exact formalPoint_add_of_ne hW h0 h0'
      (fun h ↦ hnep (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h))
      (fun h ↦ hinv (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h))

/-- For an elliptic curve `W` over `K_v` with an integral model `W₀` and `n : ℕ`, the
subgroup `E_{n+1}(K_v)` of points `(x, y)` with `exp (2 * (n + 1)) ≤ v(x)` (a pole of order
at least `2(n + 1)` at `x`, together with `0`); this is the kernel of reduction modulo
`𝔪^(n+1)`, isomorphic to the group `Ê(𝔪^(n+1))` of points of the formal group of `W₀`
(Silverman, VII.2.2).  Closure under addition comes from the formal group: both summands
are parametrized by `𝔪^(n+1)`-parameters, and the addition series preserves that level. -/
def filtration (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) (n : ℕ) : AddSubgroup W.Point where
  carrier := {P | match P with
    | .zero => True
    | @Point.some _ _ _ x _ _ => exp (2 * (n + 1) : ℤ) ≤ Valued.v x}
  zero_mem' := trivial
  neg_mem' {P} hP := by
    match P with
    | .zero => exact hP
    | @Point.some _ _ _ x y h => rw [Set.mem_setOf_eq, Point.neg_some]; exact hP
  add_mem' {P Q} hP hQ := by
    match P, Q with
    | .zero, Q =>
      rw [show (Point.zero : W.Point) = 0 from rfl, zero_add]
      exact hQ
    | @Point.some _ _ _ x₁ y₁ h₁, .zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, add_zero]
      exact hP
    | @Point.some _ _ _ x₁ y₁ h₁, @Point.some _ _ _ x₂ y₂ h₂ =>
      rw [Set.mem_setOf_eq] at hP hQ
      obtain ⟨z, hz⟩ := exists_formalPoint_eq_some hW h₁
        (le_trans (exp_le_exp.mpr (by lia)) hP)
      obtain ⟨z', hz'⟩ := exists_formalPoint_eq_some hW h₂
        (le_trans (exp_le_exp.mpr (by lia)) hQ)
      have h0 : (z () : v.adicCompletionIntegers K) ≠ 0 := by
        intro h
        rw [formalPoint_of_param_eq_zero hW h] at hz
        exact absurd hz (by simp)
      have h0' : (z' () : v.adicCompletionIntegers K) ≠ 0 := by
        intro h
        rw [formalPoint_of_param_eq_zero hW h] at hz'
        exact absurd hz' (by simp)
      have hx₁ : ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) /
          ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) = x₁ := by
        have hz2 := hz
        rw [formalPoint_of_param_ne_zero hW h0] at hz2
        simp only [Point.some.injEq] at hz2
        exact hz2.1
      have hx₂ : ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) /
          ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) = x₂ := by
        have hz2 := hz'
        rw [formalPoint_of_param_ne_zero hW h0'] at hz2
        simp only [Point.some.injEq] at hz2
        exact hz2.1
      have hzm : (z () : v.adicCompletionIntegers K) ∈
          maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) :=
        (param_pow_iff (z ()).2 h0 n).mpr (by rw [hx₁]; exact hP)
      have hzm' : (z' () : v.adicCompletionIntegers K) ∈
          maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) :=
        (param_pow_iff (z' ()).2 h0' n).mpr (by rw [hx₂]; exact hQ)
      have hsum : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = formalPoint hW (z + z') := by
        rw [formalPoint_add hW, hz, hz']
      have hsm := add_param_mem_pow hzm hzm'
      rcases eq_or_ne (((z + z') ()) : v.adicCompletionIntegers K) 0 with hs0 | hs0
      · rw [Set.mem_setOf_eq, hsum, formalPoint_of_param_eq_zero hW hs0]
        trivial
      · rw [Set.mem_setOf_eq, hsum, formalPoint_of_param_ne_zero hW hs0]
        exact (param_pow_iff ((z + z') ()).2 hs0 n).mp hsm

variable {hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W}
  {n : ℕ}

@[simp]
lemma zero_mem_filtration : (0 : W.Point) ∈ filtration hW n := trivial

@[simp]
lemma some_mem_filtration {x y : v.adicCompletion K} {h : W.Nonsingular x y} :
    (.some x y h : W.Point) ∈ filtration hW n ↔ exp (2 * (n + 1) : ℤ) ≤ Valued.v x := Iff.rfl

/-- The filtration correspondence: the parameter lies in `𝔪^(n+1)` exactly when the
associated point lies in the filtration step `E_{n+1}(K_v)`. -/
theorem mem_pow_iff_formalPoint_mem_filtration (z : W₀.formalGroupLaw.Points) (n : ℕ) :
    (z () : v.adicCompletionIntegers K) ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
      formalPoint hW z ∈ filtration hW n := by
  rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0
  · simp [h0]
  · rw [formalPoint_of_param_ne_zero hW h0, some_mem_filtration]
    exact param_pow_iff (z ()).2 h0 n

/-- Every point of the kernel of reduction comes from a parameter in `𝔪`: the
parametrization by the `𝔪`-points of the formal group is surjective onto
`filtration hW 0`. -/
theorem formalPoint_surjective {P : W.Point} (hP : P ∈ filtration hW 0) :
    ∃ z : W₀.formalGroupLaw.Points, formalPoint hW z = P := by
  match P with
  | .zero => exact ⟨0, formalPoint_of_param_eq_zero hW (z := 0) (by simp)⟩
  | .some x y h =>
    rw [some_mem_filtration] at hP
    exact exists_formalPoint_eq_some hW h (le_trans (exp_le_exp.mpr (by lia)) hP)

/-- The `𝔪`-points of the formal group law of an integral model `W₀` of `W` are the kernel
of reduction `E₁(K_v) = filtration hW 0`, via `z ↦ (x, y)` with `x = z/w(z)`,
`y = -1/w(z)`; the equivalence matches the filtration by valuation on both sides
(Silverman, VII.2.2). -/
theorem exists_points_equiv_filtration :
    ∃ θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0,
      ∀ (z : W₀.formalGroupLaw.Points) (n : ℕ),
        ((z () : v.adicCompletionIntegers K) ∈
            maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
          ((θ z : filtration hW 0) : W.Point) ∈ filtration hW n) := by
  have hmap : ∀ z : W₀.formalGroupLaw.Points, formalPoint hW z ∈ filtration hW 0 :=
    fun z ↦ (mem_pow_iff_formalPoint_mem_filtration z 0).mp (by
      rw [pow_one]
      exact (z ()).2)
  let f : W₀.formalGroupLaw.Points →+ filtration hW 0 :=
    { toFun := fun z ↦ ⟨formalPoint hW z, hmap z⟩
      map_zero' := Subtype.ext (formalPoint_of_param_eq_zero hW (z := 0) (by simp))
      map_add' := fun z z' ↦ Subtype.ext (formalPoint_add hW z z') }
  refine ⟨AddEquiv.ofBijective f
    ⟨fun z z' h ↦ formalPoint_injective hW (congrArg Subtype.val h), fun P ↦ ?_⟩,
    fun z n ↦ ?_⟩
  · obtain ⟨z, hz⟩ := formalPoint_surjective P.2
    exact ⟨z, Subtype.ext hz⟩
  · exact mem_pow_iff_formalPoint_mem_filtration z n

/-- The filtration is decreasing. -/
theorem filtration_anti {m n : ℕ} (hmn : m ≤ n) : filtration hW n ≤ filtration hW m := by
  intro P hP
  match P with
  | .zero => trivial
  | @Point.some _ _ _ x y h =>
    rw [some_mem_filtration] at hP ⊢
    refine le_trans (exp_le_exp.mpr ?_) hP
    lia

/-- If the chord slope towards the negative of the base point has valuation at least
`exp 1`, the difference of the two (integral) points lies in the kernel of reduction. -/
private lemma sub_mem_filtration_of_slope {x₀ y₀ x y : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (h : W.Nonsingular x y) (hxx : x ≠ x₀)
    (hx₀ : Valued.v x₀ ≤ 1) (hxI : Valued.v x ≤ 1)
    (hs : exp (1 : ℤ) ≤ Valued.v ((y - W.negY x₀ y₀) / (x - x₀))) :
    (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := coe_a₁ hW ▸ valued_coe_le_one W₀.a₁
  have ha₂ : Valued.v W.a₂ ≤ 1 := coe_a₂ hW ▸ valued_coe_le_one W₀.a₂
  rw [sub_eq_add_neg, Point.neg_some,
    Point.add_some (fun hc ↦ hxx hc.1), some_mem_filtration]
  rw [Affine.slope_of_X_ne hxx, Affine.addX]
  set L : v.adicCompletion K := (y - W.negY x₀ y₀) / (x - x₀) with hL
  have hL1 : (1 : ℤᵐ⁰) < Valued.v L :=
    lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; lia) hs
  have hbig : ∀ c : ℤᵐ⁰, c ≤ 1 → c < Valued.v L ^ 2 := fun c hc ↦
    lt_of_le_of_lt hc (by
      calc (1 : ℤᵐ⁰) < Valued.v L := hL1
        _ = Valued.v L ^ 1 := (pow_one _).symm
        _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL1 (by lia))
  have hrest : Valued.v (W.a₁ * L - W.a₂ - x - x₀) < Valued.v L ^ 2 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt
      (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _)
        (max_lt ?_ (hbig _ ha₂))) (hbig _ hxI))) (hbig _ hx₀))
    rw [map_mul]
    calc Valued.v W.a₁ * Valued.v L ≤ 1 * Valued.v L := mul_le_mul' ha₁ le_rfl
      _ = Valued.v L ^ 1 := by rw [one_mul, pow_one]
      _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL1 (by lia)
  rw [show L ^ 2 + W.a₁ * L - W.a₂ - x - x₀ = L ^ 2 + (W.a₁ * L - W.a₂ - x - x₀) by ring,
    Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hrest), map_pow]
  refine le_trans (le_of_eq ?_) (pow_le_pow_left' hs 2)
  rw [← exp_nsmul, nsmul_eq_mul]
  norm_num

/-- Around each integral point of the curve there is a congruence level `s` such that
every on-curve point congruent to it modulo `𝔪^s` differs from it by an element of the
kernel of reduction.  Near a `2`-torsion point the chord slope is estimated through the
finite-difference identity (nonsingularity provides the nonvanishing partial). -/
private lemma exists_level_sub_mem {x₀ y₀ : v.adicCompletion K} (h₀ : W.Nonsingular x₀ y₀)
    (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1) :
    ∃ s : ℕ, ∀ {x y : v.adicCompletion K} (h : W.Nonsingular x y),
      Valued.v (x - x₀) ≤ exp (-(s : ℤ)) → Valued.v (y - y₀) ≤ exp (-(s : ℤ)) →
      (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := coe_a₁ hW ▸ valued_coe_le_one W₀.a₁
  have ha₂ : Valued.v W.a₂ ≤ 1 := coe_a₂ hW ▸ valued_coe_le_one W₀.a₂
  have ha₃ : Valued.v W.a₃ ≤ 1 := coe_a₃ hW ▸ valued_coe_le_one W₀.a₃
  have ha₄ : Valued.v W.a₄ ≤ 1 := coe_a₄ hW ▸ valued_coe_le_one W₀.a₄
  rcases eq_or_ne (y₀ - W.negY x₀ y₀) 0 with hψ0 | hψ0
  · -- `2`-torsion base point: the partial in `x` does not vanish
    have hφ0 : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) ≠ 0 := by
      refine ((W.nonsingular_iff' x₀ y₀).mp h₀).2.resolve_right fun hc ↦ hc ?_
      rw [Affine.negY] at hψ0
      linear_combination hψ0
    have hφv : Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) ≠ 0 := by
      simpa using hφ0
    obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (W.a₁ * y₀ -
        (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = exp c := ⟨_, (exp_log hφv).symm⟩
    refine ⟨(1 - c).toNat, fun {x y} h hx hy ↦ ?_⟩
    set s : ℕ := (1 - c).toNat with hsdef
    have hsc : 1 - c ≤ (s : ℤ) := by
      rw [hsdef]
      exact Int.self_le_toNat _
    rcases eq_or_ne x x₀ with heq | hxx
    · -- same `x`-coordinate: the points coincide (`ψ = 0` collapses the dichotomy)
      have hy0 : y = y₀ := by
        rcases W.Y_eq_of_X_eq h.left h₀.left heq with hy' | hy'
        · exact hy'
        · rw [hy', ← sub_eq_zero, show W.negY x₀ y₀ - y₀ = -(y₀ - W.negY x₀ y₀) by ring,
            hψ0, neg_zero]
      have hPQ : (.some x y h : W.Point) = .some x₀ y₀ h₀ := by
        subst heq hy0
        rfl
      rw [hPQ, sub_self]
      exact zero_mem _
    · -- distinct `x`-coordinates: slope via the finite-difference identity
      have hxI : Valued.v x ≤ 1 := by
        rw [show x = (x - x₀) + x₀ by ring]
        exact le_trans (Valued.v.map_add _ _) (max_le
          (hx.trans (by rw [← exp_zero, exp_le_exp]; lia)) hx₀)
      have hid : (y - W.negY x₀ y₀) * (y - y₀) = (x - x₀) *
          (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) := by
        rw [Affine.negY]
        linear_combination (W.equation_iff x y).mp h.left -
          (W.equation_iff x₀ y₀).mp h₀.left
      -- the difference quotient is congruent to the partial, hence of its valuation
      have hyI : Valued.v y ≤ 1 := by
        rw [show y = (y - y₀) + y₀ by ring]
        exact le_trans (Valued.v.map_add _ _) (max_le
          (hy.trans (by rw [← exp_zero, exp_le_exp]; lia)) hy₀)
      have hdiff : Valued.v ((x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ -
          W.a₁ * y) - -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))) ≤
          exp (-(s : ℤ)) := by
        rw [show (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
            -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) =
            (x - x₀) * (x + 2 * x₀ + W.a₂) - W.a₁ * (y - y₀) by ring]
        refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
        · rw [map_mul]
          refine le_trans (mul_le_mul' hx ?_) (by rw [mul_one])
          refine le_trans (Valued.v.map_add _ _) (max_le (le_trans (Valued.v.map_add _ _)
            (max_le hxI ?_)) ha₂)
          calc Valued.v (2 * x₀) ≤ Valued.v 2 * Valued.v x₀ := le_of_eq (map_mul _ _ _)
            _ ≤ 1 * 1 := mul_le_mul' (valued_coe_le_one 2) hx₀
            _ = 1 := one_mul 1
        · rw [map_mul]
          exact le_trans (mul_le_mul' ha₁ hy) (by rw [one_mul])
      have hhv : Valued.v (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ -
          W.a₁ * y) = exp c := by
        rw [show (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) =
          -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) +
            ((x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
              -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))) by ring,
          Valuation.map_add_eq_of_lt_left, Valuation.map_neg, hc]
        refine lt_of_le_of_lt hdiff ?_
        rw [Valuation.map_neg, hc, exp_lt_exp]
        lia
      -- `y ≠ y₀`, and the valuation identity gives the slope bound
      have hyy : y ≠ y₀ := by
        intro hyeq
        have h0' : (x - x₀) * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ -
            W.a₁ * y) = 0 := by
          rw [← hid, hyeq, sub_self, mul_zero]
        rcases mul_eq_zero.mp h0' with hc' | hc'
        · exact hxx (sub_eq_zero.mp hc')
        · rw [hc', map_zero] at hhv
          exact exp_ne_zero hhv.symm
      have hval := congrArg Valued.v hid
      rw [map_mul, map_mul, hhv] at hval
      refine sub_mem_filtration_of_slope h₀ h hxx hx₀ hxI ?_
      rw [map_div₀]
      obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
        ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
      obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, Valued.v (y - y₀) = exp dy :=
        ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hyy)).symm⟩
      rw [hdx, hdy] at hval
      obtain ⟨nv, hnv⟩ : ∃ nv : ℤ, Valued.v (y - W.negY x₀ y₀) = exp nv := by
        refine ⟨_, (exp_log fun hc' ↦ ?_).symm⟩
        rw [hc', zero_mul] at hval
        exact mul_ne_zero exp_ne_zero exp_ne_zero hval.symm
      rw [hnv, ← exp_add, ← exp_add, exp_inj] at hval
      rw [hnv, hdx, ← exp_sub, exp_le_exp]
      have hdy' : dy ≤ -(s : ℤ) := by rwa [hdy, exp_le_exp] at hy
      lia
  · -- non-`2`-torsion base point: the slope numerator is dominated by `ψ`
    have hψv : Valued.v (y₀ - W.negY x₀ y₀) ≠ 0 := by simpa using hψ0
    obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (y₀ - W.negY x₀ y₀) = exp c :=
      ⟨_, (exp_log hψv).symm⟩
    refine ⟨(1 - c).toNat, fun {x y} h hx hy ↦ ?_⟩
    set s : ℕ := (1 - c).toNat with hsdef
    have hsc : 1 - c ≤ (s : ℤ) := by
      rw [hsdef]
      exact Int.self_le_toNat _
    have hcle : c ≤ 0 := by
      have h1 : Valued.v (y₀ - W.negY x₀ y₀) ≤ 1 := by
        rw [Affine.negY, show y₀ - (-y₀ - W.a₁ * x₀ - W.a₃) =
          y₀ + (y₀ + (W.a₁ * x₀ + W.a₃)) by ring]
        refine le_trans (Valued.v.map_add _ _) (max_le hy₀ (le_trans (Valued.v.map_add _ _)
          (max_le hy₀ (le_trans (Valued.v.map_add _ _) (max_le ?_ ha₃)))))
        rw [map_mul]
        exact le_trans (mul_le_mul' ha₁ hx₀) (by rw [one_mul])
      rwa [hc, ← exp_zero, exp_le_exp] at h1
    rcases eq_or_ne x x₀ with heq | hxx
    · rcases W.Y_eq_of_X_eq h.left h₀.left heq with hy' | hy'
      · have hPQ : (.some x y h : W.Point) = .some x₀ y₀ h₀ := by
          subst heq hy'
          rfl
        rw [hPQ, sub_self]
        exact zero_mem _
      · -- `y = negY`: excluded, since `y − y₀ = −ψ` is too large
        exfalso
        rw [hy', show W.negY x₀ y₀ - y₀ = -(y₀ - W.negY x₀ y₀) by ring, Valuation.map_neg,
          hc, exp_le_exp] at hy
        lia
    · -- distinct `x`-coordinates: the numerator has valuation `v(ψ)`
      have hxI : Valued.v x ≤ 1 := by
        rw [show x = (x - x₀) + x₀ by ring]
        exact le_trans (Valued.v.map_add _ _) (max_le
          (hx.trans (by rw [← exp_zero, exp_le_exp]; lia)) hx₀)
      have hnum : Valued.v (y - W.negY x₀ y₀) = exp c := by
        rw [show y - W.negY x₀ y₀ = (y₀ - W.negY x₀ y₀) + (y - y₀) by ring,
          Valuation.map_add_eq_of_lt_left, hc]
        refine lt_of_le_of_lt hy ?_
        rw [hc, exp_lt_exp]
        lia
      refine sub_mem_filtration_of_slope h₀ h hxx hx₀ hxI ?_
      rw [map_div₀, hnum]
      obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
        ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
      rw [hdx, ← exp_sub, exp_le_exp]
      have hdx' : dx ≤ -(s : ℤ) := by rwa [hdx, exp_le_exp] at hx
      lia

variable [Finite (R ⧸ v.asIdeal)]

/-- Each filtration step has finite index in the previous one: the parameter map modulo
`𝔪^(k+2)` is additive on the `k`-th step (the formal group law is `t₁ + t₂` to first
order) with kernel the next step, and it takes values in a finite quotient. -/
private lemma relIndex_filtration_succ_ne_zero (k : ℕ) :
    (filtration hW (k + 1)).relIndex (filtration hW k) ≠ 0 := by
  obtain ⟨θ, hθ⟩ := exists_points_equiv_filtration (hW := hW)
  -- the parameter of a point of the `k`-th filtration step
  obtain ⟨par, hpar⟩ : ∃ par : filtration hW k → W₀.formalGroupLaw.Points,
      par = fun P ↦ θ.symm ⟨P.1, filtration_anti (Nat.zero_le k) P.2⟩ := ⟨_, rfl⟩
  have hθpar (P : filtration hW k) : ((θ (par P) : filtration hW 0) : W.Point) = P.1 := by
    rw [hpar, θ.apply_symm_apply]
  have hparam (P : filtration hW k) : ((par P) () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1) :=
    (hθ _ k).mpr (by rw [hθpar]; exact P.2)
  have hpar_add (P Q : filtration hW k) : par (P + Q) = par P + par Q := by
    simp only [hpar]
    rw [← map_add]
    exact congrArg θ.symm (Subtype.ext rfl)
  -- the parameter map modulo `𝔪^(k+2)` is additive
  have hadd (P Q : filtration hW k) :
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
          ((par (P + Q)) ()) =
        Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
          ((par P) ()) +
        Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
          ((par Q) ()) := by
    rw [hpar_add]
    exact mk_add_param (hparam P) (hparam Q)
  obtain ⟨f, hf⟩ : ∃ f : filtration hW k →+ v.adicCompletionIntegers K ⧸
      (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)),
      f = AddMonoidHom.mk'
        (fun P ↦ Ideal.Quotient.mk _ (((par P) ()) : v.adicCompletionIntegers K)) hadd :=
    ⟨_, rfl⟩
  have hker : f.ker = (filtration hW (k + 1)).addSubgroupOf (filtration hW k) := by
    ext P
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hf, AddMonoidHom.mk'_apply,
      Ideal.Quotient.eq_zero_iff_mem, hθ _ (k + 1), hθpar]
  have hfin : Finite (v.adicCompletionIntegers K ⧸
      (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))) := finite_quotient_pow (k + 2)
  have hrel : (filtration hW (k + 1)).relIndex (filtration hW k) = f.ker.index :=
    congrArg AddSubgroup.index hker.symm
  rw [hrel, AddSubgroup.index_ker, Nat.card_ne_zero]
  exact ⟨⟨0, 0, map_zero f⟩, Set.Finite.to_subtype (Set.toFinite _)⟩

/-- The index of the `0`-th filtration step — the kernel of reduction `E₁(K_v)` — in
`E(K_v)` is finite: the complement consists of integral points, which form a compact set
covered by finitely many congruence neighbourhoods, each inside a single coset. -/
theorem filtration_zero_finiteIndex (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) : (filtration hW 0).FiniteIndex := by
  rw [AddSubgroup.finiteIndex_iff_finite_quotient]
  -- the compact set of integral points of the curve
  obtain ⟨Z, hZdef⟩ : ∃ Z : Set ((v.adicCompletion K) × (v.adicCompletion K)),
      Z = {p | W.Equation p.1 p.2 ∧ Valued.v p.1 ≤ 1 ∧ Valued.v p.2 ≤ 1} := ⟨_, rfl⟩
  have hZcpt : IsCompact Z := by
    have hcl : IsClosed {p : (v.adicCompletion K) × (v.adicCompletion K) |
        W.Equation p.1 p.2} := by
      have hset : {p : (v.adicCompletion K) × (v.adicCompletion K) | W.Equation p.1 p.2} =
          {p : (v.adicCompletion K) × (v.adicCompletion K) |
            p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 =
              p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆} := by
        ext p
        rw [Set.mem_setOf, Set.mem_setOf, W.equation_iff]
      rw [hset]
      exact isClosed_eq (by fun_prop) (by fun_prop)
    have hprod : IsCompact ({a : v.adicCompletion K | Valued.v a ≤ 1} ×ˢ
        {a : v.adicCompletion K | Valued.v a ≤ 1}) :=
      isCompact_integerSet.prod isCompact_integerSet
    have hZeq : Z = ({a : v.adicCompletion K | Valued.v a ≤ 1} ×ˢ
        {a : v.adicCompletion K | Valued.v a ≤ 1}) ∩
        {p : (v.adicCompletion K) × (v.adicCompletion K) | W.Equation p.1 p.2} := by
      rw [hZdef]
      ext p
      simp only [Set.mem_setOf, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hZeq]
    exact hprod.inter_right hcl
  -- nonsingularity and congruence levels on `Z`
  have hmemZ : ∀ p : ↥Z, W.Equation p.1.1 p.1.2 ∧ Valued.v p.1.1 ≤ 1 ∧
      Valued.v p.1.2 ≤ 1 := fun ⟨q, hq⟩ ↦ by
    rw [hZdef] at hq
    exact hq
  have hns : ∀ p : ↥Z, W.Nonsingular p.1.1 p.1.2 := fun p ↦
    (W.equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp (hmemZ p).1
  have hint : ∀ p : ↥Z, Valued.v p.1.1 ≤ 1 ∧ Valued.v p.1.2 ≤ 1 := fun p ↦ (hmemZ p).2
  have hloc : ∀ p : ↥Z, ∃ s : ℕ, ∀ {x y : v.adicCompletion K} (h : W.Nonsingular x y),
      Valued.v (x - p.1.1) ≤ exp (-(s : ℤ)) → Valued.v (y - p.1.2) ≤ exp (-(s : ℤ)) →
      (.some x y h : W.Point) - .some p.1.1 p.1.2 (hns p) ∈ filtration hW 0 :=
    fun p ↦ exists_level_sub_mem (hns p) (hint p).1 (hint p).2
  choose sfun hsfun using hloc
  -- the covering by congruence neighbourhoods and its finite subcover
  obtain ⟨t, ht⟩ := hZcpt.elim_finite_subcover
    (fun p : ↥Z ↦ {b : v.adicCompletion K | Valued.v (b - p.1.1) ≤ exp (-(sfun p : ℤ))} ×ˢ
      {b : v.adicCompletion K | Valued.v (b - p.1.2) ≤ exp (-(sfun p : ℤ))})
    (fun p ↦ (isOpen_le_ball _ _).prod (isOpen_le_ball _ _))
    (fun q hq ↦ Set.mem_iUnion.mpr ⟨⟨q, hq⟩, by
      refine Set.mem_prod.mpr ⟨?_, ?_⟩ <;>
        · rw [Set.mem_setOf, sub_self, map_zero]
          exact zero_le⟩)
  -- the counting surjection from the finite subcover
  refine Finite.of_surjective (α := Option {p : ↥Z // p ∈ t}) (fun o ↦ o.elim
    (0 : W.Point ⧸ filtration hW 0) (fun p ↦ QuotientAddGroup.mk
      (.some p.1.1.1 p.1.1.2 (hns p.1)))) fun c ↦ ?_
  obtain ⟨P, rfl⟩ := QuotientAddGroup.mk_surjective c
  match P with
  | .zero => exact ⟨none, rfl⟩
  | @Point.some _ _ _ x y h =>
    by_cases hmem : (.some x y h : W.Point) ∈ filtration hW 0
    · exact ⟨none, ((QuotientAddGroup.eq_zero_iff _).mpr hmem).symm⟩
    · have hxpole : ¬ exp (2 : ℤ) ≤ Valued.v x := fun hc ↦ hmem
        ((some_mem_filtration (hW := hW)).mpr (le_trans (exp_le_exp.mpr (by lia)) hc))
      obtain ⟨hxI, hyI⟩ := integral_of_not_mem hW h.left hxpole
      have hqZ : (x, y) ∈ Z := by
        rw [hZdef]
        exact ⟨h.left, hxI, hyI⟩
      obtain ⟨p, hpt, hpU⟩ := Set.mem_iUnion₂.mp (ht hqZ)
      refine ⟨some ⟨p, hpt⟩, ?_⟩
      have hd := hsfun p h (Set.mem_prod.mp hpU).1 (Set.mem_prod.mp hpU).2
      exact ((QuotientAddGroup.eq_iff_sub_mem).mpr hd).symm

/-- Each step of the valuation filtration on the points of an elliptic curve over `K_v` has
finite index, by induction: each step has finite index in the previous one
(`relIndex_filtration_succ_ne_zero`), and the `0`-th step has finite index in `E(K_v)`. -/
theorem filtration_finiteIndex (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) (n : ℕ) : (filtration hW n).FiniteIndex := by
  induction n with
  | zero => exact filtration_zero_finiteIndex hW
  | succ k ih =>
    have h1 : (filtration hW (k + 1)).index ≠ 0 := by
      rw [← AddSubgroup.relIndex_mul_index (filtration_anti (hW := hW) (Nat.le_succ k))]
      exact Nat.mul_ne_zero (relIndex_filtration_succ_ne_zero k) ih.index_ne_zero
    exact ⟨h1⟩

/-- Some step of the valuation filtration on the points of an elliptic curve over `K_v` is
isomorphic to the additive group of `𝒪_v`: for `𝔪^k` past the ramification of the residue
characteristic, the formal logarithm identifies `Ê(𝔪^k)` with `(𝔪^k, +) ≅ (𝒪_v, +)`
(Silverman, IV.6.4). -/
theorem exists_filtration_equiv (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) :
    ∃ n, Nonempty (filtration hW n ≃+ v.adicCompletionIntegers K) :=
  sorry

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [DecidableEq (v.adicCompletion K)] [CharZero K]
  [Finite (R ⧸ v.asIdeal)] (W : Affine (v.adicCompletion K)) [W.IsElliptic]

open scoped Classical in
/-- The group of points of an elliptic curve over the completion `K_v` (a characteristic-`0`
local field with finite residue field) has a subgroup of finite index that is isomorphic to
the additive group of the valuation ring `𝒪_v`.

This is the structure theorem coming from the formal group of the curve: pass to an
integral model and take a suitable step of the valuation filtration. -/
theorem exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers :
    ∃ U : AddSubgroup W.Point, U.FiniteIndex ∧ Nonempty (U ≃+ (v.adicCompletionIntegers K)) := by
  obtain ⟨C, W₀, hW⟩ := exists_variableChange_map_eq v W
  obtain ⟨n, ⟨e⟩⟩ := exists_filtration_equiv hW
  refine ⟨(filtration hW n).map (Point.equivVariableChange W C : _ →+ _), ⟨?_⟩, ?_⟩
  · rw [AddSubgroup.index_map_equiv]
    exact (filtration_finiteIndex hW n).index_ne_zero
  · exact ⟨((AddEquiv.addSubgroupMap (Point.equivVariableChange W C) _).symm.trans e)⟩

end WeierstrassCurve.Affine
