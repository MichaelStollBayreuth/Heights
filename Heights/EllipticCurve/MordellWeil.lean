import Mathlib
import Heights.Basic
import Heights.MvPolynomial
import Heights.ForMathlib.VariableChange
import Heights.EllipticCurve.WeakMordellWeil

/-!
# The Mordell-Weil Theorem

The goal of this file is the **Mordell-Weil Theorem**: the group `E(K)` of `K`-rational
points of an elliptic curve `E` over a number field `K` is finitely generated. It comes in
three versions:

* `fg_point`: for `E` in short normal form over the fraction field `K` of a Dedekind domain,
  where `K` has admissible absolute values satisfying the Northcott property and the needed
  class-group and unit-group finiteness statements are taken as hypotheses;
* `fg_point_of_variableChange`: for an arbitrary `E` over such a `K`, given an admissible
  change of variables into short normal form (which exists whenever `2` and `3` are
  invertible in `K`), by transfer along the isomorphism of point groups from
  `Heights.ForMathlib.VariableChange`;
* `fg_point_of_numberField`: for an arbitrary `E` over a number field, where all hypotheses
  are theorems.

The proof is by descent (`AddCommGroup.fg_of_descent'`, in Mathlib): the Weak Mordell-Weil
Theorem of `Heights.EllipticCurve.WeakMordellWeil` provides the finiteness of `E(K)/2E(K)`,
and the naïve height `h(P) = logHeight (x(P))` provides the required height function. The
main technical step on the way, and the bulk of this file, is the *approximate parallelogram
law* `∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`
(`approx_parallelogram_law`), proved via the addition-and-multiplication map on
`x`-coordinates and the bounds on heights of images under tuples of homogeneous polynomials
from `Heights.MvPolynomial`. Together with the Northcott property it also yields the
finiteness of sets of points of bounded naïve height (`finite_naiveHeight_le`) and of the
torsion subgroup of `E(K)` (`finite_torsion`).
-/

/-
We work with affine points; this seems to be quite a bit less painful
than using projective points.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

/-!
### `sym2x` and the addition-and-multiplication map

We show that the following diagram commutes.

```
  Sym² W ∋ {P, Q} ↦ {P+Q, P-Q} ∈ Sym² W
     ↓ sym2x                        ↓ sym2x
     ℙ²       - addSubMap -→        ℙ²
```

We now assume that `W` is given by a short Weierstrass equation `y² = x³ + a * x + b` (`hW`)
and is smooth (`hab` is equivalent to the nonvanishing of the discriminant of `W`).
-/

--#40303

open MvPolynomial Nat

lemma den_duplication_eq {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have Heq := (W'.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq

lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔ y = W'.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only

variable {F : Type*} [Field F] {W : Affine F}

lemma den_duplication_ne_zero_or_num_duplication_ne_zero {x y : F} (h : W.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
  rw [equation_iff x y] at h₁
  by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! H
    rw [b₂, b₄, b₆] at H
    grobner

section Decidable

variable [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.Equation x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  rw [negY, show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h

lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
     W.addX xP xQ (W.slope xP xQ yP yQ) =
       ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2 := by
  have hxPQ' : xP - xQ ≠ 0 := by grind only
  simp [addX, slope, hn, div_pow]
  field

/-- We give an explicit expression for `xRep` of `P + P` when `2*P ≠ 0`. -/
lemma Point.xRep_add_self_of_Y_ne {x y : F} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]

/-- We give an explicit expression for `xRep` of `P + P` when `P ≠ 0` and `2*P = 0`. -/
lemma Point.xRep_add_self_of_Y_eq {x y : F} (h : W.Nonsingular x y) (hn : y = W.negY x y) :
    (some x y h + some x y h).xRep = ![1, 0] := by
  simp only [add_self_of_Y_eq hn, xRep_zero]

/-- We give an explicit expression for `xRep` of `P + Q` when `P ≠ ±Q`. -/
lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some, addX_of_X_ne hn]

/-- We give an explicit expression for `xRep` of `P - Q` when `P ≠ ±Q`. -/
lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 + W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ)
           - (W.a₂ + xP + xQ) * (xP - xQ) ^2) / (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn, xRep_some,
    addX_of_X_ne hn]
  grind only [negY]

end Decidable

lemma finite_preimage_xRep (x : F) : {P : W.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : W.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by ext : 1; simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) : {P : W.Point | P.xRep 0 = x}.Finite := by
  have : {P : W.Point | P.xRep 0 = x} ⊆ {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset this

-- end #40303

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.Point) :
    sym2x P P = fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some .. =>
    simp only [sym2x_some_some, succ_eq_add_one, reduceAdd, sym2x_some_zero, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, sym2x_zero_zero, one_smul, addSubMap]
    ext i : 1
    fin_cases i <;> simp
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [Hrs]
    by_cases! H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      refine ⟨_, H', ?_⟩
      simp [sym2x, Point.xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma Point.sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (addSubMap W i).eval <| sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, Point.sym2x_comm 0] using P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_comm _ Q] using Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some xP yP hP).sym2x (some xQ yQ hQ)) =
        ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
          2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
          (xP - xQ) ^ 2] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap]
      ring
    have : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 this, ?_⟩
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    rw [Hrs, sym2x, Point.xRep_add_of_X_ne hP hQ hxPQ, Point.xRep_sub_of_X_ne hP hQ hxPQ,
      b₂, b₄, b₆, b₈]
    ext i : 1
    fin_cases i <;> simp [field] <;> grobner

end Decidable

/-!
### The naïve height
-/

section AAV

open Height

variable [AdmissibleAbsValues F]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. => simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

/-- The "approximate parallelogram law" for the naïve height on an elliptic curve. -/
theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- speed up `grind` below by reducing to the essentials
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end AAV

section Northcott

open Height

variable [AdmissibleAbsValues F]

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable (W) in
/-- The set of `K`-points on `W` with naïve height bounded by `B` is finite.
This is an important ingredient for the *Mordell-Weil Theorem*. -/
lemma finite_naiveHeight_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  Northcott.finite_le B

variable [DecidableEq F] [W.toAffine.IsElliptic]

/-- The torsion subgroup of the group of `K`-rational point on an elliptic curve over a
number field `K` is finite. -/
theorem finite_torsion : Finite (AddCommGroup.torsion W.Point) := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.finite_torsion_of_descent' hC

/-- **The Mordell-Weil Theorem**, general version: `E(K)` is finitely generated, for an
elliptic curve `E` in short normal form over a field `K` such that
* `K` has admissible absolute values satisfying the Northcott property (so heights work);
* `K` is the fraction field of a Dedekind domain `R`; and
* for each irreducible factor `p` of the `2`-division polynomial of `E`, the integral closure
  of `R` in `K[X]/(p)` has finite class group and finitely generated unit group.

For `K` a number field all of these hold; see `fg_point_of_numberField`.

Note that the per-factor hypotheses cannot be replaced by the corresponding hypotheses on `R`
itself: by a theorem of Claborn, refined by Leedham-Green and by Clark
(*Elliptic Dedekind domains revisited*, Enseign. Math. 55 (2009)), **every** abelian group is
the class group of the integral closure of a PID in a separable *quadratic* field extension,
so `Finite (ClassGroup R)` gives no control over the class groups of the factors. (Whether
adding `Group.FG Rˣ` rescues the implication appears to be unknown; all known proofs of the
per-factor statements require `K` to be a global field.) -/
theorem fg_point (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [W.IsShortNF]
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
    [(p : W.f.Factors) → Group.FG (W.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have H₂ (P : W.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' (W.finite_index_range_nsmulAddMonoidHom_two R) H₂ hC

/-- **The Mordell-Weil Theorem** for an arbitrary Weierstrass curve: `E(K)` is finitely
generated, given an admissible change of variables `C` bringing `E` into short normal form,
together with the finiteness hypotheses of `fg_point` for the model `C • E`. The result is
transferred along the isomorphism of point groups `Point.equivVariableChange`.

Such a `C` exists whenever `2` and `3` are invertible in `K`
(`WeierstrassCurve.exists_variableChange_isShortNF`). Invertibility of `3` cannot be dropped:
in characteristic `3`, a short normal form has `c₄ = 0`, so a curve with `c₄ ≠ 0` admits no
such change of variables. -/
theorem fg_point_of_variableChange (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] (C : VariableChange F) [(C • W).IsShortNF]
    [(p : (C • W).toAffine.f.Factors) →
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor R p))]
    [(p : (C • W).toAffine.f.Factors) →
      Group.FG ((C • W).toAffine.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have := fg_point (W := (C • W).toAffine) R
  exact AddGroup.fg_of_surjective (f := (Point.equivVariableChange W C).toAddMonoidHom)
    (Point.equivVariableChange W C).surjective

end Northcott

section NumberField

open NumberField

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]

/-- **The Mordell-Weil Theorem**: the group `E(K)` of `K`-rational points of an elliptic
curve `E` over a number field `K` is finitely generated.

The curve is brought into short normal form by an admissible change of variables (possible
since `K` has characteristic `0`), and the finiteness hypotheses of `fg_point` for the
resulting model are the class number theorem and Dirichlet's unit theorem. -/
theorem fg_point_of_numberField : AddGroup.FG W.Point := by
  have := invertibleOfNonzero (two_ne_zero (α := F))
  have := invertibleOfNonzero (three_ne_zero (α := F))
  obtain ⟨C, hC⟩ := exists_variableChange_isShortNF (W := W)
  have (p : (C • W).toAffine.f.Factors) :
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)) :=
    NumberField.finite_classGroup_integralClosure F (AdjoinRoot (p : Polynomial F))
  have (p : (C • W).toAffine.f.Factors) :
      Group.FG ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)ˣ :=
    NumberField.fg_units_integralClosure F (AdjoinRoot (p : Polynomial F))
  exact fg_point_of_variableChange (𝓞 F) C

end NumberField

end WeierstrassCurve.Affine
