import Heights.Basic
import Mathlib

/-!
### Instance for rational function fields of one variable
-/

section ratfun

noncomputable
def NNReal.e : NNReal := ⟨Real.exp 1, Real.exp_nonneg 1⟩

lemma NNReal.e_ne_zero : e ≠ 0 := coe_ne_zero.mp <| Real.exp_ne_zero 1

lemma NNReal.one_lt_e : 1 < e := mod_cast Real.one_lt_exp_iff.mpr zero_lt_one

namespace RatFunc

open Height AdmissibleAbsValues WithZeroMulInt IsDedekindDomain

variable {K : Type*} [Field K]
variable {R : Type*} [Field R] [Algebra (Polynomial K) R] [IsFractionRing (Polynomial K) R]

private lemma zero_le_norm (v : HeightOneSpectrum (Polynomial K)) (x : R) :
    0 ≤ toNNReal (e := NNReal.e) NNReal.e_ne_zero (v.valuation _ x) :=
  zero_le

-- Need to modify this to take the degree into account!
private noncomputable
def vadicAbv_aux (v : HeightOneSpectrum (Polynomial K)) (x : R) : ℝ :=
  toNNReal (e := NNReal.e) NNReal.e_ne_zero (v.valuation _ x)

private
lemma vadicAbv_aux_add_le (v : HeightOneSpectrum (Polynomial K)) (x y : R) :
    vadicAbv_aux v (x + y) ≤ max (vadicAbv_aux v x) (vadicAbv_aux v y) := by
  simp only [vadicAbv_aux]
  norm_cast
  have h_mono := (toNNReal_strictMono NNReal.one_lt_e).monotone
  exact h_mono.map_max ▸ h_mono ((v.valuation _).map_add x y)

variable (R) in
/-- The `v`-adic absolute value on `RatFunc K` defined as `exp` of the `v`-adic
valuation. -/
noncomputable
def vadicAbv (v : HeightOneSpectrum (Polynomial K)) : AbsoluteValue R ℝ where
  toFun := vadicAbv_aux v
  map_mul' _ _ := by simp only [vadicAbv_aux, _root_.map_mul, NNReal.coe_mul]
  nonneg' _ := NNReal.zero_le_coe
  eq_zero' _ := by simp only [vadicAbv_aux, NNReal.coe_eq_zero, map_eq_zero]
  add_le' x y :=
    (vadicAbv_aux_add_le v x y).trans <| max_le_add_of_nonneg (zero_le_norm ..) (zero_le_norm ..)

lemma vadicAbv.add_le_max (v : HeightOneSpectrum (Polynomial K)) (x y : R) :
    vadicAbv R v (x + y) ≤ max (vadicAbv R v x) (vadicAbv R v y) :=
  vadicAbv_aux_add_le v x y

private noncomputable
def infiniteAbv_aux' (x : RatFunc K) : ℝ :=
  haveI : DecidableEq (RatFunc K) := Classical.decEq _
  if x = 0 then 0 else Real.exp x.intDegree

variable (K R) in
noncomputable
def Polynomial.isFractionRingToRatFuncEQuiv : R ≃+* RatFunc K :=
  ((RatFunc.toFractionRingRingEquiv K).trans
    (FractionRing.algEquiv (Polynomial K) R).toRingEquiv).symm

variable (K) in
private noncomputable
def infiniteAbv_aux (x : R) : ℝ :=
  infiniteAbv_aux' (Polynomial.isFractionRingToRatFuncEQuiv K R x)

private
lemma infiniteAbv_aux_add_le (x y : R) :
    infiniteAbv_aux K (x + y) ≤ max (infiniteAbv_aux K x) (infiniteAbv_aux K y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add] -- not sure why this is necessary here...
    simp
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]
    simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · set_option backward.isDefEq.respectTransparency false in -- temporary measure
    simp [infiniteAbv_aux, infiniteAbv_aux', hxy, hx, hy, -le_sup_iff]
    positivity
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  simp only [infiniteAbv_aux, infiniteAbv_aux', map_add, EmbeddingLike.map_eq_zero_iff, hx,
    ↓reduceIte, hy]
  have : (Polynomial.isFractionRingToRatFuncEQuiv K R) (x + y) ≠ 0 := by
    rwa [ne_eq, RingEquiv.map_eq_zero_iff]
  simp only [this, ↓reduceIte]
  rw [← Monotone.map_sup Real.exp_monotone, Real.exp_le_exp]
  norm_cast
  exact intDegree_add_le ((RingEquiv.map_ne_zero_iff _).mpr hy) <| by rwa [← map_add]

private
lemma zero_le_infiniteAbv_aux (x : R) : 0 ≤ infiniteAbv_aux K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · set_option backward.isDefEq.respectTransparency false in -- temporary measure
    simp [infiniteAbv_aux, infiniteAbv_aux']
  set_option backward.isDefEq.respectTransparency false in -- temporary measure
  simpa [infiniteAbv_aux, infiniteAbv_aux', hx] using Real.exp_nonneg _

variable (K R) in
/-- The absolute value at infinity on `RatFunc K`. -/
noncomputable
def infiniteAbv : AbsoluteValue R ℝ where
  toFun := infiniteAbv_aux K
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · set_option backward.isDefEq.respectTransparency false in -- temporary measure
      simp [infiniteAbv_aux, infiniteAbv_aux']
    rcases eq_or_ne y 0 with rfl | hy
    · set_option backward.isDefEq.respectTransparency false in -- temporary measure
      simp [infiniteAbv_aux, infiniteAbv_aux']
    set_option backward.isDefEq.respectTransparency false in -- temporary measure
    simp only [infiniteAbv_aux, infiniteAbv_aux', map_mul, mul_eq_zero,
      EmbeddingLike.map_eq_zero_iff, hx, hy, or_self, ↓reduceIte, ← Real.exp_add, Real.exp_eq_exp]
    norm_cast
    exact intDegree_mul ((RingEquiv.map_ne_zero_iff _).mpr hx)
      ((RingEquiv.map_ne_zero_iff _).mpr hy)
  nonneg' x := by
    rcases eq_or_ne x 0 with rfl | hx
    · set_option backward.isDefEq.respectTransparency false in -- temporary measure
      simp [infiniteAbv_aux, infiniteAbv_aux']
    set_option backward.isDefEq.respectTransparency false in -- temporary measure
    simp [infiniteAbv_aux, infiniteAbv_aux', hx, Real.exp_nonneg]
  eq_zero' x := by
    set_option backward.isDefEq.respectTransparency false in -- temporary measure
    rcases eq_or_ne x 0 with rfl | hx <;> simp [infiniteAbv_aux, infiniteAbv_aux']
  add_le' x y :=
    (infiniteAbv_aux_add_le x y).trans <|
      max_le_add_of_nonneg (zero_le_infiniteAbv_aux _) (zero_le_infiniteAbv_aux _)

lemma infiniteAbv.add_le_max (x y : R) :
    infiniteAbv K R (x + y) ≤ max (infiniteAbv K R x) (infiniteAbv K R y) :=
  infiniteAbv_aux_add_le x y

variable (R) in
open HeightOneSpectrum Ideal in
lemma vadicAbv.mulSupport_finite_polynomial {x : Polynomial K} (hx : x ≠ 0) :
    (vadicAbv (K := K) R · (algebraMap (Polynomial K) R x)).mulSupport.Finite := by
  have (v : HeightOneSpectrum <| Polynomial K) :
      vadicAbv R v (algebraMap (Polynomial K) R x) ≠ 1 ↔
        vadicAbv R v (algebraMap (Polynomial K) R x) < 1 := by
    simp only [vadicAbv, AbsoluteValue.coe_mk, MulHom.coe_mk, vadicAbv_aux, ne_eq,
      NNReal.coe_eq_one, NNReal.coe_lt_one, ne_iff_lt_iff_le, v.valuation_of_algebraMap x]
    exact (toNNReal_le_one_iff NNReal.one_lt_e).mpr <| v.intValuation_le_one x
  have H (v : HeightOneSpectrum <| Polynomial K) :
      (vadicAbv R v) ((algebraMap (Polynomial K) R) x) < 1 ↔ x ∈ v.asIdeal := by
    simp only [vadicAbv, AbsoluteValue.coe_mk, MulHom.coe_mk, vadicAbv_aux, NNReal.coe_lt_one]
    rw [WithZeroMulInt.toNNReal_lt_one_iff NNReal.one_lt_e, valuation_of_algebraMap,
      intValuation_lt_one_iff_dvd]
    exact dvd_span_singleton
  simp_rw [Function.mulSupport, this, H, ← Ideal.dvd_span_singleton]
  apply Ideal.finite_factors
  simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, hx, not_false_eq_true]

variable (K R) in
lemma vadicAbv.mulSupport_finite {x : R} (hx : x ≠ 0) :
    (vadicAbv (K := K) R · x).mulSupport.Finite  := by
  rcases IsFractionRing.div_surjective (A := Polynomial K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  refine ((vadicAbv.mulSupport_finite_polynomial R hx.1).union
    (vadicAbv.mulSupport_finite_polynomial R hx.2)).subset fun _ ↦ ?_
  simp only [Function.mem_mulSupport, ne_eq, Set.mem_union]
  contrapose!
  simp +contextual



noncomputable
instance instRatFunc : AdmissibleAbsValues (RatFunc K) where
  archAbsVal := {}
  nonarchAbsVal := insert (infiniteAbv K (RatFunc K)) <| Set.range (vadicAbv (RatFunc K))
  isNonarchimedean v hv x y := by
    simp only [Set.mem_insert_iff, Set.mem_range] at hv
    obtain rfl | ⟨I, rfl⟩ := hv
    · exact infiniteAbv.add_le_max x y
    · exact vadicAbv.add_le_max (K := K) I x y
  hasFiniteMulSupport {x} hx := by
    rw [Function.HasFiniteMulSupport,
      ← Set.finite_image_iff (f := Subtype.val) (Set.injOn_subtype_val)]
    refine Set.Finite.subset (s := insert (infiniteAbv K (RatFunc K)) ?_) (Set.Finite.insert _ ?_) ?_
    · exact vadicAbv (K := K) (RatFunc K) '' Function.mulSupport (vadicAbv (RatFunc K) · x)
    · exact Set.Finite.image (vadicAbv (RatFunc K)) <| vadicAbv.mulSupport_finite K (RatFunc K) hx
    · aesop
  product_formula := sorry

end RatFunc

end ratfun
