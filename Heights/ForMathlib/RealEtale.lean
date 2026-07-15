import Mathlib
import Heights.ForMathlib.Basic

/-!
# Real étale algebras: the sign decomposition of `ℝ[X]/f`

For a monic squarefree real polynomial `f`, the étale `ℝ`-algebra `ℝ[X]/f` is a product of
copies of `ℝ` (one per real root) and of `ℂ` (one per irreducible quadratic factor), and the
square classes of its units are the sign patterns at the real roots. This file develops that
picture as reusable building blocks (used by the real-place analysis of the 2-Selmer group, and
intended to generalize to the descent maps of hyperelliptic curves and their Jacobians).

## Main definitions

* `Units.modPow.realSign` and `Units.modPow.realEquivOfEven`: the sign homomorphism
  `ℝˣ →* Multiplicative (ZMod 2)`, and the resulting isomorphism
  `Units.modPow ℝ n ≃* Multiplicative (ZMod 2)` for even `n ≠ 0`
  (`Units.modPow.subsingleton_real_of_odd` for odd `n`).
* `Polynomial.evalUpperEquiv`: for an irreducible real quadratic `p`, evaluation at the root
  with positive imaginary part gives `AdjoinRoot p ≃ₐ[ℝ] ℂ`.
* `Polynomial.etaleEquiv`: the evaluation isomorphism
  `AdjoinRoot f ≃ₐ[ℝ] ({x // f.eval x = 0} → ℝ) × ({p : f.Factors // (p).natDegree = 2} → ℂ)`.
* `Polynomial.modPowEtaleEquiv`: the induced
  `Units.modPow (AdjoinRoot f) 2 ≃* ({x // f.eval x = 0} → Multiplicative (ZMod 2))`.

## Main statements

* `Polynomial.mk_eq_one_iff_forall_eval_nonneg`: the square class of a unit of `ℝ[X]/f` is
  trivial exactly when its value at every real root of `f` is nonnegative.
-/
open Polynomial Complex

noncomputable section

open scoped Classical

namespace Units.modPow

/-- The sign homomorphism on the units of `ℝ`, valued in `Multiplicative (ZMod 2)`:
`ofAdd 0` for positive units, `ofAdd 1` for negative ones. -/
def realSign : ℝˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (if 0 < (u : ℝ) then 0 else 1)
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add]
    refine congrArg _ ?_
    rw [Units.val_mul]
    rcases lt_or_gt_of_ne u.ne_zero with hu | hu <;> rcases lt_or_gt_of_ne v.ne_zero with hv | hv
    · rw [if_neg (asymm hu), if_neg (asymm hv), if_pos (mul_pos_of_neg_of_neg hu hv)]; decide
    · rw [if_neg (asymm hu), if_pos hv, if_neg (asymm (mul_neg_of_neg_of_pos hu hv))]; decide
    · rw [if_pos hu, if_neg (asymm hv), if_neg (asymm (mul_neg_of_pos_of_neg hu hv))]; decide
    · rw [if_pos hu, if_pos hv, if_pos (mul_pos hu hv)]; decide

lemma realSign_surjective : Function.Surjective realSign := by
  have key : ∀ y : Multiplicative (ZMod 2), y ≠ 1 → Multiplicative.ofAdd (1 : ZMod 2) = y := by
    decide
  intro y
  rcases eq_or_ne y 1 with rfl | hy
  · exact ⟨1, map_one _⟩
  · refine ⟨-1, ?_⟩
    rw [realSign, MonoidHom.coe_mk, OneHom.coe_mk, if_neg (by norm_num)]
    exact key y hy

variable {n : ℕ}

-- The `n`-th powers of `ℝˣ` are exactly the positive units, when `n` is even and nonzero.
lemma range_powMonoidHom_real_eq_ker_realSign (hn : n ≠ 0) (he : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = realSign.ker := by
  ext u
  simp only [MonoidHom.mem_range, powMonoidHom_apply, MonoidHom.mem_ker]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨r, rfl⟩ := he
    rw [map_pow, pow_add, ← sq]
    exact (by decide : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1) _
  · intro h
    have hu : 0 < (u : ℝ) := by
      by_contra hc
      rw [realSign, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hc, ofAdd_eq_one] at h
      exact one_ne_zero h
    refine ⟨Units.mk0 ((u : ℝ) ^ (n⁻¹ : ℝ)) (Real.rpow_pos_of_pos hu _).ne', ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hu.le hn]

/-- **Block 1 (even case).** For even nonzero `n`, the group of `n`-th power classes of real
units is `Multiplicative (ZMod 2)`, via the sign. -/
def realEquivOfEven (hn : n ≠ 0) (he : Even n) :
    Units.modPow ℝ n ≃* Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (range_powMonoidHom_real_eq_ker_realSign hn he)).trans
    (QuotientGroup.quotientKerEquivOfSurjective realSign realSign_surjective)

/-- **Block 1 (odd case).** For odd `n`, every real unit is an `n`-th power, so the group of
`n`-th power classes of real units is trivial. -/
lemma subsingleton_real_of_odd (ho : Odd n) : Subsingleton (Units.modPow ℝ n) := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  refine subsingleton_of_forall_exists_pow fun u ↦ ?_
  rcases lt_or_gt_of_ne u.ne_zero with hu | hu
  · refine ⟨Units.mk0 (-((-(u : ℝ)) ^ (n⁻¹ : ℝ)))
      (neg_ne_zero.mpr (Real.rpow_pos_of_pos (by linarith) _).ne'), ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Odd.neg_pow ho,
      Real.rpow_inv_natCast_pow (by linarith) hn]
    ring
  · refine ⟨Units.mk0 ((u : ℝ) ^ (n⁻¹ : ℝ)) (Real.rpow_pos_of_pos hu _).ne', ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hu.le hn]

end Units.modPow

namespace Polynomial

variable {p : ℝ[X]} (hp : Irreducible p) (hd : p.natDegree = 2)

/-- A complex root of an irreducible real quadratic in the open upper half-plane:
the chosen root with positive imaginary part. -/
def upperRoot : ℂ :=
  let z := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose
  if 0 < z.im then z else starRingEnd ℂ z

include hp in
lemma aeval_upperRoot : aeval (upperRoot hp) p = 0 := by
  have hz := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose_spec
  rw [upperRoot]
  split_ifs with h
  · exact hz
  · rw [aeval_conj, hz, map_zero]

-- No irreducible real quadratic has a real root, so every complex root is non-real.
include hp hd in
lemma im_ne_zero_of_aeval_eq_zero {z : ℂ} (hz : aeval z p = 0) : z.im ≠ 0 := by
  intro him
  have hz' : z = algebraMap ℝ ℂ z.re := Complex.ext (by simp) (by simp [him])
  rw [hz', aeval_algebraMap_apply, map_eq_zero] at hz
  exact hp.not_isRoot_of_natDegree_ne_one (by omega) hz

include hp hd in
lemma upperRoot_im_pos : 0 < (upperRoot hp).im := by
  have hz := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose_spec
  have hne := im_ne_zero_of_aeval_eq_zero hp hd hz
  rw [upperRoot]
  split_ifs with h
  · exact h
  · rw [Complex.conj_im]
    exact neg_pos.mpr ((not_lt.mp h).lt_of_ne hne)

lemma finrank_adjoinRoot (hp0 : p ≠ 0) : Module.finrank ℝ (AdjoinRoot p) = p.natDegree := by
  have h := (AdjoinRoot.powerBasis hp0).finrank
  rwa [AdjoinRoot.powerBasis_dim hp0] at h

/-- Evaluation at the upper-half-plane root: an `ℝ`-algebra hom `ℝ[X]/p → ℂ`. -/
def evalUpperHom : AdjoinRoot p →ₐ[ℝ] ℂ :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId ℝ ℂ) (upperRoot hp)
    (by have := aeval_upperRoot hp; simpa [aeval_def] using this)

include hp in
lemma evalUpperHom_injective : Function.Injective (evalUpperHom hp) :=
  have : Fact (Irreducible p) := ⟨hp⟩
  (evalUpperHom hp).toRingHom.injective

/-- Evaluation at the upper-half-plane root gives an `ℝ`-algebra isomorphism `ℝ[X]/p ≃ ℂ`
for an irreducible real quadratic `p`. -/
def evalUpperEquiv : AdjoinRoot p ≃ₐ[ℝ] ℂ :=
  have : Fact (Irreducible p) := ⟨hp⟩
  AlgEquiv.ofBijective (evalUpperHom hp) ⟨evalUpperHom_injective hp, by
    have hsurj : Function.Surjective ⇑(evalUpperHom hp).toLinearMap := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj (evalUpperHom_injective hp), finrank_adjoinRoot hp.ne_zero,
        hd, Complex.finrank_real_complex]
    exact hsurj⟩

/-! ### The evaluation isomorphism `ℝ[X]/f ≃ ∏ℝ × ∏ℂ` -/

variable {f : ℝ[X]}

/-- The evaluation tuple: each real root to itself, each degree-2 factor to its upper root. -/
def etaleTuple (f : ℝ[X]) :
    ({x : ℝ // f.eval x = 0} → ℝ) × ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) :=
  (fun x ↦ (x : ℝ), fun p ↦ upperRoot p.1.irreducible)

-- The real-root component of `aeval (etaleTuple f) q` is `q.eval x`.
lemma aeval_etaleTuple_fst (q : ℝ[X]) (x : {x : ℝ // f.eval x = 0}) :
    (aeval (etaleTuple f) q).1 x = q.eval (x : ℝ) := by
  have h := aeval_algHom_apply
    ((Pi.evalAlgHom ℝ (fun _ : {x : ℝ // f.eval x = 0} ↦ ℝ) x).comp (AlgHom.fst ℝ _ _))
    (etaleTuple f) q
  simp only [AlgHom.comp_apply, AlgHom.fst_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  show aeval ((etaleTuple f).1 x) q = q.eval (x : ℝ)
  simp [etaleTuple, aeval_def, eval₂_id]

-- The degree-2-factor component of `aeval (etaleTuple f) q` is the value at the upper root.
lemma aeval_etaleTuple_snd (q : ℝ[X]) (p : {p : f.Factors // (p : ℝ[X]).natDegree = 2}) :
    (aeval (etaleTuple f) q).2 p = aeval (upperRoot p.1.irreducible) q := by
  have h := aeval_algHom_apply
    ((Pi.evalAlgHom ℝ (fun _ : {p : f.Factors // (p : ℝ[X]).natDegree = 2} ↦ ℂ) p).comp
      (AlgHom.snd ℝ _ _)) (etaleTuple f) q
  simp only [AlgHom.comp_apply, AlgHom.snd_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  rfl

lemma aeval_etaleTuple : aeval (etaleTuple f) f = 0 := by
  have h1 : (aeval (etaleTuple f) f).1 = 0 := by
    funext x; rw [Pi.zero_apply, aeval_etaleTuple_fst]; exact x.2
  have h2 : (aeval (etaleTuple f) f).2 = 0 := by
    funext p
    rw [Pi.zero_apply, aeval_etaleTuple_snd]
    have hd : aeval (upperRoot p.1.irreducible) (p.1 : ℝ[X]) ∣
        aeval (upperRoot p.1.irreducible) f := _root_.map_dvd _ p.1.dvd
    rw [aeval_upperRoot] at hd
    exact zero_dvd_iff.mp hd
  exact Prod.ext h1 h2

/-- Evaluation as an `ℝ`-algebra hom `ℝ[X]/f → (real roots → ℝ) × (degree-2 factors → ℂ)`. -/
def etaleEvalHom (f : ℝ[X]) :
    AdjoinRoot f →ₐ[ℝ]
      ({x : ℝ // f.eval x = 0} → ℝ) × ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId ℝ _) (etaleTuple f) (by
    have := aeval_etaleTuple (f := f); rwa [aeval_def] at this)

lemma etaleEvalHom_mk (q : ℝ[X]) : etaleEvalHom f (AdjoinRoot.mk f q) = aeval (etaleTuple f) q := by
  rw [etaleEvalHom, AdjoinRoot.liftAlgHom_mk, Algebra.toRingHom_ofId, ← aeval_def]

@[simp] lemma etaleEvalHom_mk_fst (q : ℝ[X]) (x : {x : ℝ // f.eval x = 0}) :
    (etaleEvalHom f (AdjoinRoot.mk f q)).1 x = q.eval (x : ℝ) := by
  rw [etaleEvalHom_mk, aeval_etaleTuple_fst]

@[simp] lemma etaleEvalHom_mk_snd (q : ℝ[X]) (p : {p : f.Factors // (p : ℝ[X]).natDegree = 2}) :
    (etaleEvalHom f (AdjoinRoot.mk f q)).2 p = aeval (upperRoot p.1.irreducible) q := by
  rw [etaleEvalHom_mk, aeval_etaleTuple_snd]

-- Each irreducible factor of `f` divides any `q` that vanishes at all the evaluation points.
lemma etaleEvalHom_injective (hf : f ≠ 0) (hsq : Squarefree f) :
    Function.Injective (etaleEvalHom f) := by
  have : Finite f.Factors := Factors.finite hf
  have : Fintype f.Factors := Fintype.ofFinite _
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [AdjoinRoot.mk_eq_zero]
  have hfac (p : f.Factors) : (p : ℝ[X]) ∣ q := by
    rcases eq_or_ne (p : ℝ[X]).natDegree 1 with h1 | h1
    · set x₀ := -(p : ℝ[X]).coeff 0 with hx0
      have hpx : (p : ℝ[X]) = X - C x₀ := by
        conv_lhs => rw [p.monic.eq_X_add_C h1]
        rw [hx0, map_neg, sub_neg_eq_add]
      have hroot : f.eval x₀ = 0 :=
        eval_eq_zero_of_dvd_of_eval_eq_zero p.dvd (by rw [hpx]; simp)
      have hq : q.eval x₀ = 0 := by
        have h := congrArg (·.1 ⟨x₀, hroot⟩) ha
        simpa using h
      rw [hpx]
      exact dvd_iff_isRoot.mpr hq
    · have hd2 : (p : ℝ[X]).natDegree = 2 := by
        have h0 := p.irreducible.natDegree_pos
        have h2 := p.irreducible.natDegree_le_two
        omega
      have hq : aeval (upperRoot p.irreducible) q = 0 := by
        have h := congrArg (·.2 ⟨p, hd2⟩) ha
        simpa using h
      rw [minpoly.eq_of_irreducible_of_monic p.irreducible (aeval_upperRoot p.irreducible) p.monic]
      exact minpoly.dvd ℝ _ hq
  exact ((Factors.associated_prod hf hsq).symm.dvd).trans
    (Fintype.prod_dvd_of_coprime (fun _ _ hab ↦ Factors.isCoprime hab) hfac)

lemma sum_natDegree_factors [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    ∑ p : f.Factors, (p : ℝ[X]).natDegree = f.natDegree := by
  rw [← natDegree_prod _ _ fun p _ ↦ p.ne_zero]
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (Factors.associated_prod hf hsq))

-- `#{real roots} + 2·#{degree-2 factors} = deg f`.
open Finset in
lemma card_realRoots_add_card_deg2 [Fintype {x : ℝ // f.eval x = 0}] [Fintype f.Factors]
    [Fintype {p : f.Factors // (p : ℝ[X]).natDegree = 2}] (hf : f ≠ 0) (hsq : Squarefree f) :
    Fintype.card {x : ℝ // f.eval x = 0} +
      Fintype.card {p : f.Factors // (p : ℝ[X]).natDegree = 2} * 2 = f.natDegree := by
  have hsum : ∑ p : f.Factors, (p : ℝ[X]).natDegree
      = ∑ p : f.Factors, if (p : ℝ[X]).natDegree = 1 then (1 : ℕ) else 2 :=
    Finset.sum_congr rfl fun p _ ↦ by
      have h0 := p.irreducible.natDegree_pos; have h2 := p.irreducible.natDegree_le_two
      split_ifs with h <;> omega
  have hfilter : Finset.univ.filter (fun p : f.Factors ↦ ¬ (p : ℝ[X]).natDegree = 1)
      = Finset.univ.filter (fun p : f.Factors ↦ (p : ℝ[X]).natDegree = 2) :=
    filter_congr fun p _ ↦ by
      have h0 := p.irreducible.natDegree_pos; have h2 := p.irreducible.natDegree_le_two
      omega
  rw [Fintype.card_congr Factors.linearEquivRoots.symm, Fintype.card_subtype,
    Fintype.card_subtype, ← sum_natDegree_factors hf hsq, hsum, Finset.sum_ite, hfilter,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one]

open Finset in
lemma finrank_etaleTarget (hf : f ≠ 0) (hsq : Squarefree f) :
    Module.finrank ℝ (({x : ℝ // f.eval x = 0} → ℝ) ×
      ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ)) = f.natDegree := by
  have : Finite {x : ℝ // f.eval x = 0} := (finite_setOf_isRoot hf).to_subtype
  have : Fintype {x : ℝ // f.eval x = 0} := Fintype.ofFinite _
  have : Finite f.Factors := Factors.finite hf
  have : Fintype f.Factors := Fintype.ofFinite _
  have : Fintype {p : f.Factors // (p : ℝ[X]).natDegree = 2} := Fintype.ofFinite _
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  exact card_realRoots_add_card_deg2 hf hsq

/-- **Block 2.** For nonzero squarefree `f`, evaluation gives an `ℝ`-algebra isomorphism
`ℝ[X]/f ≃ (real roots → ℝ) × (degree-2 factors → ℂ)`. -/
def etaleEquiv (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[ℝ]
      ({x : ℝ // f.eval x = 0} → ℝ) × ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) :=
  have : Finite {x : ℝ // f.eval x = 0} := (finite_setOf_isRoot hf).to_subtype
  have : Fintype {x : ℝ // f.eval x = 0} := Fintype.ofFinite _
  have : Finite f.Factors := Factors.finite hf
  have : Fintype f.Factors := Fintype.ofFinite _
  have : Fintype {p : f.Factors // (p : ℝ[X]).natDegree = 2} := Fintype.ofFinite _
  AlgEquiv.ofBijective (etaleEvalHom f) ⟨etaleEvalHom_injective hf hsq, by
    have hsurj : Function.Surjective ⇑(etaleEvalHom f).toLinearMap := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj (etaleEvalHom_injective hf hsq), finrank_adjoinRoot hf,
        finrank_etaleTarget hf hsq]
    exact hsurj⟩

end Polynomial

namespace Units.modPow

open QuotientGroup

/-- The isomorphism between the `n`-th power classes of units of a product and the product of
the `n`-th power classes; the binary analogue of `mulEquivPiModRangePowMonoidHom`. -/
def mulEquivProdModRangePow (G H : Type*) [CommGroup G] [CommGroup H] (n : ℕ) :
    (G × H) ⧸ (powMonoidHom n).range ≃*
      (G ⧸ (powMonoidHom n).range) × (H ⧸ (powMonoidHom n).range) :=
  let φ : (G × H) →* (G ⧸ (powMonoidHom n).range) × (H ⧸ (powMonoidHom n).range) :=
    (mk' _).prodMap (mk' _)
  liftEquiv (φ := φ) _
    (fun y ↦ ⟨(Quotient.out y.1, Quotient.out y.2), Prod.ext (by simp [φ]) (by simp [φ])⟩) <| by
    ext ⟨g, h⟩
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    show (∃ w, w ^ n = (g, h)) ↔ ((mk' _ g, mk' _ h) : _ × _) = 1
    rw [Prod.mk_eq_one]
    simp only [mk'_apply, eq_one_iff, MonoidHom.mem_range, powMonoidHom_apply]
    exact ⟨fun ⟨w, hw⟩ ↦ ⟨⟨w.1, congrArg Prod.fst hw⟩, ⟨w.2, congrArg Prod.snd hw⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

/-- Taking `n`-th power classes of units commutes with binary products. -/
def prodEquiv (A B : Type*) [CommMonoid A] [CommMonoid B] (n : ℕ) :
    Units.modPow (A × B) n ≃* Units.modPow A n × Units.modPow B n :=
  (congrRangePowMonoidHom MulEquiv.prodUnits n).trans (mulEquivProdModRangePow Aˣ Bˣ n)

end Units.modPow

namespace Polynomial

variable {f : ℝ[X]}

/-- **Block 3.** The square classes of units of `ℝ[X]/f` (for `f` nonzero squarefree) are the
sign patterns at the real roots of `f`: `Units.modPow (ℝ[X]/f) 2` is the power of
`Multiplicative (ZMod 2)` indexed by the real roots (the complex factors contribute nothing). -/
def modPowEtaleEquiv (hf : f ≠ 0) (hsq : Squarefree f) :
    Units.modPow (AdjoinRoot f) 2 ≃* ({x : ℝ // f.eval x = 0} → Multiplicative (ZMod 2)) :=
  have : Subsingleton (Units.modPow ℂ 2) := Units.modPow.subsingleton_of_isAlgClosed ℂ two_ne_zero
  have : Subsingleton (Units.modPow ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) 2) :=
    (Units.modPow.piEquiv (fun _ : {p : f.Factors // (p : ℝ[X]).natDegree = 2} ↦ ℂ)
      2).toEquiv.subsingleton_congr.mpr inferInstance
  have : Unique (Units.modPow ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) 2) :=
    uniqueOfSubsingleton 1
  (Units.modPow.congr (etaleEquiv hf hsq).toMulEquiv 2).trans <|
    (Units.modPow.prodEquiv _ _ 2).trans <|
      (MulEquiv.prodCongr
        ((Units.modPow.piEquiv (fun _ : {x : ℝ // f.eval x = 0} ↦ ℝ) 2).trans
          (MulEquiv.piCongrRight fun _ ↦ Units.modPow.realEquivOfEven two_ne_zero even_two))
        (MulEquiv.refl _)).trans
      MulEquiv.prodUnique

end Polynomial

namespace Units.modPow

/-- A real unit's square class is trivial exactly when the unit is nonnegative. -/
lemma realSign_eq_one_iff (u : ℝˣ) : realSign u = 1 ↔ 0 ≤ (u : ℝ) := by
  show Multiplicative.ofAdd (if 0 < (u : ℝ) then (0 : ZMod 2) else 1) = 1 ↔ 0 ≤ (u : ℝ)
  rw [ofAdd_eq_one]
  split_ifs with h
  · exact iff_of_true rfl h.le
  · exact iff_of_false (by decide) (not_le.mpr ((not_lt.mp h).lt_of_ne u.ne_zero))

end Units.modPow

namespace Polynomial

variable {f : ℝ[X]}

/-- At a real root `x`, the square class of a unit `a` of `ℝ[X]/f` is trivial exactly when its
value `a(x)` there is nonnegative. -/
lemma modPowEtaleEquiv_mk_apply (hf : f ≠ 0) (hsq : Squarefree f) {a : AdjoinRoot f}
    (ha : IsUnit a) (x : {x : ℝ // f.eval x = 0}) :
    modPowEtaleEquiv hf hsq (QuotientGroup.mk ha.unit) x = 1 ↔ 0 ≤ (etaleEvalHom f a).1 x := by
  rw [show modPowEtaleEquiv hf hsq (QuotientGroup.mk ha.unit) x
        = Units.modPow.realSign (Units.map
            ((Pi.evalMonoidHom (fun _ ↦ ℝ) x).comp (MonoidHom.fst _ _))
            (Units.mapEquiv (etaleEquiv hf hsq).toMulEquiv ha.unit)) from rfl,
    Units.modPow.realSign_eq_one_iff]
  simp only [Units.coe_map, MonoidHom.coe_comp, Function.comp_apply, Pi.evalMonoidHom_apply,
    MonoidHom.coe_fst, Units.coe_mapEquiv, IsUnit.unit_spec]
  rfl

/-- **The sign characterization** (from Block 3): the square class of a unit `a` of `ℝ[X]/f`
is trivial exactly when its value at every real root of `f` is nonnegative. -/
lemma mk_eq_one_iff_forall_eval_nonneg (hf : f ≠ 0) (hsq : Squarefree f) {a : AdjoinRoot f}
    (ha : IsUnit a) :
    (QuotientGroup.mk ha.unit : Units.modPow (AdjoinRoot f) 2) = 1 ↔
      ∀ x : {x : ℝ // f.eval x = 0}, 0 ≤ (etaleEvalHom f a).1 x := by
  rw [← map_eq_one_iff (modPowEtaleEquiv hf hsq) (modPowEtaleEquiv hf hsq).injective, funext_iff]
  exact forall_congr' fun x ↦ by
    rw [Pi.one_apply]; exact modPowEtaleEquiv_mk_apply hf hsq ha x

end Polynomial

namespace Polynomial

/-- The minimal polynomial over `ℝ` of a non-real complex number has degree `2`. -/
lemma minpoly_complex_natDegree_eq_two {z : ℂ} (hz : z.im ≠ 0) : (minpoly ℝ z).natDegree = 2 := by
  have hint : IsIntegral ℝ z := Algebra.IsIntegral.isIntegral z
  refine le_antisymm (minpoly.irreducible hint).natDegree_le_two ?_
  by_contra h
  interval_cases hdeg : (minpoly ℝ z).natDegree
  · exact absurd hdeg (minpoly.natDegree_pos hint).ne'
  · obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one ℝ z
      (by rw [degree_eq_natDegree (minpoly.ne_zero hint), hdeg]; rfl)
    exact hz (by rw [← hr]; simp)

/-- The minimal polynomial over `ℝ` of a non-real `z`, mapped to `ℂ`, is `(X - z̄)(X - z)`. -/
lemma map_minpoly_complex {z : ℂ} (hz : z.im ≠ 0) :
    (minpoly ℝ z).map (algebraMap ℝ ℂ) = (X - C (starRingEnd ℂ z)) * (X - C z) := by
  have hint : IsIntegral ℝ z := Algebra.IsIntegral.isIntegral z
  have hdvd := (minpoly ℝ z).mul_star_dvd_of_aeval_eq_zero_im_ne_zero (minpoly.aeval ℝ z) hz
  have hm2 : ((minpoly ℝ z).map (algebraMap ℝ ℂ)).Monic := (minpoly.monic hint).map _
  have hpm : ((X - C (starRingEnd ℂ z)) * (X - C z)).Monic :=
    (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hdeg : ((X - C (starRingEnd ℂ z)) * (X - C z)).natDegree
      = ((minpoly ℝ z).map (algebraMap ℝ ℂ)).natDegree := by
    rw [natDegree_map, minpoly_complex_natDegree_eq_two hz,
      natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C, natDegree_X_sub_C]
  exact (eq_of_monic_of_associated hpm hm2
    (associated_of_dvd_of_natDegree_le hdvd hm2.ne_zero hdeg.ge)).symm

/-- The complex roots of the minimal polynomial over `ℝ` of a non-real `z` are `z` and `z̄`. -/
lemma root_minpoly_complex_eq {z w : ℂ} (hz : z.im ≠ 0) (hw : aeval w (minpoly ℝ z) = 0) :
    w = z ∨ w = starRingEnd ℂ z := by
  rw [aeval_def, ← eval_map, map_minpoly_complex hz] at hw
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hw
  tauto

variable {f : ℝ[X]}

/-- The degree-2 factors of a real polynomial `f` correspond to the roots of `f` in the open
upper half-plane, via `upperRoot` (with inverse the real minimal polynomial). -/
def deg2FactorEquivUpperRoots :
    {p : f.Factors // (p : ℝ[X]).natDegree = 2} ≃ {z : ℂ // aeval z f = 0 ∧ 0 < z.im} where
  toFun p := ⟨upperRoot p.1.irreducible,
    (by have h : aeval (upperRoot p.1.irreducible) (p.1 : ℝ[X]) ∣
          aeval (upperRoot p.1.irreducible) f := _root_.map_dvd _ p.1.dvd
        rw [aeval_upperRoot] at h; exact zero_dvd_iff.mp h),
    upperRoot_im_pos p.1.irreducible p.2⟩
  invFun z :=
    have hint : IsIntegral ℝ (z : ℂ) := Algebra.IsIntegral.isIntegral _
    ⟨⟨minpoly ℝ (z : ℂ), minpoly.monic hint, minpoly.irreducible hint, minpoly.dvd ℝ _ z.2.1⟩,
      minpoly_complex_natDegree_eq_two z.2.2.ne'⟩
  left_inv p := Subtype.ext (Subtype.ext
    (minpoly.eq_of_irreducible_of_monic p.1.irreducible (aeval_upperRoot p.1.irreducible)
      p.1.monic).symm)
  right_inv z := by
    refine Subtype.ext ?_
    have him : (z : ℂ).im ≠ 0 := z.2.2.ne'
    have hirr := minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := ℝ) (z : ℂ))
    rcases root_minpoly_complex_eq him (aeval_upperRoot hirr) with h | h
    · exact h
    · exfalso
      have hpos : 0 < (starRingEnd ℂ (z : ℂ)).im :=
        h ▸ upperRoot_im_pos hirr (minpoly_complex_natDegree_eq_two him)
      rw [Complex.conj_im] at hpos
      linarith [z.2.2]

end Polynomial

/-! ### Block 4: the norm on a product algebra -/

/-- **Block 4 (product).** The `R`-norm on a product algebra is the product of the norms. -/
theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : Algebra.lmul R (A × B) x = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2)) := by
    ext <;> simp
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, h, LinearMap.det_prodMap]

/-- **Block 4 (finite product).** The `R`-norm on `ι → S` is the product of the norms. -/
theorem Algebra.norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : Type*} [CommRing S]
    [Algebra R S] [Module.Free R S] [Module.Finite R S] (g : ι → S) :
    Algebra.norm R g = ∏ i, Algebra.norm R (g i) := by
  classical
  rw [Algebra.norm_apply]
  have h : Algebra.lmul R (ι → S) g
      = LinearMap.pi (fun i ↦ (Algebra.lmul R S (g i)).comp (LinearMap.proj i)) := by
    ext x j; simp [Algebra.lmul]
  rw [h, LinearMap.det_pi]
  simp_rw [← Algebra.norm_apply]

namespace Polynomial

variable {f : ℝ[X]}

/-- **Block 4 (étale algebra).** The `ℝ`-norm of an element of `ℝ[X]/f` is the product of its
values at the real roots times the product of the `normSq` (nonnegative!) of its values at the
upper roots — the product of the component norms under `etaleEquiv`. -/
lemma norm_etale [Fintype {x : ℝ // f.eval x = 0}]
    [Fintype {p : f.Factors // (p : ℝ[X]).natDegree = 2}] (hf : f ≠ 0) (hsq : Squarefree f)
    (a : AdjoinRoot f) :
    Algebra.norm ℝ a
      = (∏ x : {x : ℝ // f.eval x = 0}, (etaleEquiv hf hsq a).1 x)
        * ∏ p : {p : f.Factors // (p : ℝ[X]).natDegree = 2},
            ((etaleEquiv hf hsq a).2 p).normSq := by
  rw [← Algebra.norm_eq_of_algEquiv (etaleEquiv hf hsq) a, Algebra.norm_prod, Algebra.norm_pi,
    Algebra.norm_pi]
  congr 1
  · exact Finset.prod_congr rfl fun x _ ↦ by rw [Algebra.norm_self]; rfl
  · exact Finset.prod_congr rfl fun p _ ↦ Algebra.norm_complex_apply _

end Polynomial

/-! ### Block 5: the norm as a product of signs -/

namespace Units.modPow

/-- Two real units with the same sign have the same square class. -/
lemma realSign_congr {u v : ℝˣ} (h : 0 < (u : ℝ) ↔ 0 < (v : ℝ)) : realSign u = realSign v := by
  show Multiplicative.ofAdd (if 0 < (u : ℝ) then _ else _) = Multiplicative.ofAdd _
  rw [if_congr h rfl rfl]

@[simp] lemma realEquivOfEven_mk {n : ℕ} (hn : n ≠ 0) (he : Even n) (u : ℝˣ) :
    realEquivOfEven hn he (QuotientGroup.mk u) = realSign u := rfl

end Units.modPow

namespace Polynomial

variable {f : ℝ[X]}

/-- **Block 5.** Under the sign decomposition, the norm map on square classes corresponds to the
product of the entries: `realEquiv (normM (mk a)) = ∏_x modPowEtaleEquiv (mk a) x`. The complex
factors contribute the (positive) `normSq`, so only the real-root signs survive. -/
lemma normM_eq_prod_modPowEtale [Fintype {x : ℝ // f.eval x = 0}]
    [Fintype {p : f.Factors // (p : ℝ[X]).natDegree = 2}] (hf : f ≠ 0) (hsq : Squarefree f)
    {a : AdjoinRoot f} (ha : IsUnit a) :
    Units.modPow.realEquivOfEven two_ne_zero even_two
        (Units.modPow.map (Algebra.norm ℝ) 2 (QuotientGroup.mk ha.unit))
      = ∏ x : {x : ℝ // f.eval x = 0}, modPowEtaleEquiv hf hsq (QuotientGroup.mk ha.unit) x := by
  rw [Units.modPow.map_unit, Units.modPow.realEquivOfEven_mk,
    show (∏ x : {x : ℝ // f.eval x = 0}, modPowEtaleEquiv hf hsq (QuotientGroup.mk ha.unit) x)
      = Units.modPow.realSign (∏ x : {x : ℝ // f.eval x = 0},
          Units.map ((Pi.evalMonoidHom (fun _ ↦ ℝ) x).comp (MonoidHom.fst _ _))
            (Units.mapEquiv (etaleEquiv hf hsq).toMulEquiv ha.unit)) from
        (map_prod Units.modPow.realSign _ _).symm]
  refine Units.modPow.realSign_congr ?_
  rw [IsUnit.unit_spec, Units.coe_prod]
  simp only [Units.coe_map, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_fst,
    Units.coe_mapEquiv, IsUnit.unit_spec]
  have hpos : (0:ℝ) < ∏ p : {p : f.Factors // (p : ℝ[X]).natDegree = 2},
      ((etaleEquiv hf hsq a).2 p).normSq := by
    refine Finset.prod_pos fun p _ ↦ Complex.normSq_pos.mpr ?_
    exact ((Prod.isUnit_iff.mp (ha.map (etaleEquiv hf hsq))).2.map (Pi.evalMonoidHom _ p)).ne_zero
  show 0 < Algebra.norm ℝ a ↔ 0 < ∏ x : {x : ℝ // f.eval x = 0}, (etaleEquiv hf hsq a).1 x
  rw [norm_etale hf hsq a, mul_pos_iff_of_pos_right hpos]

/-- If the norm class of a unit `a` of `ℝ[X]/f` is trivial, then the product of its values at the
real roots is nonnegative (a corollary of Block 5: the complex factors give the positive
`normSq`). -/
lemma prod_val_nonneg_of_map_norm_eq_one [Fintype {x : ℝ // f.eval x = 0}]
    [Fintype {p : f.Factors // (p : ℝ[X]).natDegree = 2}] (hf : f ≠ 0) (hsq : Squarefree f)
    {a : AdjoinRoot f} (ha : IsUnit a)
    (h : Units.modPow.map (Algebra.norm ℝ) 2 (QuotientGroup.mk ha.unit) = 1) :
    0 ≤ ∏ x : {x : ℝ // f.eval x = 0}, (etaleEquiv hf hsq a).1 x := by
  rw [Units.modPow.map_unit, Units.modPow.mk_eq_one_iff_isSquare, IsUnit.unit_spec,
    Real.isSquare_iff, norm_etale hf hsq a] at h
  have hpos : (0:ℝ) < ∏ p : {p : f.Factors // (p : ℝ[X]).natDegree = 2},
      ((etaleEquiv hf hsq a).2 p).normSq := by
    refine Finset.prod_pos fun p _ ↦ Complex.normSq_pos.mpr ?_
    exact ((Prod.isUnit_iff.mp (ha.map (etaleEquiv hf hsq))).2.map (Pi.evalMonoidHom _ p)).ne_zero
  exact (mul_nonneg_iff_of_pos_right hpos).mp h

end Polynomial
