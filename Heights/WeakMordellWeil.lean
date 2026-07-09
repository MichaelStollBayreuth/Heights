import Mathlib.GroupTheory.QuotientGroup.Defs
import Heights.EllipticCurve

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite when `E` is an elliptic curve
over a number field `K`.

We will use the `x-T` map approach. At least for now, we will restrict to elliptic curves
given by a short Weierstrass equation `y² = x³ + ax + b =: f(x)`, where `a = a₄` and `b = a₆`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   => done.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
   => done (the bare map is defined as `μ₀`).
3. Show that `μ` is a group homomorphism.
   => done.
4. Show that `ker μ = 2E(K)`.
   => done.
5. Show that `im μ` is contained in the kernel of the norm map on square classes.
   => done, via `AdjoinRoot.norm_mk_eq_resultant`, which says that the norm of
   `AdjoinRoot.mk g p` for monic `g` is the resultant of `g` and `p`.
6. Show that `im μ ⊆ A(S,2)`, where `S` is the set of "bad" primes, i.e., primes dividing `2`
   or the (numerator of the) discriminant of `E` or the denominator of `a` or `b`.
   => `range_μ_le_selmerGroupA` at the end of the file, for `E` over the fraction field of a
   Dedekind domain, modulo one `sorry`: the two-case valuation computation
   `μX_component_mem_selmerGroupFactor`.
7. Show that `A(S,2)` is finite. (There is some preliminary stuff in
   `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, but finiteness is still a TODO there.)
   This is where number fields, rather than general Dedekind domains, become necessary.
-/

section API

section Group

variable {G H : Type*} [Group G] [Group H]

@[to_additive]
def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group

end Group

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product
of the `b * c - a` and its two analogues. -/
lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root
of `(d - a) * b * c`. -/
lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

section Units

variable {α : Type*} [Monoid α]

@[to_additive]
lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · apply_fun Units.val at hx
    simpa using hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩

end Units

section modPow

/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def QuotientGroup.congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e <| by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u ^ n, ⟨_, rfl⟩, by simp⟩

namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

/-- A unit class in `Units.modPow α n` is trivial if and only if the representative
is an `n`-th power. -/
lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  rw [QuotientGroup.eq_one_iff]
  simp only [MonoidHom.mem_range, powMonoidHom_apply, IsUnit.exists_pow_eq_unit_iff]

/-- A product of three unit classes in `Units.modPow α n` is trivial if and only if the
product of the representatives is an `n`-th power. -/
lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← IsUnit.unit_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

/-- A monoid homomorphism `α →* β` induces a homomorphism on `n`-th power classes of units. -/
def map (φ : α →* β) (n : ℕ) : Units.modPow α n →* Units.modPow β n :=
  QuotientGroup.map _ _ (Units.map φ) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map φ u, by simp [powMonoidHom]⟩

@[simp]
lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : Units.modPow α n) = ((ha.map φ).unit : Units.modPow β n) := by
  rw [map, ← QuotientGroup.mk'_apply, QuotientGroup.map_mk']
  exact congrArg _ (Units.ext rfl)

/-- A multiplicative equivalence `α ≃* β` induces one on `n`-th power classes of units. -/
def congr (e : α ≃* β) (n : ℕ) : Units.modPow α n ≃* Units.modPow β n :=
  QuotientGroup.congrRangePowMonoidHom (Units.mapEquiv e) n

/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def piEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ) :
    Units.modPow ((i : ι) → α i) n ≃* ((i : ι) → Units.modPow (α i) n) :=
  (QuotientGroup.congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    QuotientGroup.mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

end Units.modPow

end modPow

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_setOf_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]

/-- The primes of `B` lying above a set `S` of primes of `R`. -/
def IsDedekindDomain.HeightOneSpectrum.primesAbove (S : Set (HeightOneSpectrum R)) :
    Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def IsDedekindDomain.selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Units.modPow L n) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

/-- The resultant of `f` with the linear polynomial `C x - X` is `f.eval x`.
Note the absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
lemma resultant_C_sub_X (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  have h₁ : f.resultant (X - C x) m 1 = (-1) ^ m * f.eval x := by
    have := resultant_X_sub_C_pow_right f x m 1 hm
    rwa [pow_one, mul_one, pow_one] at this
  rw [show C x - X = C (-1 : R) * (X - C x) by simp, resultant_C_mul_right, h₁,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The resultant of a monic `g` with the constant polynomial `1` is `1`. -/
lemma Monic.resultant_one_right (hg : g.Monic) (n : ℕ) :
    g.resultant 1 g.natDegree n = 1 := by
  have h := resultant_add_right_deg (f := g) (g := 1) (m := g.natDegree) (n := 0) (k := n)
    (by simp)
  rw [zero_add, ← C_1, resultant_C_zero_right, one_pow, mul_one, hg.coeff_natDegree,
    one_pow] at h
  rw [← C_1, h]

/-- Membership in `R[X]_(g.natDegree)` is the same as having degree less than `g`. -/
lemma mem_degreeLT_natDegree_iff {q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]

section

variable [Nontrivial R] {q : R[X]} {n : ℕ}

/-- A remainder modulo a monic `g` has degree less than `g`. -/
lemma modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

/-- If `q` has degree `< g.natDegree + n` and `g` is monic, then `q /ₘ g` has degree `< n`. -/
lemma divByMonic_mem_degreeLT (hg : g.Monic)
    (hq : q ∈ degreeLT R (g.natDegree + n)) : q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  have h₁ : q.natDegree < g.natDegree + n := (natDegree_lt_iff_degree_lt hq0).mpr hq
  have h₂ : g.natDegree ≤ q.natDegree := by
    by_contra hcon
    exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree (not_le.mp hcon)
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  lia

/-- A polynomial divisible by a monic `g` and of degree less than `g` is zero. -/
lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 := by
  have h₁ : q %ₘ g = q := (modByMonic_eq_self_iff hg).mpr hq
  have h₂ : q %ₘ g = 0 := (modByMonic_eq_zero_iff_dvd hg).mpr hdvd
  rw [← h₁, h₂]

private lemma Monic.divMod_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g ∧ (g * v + u) %ₘ g = u %ₘ g := by
  refine div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

/-- Dividing `g * v + u` by the monic polynomial `g`. -/
lemma Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g :=
  (hg.divMod_mul_add v u).1

/-- Reducing `g * v + u` modulo the monic polynomial `g`. -/
lemma Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g :=
  (hg.divMod_mul_add v u).2

end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`. This is the
map that `mk g : R[X]_(g.natDegree) ≃ₗ AdjoinRoot g` turns into multiplication by `mk g p`. -/
noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
lemma mulModByMonic_apply_coe (hg : g.Monic) (p : R[X])
    (q : degreeLT R g.natDegree) : (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl

/-- For monic `g`, the Sylvester map of `g` and `1`, namely `(u, v) ↦ g * v + u`, is a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`. Its inverse is
`q ↦ (q %ₘ g, q /ₘ g)`. -/
noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · rintro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
lemma coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl

/-- The inverse of `Ψ` is division with remainder by `g`. -/
lemma coe_sylvesterEquivOne_symm (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g) ∧
      ((((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g) := by
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have hq : ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X]) =
      g * (w.2 : R[X]) + (w.1 : R[X]) := by
    simp [sylvesterEquivOne]
  have h₁ : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, hq]
  refine ⟨?_, ?_⟩
  · rw [hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr h₁]
  · rw [hg.divByMonic_mul_add, (divByMonic_eq_zero_iff hg).mpr h₁, add_zero]

/-- The block-triangular endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`. -/
noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

/-- The first coordinate of `B (u, v)` is `(p * u) %ₘ g`. -/
lemma coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).1, sylvesterMap_apply_coe, hg.modByMonic_mul_add]

/-- The second coordinate of `B (u, v)` is `v + (p * u) /ₘ g`. -/
lemma coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).2, sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in
/-- The determinant of the block-triangular map `B` is the determinant of its upper-left block. -/
lemma det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  -- the upper-left block is `mulModByMonic hg p`, and `B` fixes `{0} × R[X]_n` pointwise
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
      (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester

end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

/-- Reducing `q` mod `g` does not change its class in `AdjoinRoot g`. -/
@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)

/-- Every element of `AdjoinRoot g` with `g` monic is represented by a polynomial
of degree less than that of `g`. -/
lemma exists_degree_lt_mk_eq [Nontrivial R] (hg : g.Monic) (a : AdjoinRoot g) :
    ∃ p, p.degree < g.degree ∧ a = mk g p := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  exact ⟨q %ₘ g, degree_modByMonic_lt q hg, (mk_modByMonic hg q).symm⟩

/-- `mk g` is a linear equivalence from the polynomials of degree `< g.natDegree` onto
`AdjoinRoot g`, for `g` monic. -/
noncomputable def degreeLTEquiv [Nontrivial R] (hg : g.Monic) :
    degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  ofBijective ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype) <| by
    constructor
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      replace h : mk g q = mk g q' := h
      rw [mk_eq_mk] at h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hq hq'
      refine Subtype.ext (sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg h ?_)
      exact (degree_sub_le q q').trans_lt (max_lt hq hq')
    · intro a
      obtain ⟨q, rfl⟩ := mk_surjective a
      exact ⟨⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, mk_modByMonic hg q⟩

@[simp]
lemma degreeLTEquiv_apply [Nontrivial R] (hg : g.Monic)
    (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl

/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
lemma norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic hg, map_mul]

/-- The norm of `AdjoinRoot.mk g p` over the base ring, for `g` monic, is the resultant of `g`
and `p`. Equivalently, it is the product of the values of `p` at the roots of `g`. -/
lemma norm_mk_eq_resultant [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k, comp_coe,
      symm_trans_self, refl_toLinearMap, id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]

end AdjoinRoot

section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] [DecidableEq K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

`DecidableEq K` is what gives `K[X]` its monic normalization, via
`CommGroupWithZero.instNormalizedGCDMonoid` and `Polynomial.instNormalizationMonoid`;
it also provides the `DecidableEq K[X]` that `Multiset.toFinset` needs. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p ∈ (normalizedFactors f).toFinset}

namespace Factors

lemma coe_mem (p : f.Factors) : (p : K[X]) ∈ normalizedFactors f :=
  Multiset.mem_toFinset.mp p.2

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) :=
  (prime_of_normalized_factor _ p.coe_mem).irreducible

lemma monic (p : f.Factors) : (p : K[X]).Monic := by
  rw [← normalize_normalized_factor _ p.coe_mem]
  exact monic_normalize p.irreducible.ne_zero

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd <| dvd_of_mem_normalizedFactors p.coe_mem

/-- Distinct monic irreducible factors of `f` are coprime. -/
lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| by
        have hass := Ideal.span_singleton_eq_span_singleton.mp h
        rw [← normalize_normalized_factor _ p.coe_mem, ← normalize_normalized_factor _ q.coe_mem,
          normalize_eq_normalize hass.dvd hass.symm.dvd]

/-- Distinct monic irreducible factors of `f` generate coprime ideals. -/
lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

/-- For `f` nonzero and squarefree, `(f)` is the intersection of the `(p)` for `p` a factor. -/
lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  refine Ideal.span_singleton_eq_span_singleton.mpr <|
    (prod_normalizedFactors hf).symm.trans (.of_eq ?_)
  have hcoe : ∏ p : f.Factors, (p : K[X]) = ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']

end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] [DecidableEq K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite

/-- The minimal polynomial of the root of a monic irreducible factor is the factor itself. -/
lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]

open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X]/(f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h

/-- **Chinese Remainder Theorem** for `AdjoinRoot`: for `f` nonzero and squarefree,
`K[X]/(f)` is the product of the fields `K[X]/(p)` over the monic irreducible factors `p`
of `f`. -/
noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

@[simp]
lemma equivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    equivPiFactors hf hsq (mk f q) p = mk (p : K[X]) q :=
  rfl

/-- The projection of `K[X]/(f)` onto the field factor `K[X]/(p)`. -/
noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hf hsq).toRingEquiv.toRingHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  rfl

/-- The `n`-th power classes of units of `K[X]/(f)` are the product of those of its
field factors. -/
noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    Units.modPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) n) :=
  (Units.modPow.congr (equivPiFactors hf hsq).toMulEquiv n).trans <|
    Units.modPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors. -/
@[simp]
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (ha.unit : Units.modPow (AdjoinRoot f) n) p =
      ((ha.map (projFactor hf hsq p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) n) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, Units.modPow.congr,
    QuotientGroup.congrRangePowMonoidHom, QuotientGroup.congr_mk, Units.modPow.piEquiv,
    QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]
  exact congrArg _ (Units.ext rfl)

end AdjoinRoot

end EtaleDecomposition

end API

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

lemma ringChar_ne_two_of_isElliptic_of_isShortNF [W.IsElliptic] [W.IsShortNF] :
    ringChar K ≠ 2 := by
  have := W.isUnit_Δ.ne_zero
  contrapose! this
  rw [Δ_of_isShortNF W, show (16 : K) = (2 :) * 8 by norm_num]
  nth_rewrite 1 [← this]
  simp

/-!
### Step 1: define `A`
-/

open Polynomial

/-- The polynomial on the right hand side of a short Weierstrass equation. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma separable_f [W.IsElliptic] [W.IsShortNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [f, separable_def',
    show derivative (X ^ 3 + C W.a₄ * X + C W.a₆) = C 3 * X ^ 2 + C W.a₄ by
      simp [C_ofNat]; norm_num]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a₄) * X - C (432 * W.a₆)),
    C (W.Δ)⁻¹ * (C (-96 * W.a₄) * X ^ 2 + C (144 * W.a₆) * X + C (-64 * W.a₄ ^ 2)), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isShortNF]
  simp only [C_eq_algebraMap]
  algebra

lemma equation_iff_eval_f_eq_sq [W.IsShortNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] := X ^ 2 + C x * X + C (x ^ 2 + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

lemma eval_fCofactor_self (x : K) : (W.fCofactor x).eval x = 3 * x ^ 2 + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp [fCofactor, f]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

lemma three_mul_sq_add_a₄_ne_zero [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + W.a₄ ≠ 0 := by
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hx
  have := W.Δ_of_isShortNF ▸ W.isUnit_Δ |>.ne_zero
  contrapose! this
  grobner

/-- The étale algebra associated to a short Weierstrass curve. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma exists_mk_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  conv => enter [1, ξ, 1, l, 1, m]; rw [← map_mul, ← sub_eq_zero, ← map_sub]
  have H (ξ l m : K) : (X - C ξ) * (C r * X ^ 2 + C s * X + C t) - (C l * X + C m) =
      C r * W.f + (C (-ξ * r + s) * X ^ 2 + C (-ξ * s - l - W.a₄ * r + t) * X
        + C (-ξ * t - m - W.a₆ * r)) := by
    simp only [f, C_eq_algebraMap]
    algebra
  conv =>
    enter [1, ξ, 1, l, 1, m]
    rw [H, map_add, map_mul]
    enter [1, 1, 2]
    rw [AdjoinRoot.mk_self]
  simp only [mul_zero, zero_add]
  suffices ∃ ξ l m, -ξ * r + s = 0 ∧ -ξ * s - l - W.a₄ * r + t = 0 ∧ -ξ * t - m - W.a₆ * r = 0 by
    obtain ⟨ξ, l, m, h₂, h₁, h₀⟩ := this
    refine ⟨ξ, l, m, ?_⟩
    rw [h₂, h₁, h₀]
    simp
  refine ⟨s / r, t - W.a₄ * r - s ^ 2 / r, -W.a₆ * r - t * s / r, ?_, ?_, ?_⟩ <;> field

/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

lemma exists_mk_eq' {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor,
    show ((2 :) : WithBot ℕ) = Order.succ ↑1 from rfl, Order.lt_succ_iff] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le hp⟩

/-- The norm of `x - θ` is `f x`. -/
lemma norm_mk_C_sub_X (x : K) : Algebra.norm K (AdjoinRoot.mk W.f (C x - X)) = W.f.eval x := by
  have hd : (C x - X).natDegree = 1 := by compute_degree!
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, hd, resultant_C_sub_X _ _ _ le_rfl]

/-- If `x` is a root of `f`, then the norm of `x - θ + fCofactor x`, which is the element
representing `f' θ` in this case, is the square `(3x² + a₄)²`. -/
lemma norm_mk_C_sub_X_add_fCofactor {x : K} (hx : W.f.eval x = 0) :
    Algebra.norm K (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) = (3 * x ^ 2 + W.a₄) ^ 2 := by
  have hq : (W.fCofactor x).natDegree = 2 := W.natDegree_fCofactor x
  have hqx : (W.fCofactor x).eval x = 3 * x ^ 2 + W.a₄ := W.eval_fCofactor_self x
  have hp : (C x - X + W.fCofactor x).natDegree = 2 := by
    simp only [fCofactor]
    compute_degree!
  have hpx : (C x - X + W.fCofactor x).eval x = 3 * x ^ 2 + W.a₄ := by
    rw [eval_add, ← hqx]
    simp
  rw [AdjoinRoot.norm_mk_eq_resultant W.monic_f, hp, W.natDegree_f]
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx]
  rw [show (3 : ℕ) = (W.fCofactor x).natDegree + (X - C x).natDegree by
        rw [hq, natDegree_X_sub_C],
    resultant_mul_left _ _ _ 2 hp.le, hq, natDegree_X_sub_C]
  -- the factor coming from `X - C x` is `p.eval x`
  rw [show (X - C x) = (X - C x) ^ 1 by rw [pow_one],
    resultant_X_sub_C_pow_left _ _ _ _ hp.le, pow_one, hpx]
  -- the factor coming from `fCofactor x` is `(C x - X).resultant`, since `fCofactor x ≡ 0`
  have hres : (W.fCofactor x).resultant (C x - X) 2 2 = 3 * x ^ 2 + W.a₄ := by
    have h := resultant_add_right_deg (f := W.fCofactor x) (g := C x - X) (m := 2) (n := 1)
      (k := 1) (by compute_degree!)
    simp only [show (1 : ℕ) + 1 = 2 from rfl, pow_one] at h
    rw [h, show (W.fCofactor x).coeff 2 = 1 by
        rw [← hq]; exact (W.monic_fCofactor x).coeff_natDegree,
      one_mul, resultant_C_sub_X _ _ _ hq.le, hqx]
  rw [show C x - X + W.fCofactor x = (C x - X) + W.fCofactor x * 1 by ring,
    resultant_add_mul_right (f := W.fCofactor x) (g := C x - X) (p := 1) (m := 2) (n := 2)
      (by simp) hq.le, hres]
  ring

/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  letI eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl

lemma mk_eq_mk_iff [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    AdjoinRoot.mk W.f p = AdjoinRoot.mk W.f q ↔
      p.eval x = q.eval x ∧ AdjoinRoot.mk (W.fCofactor x) p = AdjoinRoot.mk (W.fCofactor x) q := by
  rw [← EquivLike.apply_eq_iff_eq <| W.equivProdA' hx]
  simpa only [equivProdA'_apply] using Prod.mk_inj

lemma isUnit_mk_iff [W.IsElliptic] [W.IsShortNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma eval_linePolynomial_left [DecidableEq K] (xP xQ yP yQ : K) :
    eval xP (linePolynomial xP yP (W.slope xP xQ yP yQ)) = yP := by
  simp [linePolynomial]

lemma eval_linePolynomial_right [DecidableEq K] (xP xQ yP yQ : K) (h : xP ≠ xQ) :
    eval xQ (linePolynomial xP yP (W.slope xP xQ yP yQ)) = yQ := by
  simp only [linePolynomial, slope, if_neg h]
  simp
  field (disch := grind)

section

variable [W.IsShortNF]

lemma equation_iff_of_isShortNF (x y : K) :
    W.Equation x y ↔ y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  rw [W.equation_iff, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF]
  ring_nf

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rw [equation_iff_of_isShortNF x y] at h
  rw [← sq_eq_zero_iff, h, ← hf]
  simp [f]

end

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one
    (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * (X ^ 2 + C x * X + C (x ^2 + W.a₄)))) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow]
  have : (C x - X) * (X ^ 2 + C x * X + (C x ^ 2 + C W.a₄)) =
      -X ^ 3 - C W.a₄ * X - C W.a₆ + C (x ^3 + W.a₄ * x + W.a₆) := by
    simp; ring
  simp only [f, eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  rw [this, mul_add, ← C_mul, inv_mul_cancel₀ h, map_one]
  ring

section

variable [W.IsShortNF] [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  rw [isUnit_mk_iff W h]
  have H₀ : 3 * x ^ 2 + W.a₄ ≠ 0 := three_mul_sq_add_a₄_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + W.a₄ := by
    rw [eval_add, W.eval_fCofactor_self]; simp
  have H₂ : (AdjoinRoot.mk (W.fCofactor x)) (C x - X + W.fCofactor x) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := AdjoinRoot.mk (W.fCofactor x) <| C (3 * x ^ 2 + W.a₄)⁻¹ * (X + C (2 * x))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + W.a₄)⁻¹ * (X + C (2 * x))) =
      C (3 * x ^ 2 + W.a₄)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + W.a₄) * ·) using mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp

end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := Units.modPow W.A 2

/- `inferInstance` succeeds here, but instance search does not find this instance at the use
sites (e.g., for `mul_right_comm` below) unless it is declared. -/
noncomputable instance : CommGroup W.M := inferInstance

@[simp] lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr <| by simp

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]

@[simp] lemma M.inv_eq_self (m : W.M) : m⁻¹ = m := inv_eq_of_mul_eq_one_right (M.mul_self m)

variable [DecidableEq K] [W.IsShortNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of
`x - T` if `f x ≠ 0`, and to the square class of `f' T` otherwise. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dif_pos hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dif_neg hx]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp [negY], zero_add]
  exact some_ne_zero hR

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  have hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
    obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
    have hpol₀ : pol = 0 := by
      refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        apply_fun (·.eval x) at hpol
        rcases hx with rfl | rfl <;>
          rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
          simpa using hpol
      · grind
    rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    have : eval xP pol = 0 := by simpa using hpol
    rw [← IsRoot.def, ← dvd_iff_isRoot] at this
    obtain ⟨p, rfl⟩ := this
    rw [mul_comm]
    suffices p.natDegree = 0 by
      rw [natDegree_eq_zero] at this
      obtain ⟨γ, rfl⟩ := this
      exact ⟨_, rfl⟩
    contrapose! hpol₁
    replace hpol₁ : 1 ≤ p.natDegree := by lia
    rw [natDegree_mul (X_sub_C_ne_zero _) (ne_zero_of_natDegree_gt hpol₁), natDegree_X_sub_C xP]
    lia
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl

@[simp]
lemma μ₀_two_nsmul (P : W.Point) : W.μ₀ (2 • P) = 1 := by
  rw [← μ_apply, ofAdd_nsmul, map_pow, M.sq_eq_one]

/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity of polynomials. -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ ?_, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  · match P with
    | 0 => simp at hP -- cannot occur
    | .some ξ η h' =>
      rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
        Point.neg_some] at hP
      have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
      obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero H H h hP
      rw [← sq] at hpol
      obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
      exact ⟨_, _, _, hpol⟩
  · have h20 : (2 : K) ≠ 0 :=
      Ring.two_ne_zero <| ringChar_ne_two_of_isElliptic_of_isShortNF W
    have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
        X ^ 3 - C (l ^ 2) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
      simp only [f] at H
      convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
    replace H' n := congrArg (fun p ↦ p.coeff n) H'
    simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
    have H₂ : x + 2 * ξ = l ^ 2 := by simpa using congrArg (-·) (H' 2)
    have H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m := by simpa using H' 1
    have H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2 := by simpa using congrArg (-·) (H' 0)
    have hy₀ : l * ξ + m ≠ 0 := by
      have hΔ := W.isUnit_Δ.ne_zero
      rw [Δ_of_isShortNF W] at hΔ
      contrapose! hΔ
      grobner
    have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
      simp only [negY, a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero]
      grind
    have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
      simp only [slope_of_Y_ne rfl hy, a₂_of_isShortNF, mul_zero, zero_mul, add_zero,
        a₁_of_isShortNF, a₃_of_isShortNF, sub_zero, negY, sub_neg_eq_add, ← two_mul]
      rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
      field_simp
      grobner
    have heq : W.Equation ξ (l * ξ + m) := by
      rw [equation_iff_eval_f_eq_sq, ← sub_eq_zero, eq_comm]
      simpa using congrArg (·.eval ξ) H
    let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
    suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
    simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
      a₁_of_isShortNF, a₂_of_isShortNF, zero_mul, add_zero, sub_zero]
    linear_combination H₂

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity in `W.A`. -/
lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    obtain ⟨q, hq⟩ := H
    suffices q = 1 by
      rwa [this, mul_one, ← eq_sub_iff_add_eq] at hq
    have hdeg : natDegree ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2) = 3 := by
      compute_degree!
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hq₀ : q ≠ 0 := by
      intro rfl
      rw [mul_zero] at hq
      rw [hq] at hmon
      simp at hmon
    have hq₁ : q.natDegree = 0 := by
      apply_fun natDegree at hq
      rw [hdeg, natDegree_mul W.monic_f.ne_zero hq₀, W.natDegree_f] at hq
      lia
    refine (Monic.natDegree_eq_zero ?_).mp hq₁
    exact Polynomial.Monic.of_mul_monic_left W.monic_f <| hq ▸ hmon

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, hrst⟩ := W.exists_mk_eq z
  rw [hrst] at hz
  have hr : r ≠ 0 := by
    intro hr₀
    simp only [hr₀, map_zero, zero_mul, zero_add, ← map_pow] at hz
    rw [AdjoinRoot.mk_eq_mk] at hz
    obtain ⟨q, hq⟩ := hz
    have : natDegree ((C s * X + C t) ^ 2 - (C x - X)) = 1 ∨
        natDegree ((C s * X + C t) ^ 2 - (C x - X)) = 2 := by
      rcases eq_or_ne s 0 with rfl | hs
      · exact .inl <| by simp only [map_zero, zero_mul, zero_add]; compute_degree!
      · exact .inr <| by compute_degree!
    apply_fun natDegree at hq
    rcases eq_or_ne q 0 with rfl | hq₀
    · simp at hq
      lia
    · rw [natDegree_mul W.monic_f.ne_zero hq₀, natDegree_f] at hq
      lia
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_eq' (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← hp, ← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hdvd : W.fCofactor x ∣ W.f := ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| hdvd.trans hz
  rw [map_pow, hrs, map_add _ _ (fCofactor ..), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    intro rfl
    rw [← map_pow, AdjoinRoot.mk_eq_mk, map_zero, zero_mul, zero_add] at hz'
    obtain ⟨q, hq⟩ := hz'
    apply_fun natDegree at hq
    have : (C s ^ 2 - (C x - X)).natDegree = 1 := by compute_degree!
    rw [this] at hq; clear this
    rcases eq_or_ne q 0 with rfl | hq₀
    · simp at hq
    rw [natDegree_mul (W.monic_fCofactor x).ne_zero hq₀, natDegree_fCofactor] at hq
    lia
  refine ⟨-s / r, 1 / r, -x / r, ?_⟩
  rw [← map_pow] at hz'
  rw [AdjoinRoot.mk_eq_mk] at hz' ⊢
  obtain ⟨q, hq⟩ := hz'
  apply_fun (· * (X - C x)) at hq
  rw [mul_right_comm, ← f_eq_mul_of_eval_eq_zero _ hx] at hq
  replace hq : q * W.f = ((C r * X + C s) ^ 2 - (C x - X)) * (X - C x) := by
    rw [mul_comm]; exact hq.symm
  refine ⟨C (1 / r ^ 2) * q, ?_⟩
  rw [eq_comm, mul_comm W.f]
  apply_fun (C (r ^ 2) * ·) using mul_right_injective₀ <| by simp [hr₀]
  dsimp only
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  rw [mul_one_div_cancel <| pow_ne_zero 2 hr₀, map_one, one_mul, hq]
  conv_rhs =>
    rw [sub_neg_eq_add, mul_add, ← mul_assoc, map_pow, ← mul_pow, mul_sub (C r), ← map_mul,
      mul_div_cancel₀ _ hr₀]
    enter [2]
    rw [← mul_pow, mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hr₀, map_one, one_mul,
      ← map_mul, mul_div_cancel₀ _ hr₀]
  simp only [C_eq_algebraMap]
  algebra

lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · exact eq_two_smul_of_μ_eq_one_of_eq h hμ hx
  · exact eq_two_smul_of_μ_eq_one_of_ne h hμ hx

end kernel

/- Maybe it is better to define `μ : W.Point →+ Additive M`
instead of `Multiplicative W.Point →* M`? -/

/-- The kernel of `μ` is exactly `2 • W(K)`. -/
lemma ker_μ_eq : (μ (W := W)).ker = (nsmulAddMonoidHom 2).range.toSubgroup := by
  ext P'
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [MonoidHom.mem_ker, μ_apply, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · match P with
    | 0 => exact fun _ ↦ ⟨0, by simp⟩
    | .some x y h => exact fun hμ ↦ (eq_two_smul_of_μ_eq_one h hμ).imp fun Q hQ ↦ hQ.symm
  · rintro ⟨Q, rfl⟩
    exact μ₀_two_nsmul Q

/-- A criterion for the validity of the weak Mordell-Weil Theorem. -/
lemma finite_index_range_nsmulAddMonoidHom_two_iff :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex ↔ Finite (μ (W := W)).range := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff, ← ker_μ_eq,
    Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (μ (W := W))).symm.toEquiv]
  exact Subgroup.finiteIndex_iff_finite_quotient

/-!
### Step 5: show that `im μ` is contained in the kernel of the norm map.

The norm `Algebra.norm K : W.A →* K` sends units to units, hence induces a homomorphism
`normM : W.M →* Units.modPow K 2` on square classes. We must show `normM ∘ μ = 1`.

Writing `f = (X - θ₁) * (X - θ₂) * (X - θ₃)` over a splitting field, the two cases are:

* if `f x ≠ 0`, then `N (x - θ) = ∏ᵢ (x - θᵢ) = f x = y²`, a square;
* if `f x = 0`, then `N (f' θ) = (3x² + a₄)²`, again a square.

Both are instances of `AdjoinRoot.norm_mk_eq_resultant`: the norm of `AdjoinRoot.mk g p` for
monic `g` is the resultant of `g` and `p`. See `norm_mk_C_sub_X` and
`norm_mk_C_sub_X_add_fCofactor` in Step 1 above, which deduce them from it by resultant algebra;
in the second case the factorization `f = fCofactor x * (X - C x)` splits the resultant into two
factors, each equal to `(W.fCofactor x).eval x = 3x² + a₄`.

`AdjoinRoot.norm_mk_eq_resultant` is proved in the API section; it is a general fact about
`AdjoinRoot g` for monic `g` and looks worth upstreaming.
-/

section Step5

/-- The norm map on square classes, induced by `Algebra.norm K : W.A →* K`. -/
noncomputable def normM : W.M →* Units.modPow K 2 :=
  Units.modPow.map (Algebra.norm K) 2

/-- The image of `μX` lies in the kernel of the norm map on square classes. -/
lemma normM_μX_eq_one {x y : K} (h : W.Equation x y) : W.normM (W.μX x) = 1 := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, normM, Units.modPow.map_unit, Units.modPow.unit_eq_one_iff]
    exact ⟨3 * x ^ 2 + W.a₄, (W.norm_mk_C_sub_X_add_fCofactor hx).symm⟩
  · rw [μX_of_eval_f_ne_zero hx, normM, Units.modPow.map_unit, Units.modPow.unit_eq_one_iff]
    exact ⟨y, by rw [W.norm_mk_C_sub_X, (equation_iff_eval_f_eq_sq W x y).mp h]⟩

@[simp]
lemma normM_μ₀_eq_one (P : W.Point) : W.normM (W.μ₀ P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => exact normM_μX_eq_one h.1

/-- The image of `μ` is contained in the kernel of the norm map on square classes. -/
lemma range_μ_le_ker_normM : (μ (W := W)).range ≤ (normM (W := W)).ker := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [MonoidHom.mem_ker, μ_apply]
  exact normM_μ₀_eq_one P

end Step5


end WeierstrassCurve.Affine

/-!
## Step 6: `im μ ⊆ A(S,2)`

The right level of generality is: `R` a Dedekind domain, `K = Frac R`, and `E/K` given by a
short Weierstrass equation. Everything Step 6 needs — a height-one spectrum, the `v`-adic
valuations, and unique factorization of fractional ideals — is exactly the Dedekind package.
Number fields are *not* needed until Step 7.

`Mathlib.RingTheory.DedekindDomain.SelmerGroup` already defines, for a Dedekind domain `R` with
fraction field `K`, the group `IsDedekindDomain.selmerGroup : Subgroup (Units.modPow K n)`,
namely the classes whose valuation is `≡ 0 mod n` at every `v ∉ S`. Note that its ambient group
is literally our `Units.modPow K n` (that file has it only as a local notation). So the target
`A(S,2)` should be assembled out of `selmerGroup`s, not defined from scratch.

The obstruction is that `A = AdjoinRoot f` is an étale algebra, not a field, so it has no
`HeightOneSpectrum`. The unavoidable intermediate step is therefore:

**Step 5.5 (decomposition).** `f` is separable, so `A ≃ₐ[K] ((i : ι) → L i)`, a finite product of
finite separable field extensions `L i` of `K`, indexed by the irreducible factors of `f`.
Consequently `W.M = Units.modPow A 2 ≃* ((i : ι) → Units.modPow (L i) 2)`.

This is set up in the API section under "Decomposition of `K[X]/(f)` into a product of fields":
the index type is `Polynomial.Factors f`, the decomposition is `AdjoinRoot.equivPiFactors`, and
the induced isomorphism on `n`-th power classes is `AdjoinRoot.modPowEquivPiFactors`. Each factor
already gets `Field`, `Algebra K`, and `FiniteDimensional K` instances, and
`Polynomial.Factors.separable` supplies separability of the factors.

With that in hand:

* for each `i`, `R i := integralClosure R (L i)` is again a Dedekind domain
  (`IsIntegralClosure.isDedekindDomain`) with fraction field `L i`, so
  `IsDedekindDomain.selmerGroup` applies;
* `A(S,2)` is the preimage under the above isomorphism of the product of the
  `selmerGroup (S := S i) (n := 2)`, where `S i` is the set of primes of `R i` above `S`;
* the containment `im μ ⊆ A(S,2)` is checked factor by factor: for `P = (x, y)` and `w` a prime
  of `R i` not above `S`, the valuation `w (x - θ i)` is even. The two cases are
  `v x < 0` (then `v x = -2k`, `v y = -3k` and `w (x - θ i) = -2k` for every `w ∣ v`) and
  `v x ≥ 0` (then `x, y` are `v`-integral, `∏ᵢ (x - θ i) = f x = y²`, and the factors are
  pairwise coprime away from primes dividing `disc f`, which divides `Δ`).

Step 7 (finiteness of `A(S,2)`) then reduces to finiteness of each `L i ⟮S i, 2⟯`, which needs
`S i` finite, the class group of `R i` finite, and `(R i)ˣ` finitely generated — i.e. number
fields. Mathlib lists finiteness of `selmerGroup` as a TODO.

All the structure is in place below: `badPrimes` (`S`) and its finiteness,
`AdjoinRoot.isSeparable_of_separable` (so that `IsIntegralClosure.isDedekindDomain` applies to
each factor), `IsDedekindDomain.HeightOneSpectrum.primesAbove` (the `S i`),
`IsDedekindDomain.selmerGroupAbove`, `selmerGroupA` (`A(S,2)`, as a subgroup of `W.M`), and
`range_μ_le_selmerGroupA` (Step 6 itself). The one remaining gap is the arithmetic input
`μX_component_mem_selmerGroupFactor`, the two-case valuation computation.
-/

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial

-- Step 6 needs neither `DecidableEq K` nor the group structure on points, so we re-declare the
-- variables rather than inheriting the ones used for Steps 2-5.
variable {K : Type*} [Field K] (W : Affine K)

/-- The set of "bad" primes of `R`: those dividing `2` or the discriminant of `W`, and those
occurring in a denominator of `a₄` or of `a₆` (the latter two are the supports of `a₄` and `a₆`
in the sense of `IsDedekindDomain.HeightOneSpectrum.Support`). Away from these, the `x - T` map
lands in the `2`-Selmer group. -/
def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- There are only finitely many bad primes: `2` and `W.Δ` are nonzero, and the support of any
element of `K` is finite. -/
lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsShortNF] : (W.badPrimes R).Finite :=
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_isElliptic_of_isShortNF W)
  (((HeightOneSpectrum.finite_setOf_valuation_ne_one h2).union
    (HeightOneSpectrum.finite_setOf_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₄)).union (HeightOneSpectrum.Support.finite R W.a₆)

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero

lemma squarefree_f [W.IsElliptic] [W.IsShortNF] : Squarefree W.f := (separable_f W).squarefree

section Selmer

variable [DecidableEq K] [W.IsElliptic] [W.IsShortNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- The `2`-Selmer group of the field factor `AdjoinRoot p` of `W.A`, relative to the primes of
its ring of integers lying above the bad primes of `R`. -/
noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup (Units.modPow (AdjoinRoot (p : K[X])) 2) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  have := IsIntegralClosure.isDedekindDomain R K (AdjoinRoot (p : K[X]))
    (integralClosure R (AdjoinRoot (p : K[X])))
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K (AdjoinRoot (p : K[X]))
    (integralClosure R (AdjoinRoot (p : K[X])))
  IsDedekindDomain.selmerGroupAbove R (integralClosure R (AdjoinRoot (p : K[X])))
    (AdjoinRoot (p : K[X])) (W.badPrimes R) 2

/-- `A(S,2)` in the product decomposition: the product of the `2`-Selmer groups of the field
factors of `W.A`. -/
noncomputable def selmerGroupPi :
    Subgroup ((p : W.f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) 2) :=
  Subgroup.pi Set.univ (W.selmerGroupFactor R)

/-- `A(S,2)`, as a subgroup of `W.M`: the classes whose image in each field factor lies in the
`2`-Selmer group of that factor. Step 6 asserts that `im μ ≤ A(S,2)`. -/
noncomputable def selmerGroupA : Subgroup W.M :=
  (W.selmerGroupPi R).comap
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).toMonoidHom

lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R p := by
  simp [selmerGroupA, selmerGroupPi, Subgroup.mem_pi]

/-- The heart of Step 6: for a point `(x, y)` of `W` and a field factor `K[X]/(p)` of `W.A`,
the square class of the image of the `x - T` map lies in the `2`-Selmer group of that factor.

TODO: prove. Let `θ` be the root of `p` and `𝓞` the integral closure of `R` in `K[X]/(p)`, and
let `w` be a prime of `𝓞` not lying above a bad prime `v` of `R`. One shows `w (x - θ)` is even,
distinguishing two cases according to the sign of `v x`:

* `v x < 0`. Then, from `y ^ 2 = f x` and `v` being coprime to the denominators of `a₄`, `a₆`,
  one gets `v x = -2 k` and `v y = -3 k` for some `k > 0`, and `w (x - θ) = e * v x = -2 e k`
  for every `w ∣ v`, since `w θ ≥ 0`.
* `v x ≥ 0`. Then `x` and `y` are `v`-integral and `∏ q (x - θ q) = f x = y ^ 2` has even
  valuation at every `w`. The factors `x - θ q` are pairwise coprime at every `w` not dividing
  the discriminant of `f`, which divides `Δ`; since `v ∉ badPrimes`, `w (x - θ)` is therefore
  itself even. -/
lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R p :=
  sorry

/-- **Step 6**: the image of `μ` is contained in `A(S,2)`. -/
theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R h.1 p

end Selmer

end WeierstrassCurve.Affine
