# Heights

This project formalizes some basic properties of height functions, at a level of generality that
applies uniformly to algebraic number fields, to function fields, and beyond.

The general set-up is the following. Let `K` be a field.
* We need a family of absolute values `|·|ᵥ` on `K`.
* All but finitely many of these are non-archimedean (i.e., `|x+y| ≤ max |x| |y|`).
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many `v`.
* We have the *product formula* `∏ v, |x|ᵥ = 1` for all `x ≠ 0` in `K`.

## Status

The core of this theory was developed here and has since been **upstreamed to Mathlib**, where it
now lives under [`Mathlib.NumberTheory.Height`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Height/Basic.html)
(the individual locations are given below). This repository remains as the development ground and a
record of the work — in particular of several alternative implementations that were explored along
the way, now collected under [`Heights/Archive`](Heights/Archive).

The **elliptic-curve application** built on top of this machinery — the Mordell-Weil theorem and
explicit 2-descent (the 2-Selmer group, formal groups over local fields, …), together with the
`ForMathlib` supporting theory — has moved to its own repository,
[EllipticCurves](https://github.com/MichaelStollBayreuth/EllipticCurves).

## Main definitions (now in Mathlib)

We define *multiplicative heights* and *logarithmic heights* (the latter are the real logarithms of
the former). All of the following are now in `Mathlib.NumberTheory.Height`; they were first
developed here in [`Heights/Basic.lean`](Heights/Basic.lean).

* `mulHeight₁ x` and `logHeight₁ x` for `x : K` — the height of an element of `K`
  (`Mathlib.NumberTheory.Height.Basic`).
* `mulHeight x` and `logHeight x` for `x : ι → K` with `ι` finite — the height of a tuple
  representing a point in projective space, invariant under scaling by nonzero elements of `K`
  (`Mathlib.NumberTheory.Height.Basic`).
* `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K` — the height of `x` restricted to
  any finite subtype containing its support (`Mathlib.NumberTheory.Height.Basic`).
* `Projectivization.mulHeight` and `Projectivization.logHeight` on `Projectivization K (ι → K)`
  (assuming `Finite ι`) — the height of a point on projective space
  (`Mathlib.NumberTheory.Height.Projectivization`).

The class packaging the requirements above is `Height.AdmissibleAbsValues K`
(`Mathlib.NumberTheory.Height.Basic`).

## Main results (now in Mathlib)

First developed here in [`Heights/NumberField.lean`](Heights/NumberField.lean),
[`Heights/Rat.lean`](Heights/Rat.lean) and [`Heights/MvPolynomial.lean`](Heights/MvPolynomial.lean),
now in `Mathlib.NumberTheory.Height`:

* The instance of `AdmissibleAbsValues` for number fields
  (`Mathlib.NumberTheory.Height.NumberField`).
* The **Northcott property**: sets of elements of bounded height are finite —
  `NumberField.finite_setOf_mulHeight₁_le` and `finite_setOf_logHeight₁_le`, and the propagation
  from `mulHeight₁` to the other heights in `Mathlib.NumberTheory.Height.Northcott`.
* The multiplicative height of a tuple of rational numbers consisting of coprime integers is the
  maximum of the absolute values of the entries — `mulHeight_eq_max_abs_of_gcd_eq_one`
  (`Mathlib.NumberTheory.Height.NumberField`).
* Bounds on heights of images under tuples of homogeneous polynomials — `mulHeight_eval_le`,
  `logHeight_eval_le`, … (`Mathlib.NumberTheory.Height.MvPolynomial`).
* The naïve height on an elliptic curve and the *approximate parallelogram law*
  (`Mathlib.NumberTheory.Height.EllipticCurve`).

The *descent* argument underlying the Mordell-Weil theorem — an abelian group `G` with a suitable
height function and `G/2G` finite is finitely generated — was also first developed here and is now
`AddCommGroup.fg_of_descent` in `Mathlib.GroupTheory.Descent`.

## Implementation and the archived variants

`AdmissibleAbsValues` can be implemented in several ways; the design involves a few independent
choices:

* absolute values valued in `ℝ≥0` vs. in `ℝ`;
* one common indexing type for all absolute values, two separate ones (archimedean /
  non-archimedean), or no indexing type at all (`Finset`s/`Multiset`s and `Set`s).

The version that was finally chosen and upstreamed uses a `Multiset` of (archimedean) absolute
values — with multiplicities corresponding to weights — together with a `Set` of nonarchimedean
ones ([`Heights/Basic.lean`](Heights/Basic.lean), with the number-field instance in
[`Heights/NumberField.lean`](Heights/NumberField.lean)). The switch to this approach was prompted by
a comment on the [first PR to Mathlib](https://github.com/leanprover-community/mathlib4/pull/33054):
a class using indexing types could lead to universe problems later on.

Three earlier approaches are kept under [`Heights/Archive`](Heights/Archive):

* [`Archive/Alternative`](Heights/Archive/Alternative) — *one* indexing type for all absolute
  values, valued in `K →*₀ ℝ≥0` with a weakened triangle inequality `|x+y|ᵥ ≤ Cᵥ·max |x|ᵥ |y|ᵥ`
  (so that `Cᵥ = 1` for all but finitely many `v`). This gives access to the richer
  `OrderedCommMonoid` API of `ℝ≥0`, but cannot reuse the existing `AbsoluteValue` type, yields
  slightly weaker bounds for sums of several terms, and makes the number-field instance cumbersome
  (the natural index `InfinitePlace K ⊕ FinitePlace K` forces `Sum.elim`/`match` throughout).
* [`Archive/WithTypes`](Heights/Archive/WithTypes) — *two* indexing types, archimedean and
  non-archimedean, with weights for the archimedean ones and `AbsoluteValue K ℝ`. The number-field
  instance is easy (thanks to Fabrizio Barroero's preparatory work), but the heights are defined via
  a product of a `Finset.prod` and a `finprod` rather than a single `finprod`.
* [`Archive/NoTypes`](Heights/Archive/NoTypes) — a `Finset` of archimedean absolute values with a
  weight function, together with a `Set` of nonarchimedean ones.

(A note on `ℝ≥0` vs `ℝ`: `ℝ≥0` is an `OrderedCommMonoid`, which is convenient for the pervasive
order arguments; but `FinitePlace`/`InfinitePlace` of a number field are `ℝ`-valued, so an
`ℝ≥0`-valued setup incurs friction in the number-field instance.)

## Further developments

* In [`Heights/WeakAbsoluteValue.lean`](Heights/WeakAbsoluteValue.lean) we prove that a "weak"
  `ℝ`-valued absolute value `v` — one satisfying only `v (x + y) ≤ 2 · max (v x) (v y)` — is in fact
  an absolute value.
