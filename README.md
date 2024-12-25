# Heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We need a family of absolute values `|·|_v` on `K`.
* All but finitely many of these are non-archimedean (i.e., `|x+y| ≤ max |x| |y|`).
* For a given `x ≠ 0` in `K`, `|x|_v = 1` for all but finitely many `v`.
* We have the *product formula* `∏ v, |x|_v = 1` for all `x ≠ 0` in `K`.

## Implementation

We try two implementations of the class `AdmissibleAbsValues K` that reflects
these requirements.

* In [__Basic.lean__](Heights/Basic.lean) we use *one* indexing type for *all*
  absolute values, non-archimedean and archimedean alike. Since we want to use
  powers of standard archimedean absolute values, we only require a weaker triangle inequality:
  `|x+y|_v ≤ C_v * max |x|_v |y|_v` for some constant `C_v`.
  (The usual triangle inequality implies this with `C_v = 2`.) 
  The requirement "all but finitely many absolute values are non-archimedean" then translates into
  `C_v = 1` for all but finitely many `v`. A disadvantage is that we cannot use the existing
  `AbsoluteValue` type (because that requires the usual triangle inequality). Instead, we
  use `K →*₀ ℝ≥0` together with the weak triangle inequality above. A slight further disadvantage
  is that the obtain less-than-optimal bounds for heights of sums with more than two terms,
  e.g., we get that `H_ℚ (x + y + z) ≤ 4 * H_ℚ x * H_ℚ y * H_ℚ z` instead of `≤ 3 * ⋯`.
  A downside of this approach is that it becomes rather cumbersome to set up the relevant
  structure for a number field. The natural indexing type is the sum type
  `InfinitePlace K ⊕ FinitePlace K`, which requires all functions and proofs to
  either go via `Sum.elim` or `match` expressions, and the API for such functions
  (e.g., for `mulSupport` or `finprod`) is a bit lacking.

* In [__Variant.lean__](Heights/Variant.lean) we instead use *two* indexing types,
  one for the archimedean and one for the non-archimedean absolute values.
  For the archimedean ones, we need "weights" (which are the exponents with which
  the absolute values occur in the product formula). We can then use the type `AbsoluteValue K ℝ`.
  A downside is that the definitions of the various heights (and therefore also the
  proofs of their basic properties) are more involved, because they involve a
  product of a `Finset.prod` for the archimedean absolute values and a `finprod` for
  the non-archimedean ones instead of just one `finprod` over all places.
  A big advantage is that it is now quite easy to set up an instance of
  `AdmissibleAbsValues K` for number fields `K` (thanks to Fabrizio Barroero's
  preparatory worl).

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `mulHeight₁ x` and `logHeight₁ x` for `x : K`. This is the height of an element of `K`.
* `mulHeight x` and `logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K` (for `x ≠ 0`).
* `mulHeight_finsupp x` and `logHeight_finsupp x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to any finite subtype containing the support of `x`.
