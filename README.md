# Heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We need a family of absolute values `|·|ᵥ` on `K`.
* All but finitely many of these are non-archimedean (i.e., `|x+y| ≤ max |x| |y|`).
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many `v`.
* We have the *product formula* `∏ v, |x|ᵥ = 1` for all `x ≠ 0` in `K`.

## Implementation

We try several implementations of the class `AdmissibleAbsValues K` that reflects
these requirements.

* In [__Basic-Alternative.lean__](Heights/Basic-Alternative.lean) we use *one* indexing type for *all*
  absolute values, non-archimedean and archimedean alike. Since we want to use
  powers of standard archimedean absolute values, we only require a weaker triangle inequality:
  `|x+y|ᵥ ≤ Cᵥ * max |x|ᵥ |y|ᵥ` for some constant `Cᵥ`.
  (The usual triangle inequality implies this with `Cᵥ = 2`.) 
  The requirement "all but finitely many absolute values are non-archimedean" then translates into
  `Cᵥ = 1` for all but finitely many `v`. A disadvantage is that we cannot use the existing
  `AbsoluteValue` type (because that requires the usual triangle inequality). Instead, we
  use `K →*₀ ℝ≥0` together with the weak triangle inequality above. A slight further disadvantage
  is that we obtain less-than-optimal bounds for heights of sums with more than two terms,
  e.g., we get that `H_ℚ (x + y + z) ≤ 4 * H_ℚ x * H_ℚ y * H_ℚ z` instead of `≤ 3 * ⋯`.
  A downside of this approach is that it becomes rather cumbersome to set up the relevant
  structure for a number field. The natural indexing type is the sum type
  `InfinitePlace K ⊕ FinitePlace K`, which requires all functions and proofs to
  either go via `Sum.elim` or `match` expressions, and the API for such functions
  (e.g., for `mulSupport` or `finprod`) is a bit lacking.
  See [__Instances-Alternative.lean__](Heights/Instances-Alternative.lean) for an attempt at providing
  an instance of `AdmissibleAbsValues` for a number field.

* In [__BasicWithTypes.lean__](Heights/BasicWithTypes.lean) we instead use *two* indexing types,
  one for the archimedean and one for the non-archimedean absolute values.
  For the archimedean ones, we need "weights" (which are the exponents with which
  the absolute values occur in the product formula). We can then use the type `AbsoluteValue K ℝ`.
  A downside is that the definitions of the various heights (and therefore also the
  proofs of their basic properties) are more involved, because they involve a
  product of a `Finset.prod` for the archimedean absolute values and a `finprod` for
  the non-archimedean ones instead of just one `finprod` over all places.
  A big advantage is that it is now quite easy to set up an instance of
  `AdmissibleAbsValues K` for number fields `K` (thanks to Fabrizio Barroero's
  preparatory work); see [__InstancesWithTypes.lean__](Heights/InstancesWithTypes.lean).

* In [__Basic.lean__](Heights/Basic.lean) we replace the indexing types by 
  a `Multiset` of (archimedean) absolute values (with multiplicities corresponding to weights)
  and a `Set` of nonarchimedean absolte values. As can be seen in
  [__Instances.lean__](Heights/Instances.lean), this needs a bit more glue to set up the
  instance for number fields, but otherwise is quite workable.

* A further variant can be found in [__BasicNoTypes.lean__](Heights/BasicNoTypes.lean).
  Here we use a `Finset` for the archimedean absolute values with a weight function,
  together with a `Set` for the nonarchimedean ones. 

There are actually several independent design decisions involved:
* absolute values with values in `ℝ≥0` vs. with values in `ℝ`
* one common indexing type vs. two separate ones for archimedean/non-archimedean
  absolute values
* or no indexing type at all; instead use Finsets or Multisets and Sets

The various versions implemented here combine
* `ℝ≥0` with one indexing type (Basic-Alternative.lean),
* `ℝ` with two indexing types and weights (BasicWithTypes.lean),
* `ℝ` with a multiset and a set (Basic.lean),
* `ℝ` with a finset (plus weights) and a set.

Advantage of `ℝ≥0` over `ℝ`:
* `ℝ≥0` is an `OrderedCommMonoid` (which `ℝ` is not); this gives access to a broader API
  for arguments that involve the order (which are rather pervasive in our context).

Disadvantage:
* The `FinitePlace`s and `InfinitePlace`s of a `NumberField` are defined to be
  `AbsoluteValue`s with values in `ℝ`, so there is some friction in translating
  to a setting with `ℝ≥0`-valued absolute values.
  See [Instances-Alternative.lean](Heights/Instances-Alternative.lean)
  for what this means. (Instead of using `ℝ` in `AdmissibleAbsValues`, one could
  of course refactor the other side to use `ℝ≥0`. I don't have a feeling for the
  ramifications of that.)

In a comment on the
[first PR to Mathlib](https://github.com/leanprover-community/mathlib4/pull/33054)
(which was following BasicWithTypes.lean),
it was pointed out that a class using indexing types could potentially lead to problems
with universes later on. We will therefore switch to the multiset+set approach
as in [__Basic.lean__](Heights/Basic.lean) and [__Instances.lean__](Heights/Instances.lean).


## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `mulHeight₁ x` and `logHeight₁ x` for `x : K`. This is the height of an element of `K`.
* `mulHeight x` and `logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K`.
* `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to any finite subtype containing the support of `x`.
* `Projectivization.mulHeight` and `Projectivization.logHeight` on
  `Projectivization K (ι → K)` (assuming `Finite ι`). This is the height of a point
  on projective space (with fixed basis).

## Main results

We set up an instance of `AdmissibleAbsValues` for number fields
(see [__NumberFields.lean__](Heights/NumberFields.lean)).

Apart from basic properties of `mulHeight₁` and `mulHeight` (and their logarithmic counterparts),
we also show (using the implementation in [Basic.lean](Heights/Basic.lean)):
* The multiplicative height of a tuple of rational numbers consisting of coprime integers
  is the maximum of the absolute values of the entries
  (see `Rat.mulHeight_eq_max_abs_of_gcd_eq_one` in [__Rat.lean__](Heights/Rat.lean)).
* The height on projective space over `ℚ` satisfies the *Northcott Property*:
  the set of elements of bounded height is finite (see
  `Projectivization.Rat.finite_of_mulHeight_le` and `Projectivization.Rat.finite_of_logHeight_le`
  in [__Rat.lean__](Heights/Rat.lean)).
* The height on `ℚ` satisfies the *Northcott Property* (see `Rat.finite_of_mulHeight_le` and
  `Rat.finite_of_logHeight_le` in [__Rat.lean__](Heights/Rat.lean)).

## Further developments

* In [__Descent.lean__](Heights/Descent.lean) we provide a proof of the "infinite descent"
  part of the *Mordell-Weil Theorem*, i.e., the implication
  "`G/n•G` finite ⇒ `G` finitely generated", assuming there is a suitable kind
  of height function on the additive commutative group `G`. See (the additivized version of)
  `CommGroup.fg_of_descent`.

## Work in progress

* In [__MvPolynomial.lean__](Heights/MvPolynomial.lean) we develop a proof for general
  upper and lower bounds on the `mulHeight` of the image of a tuple under a tuple
  of homogeneous polynomial maps of the same degree.