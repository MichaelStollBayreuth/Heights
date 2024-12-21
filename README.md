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

In the context of the product formula (and to allow for some flexibility as to normalizations),
it makes sense to weaken the triangle inequality for archimedean absolute values from
`|x+y| ≤ |x| + |y|` to `|x+y| ≤ C_v * max |x| |y|` for some constant `C_v`.
(The usual triangle inequality implies this with `C_v = 2`, but it will still be true
for powers of an archimedean absolute value.) The main motivation is that we want
to allow the square of the standard absolute value on a complex embedding of a number field.
The requirement "all but finitely many absolute values are non-archimedean" then translates into
`C_v = 1` for all but finitely many `v`. A disadvantage is that we cannot use the existing
`AbsoluteValue` type (because that requires the usual triangle inequality). Instead, we
use `K →*₀ ℝ≥0` together with the weak triangle inequality above. A further disadvantage
is that the obtain less-than-optimal bounds for heights of sums with more than two terms,
e.g., we get that `H_ℚ (x + y + z) ≤ 4 * H_ℚ x * H_ℚ y * H_ℚ z` instead of `≤ 3 * ⋯`.

A possible alternative could be to use a family of `AbsoluteValue`s together with a family
of exponents `e_v` such that the product formula holds in the form `∏ v, |x|_v ^ e_v = 1`.
Disadvangtages of this approach are the mostly unnecessary additional degrees of freedom
in the pairs `(|·|_v, e_v)` and that we need to separately encode the requirement that
all but finitely many of the absolute values are non-archimedean.

We realize the first alternative above via the class `AdmissibleAbsValues K`.

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