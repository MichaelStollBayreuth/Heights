import Mathlib.NumberTheory.Height.Instances
import Heights.Basic
/-!
# Instances of AdmissibleAbsValues

We provide instances of `Height.AdmissibleAbsValues` for

* algebraic number fields.

## TODO

* Fields of rational functions in `n` variables.

* Finite extensions of fields with `Height.AdmissibleAbsValues`.

-/

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K]

variable  [NumberField K]

/-- This is the familiar definition of the multiplicative height on tuples
of number field elements. -/
lemma mulHeight_eq {ι : Type*} (x : ι → K) :
    mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, mulHeight, prod_archAbsVal_eq,
    prod_nonarchAbsVal_eq fun v ↦ ⨆ i, v (x i)]

end NumberField
