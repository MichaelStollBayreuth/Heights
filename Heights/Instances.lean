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

end NumberField
