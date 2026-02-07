import Heights.BasicWithTypes
import Mathlib.NumberTheory.NumberField.ProductFormula

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

section number_field

open NumberField Height

noncomputable
instance NumberField.instAdmissibleAbsValues {K : Type*} [Field K] [NumberField K] :
    AdmissibleAbsValues K where
  ArchAbsVal := InfinitePlace K
  archAbsVal v := v.val
  archAbsVal_fintype := inferInstance
  weight := InfinitePlace.mult
  weight_pos _ := InfinitePlace.mult_pos
  NonarchAbsVal := FinitePlace K
  nonarchAbsVal v := v.val
  strong_triangle_ineq := FinitePlace.add_le
  mulSupport_nonarchAbsVal_finite := FinitePlace.mulSupport_finite
  product_formula := prod_abs_eq_one

end number_field
