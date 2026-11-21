import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

open AddMonoidAlgebra

namespace ReciprocityTheory.ChartRestriction.G.Semi

instance twoUniqueSums_of_free (X : Type*) [AddCommGroup X] [Module.Free ℤ X] :
    TwoUniqueSums X :=
  (AddEquiv.twoUniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance

end ReciprocityTheory.ChartRestriction.G.Semi
