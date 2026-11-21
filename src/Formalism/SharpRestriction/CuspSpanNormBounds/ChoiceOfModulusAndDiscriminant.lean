import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory TensorProduct
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.ChoiceOfModulusAndDiscriminant

open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_branch

def adm6 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_wigner

end Formalism.MainNotions.ChoiceOfModulusAndDiscriminant
