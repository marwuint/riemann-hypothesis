import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.HereditaryPositivity
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialLemmaE
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.FormalDegreeBessel.FinalIO
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

namespace Formalism.MainNotions

theorem RadialRules.condition_iff_additive_maps (D : Formalism.BasicNotions.D7) : RadialRules.adm5 D ↔ ChoiceOfModulusAndDiscriminant.adm5 D := Iff.rfl
theorem RadialRules.residualIrreducibility_forms_equivalent (D : Formalism.BasicNotions.D7) : RadialRules.adm6 D ↔ ChoiceOfModulusAndDiscriminant.adm6 D := Iff.rfl

end Formalism.MainNotions
