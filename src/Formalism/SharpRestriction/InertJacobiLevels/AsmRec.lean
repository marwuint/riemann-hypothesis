import Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
import Formalism.SharpRestriction.InertJacobiLevels.TiesAsm
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev Core : Type 1 := Σ R : Ranks, Host R × (↥(R.Psi) → HCParam R)

end Formalism.MainNotions.Inhab

end
