import Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.TiesAsm
import Formalism.SharpRestriction.GrowthBounds.DefsInst

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

def gdOf (R : Ranks) : GC.GD := ⟨R, ⟨∅, ∅, 0, fun _ => PrimeClass.splitK⟩, fun _ => 0⟩

def glOf (R : Ranks) (sc : Scale) (Sc eta : ℝ) : GC.GParameters (gdOf R) := ⟨sc, Sc, eta⟩

end Formalism.MainNotions.Inhab

end
