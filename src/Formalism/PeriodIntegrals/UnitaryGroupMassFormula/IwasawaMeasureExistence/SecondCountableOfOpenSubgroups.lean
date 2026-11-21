import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

noncomputable section

namespace PI.IwaMeasEx.Sk

open MeasureTheory Topology Filter Matrix
open scoped TensorProduct
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma

section Gf

variable (I : AutInst)

instance borelSpace_Gf : BorelSpace I.Gf := ⟨rfl⟩

end Gf

end PI.IwaMeasEx.Sk

end
