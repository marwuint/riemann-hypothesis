import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MemLeviGLOf

noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Frame

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J)

abbrev Bm : Matrix (Fin I.n) (Fin I.n) I.E := (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E)

abbrev Gm : Matrix (Fin I.n) (Fin I.n) I.E := (Bm Fr)ᴴ * I.J * Bm Fr

end Frame

end PI.IwaMeasEx.PD

end
