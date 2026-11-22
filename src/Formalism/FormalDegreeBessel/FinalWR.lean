import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRPres
import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
import Mathlib
import Formalism.YangianSpanCharacter.StatementT

noncomputable section

namespace Formalism.QuantumDeterminants

theorem presOps : PresOps := preserved_operators_holds
theorem linOps : LinOps := linear_operators_holds
theorem weylFun : WeylFun := weyl_functional_holds
theorem commFun : CommFun := commuting_functional_holds

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Formalism.QuantumDeterminants
