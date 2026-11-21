import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FixedLineProofA

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem fixed_line_exists : FixedLine :=
  fixedLine_proof_A

end PI.WGB
