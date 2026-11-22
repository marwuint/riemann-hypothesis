import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.AntitoneOfMemGtBox
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Branch
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

theorem stripsMem : StripsMem := Formalism.InvariantFactorPaths.GelfandTsetlinBases.strips_mem
theorem gtPieri : GTPieri := Formalism.InvariantFactorPaths.GelfandTsetlinBases.gelfand_tsetlin_pieri
theorem stdCountGT : StdCountGT := Formalism.InvariantFactorPaths.GelfandTsetlinBases.standard_count_gt
theorem countCont : CountCont := countCont_of stripsMem gtPieri stdCountGT
theorem countPAll : CountPAll := countPAll_of countCont

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
