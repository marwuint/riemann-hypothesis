import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesAcrZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForD

set_option backward.isDefEq.respectTransparency false

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem out : Out l := out_of_rin l (CrystallineSemistableComparison.R.forD l)

end CrystallineSemistableComparison.D
