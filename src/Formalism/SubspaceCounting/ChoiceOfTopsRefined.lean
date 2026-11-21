import Formalism.SubspaceCounting.Statement
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers
import Formalism.SubspaceCounting.StatementB
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbits
import Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
import Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartB
import Formalism.SubspaceCounting.SubspaceCountingProofs.SubspaceCount
import Formalism.SubspaceCounting.SubspaceCountingProofs.TypeIIDown
import Formalism.SubspaceCounting.SubspaceCountingProofs.WalkSharp
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbitsRefined
import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
import Formalism.SubspaceCounting.SubspaceCountingProofs.MarkedRun
import Formalism.SubspaceCounting.SubspaceCountingProofs.DetDivides
import Formalism.SubspaceCounting.StatementW

namespace Formalism.G0.Top

theorem walkSharp : Formalism.G0.WalkSharp := Formalism.G0.walkSharp_true

theorem subspaceCount : Formalism.G0.SubspaceCount := Formalism.G0.countSubspacesEq

theorem typeIIDown : Formalism.G0.TypeIIDown := Formalism.G0.countAboveRangeCodimFormula

theorem markedRun : Formalism.G0.MarkedRun := Formalism.G0.marked_run

end Formalism.G0.Top
