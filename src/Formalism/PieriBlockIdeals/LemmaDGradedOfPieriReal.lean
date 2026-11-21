import Mathlib
import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.StatementLP
import Formalism.PieriBlockIdeals.StatementLR

namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def ColumnsRealOfPieriReal : Prop := LR.PieriReal → LR.ColumnsReal

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
