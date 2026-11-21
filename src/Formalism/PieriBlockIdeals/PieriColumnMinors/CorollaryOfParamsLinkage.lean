import Formalism.PieriBlockIdeals.StatementDown
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.ColumnsPieriSkeleton
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealOfSkeleton
import Formalism.PieriBlockIdeals.PieriColumnMinors.IrreducibleGeneration

namespace Formalism.CohomologicalDescent.Down

theorem hG : LD.LemmaDGraded :=
  LR.real_of_pieri LPR.pieri_real_form (ColumnMinorsFromPieri.columns_real_of_pieri_real LPR.pieri_real_form)

theorem inclusion_w_real_holds : InclWReal := ShortWeightBounds.inclusion_w_real_holds hG

end Formalism.CohomologicalDescent.Down
