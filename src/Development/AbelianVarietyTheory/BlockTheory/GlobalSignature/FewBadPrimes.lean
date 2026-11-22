import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX

variable {R : Ranks}

def condE (H : Host R) : ℕ := H.QS * H.q * H.d

end GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

end
