import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink
import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

theorem intQ_apply (r n : ℕ) (q : MvPolynomial (Fin r × Fin n) ℤ) : intQ r n q = map (Int.castRingHom ℚ) q := rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
