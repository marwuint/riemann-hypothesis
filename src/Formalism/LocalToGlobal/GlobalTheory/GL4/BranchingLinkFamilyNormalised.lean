import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink
import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

def shiftW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := fun i j h => by have := lam.anti h; simp only; omega

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
