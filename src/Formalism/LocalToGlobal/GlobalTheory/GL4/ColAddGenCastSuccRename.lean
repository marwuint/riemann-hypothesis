import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingLinkFamilyNormalised
import Formalism.BranchSandwichDivisors.StatementW

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree

theorem scaleMat_eq_zScale (n : ℕ) (T : ℝ) : scaleMat n T = Formalism.BranchingDeterminantCap.zScale n (Real.sqrt T) := rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
