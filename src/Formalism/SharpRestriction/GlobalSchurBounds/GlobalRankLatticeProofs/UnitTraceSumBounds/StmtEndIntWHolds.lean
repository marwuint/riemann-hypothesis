import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpInertOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
import Mathlib
import Formalism.PeriodIntegrals.OkpInert
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime

namespace Formalism.MainNotions.Ext

theorem okpInertG_holds : OkpInertG := PI.OkpW.okpInert_main

theorem inertPrime_holds : InertPrime := isPrime_span_of_jacobi_neg_one

theorem okpInert_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.okpInert D := okpInert_of okpInertG_holds inertPrime_holds D

end Formalism.MainNotions.Ext
