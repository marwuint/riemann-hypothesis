import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Mathlib
import Formalism.LandauZeroFreeBounds.NoZeroComplex
import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
import Formalism.GL3MeanSquares.HookFormulaTorsion.MeanSquareOfPrimeNumberTheorem
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL

noncomputable section

namespace Formalism.MainNotions.Pk.SD

open Formalism.BasicNotions Formalism.MainNotions.S

structure RowsG {eps : ℝ} (Fm : FamP eps) : Prop where

  b5rec : ShortIntervalPrimes.FamilyPrimesAsPropTwoFive Fm
  b7rec : ShortIntervalPrimes.FamilyPrimesAsPropTwoSeven Fm

  familyRankBoundFourth : ShortIntervalPrimes.FamilyAdmittedLemmaFour Fm
  familyRankBoundEighth : ShortIntervalPrimes.FamilyTemperatureAsymptotic Fm

end Formalism.MainNotions.Pk.SD

end
