import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTw
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTwMeas
import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.BesselNVGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold psiGen psi ell ellA
  rw [Finset.mul_sum]

end Formalism.L2.S.Pv.Mom
