import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTw
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTwMeas
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchur
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParamTieG (D : D7) (Cn : ℝ) : Prop :=
  0 < kaS D ∧ ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    ∃ h : ℝ, GapAtLeast (epsSH D.R) lam' h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

end Formalism.L2.S.Pv.Mom
