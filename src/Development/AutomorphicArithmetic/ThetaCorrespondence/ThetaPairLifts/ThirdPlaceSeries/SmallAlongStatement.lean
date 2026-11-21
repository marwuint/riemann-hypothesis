import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PassIn3OfRows
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfSEEofTT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourFRLeMinGOfSizeG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlong

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  exact @_root_.GlobalTheory.Fc.Ind.small_along_alt
end
