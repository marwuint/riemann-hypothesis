import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousDefiniteThetaIntegralVectorForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModerateGrowthDefiniteThetaIntegralVectorForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiplicitySpaceAllLevelsValuesSmoothCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivariance
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgree
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaMod
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_theta_mod_of_is_canon : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  first | exact @_root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon | exact _root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon | (intros; apply _root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon <;> assumption)
end
