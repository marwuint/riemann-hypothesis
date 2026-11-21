import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaJets

theorem jetsPh_all : ∀ D : D7, GL3Theta.jetsPh D := fun D =>
  Formalism.MainNotions.Ext.CutA.jetsPh_of' Formalism.MainNotions.Ext.CutA.jetsHigh_holds Formalism.MainNotions.Ext.CutA.jetsOne_holds
    Formalism.MainNotions.Ext.CutA.jetsTwo_holds D (_root_.GlobalTheory.ThetaCube.cube_addInt_beBiadd D).1 (_root_.GlobalTheory.CMEndo.endo_all D).2.1 (_root_.GlobalTheory.CMEndo.endo_all D).2.2

end GlobalTheory.ThetaJets
