import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InfWtEqInfOfStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory
theorem weightParam_of_pin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  intro hL D P
  exact _root_.GlobalTheory.WeightParamTie.weightParam_of_levelTied D P.M P.tp.tup P.H.level (_root_.GlobalTheory.EtaInfType.main D P.cf P.C P.tp P.chr) (_root_.GlobalTheory.T.infWt_eq_infOf_of_isDual D P.M P.tp.tup P.H)
end GlobalTheory
end
