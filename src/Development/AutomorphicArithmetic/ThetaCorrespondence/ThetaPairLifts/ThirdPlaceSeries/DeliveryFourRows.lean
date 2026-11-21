import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeoAct
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEveryEmbeddingThirdKind
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRowFiresOfWeakCharacterisation
import Formalism.LocalRingCardinality.NFLeTwoMulTSq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecayStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaFireRowRecTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisationStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem atAll_fourRows' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
      AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  intro hDS hHC hRD hCW 𝒜 σ
  have hF : AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ := fun Fm hc x hx i =>
    _root_.GlobalTheory.T.indefinite_scale_theta_equality_alt hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B
  refine ⟨hF, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_identity_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).Rr (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.framesEx_of_realPins_indefinite_scale _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).pins
end GlobalTheory.Fc.Ind
end
end
