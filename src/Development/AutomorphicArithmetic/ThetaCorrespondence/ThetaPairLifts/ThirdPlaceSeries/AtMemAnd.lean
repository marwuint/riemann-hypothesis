import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeSplitOneOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvParamsOfRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLResidueTypePrimeDvdCardTypeGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfJointCond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLabelDeterminant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem atMem_mono {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem atMem_and' {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
theorem atMem_mono_of_colPin {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
