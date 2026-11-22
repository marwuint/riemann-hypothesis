import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSPos
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainOntoCuspFormsOfInnerProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralBottomDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvariance
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListProdMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamUnitaryHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatios
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpecStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPinsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReading
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownward
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsMemBaseChainStageZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremFromPublishedResultsAltAltAltAlt

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop
namespace GlobalTheory.Fam
theorem miAt_of_truePack_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.TruePackAlt W → 1 ≤ D.R.rS → PuNZ D → _root_.GlobalTheory.Fam.RealPackageCondition W := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 D L hT Gi Gl Kc Yd cX ex W hW hR hP
  cases hW with
  | mk W hA =>
    exact _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 W hA hR hP
end GlobalTheory.Fam
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.TruePackAlt W → 1 ≤ D.R.rS → PuNZ D → _root_.GlobalTheory.Fam.RealPackageCondition W := by
  first | exact @_root_.GlobalTheory.Fam.miAt_of_truePack_alt_alt | exact _root_.GlobalTheory.Fam.miAt_of_truePack_alt_alt | (intros; apply _root_.GlobalTheory.Fam.miAt_of_truePack_alt_alt <;> assumption)
end
end
