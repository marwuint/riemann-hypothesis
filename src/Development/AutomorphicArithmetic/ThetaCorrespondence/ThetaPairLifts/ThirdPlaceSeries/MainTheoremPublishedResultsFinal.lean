import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonvanishingFromTruePack
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevTruePackOfPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePackOfBWitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PuNZMemberStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremFromPublishedResultsAltAltAltAltAlt

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem miStar_row_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hDiag hL p hRX hPt
  have hTrue : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b)) := by
    refine hPt.imp fun κ K β c b _ _ hl hP => ?_
    obtain ⟨q, b', ⟨w⟩, he⟩ := hl
    have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
        (_root_.GlobalTheory.Fam.BundlePointConditions t.2.2 → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt t.2.2)) → _root_.GlobalTheory.Fam.BundlePointConditions s.2.2 → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt s.2.2) := by
      rintro _ _ rfl h
      exact h
    exact key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he (fun hP' => _root_.GlobalTheory.T.true_pack_of_bundle_witness q b' w (hRX K q) hP') hP
  have hPu := _root_.GlobalTheory.T.puNZ_of_truePack hDiag hL p hTrue
  refine ((hPt.and hTrue).and hPu).imp fun κ K β c b _ _ _ H => ?_
  exact _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (_root_.GlobalTheory.Fam.packB_alt b) H.1.2 H.1.1.rS H.2
end GlobalTheory.Fam
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_published_results_final_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  first | exact @_root_.GlobalTheory.Fam.miStar_row_alt_alt | exact _root_.GlobalTheory.Fam.miStar_row_alt_alt | (intros; apply _root_.GlobalTheory.Fam.miStar_row_alt_alt <;> assumption)
end
end
