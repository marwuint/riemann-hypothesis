import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMember
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepConstantsTupleIndep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainLValueQuotientFactorization
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFirstStageLValuesPositive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoubling
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterOfOneNonzeroValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainRealZetaNonvanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistEulerFactorsRestoreProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpParameterOfTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpLowerBlockParameterProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem scalars_of_given_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hHCF hCRD hDSC hHCM hCW hHowe hUDG D G _ _ Pl0 T A Ks _ _ _ R F g hNG hHecke
  have soft : SoftQ D := _root_.GlobalTheory.ChainTw.softQ_all hHCF hCRD D
  have law : LevelLawQ D := _root_.GlobalTheory.ChainTw.TwLaw.levelLawQ D
  have restore : Restore D := _root_.GlobalTheory.ChainTw.restore_holds D
  have lfull : LFull D := _root_.GlobalTheory.ChainTw.lFull_holds D
  have upSpan : UpSpanQ D := _root_.GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of hDSC hHCM hCRD hCW D law
  have upAdj : UpAdjQ D := _root_.GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay hCRD D
  have upVal : UpVal D := _root_.GlobalTheory.ChainTw.upVal_of_span_adj D soft upSpan upAdj
  have exact : StepExactNS D :=
    _root_.GlobalTheory.ChainTw.ExactNS.stepExactNS D hHecke soft (_root_.GlobalTheory.ChainTw.Peel.qPeel_holds hUDG hCRD D) (_root_.GlobalTheory.ChainTw.LevIntProof.levInt D law)
  have lam : StepLam D := _root_.GlobalTheory.ChainTw.stepLam_of_ns D soft (_root_.GlobalTheory.ChainTw.upParQ_of_transfer hCRD hHowe D) (_root_.GlobalTheory.ChainTw.upQ_holds hCRD D)
    (_root_.GlobalTheory.LowerBlockParam.qOfVal D soft) upVal exact lfull restore
  have hX : RangeX R := _root_.GlobalTheory.ChainTw.rangeX_of_given R F g
  have chain : ∀ h : RangeX R, RChain R h := _root_.GlobalTheory.ChainTw.rChain_of_given R F g
  have zeta : RealZetaQ D := _root_.GlobalTheory.RealZetaTw.realZetaTw hHCM D (_root_.GlobalTheory.TwArch.archOnRecord_closed hDSC hHCM D)
  have unif : RUnif R hX := _root_.GlobalTheory.ChainTw.UnifFree.rUnif_of R F g hNG zeta restore hX (chain hX)
    (_root_.GlobalTheory.RealMeasOne.one_real_measure R F g chain hX) (_root_.GlobalTheory.ChainTw.VolScale.rVol_of_given R F g chain hX) (_root_.GlobalTheory.ChainTw.RNrmProof.rNrm_of_given R F g)
  exact _root_.GlobalTheory.ChainTw.scalars_of_realisation R F g hNG soft (_root_.GlobalTheory.LowerBlockParam.qOfVal D soft) (_root_.GlobalTheory.ChainTw.lPos_of_rapidDecay hCRD D) lfull lam hX
    (chain hX) (_root_.GlobalTheory.ChainTwNorm.normX R F g hX) unif (_root_.GlobalTheory.ChainTw.rowPar_of_chain hCRD R F g chain hX) (_root_.GlobalTheory.ChainTw.IPDictPf.main R F g)

end GlobalTheory.ChainTw
