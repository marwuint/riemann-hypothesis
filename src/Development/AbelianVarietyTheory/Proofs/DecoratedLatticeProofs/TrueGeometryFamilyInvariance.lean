import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActRamifiedColumnsVanishingStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankOneGramRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescalingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistIdentity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndex
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelPreservesRamifiedFormsLiveCharts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsLow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLattStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDense
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

theorem GlobalTheory.Fam.finComb3 (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' c'' : WO S T →₀ ℂ) :
    GlobalTheory.SeeSaw.IsFinComb c → GlobalTheory.SeeSaw.IsFinComb c' → GlobalTheory.SeeSaw.IsFinComb c'' → ∃ d, GlobalTheory.SeeSaw.IsFinComb d ∧
      ∀ f, comb ψ S T d f = comb ψ S T c (comb ψ S T c' (comb ψ S T c'' f)) := by
  intro h h' h''
  obtain ⟨c1, hs1, he1⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c' c''
  obtain ⟨d, hs, he⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c c1
  have key : ∀ x y : WO S T, Matrix.map x (infPart D) = 0 → Matrix.map y (infPart D) = 0 →
      Matrix.map (x + y) (infPart D) = 0 := by
    intro x y hx hy
    rw [Matrix.map_add _ (fun a b => (infPart D).map_add a b), hx, hy, add_zero]
  refine ⟨d, fun w hw => ?_, fun f => by rw [he, he1]⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hs w hw
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hs1 y hy
  exact key _ _ (h x hx) (key _ _ (h' y1 hy1) (h'' y2 hy2))

