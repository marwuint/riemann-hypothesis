import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyConditional
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFSMass
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegreeIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHSMTransport
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKrullDimMatAct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGraphDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGramMono
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulePieceHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem

namespace PositivityTheory.LocalParametersCuspidal.MB.HSM

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
  ReciprocityTheory.ChartRestriction.G.AI.I1

theorem theoremHSMBlock (hAIS : ArithIntersectionSystemStatement) (hResK : ResK.ResKStatement) :
    TheoremHSMBlock.Statement := by
  have hGr : GraphStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.graphStatement
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hRes : ResExistsStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hResK
  have hPts : PtsIntegrableStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hResK
  have hPF : PFCoordStatement := (_root_.GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord hRes).2
  have hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι := Targets.existsUniqueAll
  have hGF : GenFibreExistsStatement := Targets.genFibreExists
  have hIso : IsomInvariance.Statement := IsomInvariance.proof (Inter.RatR.proof hPts)
  have hCM : ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr hIso GraphIsometric.proof
  have hDim : FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hDG : Inter.DegreeGeneric.Statement :=
    GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hPts (Inter.PtsAbsMeasurable.proof hRes)
  have h6 : ProjFrameGraphDeg.Statement :=
    ProjFrameGraphDeg.proof hEU ProjFrameFibrePt.full ProjFrameFibreDeg.full
  have h15 : GraphChangeOfModel.Statement :=
    GraphChangeOfModel.proof hAI3 hGr hGF hEU hIso GraphIsometricForms.full
  have h16 : BlockGraphDeg.Statement :=
    BlockGraphDeg.proof hGr BlockGraphImage.full hGF hDim hEU Closed.Inter.ChartRankAdjoin
      BlockGraphFibreRatio.full
  have h18 : VeroneseGraphDeg.Statement :=
    VeroneseGraphDeg.proof hGr VeroneseGraphImage.full hDim hEU
  exact TheoremHSMBlock.of_open TwoBlockPieceIndex.proof TwoBlockModuleFinite.proof
    ModulePieceHilbert.proof TwoBlockModuleCycle.proof hPF hCM h6
    (HSMTransport.proof KrullDimMatAct.proof)
    (ResolutionDegree.proof PullFSExtension.full ProjFSMass.proof) ResolutionMixedBridge.full
    (BlockResolutionImageSup.proof ChartSupBound.full)
    (BlockResolutionDegreeIntegral.proof (GenDegGeomDeg.proof hDG)) BlockResolutionMixedBridge.full
    hAbs BlockImageInverse.proof h15 h16 VeroneseGramMono.proof h18

end PositivityTheory.LocalParametersCuspidal.MB.HSM
