import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTp
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitT
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpIntegrandLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRegAboveWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsMonoSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNMixedExpand
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNVbInt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryNull
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.HtBoundary
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNbarLeviChartReg
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRefChartDisc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartMargin
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLeviLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds

noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
