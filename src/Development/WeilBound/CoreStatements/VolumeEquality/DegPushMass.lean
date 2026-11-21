import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVerticalTwistGenDeg
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariant
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement

noncomputable section

namespace SheetDecomposition

open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem muMass : MuMass := by
  intro hG hP E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or hII
  classical
  have : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
  obtain ⟨U, M, S, S', -, h0, ht, hS, hS', -⟩ := _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_regularisations_tied hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨Cd, rfl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight K J II _ Ω W Dc U h0 ht
  let X : ComponentSetting Dc ℤ (Fin 2 → ℤ) := ⟨Hd, Cd, M, S, hS, S', hS', 0, 0⟩
  have hA := (GlobalTheory.T.height_comparison_between_models hG hP K J II _ Ω W Dc Hd M M S S 0 hII hS hS).1
  have hL := (_root_.GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit II _ K J Ω W Dc ℤ (Fin 2 → ℤ) X 0 hII.1 hA).2
  have hSm := MuRegSmooth.proof HermExtend.proof (ProjSmoothAlong.proof HoloInjDerivInj.proof _root_.GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart)
    (VertFactorSmooth.proof VertFactorPos.proof) VertFactorPos.proof II _ K J Ω W Dc ℤ (Fin 2 → ℤ) X 0
  have hg := _root_.GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system ⟨II, hII⟩ hG.2.2.2.2.1
  refine tendsto_nhds_unique hL (tendsto_const_nhds.congr' ?_)
  filter_upwards [hSm] with t hs
  have hvert : ∀ p ∈ Dc.SB 0, p.Prime ∧ IsVerticalDivisorAt (mCoordIdeal Dc.y) p (Dc.vdeg p) (Dc.vnum p) (Dc.vden p) :=
    fun p hp => ⟨Dc.S_prime p (Finset.mem_filter.1 hp).1, Dc.vertical p (Finset.mem_filter.1 hp).1⟩
  have ha : (muReg X.H X.S 0 t).a = Hd.aMu + ∑ p ∈ Dc.SB 0, Dc.vdeg p := by
    rw [muReg, smoothRep_a]
    rfl
  rw [hg K J Ω Dc.y Dc.n _ Dc.arith hs, ha,
    VerticalTwistGenDeg.proof K J (mCoordIdeal Dc.y) Dc.n Hd.aMu (Dc.SB 0) Dc.vdeg Dc.vnum Dc.vden Dc.arith hvert]

end SheetDecomposition
