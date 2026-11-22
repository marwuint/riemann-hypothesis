import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.MonomialMeanResidues.FilteredDegree
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GoodOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.LiftDataTimeEqWeightTime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrasadVolumeSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetOfThickPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.WeilBound.CoreStatements.ArcCellEmbeddings.TraceVolumeDimensionStandard
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateCokernelSharp

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact : HT.FarguesExact → HT.FarguesHodgeTate := by
  intro hE p _ C _ _ _ v O _ _ _ hv hp hc G
  refine ⟨fun κ hκ w => HT.hodge_tate_cokernel_sharp p C v O hv hp hc G κ ?_ w, hE p C v O hv hp hc G⟩
  split_ifs at hκ with h2
  · subst h2
    have h4 : (4 : C) = ((2 : ℕ) : C) * ((2 : ℕ) : C) := by norm_num
    rw [h4, map_mul] at hκ
    have h1 : (2 - 1 : ℕ) = 1 := rfl
    rw [h1, pow_one]
    exact hκ.trans (mul_le_of_le_one_left' hp.le)
  · exact hκ
