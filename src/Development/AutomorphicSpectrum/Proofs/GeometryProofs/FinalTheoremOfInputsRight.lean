import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpHodgeTiedHolds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidance
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerVolumeTheorem
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveStatementHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_volume_of_reduced : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → ThetaUnifAV → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hM hKF hSA hNS hResK hFHT hGaga hLLD hPB hHS hAn hNine hPts hAvoid hQ hZ hTheta
  have hGiven : Top.Given :=
    GlobalTheory.T.final_theorem_of_inputs_left hM hKF hSA hNS hResK hFHT hGaga hLLD hPB hHS hAn hNine
  have hW : Out.WeilSt := GlobalTheory.CompanionTheory.Ar.Link.weilSt
  have hHTD : GR.HodgeTateDatumStatement := GlobalTheory.CompanionTheory.Ar.GR.Top.main
  have hOrd : GR.OrdinaryCurveStatement := _root_.GlobalTheory.CompanionTheory.Ar.Link.ordinaryCurveStatement
  have hFam : Num.FamilyExistsPos := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds hFHT hQ hZ hHTD hOrd
  have hCmpSt : Cmp.CmpSt := _root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance hPB hAvoid hResK
  have hTied : HodgeComparisonCompatibility := _root_.GlobalTheory.CompanionTheory.Ar.CmpTied.cmpHodgeTied
  have hPair : Cmp.CmpPair := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair hPB hCmpSt hTied hTheta
  exact _root_.GlobalTheory.CompanionTheory.Ar.Top.goodTower_and_volume hGiven hPts hAvoid hW hFam hPair

end GlobalTheory.CompanionTheory.Ar.Top
