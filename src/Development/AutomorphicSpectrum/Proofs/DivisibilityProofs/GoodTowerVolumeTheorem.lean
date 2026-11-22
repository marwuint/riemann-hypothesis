import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGoodRootTower
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VolumeTheoremOfInputs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstantsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFargues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidance
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_and_volume :
    Top.Given → PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → Out.WeilSt → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos →
      Cmp.CmpPair → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hG hPts hAv hW hFam hPair
  have hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have hFHT : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hGaga : Flat.GagaSections := hG.2.2.2.2.2.2.2.1
  have hPB : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hA0 := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hGaga
  have hA1 := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga hR hGaga
  refine ⟨?_, ?_⟩
  · intro E _ _ _ H D Xo l c Y _ hgl hs hp hq
    exact _root_.GlobalTheory.CompanionTheory.Ar.TopTower.exists_good_tower hG hW hA0 hA1 E H D Xo l c Y hgl hs hp hq
  · exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs hG hPts hW (GlobalTheory.T.exists_geometric_height_constants hG hW _root_.GlobalTheory.CompanionTheory.Ar.Fl.flatDegree) (_root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos hFam)
      (_root_.GlobalTheory.CompanionTheory.Ar.Num.trivFlagOnHodge_of_fargues hFHT) _root_.GlobalTheory.CompanionTheory.Ar.Fl.flatDegree _root_.GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut hPair (_root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance hPB hAv hR)

end GlobalTheory.CompanionTheory.Ar.Top
