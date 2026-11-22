import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AntisymmetricPerturbationHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem given_of_inputs : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → Top.Given :=
  fun hModel hKey hSAH hSegre hResK hFar hGaga hLLD hPB hHS hAn hNine =>
    ⟨hModel, hKey, hSAH, hSegre, hResK, _root_.GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds, hFar, hGaga, (_root_.GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel hLLD).1, hPB, hHS, hAn, hNine,
      _root_.GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds⟩

end GlobalTheory.CompanionTheory.Ar.Top
