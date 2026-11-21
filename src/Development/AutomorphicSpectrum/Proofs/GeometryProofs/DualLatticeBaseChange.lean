import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModels
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHolds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dual_baseChange_fractionField : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) :=
  @PositivityTheory.Xgn.exists_dual_base_change

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
