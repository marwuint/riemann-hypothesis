import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieLineDegreeOfEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisation
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

theorem GlobalTheory.LamF.lamDegSt_logOm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re :=
  fun hΘ hL =>
    _root_.GlobalTheory.LamF.lamDegSt_of_degSt
      (_root_.GlobalTheory.CM.PureDeg.degSt (_root_.GlobalTheory.cmCurve_of_uniformisation hΘ hL.polBaseChange _root_.GlobalTheory.semiAbelian_hom_extends_uniquely_dvr) hΘ hL _root_.GlobalTheory.semiAbelian_hom_extends_uniquely_dvr) hΘ hL
