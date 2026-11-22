import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelongStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I4

theorem contractMixed_closed : ContractMixedStatement :=
  have hIntZero : Inter.PFIntZero.Statement :=
    Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)
  have hVert : Inter.PFVert.Statement :=
    Inter.PFVert.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _) Targets.contractMixedField
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    hIntZero hVert

theorem arithIntersectionSystem_of_poincareLelong_resK :
    GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := fun hPL hRK =>
  Targets.ArithIntersectionSystem.of_found
    (GlobalTheory.T.intersection_exists_of_poincare_lelong hPL (_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hRK))
    (_root_.GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord (_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hRK)).2
    contractMixed_closed

end GlobalTheory.CompanionTheory.Ar.Pub
