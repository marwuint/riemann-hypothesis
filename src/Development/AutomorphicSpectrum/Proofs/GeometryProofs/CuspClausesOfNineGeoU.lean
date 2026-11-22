import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights.LowerBoundFree (AmpleOnGenericFibre)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {Ω : Type} [Field Ω]

theorem geomDeg_eq (hD : DegreeStatement) {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1))
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) : geomDeg W A d = genDeg W d A.a := by
  classical
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hD K ι W d (fun _ => A) hW (fun _ => hA)
  have hpot : pot (fun _ : Fin d => A) = fun (_ : Fin d) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq
