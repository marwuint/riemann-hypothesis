import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsArcFamilyPointWithFramesProof
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.CoordReduce

open ReciprocityTheory.ChartRestriction.G.Out in

theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

end GlobalTheory.CoordReduce
