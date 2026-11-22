import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e))) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (_root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  unfold LieModel.Lifts at h
  rw [Category.comp_id] at h
  exact h

end GlobalTheory.CompanionTheory.Ar
