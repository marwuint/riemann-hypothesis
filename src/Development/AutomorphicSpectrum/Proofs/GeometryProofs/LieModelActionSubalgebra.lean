import Mathlib
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie

theorem lieModel_along_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M₀ B _ act ρ₀ h₀ O _ _ R x hx
  subst hx
  obtain ⟨L, iL, mL, ⟨M⟩⟩ := lieModel_exists X G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G R x L M B act.act act.hom act.one act.mul act.add
  have hsm : ∀ (a : R) (t : Li), a • t = algebraMap R Ω a • t := fun _ _ => rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ x = spMap (algebraMap R Ω) ≫ x := rfl
  have ex : ∀ e, ∃ t, M₀.pt t = LieTangent.epsBase (algebraMap R Ω) hφ ≫ M.pt e :=
    fun e => M₀.onto _ (LieTangent.isTanAt_base _ hφ (M.tan e))
  choose f hf using ex
  let j : L →ₗ[R] Li :=
    { toFun := f
      map_add' := fun a b => M₀.inj (by rw [M₀.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M₀.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          LieTangent.base_scale, Category.assoc]) }
  have hl : ∀ v, (M₀.pt (j v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left := fun v => by
    change (M₀.pt (f v)).left = _
    rw [hf]
    rfl
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X G R x L M
  refine ⟨L, iL, mL, M, ρ, j, h1, h2, hρ, h3 Ω Li M₀ j hl, hl, fun a v => M₀.inj ?_⟩
  change M₀.pt (f (ρ a v)) = M₀.pt (ρ₀ a (f v))
  rw [h₀ a, hf, hf, hρ a, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie
