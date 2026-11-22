import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocallyQuasiFiniteOfQuasiFiniteAt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.PowQuotient

variable {S S' : Scheme.{0}}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {n : ℕ} (a : Fin n → (G ⟶ H))
    (ha : ∀ i, IsMonHom (a i)) : IsMonHom (∏ i, a i) :=
  Finset.prod_induction a (fun z => IsMonHom z) (fun x y _ _ => isMonHom_mul x y) isMonHom_one fun i _ => ha i

end GlobalTheory.PowQuotient

namespace GlobalTheory

end GlobalTheory
