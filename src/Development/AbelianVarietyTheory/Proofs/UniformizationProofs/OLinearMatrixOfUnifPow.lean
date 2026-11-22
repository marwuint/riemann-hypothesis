import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProductUniformizationTorusIsPower

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowMatrixLinear

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end General

local instance splitTorus_isCommMonObj (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

end PowMatrixLinear

end GlobalTheory
