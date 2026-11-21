import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

namespace BiextCheck

open SplitTorus (bcMap bcMap_hom)

variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem connectedSpace_torus (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    ConnectedSpace (splitTorus S X).left :=
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  GroupConn.connectedSpace_of_section (splitTorus S X).hom (η : 𝟙_ (Over S) ⟶ splitTorus S X).left (Over.w _)

abbrev SQ : Scheme.{0} := Spec (CommRingCat.of ℚ)

instance : ConnectedSpace (splitTorus SQ ℤ).left := connectedSpace_torus _ _

end BiextCheck

end GlobalTheory.UU
end
