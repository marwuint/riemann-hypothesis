import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassChartIso
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCechAlgebra
import GroundTheory.ArithmeticGeometry.ModularCurves.CechTwoOpens
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RiemannRoch
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Overlap

noncomputable abbrev varZY : HomRing W := var W 2 * var W 1

noncomputable abbrev mapZ : Away (homGrading W) (var W 2) →+* Away (homGrading W) (varZY W) :=
  awayMap (homGrading W) (var_mem W 1) rfl

@[instance_reducible]
noncomputable def overlapAlgebra : Algebra (Away (homGrading W) (var W 2)) (Away (homGrading W) (varZY W)) :=
  (mapZ W).toAlgebra

attribute [local instance] overlapAlgebra

instance : IsLocalization.Away
    (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1))
    (Away (homGrading W) (varZY W)) :=
  Away.isLocalization_mul (var_mem W 2) (var_mem W 1) rfl one_ne_zero

end Overlap

end Weierstrass

namespace Weierstrass

end Weierstrass

namespace Weierstrass

end Weierstrass

namespace Weierstrass

end Weierstrass

end GroundTheory.Arith.Modular
