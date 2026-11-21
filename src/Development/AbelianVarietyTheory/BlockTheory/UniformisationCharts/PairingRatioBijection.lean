import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.TorusPointForms

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

variable {D F}

variable (R F) in

abbrev TKF : Over (Spec (CommRingCat.of (FractionRing R))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))

variable (P : PolAV (Spec (CommRingCat.of (FractionRing R))))

variable (F) in

abbrev SecA (k : ℕ) : Type := LB.Sec (LPow P.A P.L (k : ℤ) (TKF R F))

variable {P}

variable (D F)

variable (P)

end GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
