import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

section Open

variable {S : Scheme.{0}} {X T : Over S}

def InOpen (U : X.left.Opens) (w : T ⟶ X) : Prop := w.left ⁻¹ᵁ U = ⊤

theorem inOpen_top (w : T ⟶ X) : InOpen ⊤ w := rfl

end Open

end GlobalTheory.WeilIntegral
