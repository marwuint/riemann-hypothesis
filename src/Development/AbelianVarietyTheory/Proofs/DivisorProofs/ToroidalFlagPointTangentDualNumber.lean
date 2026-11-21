import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigLetters

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

def tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : TanM x0 t.G :=
  mkT (ovT hv) (smT_zero_ovT hv)

theorem tv_tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : tv (tvG hv) = ovT hv := rfl

end Tan

end GlobalTheory.EigLetters
