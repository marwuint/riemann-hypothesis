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

end Tan

end GlobalTheory.EigLetters
