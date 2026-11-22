import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end One

def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
