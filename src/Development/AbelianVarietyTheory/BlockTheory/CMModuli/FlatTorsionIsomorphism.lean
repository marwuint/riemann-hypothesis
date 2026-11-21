import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

structure GtTors (D : Out.DegPre R) (k : ℕ) (T : Over (Sp R)) where

  g : Out.GtPt D T

  tors : ∃ z : Out.GtPt D T, Out.GtPt.IsNsmul k g z ∧ z.IsZero

def torsScheme {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ) : Over S :=
  pullback ((𝟙 G : G ⟶ G) ^ k) η[G]

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism
