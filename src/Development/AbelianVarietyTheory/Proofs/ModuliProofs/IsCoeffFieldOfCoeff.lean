import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoefficientFieldBaseChange

noncomputable section

namespace GlobalTheory.ModuliCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Tor.Host E}

variable {D : Tor.Datum H} {l : Tor.Level H}

theorem isCoeffField_of_coeff (c : Tor.Coeff l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l c.F where
  fin := c.fin
  conj := c.conj
  root := c.zeta_mem

end GlobalTheory.ModuliCompare
