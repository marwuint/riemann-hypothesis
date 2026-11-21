import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PeriodMapPresentation

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Fibre

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))

abbrev univG : Over Xo.X := Xo.univ.t.G

end Fibre

theorem incl_over (l : Level H) : (KA l).val.toRingHom (baseKA l).ρ = H.rt0 := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
