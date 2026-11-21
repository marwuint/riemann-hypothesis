import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie

attribute [local instance] Over.cartesianMonoidalCategory

section Extend

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

abbrev fstOver (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : DualNumber S →ₐ[R] S :=
  (Chart.fstD S).restrictScalars R

variable {S}

abbrev scaleOver (R : Type) [CommRing R] [Algebra R S] (s : S) : DualNumber S →ₐ[R] DualNumber S :=
  (Chart.scaleD s).restrictScalars R

end Extend

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie
