import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace PositivityTheory.JLift

variable {R : Type} [CommRing R] {I : Ideal R} {X₀ : Scheme.{0}}

structure Pt (κ : DividedPowers I) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) : Type 1 where

  T : Thick κ s₀

  y : Sp T.B ⟶ X.left
  w : y ≫ X.hom = spMap (algebraMap R T.B)
  red : spMap T.π ≫ y = T.x ≫ i

variable {κ : DividedPowers I} {s₀ : X₀ ⟶ Sp R} {X : Over (Sp R)} {i : X₀ ⟶ X.left}

end PositivityTheory.JLift
