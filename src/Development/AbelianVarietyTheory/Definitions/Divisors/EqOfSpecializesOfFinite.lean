import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.ArInt GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

structure ArMod (D : ℕ) where

  k : Type
  [ring : CommRing k]

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp k
  av : IsArithVar p D

attribute [instance] ArMod.ring ArMod.int

abbrev GeomPt {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (ι : k →+* AlgebraicClosure ℚ) : Type :=
  GlobalTheory.Points.PtsOver p (spMap ι)

abbrev GeomPt.base {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : k →+* AlgebraicClosure ℚ}
    (z : GeomPt p ι) : X :=
  z.1 (IsLocalRing.closedPoint (AlgebraicClosure ℚ))

abbrev GeomPt.push {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}
    {ι : k →+* AlgebraicClosure ℚ} (π : X' ⟶ X) (hπ : π ≫ p = q) (z : GeomPt q ι) : GeomPt p ι :=
  GlobalTheory.Points.PtsOver.map π hπ _ z

section Points

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k} {ι : k →+* AlgebraicClosure ℚ}

theorem GeomPt.base_push (π : X' ⟶ X) (hπ : π ≫ p = q) (z : GeomPt q ι) : (z.push π hπ).base = π z.base := rfl

end Points

variable {D : D7} {Y : ShimX D.what₂.Tau}

namespace ProjEx

end ProjEx

end GlobalTheory.Mean4O
