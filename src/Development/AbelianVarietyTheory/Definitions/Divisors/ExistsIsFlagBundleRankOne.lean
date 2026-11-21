import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def IsFlagBundle {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
    ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
      e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam.Pad

def rkB (ι : Type) (N j : ℕ) (a : ι × Bool) : ℕ := cond a.2 j (N - j)

end GlobalTheory.CovTest

end
