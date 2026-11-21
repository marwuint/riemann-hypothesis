import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def VolNef : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → arVol L D = (a : EReal)

end GlobalTheory.Published
