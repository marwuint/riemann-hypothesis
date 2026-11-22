import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.FlagZ.Taut

variable (ι : Type) [Fintype ι] (N : ℕ)

abbrev stdE : (Sp ℤ).Modules := (HermVB.std (𝟙 (Sp ℤ)) N).E

variable {N} in

def colSec {A : Type} [CommRing A] (x : Sp A ⟶ Sp ℤ) (g : Matrix (Fin N) (Fin N) A) (j : Fin N) :
    Γ((Scheme.Modules.pullback x).obj (stdE N), ⊤) :=
  ∑ i, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (g i j) •
    GlobalTheory.QCoh.pullbackSections x (stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)

end GlobalTheory.FlagZ.Taut
