import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section
namespace GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiUnitOn_iff_interior (D : Out.DegPre R) (χ : D.X) (U : Set (Sp R)) :
    PsiUnitOn D χ U ↔ PsiUnitOn D χ (interior U) :=
  ⟨fun h j V hV hU => h j V hV (hU.trans interior_subset),
   fun h j V hV hU => h j V hV (interior_maximal hU V.isOpen)⟩

end GlobalTheory.DegActCheck
