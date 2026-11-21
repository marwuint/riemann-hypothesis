import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageInertiaOfPotentialGoodReduction
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPotentialGoodReductionOfFiniteImageInertia
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem potentialGoodReduction_of_neronOggShafarevich :
    GlobalTheory.Published.NeronOggShafarevichSt → GlobalTheory.Published.PotentialGoodReductionSt := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl
  exact ⟨_root_.GlobalTheory.finite_image_inertia_of_potentialGoodReduction h R K Ω V hV A hA l hl, _root_.GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia h R K Ω V hV A hA l hl⟩

end GlobalTheory
