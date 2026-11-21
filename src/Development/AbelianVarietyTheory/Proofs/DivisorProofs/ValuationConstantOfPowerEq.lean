import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.ValConstOfPowEq

noncomputable section

section Units

variable {X Y Z : Scheme.{0}}

theorem res_pullU_comp (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {W : Z.Opens}
    (h : W ≤ g ⁻¹ᵁ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU g _ (pullU f U x)) = res (U := (g ≫ f) ⁻¹ᵁ U) h (pullU (g ≫ f) U x) := rfl

end Units

end
end GlobalTheory.ValConstOfPowEq
