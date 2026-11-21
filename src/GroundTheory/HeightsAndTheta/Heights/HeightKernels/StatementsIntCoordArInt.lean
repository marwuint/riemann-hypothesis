import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordArInt.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (_ : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks T))) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm Ab → IsSectionOn Q Ab s →
    arInt (Q.comap (intCoordSubst A)) (intCoordSubst B s) (intCoordLine B ⟨A, hBA⟩ Ab)
        (fun j => intCoordLine B ⟨A, hBA⟩ (L j)) =
      arInt Q s Ab L

end

end GroundTheory.Heights₂.Heights
