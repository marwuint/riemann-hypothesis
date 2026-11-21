import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

section Norm
variable {K : Type} [Field K] (P : PolAV (Sp K))

def HasTrace (ψ : P.A ⟶ P.A) (t : ℤ) : Prop :=
  ∀ M : ℕ, (M : K) ≠ 0 → ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ M = 1) →
    (∀ z : baseOver (Sp K) ⟶ P.A, z ^ M = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℕ,
      (∀ i, y i ≫ ψ = linComb y fun l => B l i) → ((B.trace : ℕ) : ZMod M) = (t : ZMod M)

end Norm

end GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel
